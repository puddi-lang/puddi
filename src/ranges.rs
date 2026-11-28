//! Value ranges of integer locals, used by code generation to drop overflow checks that
//! cannot fail, such as `i += 1` inside `while i < n`.
//!
//! Facts come from the condition of an `if` (which is also how `while` loops are lowered)
//! and hold inside the branch until the local is assigned. Before a loop is generated,
//! every local the loop assigns loses its facts, since a later iteration runs the start
//! of the body after the assignment.

use std::collections::{HashMap, HashSet};

use crate::ir::{Arm, Expr, ExprKind, Lit, LocalId, LocalInfo, Pat, PatKind, PrimOp, Stmt};
use crate::types::{IntTy, Ty};

pub type Range = (i128, i128);

#[derive(Default)]
pub struct Ranges {
    known: HashMap<LocalId, Range>,
    /// every local assigned so far, used to find what a branch assigned
    killed: HashSet<LocalId>,
}

impl Ranges {
    pub fn kill(&mut self, id: LocalId) {
        self.known.remove(&id);
        self.killed.insert(id);
    }

    /// Facts before entering a branch, and the assignments seen so far.
    pub fn save(&self) -> (HashMap<LocalId, Range>, HashSet<LocalId>) {
        (self.known.clone(), self.killed.clone())
    }

    /// Back to the facts of `save`, minus the locals assigned since.
    pub fn restore(&mut self, saved: &(HashMap<LocalId, Range>, HashSet<LocalId>)) {
        let assigned: Vec<LocalId> = self.killed.difference(&saved.1).copied().collect();
        self.known = saved.0.clone();
        for id in assigned {
            self.known.remove(&id);
        }
    }

    /// Adds what is known when `cond` evaluated to `truth`.
    pub fn assume(&mut self, cond: &Expr, truth: bool, locals: &[LocalInfo]) {
        let mut assigned = HashSet::new();
        assigned_in(cond, &mut assigned);
        if !assigned.is_empty() {
            return;
        }
        let mut facts = Vec::new();
        cond_facts(cond, truth, locals, &mut facts);
        for (id, lo, hi) in facts {
            let e = self.known.entry(id).or_insert((i128::MIN, i128::MAX));
            *e = (e.0.max(lo), e.1.min(hi));
        }
    }

    /// Forgets the locals that `body` assigns (before generating a loop).
    pub fn enter_loop(&mut self, body: &Expr) {
        let mut assigned = HashSet::new();
        assigned_in(body, &mut assigned);
        for id in assigned {
            self.kill(id);
        }
    }

    /// The range of an integer expression's value, if narrower than its type.
    pub fn of(&self, e: &Expr, it: IntTy) -> Range {
        let full = (it.min(), it.max());
        match &e.kind {
            ExprKind::Lit(Lit::Int(v)) => (*v, *v),
            ExprKind::Local(id) => self.known.get(id).map(|r| (r.0.max(full.0), r.1.min(full.1))).unwrap_or(full),
            ExprKind::Intrinsic(name, _, args) if name == "select" && args.len() == 3 => {
                let (a, b) = (self.of(&args[1], it), self.of(&args[2], it));
                (a.0.min(b.0), a.1.max(b.1))
            }
            _ => full,
        }
    }

    /// Whether `a op b` stays within `it`, so the overflow check can be left out.
    pub fn cannot_overflow(&self, op: PrimOp, it: IntTy, a: &Expr, b: &Expr) -> bool {
        let (x, y) = (self.of(a, it), self.of(b, it));
        let full = (it.min(), it.max());
        if x == full && y == full {
            return false;
        }
        let r = match op {
            PrimOp::Add => (x.0.checked_add(y.0), x.1.checked_add(y.1)),
            PrimOp::Sub => (x.0.checked_sub(y.1), x.1.checked_sub(y.0)),
            PrimOp::Mul => {
                let ps = [x.0.checked_mul(y.0), x.0.checked_mul(y.1), x.1.checked_mul(y.0), x.1.checked_mul(y.1)];
                if ps.iter().any(|p| p.is_none()) {
                    return false;
                }
                let ps: Vec<i128> = ps.iter().map(|p| p.unwrap()).collect();
                (ps.iter().min().copied(), ps.iter().max().copied())
            }
            _ => return false,
        };
        matches!(r, (Some(lo), Some(hi)) if lo >= full.0 && hi <= full.1)
    }
}

fn int_local(e: &Expr, locals: &[LocalInfo]) -> Option<(LocalId, IntTy)> {
    match (&e.kind, &e.ty) {
        (ExprKind::Local(id), Ty::Int(it)) if !locals[*id].boxed && locals[*id].capture.is_none() => Some((*id, *it)),
        _ => None,
    }
}

fn negate(op: PrimOp) -> Option<PrimOp> {
    Some(match op {
        PrimOp::Lt => PrimOp::Ge,
        PrimOp::Le => PrimOp::Gt,
        PrimOp::Gt => PrimOp::Le,
        PrimOp::Ge => PrimOp::Lt,
        PrimOp::Eq => PrimOp::Ne,
        PrimOp::Ne => PrimOp::Eq,
        _ => return None,
    })
}

fn mirror(op: PrimOp) -> PrimOp {
    match op {
        PrimOp::Lt => PrimOp::Gt,
        PrimOp::Le => PrimOp::Ge,
        PrimOp::Gt => PrimOp::Lt,
        PrimOp::Ge => PrimOp::Le,
        o => o,
    }
}

fn cond_facts(c: &Expr, truth: bool, locals: &[LocalInfo], out: &mut Vec<(LocalId, i128, i128)>) {
    match &c.kind {
        // `a && b` is lowered to `if a { b } else { false }`, `a || b` to `if a { true } else { b }`
        ExprKind::If(a, b, f) if truth && matches!(f.kind, ExprKind::Lit(Lit::Bool(false))) => {
            cond_facts(a, true, locals, out);
            cond_facts(b, true, locals, out);
        }
        ExprKind::If(a, t, b) if !truth && matches!(t.kind, ExprKind::Lit(Lit::Bool(true))) => {
            cond_facts(a, false, locals, out);
            cond_facts(b, false, locals, out);
        }
        ExprKind::Prim(PrimOp::Not, _, args) if args.len() == 1 => cond_facts(&args[0], !truth, locals, out),
        ExprKind::Prim(op, Ty::Int(_), args) if args.len() == 2 => {
            let Some(op) = (if truth { Some(*op) } else { negate(*op) }) else { return };
            if let Some((id, it)) = int_local(&args[0], locals) {
                bound(id, it, op, &args[1], out);
            }
            if let Some((id, it)) = int_local(&args[1], locals) {
                bound(id, it, mirror(op), &args[0], out);
            }
        }
        _ => {}
    }
}

/// What `local op other` tells about the local.
fn bound(id: LocalId, it: IntTy, op: PrimOp, other: &Expr, out: &mut Vec<(LocalId, i128, i128)>) {
    let (min, max) = (it.min(), it.max());
    let r = match (&other.kind, op) {
        (ExprKind::Lit(Lit::Int(c)), PrimOp::Lt) => (min, c - 1),
        (ExprKind::Lit(Lit::Int(c)), PrimOp::Le) => (min, *c),
        (ExprKind::Lit(Lit::Int(c)), PrimOp::Gt) => (c + 1, max),
        (ExprKind::Lit(Lit::Int(c)), PrimOp::Ge) => (*c, max),
        (ExprKind::Lit(Lit::Int(c)), PrimOp::Eq) => (*c, *c),
        // compared with any value of the same type
        (_, PrimOp::Lt) => (min, max - 1),
        (_, PrimOp::Gt) => (min + 1, max),
        _ => return,
    };
    out.push((id, r.0, r.1));
}

/// Locals assigned (or bound by a pattern, which re-runs in a loop) anywhere in `e`.
pub fn assigned_in(e: &Expr, out: &mut HashSet<LocalId>) {
    match &e.kind {
        ExprKind::SetLocal(id, v) => {
            out.insert(*id);
            assigned_in(v, out);
        }
        ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::FnValue(_) | ExprKind::Closure { .. } | ExprKind::Continue(_) | ExprKind::Unreachable => {}
        ExprKind::Call(_, args) | ExprKind::Intrinsic(_, _, args) | ExprKind::StructNew(args) | ExprKind::EnumNew(_, args) | ExprKind::TupleNew(args) | ExprKind::ArrayLit(args) | ExprKind::Prim(_, _, args) | ExprKind::StrConcat(args) => {
            args.iter().for_each(|a| assigned_in(a, out))
        }
        ExprKind::CallIndirect(f, args) => {
            assigned_in(f, out);
            args.iter().for_each(|a| assigned_in(a, out));
        }
        ExprKind::DynCall { recv, args, .. } => {
            assigned_in(recv, out);
            args.iter().for_each(|a| assigned_in(a, out));
        }
        ExprKind::Field(x, _, _) | ExprKind::Loop(_, x) | ExprKind::Return(x) | ExprKind::Cast(x) | ExprKind::DynNew(x, _) | ExprKind::Discard(x) => assigned_in(x, out),
        ExprKind::Break(_, v) => {
            if let Some(v) = v {
                assigned_in(v, out);
            }
        }
        ExprKind::SetField(a, _, b) | ExprKind::ArrayGuard(a, b) => {
            assigned_in(a, out);
            assigned_in(b, out);
        }
        ExprKind::Block(stmts, tail) => {
            for s in stmts {
                match s {
                    Stmt::Let(p, x) => {
                        pat_binds(p, out);
                        assigned_in(x, out);
                    }
                    Stmt::Expr(x) => assigned_in(x, out),
                }
            }
            if let Some(t) = tail {
                assigned_in(t, out);
            }
        }
        ExprKind::If(a, b, c) => {
            assigned_in(a, out);
            assigned_in(b, out);
            assigned_in(c, out);
        }
        ExprKind::Match(s, arms) => {
            assigned_in(s, out);
            for Arm { pat, guard, body, .. } in arms {
                pat_binds(pat, out);
                if let Some(g) = guard {
                    assigned_in(g, out);
                }
                assigned_in(body, out);
            }
        }
    }
}

fn pat_binds(p: &Pat, out: &mut HashSet<LocalId>) {
    match &p.kind {
        PatKind::Bind(id, sub) => {
            out.insert(*id);
            if let Some(s) = sub {
                pat_binds(s, out);
            }
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Range(..) => {}
        PatKind::Tuple(ps) | PatKind::Or(ps) => ps.iter().for_each(|p| pat_binds(p, out)),
        PatKind::Struct(fs) | PatKind::Variant(_, fs) => fs.iter().for_each(|(_, p)| pat_binds(p, out)),
        PatKind::List(ps, rest) => {
            ps.iter().for_each(|p| pat_binds(p, out));
            if let Some(Some(id)) = rest {
                out.insert(*id);
            }
        }
    }
}
