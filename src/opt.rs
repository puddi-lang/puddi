//! Inlining of higher-order calls, run on the typed IR before code generation.
//!
//! Iterator adapters and other higher-order functions call their closures through
//! `call_ref`, which V8 inlines speculatively but Wasmtime cannot. This pass inlines a
//! direct call when one of its arguments is a known closure (or a struct literal holding
//! one), forwards reads of never-assigned struct fields to the value the struct was built
//! with, and inlines calls of closures whose literal is known. Repeating these steps turns
//! `(0..n).map(f).filter(g).fold(0, h)` into one loop with the three closure bodies inline.
//!
//! A local is "immutable" when it is bound once, never assigned and not boxed. Since
//! locals are lexically scoped and have unique ids, a use of an immutable local always
//! sees the value its single `let` produced, so a closure literal bound to one can be
//! inlined wherever the local is called, with its captures read from the captured locals.

use std::collections::{HashMap, HashSet};

use crate::diag::Span;
use crate::elab::Global;
use crate::ir::*;
use crate::types::{AdtId, Ty};

mod tape;

/// Largest callee (in IR nodes) that is inlined.
const MAX_CALLEE: usize = 600;
/// A function stops growing once it reaches this size.
const MAX_BODY: usize = 40_000;
const ROUNDS: usize = 16;

pub fn run(g: &mut Global) {
    if std::env::var_os("PUD_NO_OPT").is_some() {
        return;
    }
    let mut set_fields = HashSet::new();
    for f in g.funcs.iter().flatten() {
        visit(&f.body, &mut |e| {
            if let ExprKind::SetField(a, i, _) = &e.kind {
                if let Ty::Adt(id, _) = &a.ty {
                    set_fields.insert((*id, *i));
                }
            }
        });
    }
    for idx in 0..g.funcs.len() {
        let Some(mut f) = g.funcs[idx].take() else { continue };
        if f.extern_.is_none() {
            optimize(&g.funcs, &g.insts, &set_fields, &mut f, idx);
        }
        g.funcs[idx] = Some(f);
    }
}

struct Opt<'a> {
    funcs: &'a [Option<Func>],
    insts: &'a HashMap<FnInst, usize>,
    set_fields: &'a HashSet<(AdtId, usize)>,
    locals: Vec<LocalInfo>,
    next_label: u32,
    size: usize,
    defs: HashMap<LocalId, Expr>,
    immutable: Vec<bool>,
    /// reads of each local
    uses: Vec<u32>,
    changed: bool,
}

fn optimize(funcs: &[Option<Func>], insts: &HashMap<FnInst, usize>, set_fields: &HashSet<(AdtId, usize)>, f: &mut Func, idx: usize) {
    let mut max_label = 0;
    visit(&f.body, &mut |e| match &e.kind {
        ExprKind::Loop(l, _) | ExprKind::Break(l, _) | ExprKind::Continue(l) => max_label = max_label.max(*l + 1),
        _ => {}
    });
    let mut o = Opt {
        funcs,
        insts,
        set_fields,
        locals: std::mem::take(&mut f.locals),
        next_label: max_label,
        size: size(&f.body),
        defs: HashMap::new(),
        immutable: Vec::new(),
        uses: Vec::new(),
        changed: false,
    };
    // a small recursive function gets its recursive calls inlined once, which halves the
    // calls of `fib`-like recursion (V8 does the same); the copies keep calling the function
    let n = size(&f.body);
    if !f.is_closure && n <= MAX_SELF {
        let mut calls = 0;
        visit(&f.body, &mut |e| calls += matches!(&e.kind, ExprKind::Call(i, _) if insts.get(i) == Some(&idx)) as usize);
        if (1..=2).contains(&calls) && !uses_context(&f.body) {
            let orig = Func { locals: o.locals.clone(), ..f.clone() };
            o.inline_self(&mut f.body, &orig, idx);
            flatten(&mut f.body);
            o.size = size(&f.body);
        }
    }
    for _ in 0..ROUNDS {
        o.analyze(&f.body, &f.params);
        o.changed = false;
        o.rewrite(&mut f.body);
        if o.changed {
            flatten(&mut f.body);
        }
        let removed = tape::eliminate(&mut f.body, o.locals.len());
        if !o.changed && !removed {
            break;
        }
        o.size = size(&f.body);
    }
    f.locals = o.locals;
}

impl<'a> Opt<'a> {
    fn analyze(&mut self, body: &Expr, params: &[LocalId]) {
        let n = self.locals.len();
        let mut binds = vec![0u32; n];
        let mut assigned = vec![false; n];
        let mut uses = vec![0u32; n];
        for &p in params {
            binds[p] += 1;
        }
        self.defs.clear();
        let defs = &mut self.defs;
        visit(body, &mut |e| match &e.kind {
            ExprKind::Local(id) => uses[*id] += 1,
            ExprKind::Closure { captures, .. } => captures.iter().for_each(|c| uses[*c] += 1),
            ExprKind::SetLocal(id, _) => assigned[*id] = true,
            ExprKind::Block(stmts, _) => {
                for s in stmts {
                    if let Stmt::Let(p, x) = s {
                        pat_ids(p, &mut |id| binds[id] += 1);
                        if let PatKind::Bind(id, None) = p.kind {
                            if matches!(x.kind, ExprKind::Closure { .. } | ExprKind::StructNew(_) | ExprKind::Local(_) | ExprKind::FnValue(_)) {
                                defs.insert(id, x.clone());
                            }
                        }
                    }
                }
            }
            ExprKind::Match(_, arms) => {
                for a in arms {
                    pat_ids(&a.pat, &mut |id| binds[id] += 1);
                }
            }
            _ => {}
        });
        self.immutable = (0..n).map(|i| !self.locals[i].boxed && binds[i] <= 1 && !assigned[i]).collect();
        self.uses = uses;
        let imm = &self.immutable;
        self.defs.retain(|id, _| imm[*id]);
    }

    /// The expression an immutable local chain was bound to.
    fn resolve<'e>(&'e self, mut e: &'e Expr) -> &'e Expr {
        for _ in 0..32 {
            match &e.kind {
                ExprKind::Local(id) if self.immutable[*id] => match self.defs.get(id) {
                    Some(d) => e = d,
                    None => return e,
                },
                _ => return e,
            }
        }
        e
    }

    fn is_atom(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Lit(_) | ExprKind::FnValue(_) => true,
            ExprKind::Local(id) => self.immutable[*id],
            _ => false,
        }
    }

    /// Whether the value is a known closure or a struct literal holding one.
    fn closure_ish(&self, e: &Expr, depth: u32) -> bool {
        match &self.resolve(e).kind {
            ExprKind::Closure { .. } | ExprKind::FnValue(_) => true,
            ExprKind::StructNew(args) if depth > 0 => args.iter().any(|a| self.closure_ish(a, depth - 1)),
            _ => false,
        }
    }

    fn fresh_label(&mut self) -> u32 {
        self.next_label += 1;
        self.next_label - 1
    }

    fn rewrite(&mut self, e: &mut Expr) {
        children_mut(e, &mut |c| self.rewrite(c));
        if let Some(new) = self.replacement(e) {
            *e = new;
            self.changed = true;
        }
    }

    fn replacement(&mut self, e: &Expr) -> Option<Expr> {
        match &e.kind {
            ExprKind::Field(x, None, i) if matches!(x.kind, ExprKind::Local(_)) => {
                let Ty::Adt(adt, _) = &x.ty else { return None };
                if self.set_fields.contains(&(*adt, *i)) {
                    return None;
                }
                let ExprKind::StructNew(args) = &self.resolve(x).kind else { return None };
                let a = args.get(*i)?;
                self.is_atom(a).then(|| a.clone())
            }
            ExprKind::CallIndirect(callee, args) if matches!(callee.kind, ExprKind::Local(_)) => {
                let target = match &self.resolve(callee).kind {
                    ExprKind::Closure { func, captures } => Ok((*func, captures.clone())),
                    ExprKind::FnValue(inst) => Err(inst.clone()),
                    _ => return None,
                };
                match target {
                    Ok((func, captures)) => self.inline_closure(func, &captures, args, e.span),
                    Err(inst) => Some(Expr { kind: ExprKind::Call(inst, args.clone()), ty: e.ty.clone(), span: e.span }),
                }
            }
            ExprKind::Call(inst, args) => {
                let funcs = self.funcs;
                let callee = funcs[*self.insts.get(inst)?].as_ref()?;
                if callee.extern_.is_some() || callee.is_closure || callee.ret == Ty::Never {
                    return None;
                }
                // tiny functions (accessors, wrappers of one intrinsic) are always inlined:
                // V8 without Liftoff's call counts would otherwise keep the calls
                let tiny = size(&callee.body) <= TINY && !has_return(&callee.body);
                if !tiny && !args.iter().any(|a| self.closure_ish(a, 2)) && !self.matches_ctor_arg(callee, args) {
                    return None;
                }
                let n = size(&callee.body);
                if n > MAX_CALLEE || self.size + n > MAX_BODY || uses_context(&callee.body) {
                    return None;
                }
                self.size += n;
                Some(self.inline_body(callee, vec![None; callee.locals.len()], args, e.span))
            }
            ExprKind::Match(scrut, arms) => self.simplify_match(e, scrut, arms),
            ExprKind::Block(stmts, tail) => self.match_on_init(e, stmts, tail.as_deref()),
            _ => None,
        }
    }

    /// `let x = E; ..; match x { .. }` with x read once and only immutable values bound in
    /// between: match on E directly, so that a constructor E can meet the arms.
    fn match_on_init(&self, e: &Expr, stmts: &[Stmt], tail: Option<&Expr>) -> Option<Expr> {
        let scrut_of = |x: &Expr, id: LocalId| matches!(&x.kind, ExprKind::Match(s, _) if matches!(s.kind, ExprKind::Local(y) if y == id));
        for i in 0..stmts.len() {
            let Stmt::Let(Pat { kind: PatKind::Bind(x, None), .. }, init) = &stmts[i] else { continue };
            if self.uses[*x] != 1 || self.locals[*x].boxed {
                continue;
            }
            let mut j = i + 1;
            while j < stmts.len() && matches!(&stmts[j], Stmt::Let(Pat { kind: PatKind::Bind(_, None), .. }, v) if self.is_atom(v)) {
                j += 1;
            }
            let target = match stmts.get(j) {
                Some(Stmt::Let(_, m)) | Some(Stmt::Expr(m)) => m,
                None => match tail {
                    Some(t) => t,
                    None => continue,
                },
            };
            if !scrut_of(target, *x) {
                continue;
            }
            let ExprKind::Match(_, arms) = &target.kind else { unreachable!() };
            let m = Expr { kind: ExprKind::Match(Box::new(init.clone()), arms.clone()), ty: target.ty.clone(), span: target.span };
            let mut new_stmts: Vec<Stmt> = stmts.to_vec();
            let mut new_tail = tail.cloned();
            match new_stmts.get_mut(j) {
                Some(Stmt::Let(_, t)) | Some(Stmt::Expr(t)) => *t = m,
                None => new_tail = Some(m),
            }
            new_stmts.remove(i);
            return Some(Expr { kind: ExprKind::Block(new_stmts, new_tail.map(Box::new)), ty: e.ty.clone(), span: e.span });
        }
        None
    }

    /// A small callee that matches on a parameter whose argument is a constructor (or a
    /// call returning one), like `opt.unwrap_or(d)` on `map.get(k)`.
    fn matches_ctor_arg(&self, callee: &Func, args: &[Expr]) -> bool {
        if size(&callee.body) > SMALL {
            return false;
        }
        let ExprKind::Match(scrut, _) = &peel(&callee.body).kind else { return false };
        let ExprKind::Local(p) = scrut.kind else { return false };
        let Some(k) = callee.params.iter().position(|&q| q == p) else { return false };
        args.get(k).is_some_and(|a| self.ctor_source(a))
    }

    /// Whether the value is a known constructor or a call of a small function returning one.
    fn ctor_source(&self, e: &Expr) -> bool {
        match &self.resolve(e).kind {
            ExprKind::EnumNew(..) => true,
            ExprKind::Call(inst, _) => self.ctor_fn(inst).is_some(),
            _ => false,
        }
    }

    /// A small function whose result is always a constructor expression.
    fn ctor_fn(&self, inst: &FnInst) -> Option<&'a Func> {
        let funcs = self.funcs;
        let f = funcs[*self.insts.get(inst)?].as_ref()?;
        if f.extern_.is_some() || f.is_closure || size(&f.body) > SMALL_CTOR || !ctor_leaf(&f.body) || has_return(&f.body) || uses_context(&f.body) {
            return None;
        }
        Some(f)
    }

    fn simplify_match(&mut self, e: &Expr, scrut: &Expr, arms: &[Arm]) -> Option<Expr> {
        let mk = |kind: ExprKind| Expr { kind, ty: e.ty.clone(), span: e.span };
        if scrut.ty == Ty::Never {
            return Some(scrut.clone());
        }
        match &scrut.kind {
            // match { s; t } { .. }  ==>  { s; match t { .. } }
            ExprKind::Block(stmts, Some(t)) => Some(mk(ExprKind::Block(stmts.clone(), Some(Box::new(mk(ExprKind::Match(t.clone(), arms.to_vec()))))))),
            // match (if c { A } else { B }) { .. }  ==>  if c { match A { .. } } else { match B { .. } }
            ExprKind::If(c, a, b) if ctor_leaf(a) && ctor_leaf(b) => {
                let ma = mk(ExprKind::Match(a.clone(), arms.to_vec()));
                let mb = mk(ExprKind::Match(b.clone(), arms.to_vec()));
                Some(mk(ExprKind::If(c.clone(), Box::new(ma), Box::new(mb))))
            }
            ExprKind::EnumNew(vi, args) => select_arm(*vi, args, scrut, arms, e, |a| pure(a)),
            ExprKind::Local(_) => match &self.resolve(scrut).kind {
                ExprKind::EnumNew(vi, args) if args.iter().all(|a| self.is_atom(a)) => {
                    let args = args.clone();
                    let vi = *vi;
                    select_arm(vi, &args, scrut, arms, e, |_| true)
                }
                _ => None,
            },
            ExprKind::Call(inst, args) => {
                let f = self.ctor_fn(inst)?;
                let n = size(&f.body);
                if self.size + n > MAX_BODY {
                    return None;
                }
                self.size += n;
                let inlined = self.inline_body(f, vec![None; f.locals.len()], args, scrut.span);
                Some(mk(ExprKind::Match(Box::new(inlined), arms.to_vec())))
            }
            _ => None,
        }
    }

    fn inline_self(&mut self, e: &mut Expr, orig: &Func, idx: usize) {
        children_mut(e, &mut |c| self.inline_self(c, orig, idx));
        if let ExprKind::Call(inst, args) = &e.kind {
            if self.insts.get(inst) == Some(&idx) {
                *e = self.inline_body(orig, vec![None; orig.locals.len()], args, e.span);
            }
        }
    }

    fn inline_closure(&mut self, func: usize, captures: &[LocalId], args: &[Expr], span: Span) -> Option<Expr> {
        let funcs = self.funcs;
        let cf = funcs.get(func)?.as_ref()?;
        if !cf.is_closure || cf.ret == Ty::Never || captures.iter().any(|&c| self.locals[c].boxed) || cf.locals.iter().any(|l| l.capture.is_some() && l.boxed) {
            return None;
        }
        let n = size(&cf.body);
        if n > MAX_CALLEE || self.size + n > MAX_BODY || uses_context(&cf.body) {
            return None;
        }
        let map: Vec<Option<LocalId>> = cf.locals.iter().map(|l| l.capture.map(|k| captures[k])).collect();
        self.size += n;
        Some(self.inline_body(cf, map, args, span))
    }

    /// `callee`'s body with fresh locals (except those already mapped), its parameters
    /// bound to `args` and `return` turned into a break out of a wrapper loop.
    fn inline_body(&mut self, callee: &Func, mut map: Vec<Option<LocalId>>, args: &[Expr], span: Span) -> Expr {
        for (i, l) in callee.locals.iter().enumerate() {
            if map[i].is_none() {
                map[i] = Some(self.locals.len());
                self.locals.push(LocalInfo { is_param: false, capture: None, ..l.clone() });
            }
        }
        let map: Vec<LocalId> = map.into_iter().map(|m| m.unwrap()).collect();
        let ret_label = self.fresh_label();
        let mut labels = HashMap::new();
        let mut body = callee.body.clone();
        let mut has_ret = false;
        self.remap(&mut body, &map, &mut labels, ret_label, &mut has_ret);
        let stmts: Vec<Stmt> = callee
            .params
            .iter()
            .zip(args)
            .map(|(&p, a)| Stmt::Let(Pat { kind: PatKind::Bind(map[p], None), ty: callee.locals[p].ty.clone(), span }, a.clone()))
            .collect();
        let ret = callee.ret.clone();
        let tail = if has_ret {
            let brk = Expr { kind: ExprKind::Break(ret_label, Some(Box::new(body))), ty: Ty::Never, span };
            Expr { kind: ExprKind::Loop(ret_label, Box::new(brk)), ty: ret.clone(), span }
        } else {
            body
        };
        Expr { kind: ExprKind::Block(stmts, Some(Box::new(tail))), ty: ret, span }
    }

    fn remap(&mut self, e: &mut Expr, map: &[LocalId], labels: &mut HashMap<u32, u32>, ret_label: u32, has_ret: &mut bool) {
        children_mut(e, &mut |c| self.remap(c, map, labels, ret_label, has_ret));
        let mut label = |l: &mut u32, me: &mut Self| *l = *labels.entry(*l).or_insert_with(|| me.fresh_label());
        match &mut e.kind {
            ExprKind::Local(id) | ExprKind::SetLocal(id, _) => *id = map[*id],
            ExprKind::Closure { captures, .. } => captures.iter_mut().for_each(|c| *c = map[*c]),
            ExprKind::Loop(l, _) | ExprKind::Break(l, _) | ExprKind::Continue(l) => label(l, self),
            ExprKind::Block(stmts, _) => {
                for s in stmts {
                    if let Stmt::Let(p, _) = s {
                        pat_ids_mut(p, &mut |id| *id = map[*id]);
                    }
                }
            }
            ExprKind::Match(_, arms) => arms.iter_mut().for_each(|a| pat_ids_mut(&mut a.pat, &mut |id| *id = map[*id])),
            _ => {}
        }
        if let ExprKind::Return(_) = e.kind {
            let ExprKind::Return(v) = std::mem::replace(&mut e.kind, ExprKind::Unreachable) else { unreachable!() };
            e.kind = ExprKind::Break(ret_label, Some(v));
            *has_ret = true;
        }
    }
}

/// Largest function that is inlined wherever it is called.
const TINY: usize = 12;
/// Largest recursive function whose recursive calls are inlined once.
const MAX_SELF: usize = 80;
/// Largest callee inlined because it matches on a constructor argument.
const SMALL: usize = 60;
/// Largest constructor-returning callee inlined into a `match`.
const SMALL_CTOR: usize = 120;

/// The expression without wrapping statement-less blocks.
fn peel(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Block(stmts, Some(t)) if stmts.is_empty() => peel(t),
        _ => e,
    }
}

/// Whether every value `e` can produce is a constructor expression (or it diverges).
fn ctor_leaf(e: &Expr) -> bool {
    if e.ty == Ty::Never {
        return true;
    }
    match &e.kind {
        ExprKind::EnumNew(..) => true,
        ExprKind::Block(_, Some(t)) => ctor_leaf(t),
        ExprKind::If(_, a, b) => ctor_leaf(a) && ctor_leaf(b),
        _ => false,
    }
}

fn has_return(e: &Expr) -> bool {
    let mut found = false;
    visit(e, &mut |x| found |= matches!(x.kind, ExprKind::Return(_)));
    found
}

/// `match` on a known variant: the first arm that certainly matches, with its bindings
/// taken from the payload. None if an earlier arm could match or has a guard, or the
/// matching arm's pattern needs more than bindings.
fn select_arm(vi: usize, args: &[Expr], scrut: &Expr, arms: &[Arm], e: &Expr, discardable: impl Fn(&Expr) -> bool) -> Option<Expr> {
    for arm in arms {
        if arm.guard.is_some() {
            return None;
        }
        let mut stmts = Vec::new();
        match &arm.pat.kind {
            PatKind::Wild => {
                for a in args {
                    if !discardable(a) {
                        stmts.push(Stmt::Expr(a.clone()));
                    }
                }
            }
            PatKind::Bind(_, None) => stmts.push(Stmt::Let(arm.pat.clone(), scrut.clone())),
            PatKind::Variant(vj, _) if *vj != vi => continue,
            PatKind::Variant(_, fields) => {
                let mut bind: Vec<Option<&Pat>> = vec![None; args.len()];
                for (k, p) in fields {
                    match &p.kind {
                        PatKind::Wild => {}
                        PatKind::Bind(_, None) if *k < args.len() => bind[*k] = Some(p),
                        _ => return None,
                    }
                }
                for (k, a) in args.iter().enumerate() {
                    match bind[k] {
                        Some(p) => stmts.push(Stmt::Let(p.clone(), a.clone())),
                        None if !discardable(a) => stmts.push(Stmt::Expr(a.clone())),
                        None => {}
                    }
                }
            }
            _ => return None,
        }
        return Some(Expr { kind: ExprKind::Block(stmts, Some(Box::new(arm.body.clone()))), ty: e.ty.clone(), span: e.span });
    }
    None
}

/// Intrinsics that depend on the function they appear in.
fn uses_context(body: &Expr) -> bool {
    let mut found = false;
    visit(body, &mut |e| {
        if let ExprKind::Intrinsic(name, _, _) = &e.kind {
            if matches!(name.as_str(), "host_async" | "worker_dispatch") || name.starts_with("cabi_") {
                found = true;
            }
        }
    });
    found
}

fn size(e: &Expr) -> usize {
    let mut n = 0;
    visit(e, &mut |_| n += 1);
    n
}

/// Moves the statements of blocks in `let` and statement position into the enclosing
/// block (locals have unique ids, so widening their scope changes nothing).
fn flatten(e: &mut Expr) {
    children_mut(e, &mut flatten);
    if let ExprKind::Block(stmts, tail) = &mut e.kind {
        let old = std::mem::take(stmts);
        for s in old {
            match s {
                Stmt::Let(p, Expr { kind: ExprKind::Block(inner, Some(t)), .. }) => {
                    stmts.extend(inner);
                    stmts.push(Stmt::Let(p, *t));
                }
                Stmt::Expr(Expr { kind: ExprKind::Block(inner, t), .. }) => {
                    stmts.extend(inner);
                    if let Some(t) = t {
                        stmts.push(Stmt::Expr(*t));
                    }
                }
                s => stmts.push(s),
            }
        }
        if let Some(t) = tail {
            if let ExprKind::Block(inner, it) = &mut t.kind {
                if it.is_some() {
                    stmts.append(inner);
                    let it = it.take().unwrap();
                    *tail = Some(it);
                }
            }
        }
    }
}

fn pure(e: &Expr) -> bool {
    if e.ty == Ty::Never {
        return false;
    }
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::FnValue(_) | ExprKind::Closure { .. } => true,
        ExprKind::StructNew(a) | ExprKind::TupleNew(a) | ExprKind::EnumNew(_, a) => a.iter().all(pure),
        _ => false,
    }
}

// ---------------- traversal ----------------

pub fn visit(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    children(e, &mut |c| visit(c, f));
}

fn children(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::FnValue(_) | ExprKind::Closure { .. } | ExprKind::Continue(_) | ExprKind::Unreachable => {}
        ExprKind::SetLocal(_, v) | ExprKind::Field(v, _, _) | ExprKind::Loop(_, v) | ExprKind::Return(v) | ExprKind::Cast(v) | ExprKind::DynNew(v, _) | ExprKind::Discard(v) => f(v),
        ExprKind::Break(_, v) => {
            if let Some(v) = v {
                f(v)
            }
        }
        ExprKind::Call(_, a) | ExprKind::Intrinsic(_, _, a) | ExprKind::StructNew(a) | ExprKind::EnumNew(_, a) | ExprKind::TupleNew(a) | ExprKind::ArrayLit(a) | ExprKind::Prim(_, _, a) | ExprKind::StrConcat(a) => a.iter().for_each(f),
        ExprKind::CallIndirect(c, a) => {
            f(c);
            a.iter().for_each(f);
        }
        ExprKind::DynCall { recv, args, .. } => {
            f(recv);
            args.iter().for_each(f);
        }
        ExprKind::SetField(a, _, b) | ExprKind::ArrayGuard(a, b) => {
            f(a);
            f(b);
        }
        ExprKind::Block(stmts, tail) => {
            for s in stmts {
                match s {
                    Stmt::Let(_, x) | Stmt::Expr(x) => f(x),
                }
            }
            if let Some(t) = tail {
                f(t);
            }
        }
        ExprKind::If(a, b, c) => {
            f(a);
            f(b);
            f(c);
        }
        ExprKind::Match(s, arms) => {
            f(s);
            for a in arms {
                if let Some(g) = &a.guard {
                    f(g);
                }
                f(&a.body);
            }
        }
    }
}

fn children_mut(e: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    match &mut e.kind {
        ExprKind::Lit(_) | ExprKind::Local(_) | ExprKind::FnValue(_) | ExprKind::Closure { .. } | ExprKind::Continue(_) | ExprKind::Unreachable => {}
        ExprKind::SetLocal(_, v) | ExprKind::Field(v, _, _) | ExprKind::Loop(_, v) | ExprKind::Return(v) | ExprKind::Cast(v) | ExprKind::DynNew(v, _) | ExprKind::Discard(v) => f(v),
        ExprKind::Break(_, v) => {
            if let Some(v) = v {
                f(v)
            }
        }
        ExprKind::Call(_, a) | ExprKind::Intrinsic(_, _, a) | ExprKind::StructNew(a) | ExprKind::EnumNew(_, a) | ExprKind::TupleNew(a) | ExprKind::ArrayLit(a) | ExprKind::Prim(_, _, a) | ExprKind::StrConcat(a) => a.iter_mut().for_each(f),
        ExprKind::CallIndirect(c, a) => {
            f(c);
            a.iter_mut().for_each(f);
        }
        ExprKind::DynCall { recv, args, .. } => {
            f(recv);
            args.iter_mut().for_each(f);
        }
        ExprKind::SetField(a, _, b) | ExprKind::ArrayGuard(a, b) => {
            f(a);
            f(b);
        }
        ExprKind::Block(stmts, tail) => {
            for s in stmts {
                match s {
                    Stmt::Let(_, x) | Stmt::Expr(x) => f(x),
                }
            }
            if let Some(t) = tail {
                f(t);
            }
        }
        ExprKind::If(a, b, c) => {
            f(a);
            f(b);
            f(c);
        }
        ExprKind::Match(s, arms) => {
            f(s);
            for a in arms {
                if let Some(g) = &mut a.guard {
                    f(g);
                }
                f(&mut a.body);
            }
        }
    }
}

fn pat_ids(p: &Pat, f: &mut dyn FnMut(LocalId)) {
    match &p.kind {
        PatKind::Bind(id, sub) => {
            f(*id);
            if let Some(s) = sub {
                pat_ids(s, f);
            }
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Range(..) => {}
        PatKind::Tuple(ps) | PatKind::Or(ps) => ps.iter().for_each(|p| pat_ids(p, f)),
        PatKind::Struct(fs) | PatKind::Variant(_, fs) => fs.iter().for_each(|(_, p)| pat_ids(p, f)),
        PatKind::List(ps, rest) => {
            ps.iter().for_each(|p| pat_ids(p, f));
            if let Some(Some(id)) = rest {
                f(*id);
            }
        }
    }
}

fn pat_ids_mut(p: &mut Pat, f: &mut dyn FnMut(&mut LocalId)) {
    match &mut p.kind {
        PatKind::Bind(id, sub) => {
            f(id);
            if let Some(s) = sub {
                pat_ids_mut(s, f);
            }
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Range(..) => {}
        PatKind::Tuple(ps) | PatKind::Or(ps) => ps.iter_mut().for_each(|p| pat_ids_mut(p, f)),
        PatKind::Struct(fs) | PatKind::Variant(_, fs) => fs.iter_mut().for_each(|(_, p)| pat_ids_mut(p, f)),
        PatKind::List(ps, rest) => {
            ps.iter_mut().for_each(|p| pat_ids_mut(p, f));
            if let Some(Some(id)) = rest {
                f(id);
            }
        }
    }
}
