//! A function-local liveness tape over the structured IR.
//!
//! Values have stable indices and share a flat operand table. The statement
//! schedule follows the tree's control flow and can omit dead values without
//! changing their indices. Effects and control flow stay in their original order.

use std::ops::Range;

use crate::ir::{Expr, ExprKind, Lit, LocalId, Pat, PatKind, Stmt};
use crate::types::{IntTy, Ty};

use super::{children, children_mut, pure, visit};

type NodeId = usize;

struct Value {
    operands: Range<usize>,
    next_definition: Option<NodeId>,
    live: bool,
}

#[derive(Clone, Copy)]
enum Scheduled {
    Keep,
    Drop,
    Value(NodeId),
    /// The guard is required independently of demand for the element.
    ArrayRead(Option<NodeId>),
}

struct Tape {
    values: Vec<Value>,
    operands: Vec<LocalId>,
    schedule: Vec<Scheduled>,
    definitions: Vec<Option<NodeId>>,
    pending: Vec<LocalId>,
}

pub(super) fn eliminate(body: &mut Expr, locals: usize) -> bool {
    let mut tape = Tape {
        values: Vec::new(),
        operands: Vec::new(),
        schedule: Vec::new(),
        definitions: vec![None; locals],
        pending: Vec::new(),
    };
    tape.collect(body);
    tape.mark_live();
    let mut schedule = tape.schedule.iter().copied();
    let mut changed = false;
    tape.compact(body, &mut schedule, &mut changed);
    debug_assert!(schedule.next().is_none());
    changed
}

impl Tape {
    fn define(&mut self, local: LocalId, value: Option<&Expr>) -> NodeId {
        let start = self.operands.len();
        if let Some(value) = value {
            visit(value, &mut |e| local_uses(e, |id| self.operands.push(id)));
        }
        let id = self.values.len();
        self.values.push(Value {
            operands: start..self.operands.len(),
            next_definition: self.definitions[local].replace(id),
            live: false,
        });
        id
    }

    fn collect(&mut self, e: &Expr) {
        local_uses(e, |id| self.pending.push(id));
        if let ExprKind::Block(stmts, tail) = &e.kind {
            for s in stmts {
                let (binding, value, simple) = match s {
                    Stmt::Let(Pat { kind: PatKind::Bind(id, None), .. }, value) => (Some(*id), value, true),
                    Stmt::Let(Pat { kind: PatKind::Wild, .. }, value) | Stmt::Expr(value) => (None, value, true),
                    Stmt::Let(_, value) => (None, value, false),
                };
                let action = if simple && pure(value) {
                    binding.map_or(Scheduled::Drop, |id| Scheduled::Value(self.define(id, Some(value))))
                } else if simple && scalar_array_read(value) {
                    Scheduled::ArrayRead(binding.map(|id| self.define(id, None)))
                } else {
                    Scheduled::Keep
                };
                self.schedule.push(action);
                if matches!(action, Scheduled::Keep | Scheduled::ArrayRead(_)) {
                    self.collect(value);
                }
            }
            if let Some(tail) = tail {
                self.collect(tail);
            }
        } else {
            children(e, &mut |child| self.collect(child));
        }
    }

    fn mark_live(&mut self) {
        while let Some(local) = self.pending.pop() {
            // A local can have several reaching bindings in the structured IR.
            // Conservatively demand every one and expand their operands once.
            let mut id = self.definitions[local].take();
            while let Some(current) = id {
                let value = &mut self.values[current];
                value.live = true;
                self.pending.extend_from_slice(&self.operands[value.operands.clone()]);
                id = value.next_definition;
            }
        }
    }

    fn compact(&self, e: &mut Expr, schedule: &mut impl Iterator<Item = Scheduled>, changed: &mut bool) {
        if let ExprKind::Block(stmts, tail) = &mut e.kind {
            *stmts = std::mem::take(stmts)
                .into_iter()
                .filter_map(|mut stmt| {
                    let action = schedule.next().expect("each statement has a tape entry");
                    if matches!(action, Scheduled::Drop) || matches!(action, Scheduled::Value(id) if !self.values[id].live) {
                        // Only pure subtrees, which contain no scheduled statements.
                        *changed = true;
                        return None;
                    }
                    let value = match &mut stmt {
                        Stmt::Let(_, value) | Stmt::Expr(value) => value,
                    };
                    self.compact(value, schedule, changed);
                    if matches!(action, Scheduled::ArrayRead(id) if id.is_none_or(|id| !self.values[id].live)) {
                        let (Stmt::Let(_, mut value) | Stmt::Expr(mut value)) = stmt;
                        keep_array_guard(&mut value);
                        *changed = true;
                        return Some(Stmt::Expr(value));
                    }
                    Some(stmt)
                })
                .collect();
            if let Some(tail) = tail {
                self.compact(tail, schedule, changed);
            }
        } else {
            children_mut(e, &mut |child| self.compact(child, schedule, changed));
            if matches!(&e.kind, ExprKind::Discard(value) if scalar_array_read(value)) {
                let ExprKind::Discard(value) = std::mem::replace(&mut e.kind, ExprKind::Lit(Lit::Unit)) else {
                    unreachable!()
                };
                *e = *value;
                keep_array_guard(e);
                *changed = true;
            }
        }
    }
}

fn local_uses(e: &Expr, mut use_local: impl FnMut(LocalId)) {
    match &e.kind {
        ExprKind::Local(id) | ExprKind::SetLocal(id, _) => use_local(*id),
        ExprKind::Closure { captures, .. } => captures.iter().copied().for_each(use_local),
        _ => {}
    }
}

fn scalar_array_read(e: &Expr) -> bool {
    if e.ty == Ty::Never {
        return false;
    }
    match &e.kind {
        ExprKind::Block(_, Some(tail)) => scalar_array_read(tail),
        ExprKind::Intrinsic(name, _, args) if name == "array_get" => match args.as_slice() {
            [Expr { ty: Ty::Array(elem), .. }, Expr { ty: Ty::Int(IntTy::I32), .. }] => {
                matches!(elem.as_ref(), Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Unit)
            }
            _ => false,
        },
        _ => false,
    }
}

fn keep_array_guard(e: &mut Expr) {
    e.ty = Ty::Unit;
    match &mut e.kind {
        ExprKind::Block(_, Some(tail)) => keep_array_guard(tail),
        ExprKind::Intrinsic(_, _, args) => {
            let [array, index]: [Expr; 2] = std::mem::take(args).try_into().expect("an array read has two operands");
            e.kind = ExprKind::ArrayGuard(Box::new(array), Box::new(index));
        }
        _ => unreachable!("an array read was scheduled for its guard"),
    }
}
