//! Semantic types.

use std::fmt;

pub type AdtId = usize;
pub type TraitId = usize;
pub type FnId = usize;
pub type ImplId = usize;
pub type ModId = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntTy {
    pub fn signed(self) -> bool {
        matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64)
    }
    pub fn bits(self) -> u32 {
        match self {
            IntTy::I8 | IntTy::U8 => 8,
            IntTy::I16 | IntTy::U16 => 16,
            IntTy::I32 | IntTy::U32 => 32,
            IntTy::I64 | IntTy::U64 => 64,
        }
    }
    pub fn is64(self) -> bool {
        self.bits() == 64
    }
    pub fn min(self) -> i128 {
        if self.signed() { -(1i128 << (self.bits() - 1)) } else { 0 }
    }
    pub fn max(self) -> i128 {
        if self.signed() { (1i128 << (self.bits() - 1)) - 1 } else { (1i128 << self.bits()) - 1 }
    }
    pub fn name(self) -> &'static str {
        match self {
            IntTy::I8 => "I8",
            IntTy::I16 => "I16",
            IntTy::I32 => "Int",
            IntTy::I64 => "I64",
            IntTy::U8 => "U8",
            IntTy::U16 => "U16",
            IntTy::U32 => "U32",
            IntTy::U64 => "U64",
        }
    }
    pub fn all() -> [IntTy; 8] {
        [IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64, IntTy::U8, IntTy::U16, IntTy::U32, IntTy::U64]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FloatTy {
    F32,
    F64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Str,
    Unit,
    Never,
    Tuple(Vec<Ty>),
    Adt(AdtId, Vec<Ty>),
    Array(Box<Ty>),
    Fn(Vec<Ty>, Box<Ty>),
    Dyn(TraitId, Vec<Ty>, Vec<(String, Ty)>),
    Param(u32),
    /// Associated type projection `T.Name`, resolved after substitution.
    Proj(Box<Ty>, String),
    Var(u32),
    Error,
}

pub const INT: Ty = Ty::Int(IntTy::I32);

/// Tests whether two impl headers can denote the same types. The caller gives
/// each header its own variable IDs, including across the trait arguments.
pub fn unify_headers(mut pending: Vec<(Ty, Ty)>, variables: u32) -> Option<Vec<Ty>> {
    use std::collections::HashMap;

    fn resolve<'a>(mut ty: &'a Ty, bindings: &'a HashMap<u32, Ty>) -> &'a Ty {
        while let Ty::Var(id) = ty {
            let Some(bound) = bindings.get(id) else { break };
            ty = bound;
        }
        ty
    }

    fn occurs(id: u32, ty: &Ty, bindings: &HashMap<u32, Ty>) -> bool {
        match resolve(ty, bindings) {
            Ty::Var(other) => id == *other,
            Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(|ty| occurs(id, ty, bindings)),
            Ty::Array(ty) | Ty::Proj(ty, _) => occurs(id, ty, bindings),
            Ty::Fn(args, ret) => args.iter().any(|ty| occurs(id, ty, bindings)) || occurs(id, ret, bindings),
            Ty::Dyn(_, args, assoc) => args.iter().chain(assoc.iter().map(|(_, ty)| ty)).any(|ty| occurs(id, ty, bindings)),
            _ => false,
        }
    }

    fn substitute(ty: &Ty, bindings: &HashMap<u32, Ty>) -> Ty {
        match resolve(ty, bindings) {
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| substitute(t, bindings)).collect()),
            Ty::Adt(id, ts) => Ty::Adt(*id, ts.iter().map(|t| substitute(t, bindings)).collect()),
            Ty::Array(t) => Ty::Array(Box::new(substitute(t, bindings))),
            Ty::Fn(args, ret) => Ty::Fn(args.iter().map(|t| substitute(t, bindings)).collect(), Box::new(substitute(ret, bindings))),
            Ty::Dyn(id, args, assoc) => Ty::Dyn(*id, args.iter().map(|t| substitute(t, bindings)).collect(),
                assoc.iter().map(|(n, t)| (n.clone(), substitute(t, bindings))).collect()),
            Ty::Proj(t, name) => Ty::Proj(Box::new(substitute(t, bindings)), name.clone()),
            ty => ty.clone(),
        }
    }

    let mut bindings = HashMap::new();
    while let Some((left, right)) = pending.pop() {
        let left = resolve(&left, &bindings);
        let right = resolve(&right, &bindings);
        if left == right {
            continue;
        }
        match (left, right) {
            (Ty::Error | Ty::Proj(..), _) | (_, Ty::Error | Ty::Proj(..)) => {}
            (Ty::Var(id), ty) | (ty, Ty::Var(id)) => {
                if occurs(*id, ty, &bindings) {
                    return None;
                }
                bindings.insert(*id, ty.clone());
            }
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                pending.extend(a.iter().cloned().zip(b.iter().cloned()));
            }
            (Ty::Adt(i, a), Ty::Adt(j, b)) if i == j && a.len() == b.len() => {
                pending.extend(a.iter().cloned().zip(b.iter().cloned()));
            }
            (Ty::Array(a), Ty::Array(b)) => pending.push(((**a).clone(), (**b).clone())),
            (Ty::Fn(a, ar), Ty::Fn(b, br)) if a.len() == b.len() => {
                pending.extend(a.iter().cloned().zip(b.iter().cloned()));
                pending.push(((**ar).clone(), (**br).clone()));
            }
            (Ty::Dyn(i, a, aa), Ty::Dyn(j, b, ba)) if i == j && a.len() == b.len()
                && aa.len() == ba.len() && aa.iter().zip(ba).all(|((an, _), (bn, _))| an == bn) => {
                pending.extend(a.iter().cloned().zip(b.iter().cloned()));
                pending.extend(aa.iter().zip(ba).map(|((_, a), (_, b))| (a.clone(), b.clone())));
            }
            _ => return None,
        }
    }
    Some((0..variables).map(|i| substitute(&Ty::Var(i), &bindings)).collect())
}

impl Ty {
    pub fn is_numeric(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_))
    }
    pub fn has_params(&self) -> bool {
        match self {
            Ty::Param(_) | Ty::Proj(..) => true,
            Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(|t| t.has_params()),
            Ty::Array(t) => t.has_params(),
            Ty::Fn(ps, r) => ps.iter().any(|t| t.has_params()) || r.has_params(),
            Ty::Dyn(_, ts, a) => ts.iter().any(|t| t.has_params()) || a.iter().any(|(_, t)| t.has_params()),
            _ => false,
        }
    }
    pub fn has_vars(&self) -> bool {
        match self {
            Ty::Var(_) => true,
            Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(|t| t.has_vars()),
            Ty::Array(t) | Ty::Proj(t, _) => t.has_vars(),
            Ty::Fn(ps, r) => ps.iter().any(|t| t.has_vars()) || r.has_vars(),
            Ty::Dyn(_, ts, a) => ts.iter().any(|t| t.has_vars()) || a.iter().any(|(_, t)| t.has_vars()),
            _ => false,
        }
    }
    /// Substitute generic parameters.
    pub fn subst(&self, args: &[Ty]) -> Ty {
        match self {
            Ty::Param(i) => args.get(*i as usize).cloned().unwrap_or(Ty::Error),
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| t.subst(args)).collect()),
            Ty::Adt(id, ts) => Ty::Adt(*id, ts.iter().map(|t| t.subst(args)).collect()),
            Ty::Array(t) => Ty::Array(Box::new(t.subst(args))),
            Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(|t| t.subst(args)).collect(), Box::new(r.subst(args))),
            Ty::Dyn(id, ts, a) => Ty::Dyn(*id, ts.iter().map(|t| t.subst(args)).collect(), a.iter().map(|(n, t)| (n.clone(), t.subst(args))).collect()),
            Ty::Proj(t, n) => Ty::Proj(Box::new(t.subst(args)), n.clone()),
            other => other.clone(),
        }
    }
}

/// Lossless implicit widening.
pub fn widens_to(from: &Ty, to: &Ty) -> bool {
    use IntTy::*;
    match (from, to) {
        (Ty::Int(a), Ty::Int(b)) => {
            if a == b {
                return true;
            }
            match (a.signed(), b.signed()) {
                (true, true) | (false, false) => b.bits() > a.bits(),
                (false, true) => b.bits() > a.bits(),
                (true, false) => false,
            }
        }
        (Ty::Int(a), Ty::Float(FloatTy::F32)) => matches!(a, I8 | I16 | U8 | U16),
        (Ty::Int(a), Ty::Float(FloatTy::F64)) => !a.is64(),
        (Ty::Float(FloatTy::F32), Ty::Float(FloatTy::F64)) => true,
        (Ty::Float(a), Ty::Float(b)) => a == b,
        _ => false,
    }
}

/// Narrowest numeric type both operands widen to.
pub fn common_numeric(a: &Ty, b: &Ty) -> Option<Ty> {
    if widens_to(a, b) {
        return Some(b.clone());
    }
    if widens_to(b, a) {
        return Some(a.clone());
    }
    let candidates = [
        Ty::Int(IntTy::I16),
        Ty::Int(IntTy::I32),
        Ty::Int(IntTy::I64),
        Ty::Float(FloatTy::F32),
        Ty::Float(FloatTy::F64),
    ];
    candidates.into_iter().find(|c| widens_to(a, c) && widens_to(b, c))
}

/// Display helper that needs names for ADTs and traits.
pub struct TyDisplay<'a> {
    pub ty: &'a Ty,
    pub adt_names: &'a dyn Fn(AdtId) -> String,
    pub trait_names: &'a dyn Fn(TraitId) -> String,
    pub param_names: &'a [String],
}

impl<'a> TyDisplay<'a> {
    fn sub<'b>(&'b self, t: &'b Ty) -> TyDisplay<'b> {
        TyDisplay { ty: t, adt_names: self.adt_names, trait_names: self.trait_names, param_names: self.param_names }
    }
}

impl fmt::Display for TyDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sub = |t| self.sub(t);
        match self.ty {
            Ty::Int(i) => write!(f, "{}", i.name()),
            Ty::Float(FloatTy::F64) => write!(f, "Float"),
            Ty::Float(FloatTy::F32) => write!(f, "F32"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Char => write!(f, "Char"),
            Ty::Str => write!(f, "Str"),
            Ty::Unit => write!(f, "()"),
            Ty::Never => write!(f, "Never"),
            Ty::Tuple(ts) => {
                write!(f, "(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", sub(t))?;
                }
                if ts.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            Ty::Adt(id, ts) => {
                write!(f, "{}", (self.adt_names)(*id))?;
                if !ts.is_empty() {
                    write!(f, "<")?;
                    for (i, t) in ts.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", sub(t))?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Ty::Array(t) => write!(f, "Array<{}>", sub(t)),
            Ty::Fn(ps, r) => {
                write!(f, "fn(")?;
                for (i, t) in ps.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", sub(t))?;
                }
                write!(f, ") -> {}", sub(r))
            }
            Ty::Dyn(id, ts, a) => {
                write!(f, "dyn {}", (self.trait_names)(*id))?;
                if !ts.is_empty() || !a.is_empty() {
                    write!(f, "<")?;
                    let mut first = true;
                    for t in ts {
                        if !first {
                            write!(f, ", ")?;
                        }
                        first = false;
                        write!(f, "{}", sub(t))?;
                    }
                    for (n, t) in a {
                        if !first {
                            write!(f, ", ")?;
                        }
                        first = false;
                        write!(f, "{n} = {}", sub(t))?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Ty::Param(i) => write!(f, "{}", self.param_names.get(*i as usize).cloned().unwrap_or_else(|| format!("T{i}"))),
            Ty::Proj(t, n) => write!(f, "{}.{n}", sub(t)),
            Ty::Var(_) => write!(f, "_"),
            Ty::Error => write!(f, "{{error}}"),
        }
    }
}
