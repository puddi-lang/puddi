//! Typed intermediate representation produced by elaboration and consumed by
//! code generation. All types in finished IR are concrete.

use crate::diag::Span;
use crate::types::*;

pub type LocalId = usize;
pub type LabelId = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnInst {
    pub fn_id: FnId,
    pub targs: Vec<Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitRef {
    pub trait_id: TraitId,
    pub args: Vec<Ty>,
}

#[derive(Clone, Debug)]
pub struct LocalInfo {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    pub boxed: bool,
    pub is_param: bool,
    /// For closure capture locals: index into the env.
    pub capture: Option<usize>,
}

#[derive(Clone, Debug)]
pub enum Lit {
    Int(i128),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
    Unit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Neg,
    Not,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Lit(Lit),
    Local(LocalId),
    SetLocal(LocalId, Box<Expr>),
    Call(FnInst, Vec<Expr>),
    Intrinsic(String, Vec<Ty>, Vec<Expr>),
    /// Check a scalar array read without fetching its element. Produces unit.
    ArrayGuard(Box<Expr>, Box<Expr>),
    CallIndirect(Box<Expr>, Vec<Expr>),
    FnValue(FnInst),
    Closure { func: usize, captures: Vec<LocalId> },
    StructNew(Vec<Expr>),
    EnumNew(usize, Vec<Expr>),
    TupleNew(Vec<Expr>),
    ArrayLit(Vec<Expr>),
    /// Read field `idx` of a struct value; for enums `variant` selects the payload struct.
    Field(Box<Expr>, Option<usize>, usize),
    SetField(Box<Expr>, usize, Box<Expr>),
    Block(Vec<Stmt>, Option<Box<Expr>>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<Arm>),
    Loop(LabelId, Box<Expr>),
    Break(LabelId, Option<Box<Expr>>),
    Continue(LabelId),
    Return(Box<Expr>),
    Prim(PrimOp, Ty, Vec<Expr>),
    Cast(Box<Expr>),
    StrConcat(Vec<Expr>),
    DynNew(Box<Expr>, TraitRef),
    DynCall { recv: Box<Expr>, trait_ref: TraitRef, method: String, args: Vec<Expr> },
    /// Evaluate and discard; result is unit.
    Discard(Box<Expr>),
    Unreachable,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Let(Pat, Expr),
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Pat {
    pub kind: PatKind,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    Wild,
    Bind(LocalId, Option<Box<Pat>>),
    Lit(Lit),
    Range(Lit, Lit, bool),
    Tuple(Vec<Pat>),
    /// Struct pattern: (field index, pattern)
    Struct(Vec<(usize, Pat)>),
    /// Enum variant pattern: variant index, (field index, pattern)
    Variant(usize, Vec<(usize, Pat)>),
    Or(Vec<Pat>),
    /// List pattern: prefix patterns, optional rest binding (Some(None) = `..`)
    List(Vec<Pat>, Option<Option<LocalId>>),
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub params: Vec<LocalId>,
    pub locals: Vec<LocalInfo>,
    pub ret: Ty,
    pub body: Expr,
    /// For closures: the env field types (in capture order) and captured outer locals.
    pub is_closure: bool,
    pub export: Option<String>,
    pub extern_: Option<(String, String)>,
}
