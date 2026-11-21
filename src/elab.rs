//! Elaboration: type inference and lowering of function bodies to IR.
//!
//! Generic functions are checked per instantiation with concrete type
//! arguments (monomorphization happens here).

use std::collections::{HashMap, HashSet, VecDeque};

use crate::ast::{self, BinOp, UnOp};
use crate::diag::{Diag, Span};
use crate::ir::{self, Expr, ExprKind, FnInst, Lit, LocalId, LocalInfo, Pat, PatKind, PrimOp, Stmt, TraitRef};
use crate::program::*;
use crate::types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VarKind {
    General,
    Int,
    Float,
}

pub struct Global<'p> {
    pub prog: &'p Program,
    pub funcs: Vec<Option<ir::Func>>,
    pub insts: HashMap<FnInst, usize>,
    queue: VecDeque<FnInst>,
    pub errors: Vec<Diag>,
    pub warnings: Vec<Diag>,
    seen: HashSet<(Span, String)>,
    /// (concrete type, trait) -> methods in vtable order
    pub vtables: HashMap<(Ty, TraitRef), Vec<(String, FnInst)>>,
    pub vtable_order: Vec<(Ty, TraitRef)>,
    pub entry: Option<usize>,
    pub tests: Vec<(String, usize)>,
    /// Functions run by `__worker_entry(k)` in a worker instance.
    pub worker_entries: Vec<usize>,
    /// Replacement bodies for functions (the pruned platform dispatchers).
    pub body_override: HashMap<FnId, ast::Block>,
}

impl<'p> Global<'p> {
    pub fn new(prog: &'p Program) -> Global<'p> {
        Global {
            prog,
            funcs: Vec::new(),
            insts: HashMap::new(),
            queue: VecDeque::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
            seen: HashSet::new(),
            vtables: HashMap::new(),
            vtable_order: Vec::new(),
            entry: None,
            tests: Vec::new(),
            worker_entries: Vec::new(),
            body_override: HashMap::new(),
        }
    }

    pub fn error(&mut self, d: Diag) {
        if self.seen.insert((d.span, d.msg.clone())) {
            self.errors.push(d);
        }
    }

    pub fn warn(&mut self, mut d: Diag) {
        d.warning = true;
        if self.seen.insert((d.span, d.msg.clone())) {
            self.warnings.push(d);
        }
    }

    pub fn request(&mut self, inst: FnInst) -> usize {
        if let Some(&i) = self.insts.get(&inst) {
            return i;
        }
        let i = self.funcs.len();
        self.funcs.push(None);
        self.insts.insert(inst.clone(), i);
        self.queue.push_back(inst);
        i
    }

    pub fn run(&mut self) {
        while let Some(inst) = self.queue.pop_front() {
            let idx = self.insts[&inst];
            let f = elaborate_fn(self, &inst);
            self.funcs[idx] = Some(f);
        }
    }

    /// Elaborates an already elaborated function again (after its body was overridden).
    pub fn reelaborate(&mut self, inst: FnInst) {
        let idx = self.request(inst.clone());
        if self.funcs[idx].is_some() {
            let f = elaborate_fn(self, &inst);
            self.funcs[idx] = Some(f);
        }
    }

    fn reserve(&mut self) -> usize {
        self.funcs.push(None);
        self.funcs.len() - 1
    }
}

struct LoopCx {
    label: u32,
    break_ty: Ty,
    allows_value: bool,
    has_break: bool,
}

struct FnCx {
    is_async: bool,
    locals: Vec<LocalInfo>,
    scopes: Vec<Vec<(String, LocalId)>>,
    captures: Vec<(LocalId, LocalId)>,
    ret: Ty,
    loops: Vec<LoopCx>,
}

impl FnCx {
    fn new(ret: Ty) -> FnCx {
        FnCx { is_async: false, locals: Vec::new(), scopes: vec![Vec::new()], captures: Vec::new(), ret, loops: Vec::new() }
    }
}

struct Elab<'g, 'p> {
    g: &'g mut Global<'p>,
    prog: &'p Program,
    vars: Vec<(Option<Ty>, VarKind)>,
    cxs: Vec<FnCx>,
    module: ModId,
    self_ty: Option<Ty>,
    self_impl: Option<ImplId>,
    targs: Vec<Ty>,
    gen_names: Vec<String>,
    const_stack: Vec<usize>,
    next_label: u32,
    next_tmp: u32,
    closures: Vec<(usize, ir::Func)>,
}

fn elaborate_fn(g: &mut Global, inst: &FnInst) -> ir::Func {
    let prog = g.prog;
    let f = &prog.fns[inst.fn_id];
    let mut el = Elab {
        g,
        prog,
        vars: Vec::new(),
        cxs: Vec::new(),
        module: f.module,
        self_ty: f.self_ty.as_ref().map(|t| prog.normalize_proj(t.subst(&inst.targs))),
        self_impl: f.owner.impl_id(),
        targs: inst.targs.clone(),
        gen_names: f.generics.iter().map(|g| g.name.clone()).collect(),
        const_stack: Vec::new(),
        next_label: 0,
        next_tmp: 0,
        closures: Vec::new(),
    };
    let ret = prog.normalize_proj(f.ret.subst(&inst.targs));
    let mut cx = FnCx::new(ret.clone());
    let mut params = Vec::new();
    for (n, t) in &f.params {
        let t = prog.normalize_proj(t.subst(&inst.targs));
        let id = cx.locals.len();
        cx.locals.push(LocalInfo { name: n.clone(), ty: t, mutable: false, boxed: false, is_param: true, capture: None });
        cx.scopes[0].push((n.clone(), id));
        params.push(id);
    }
    el.cxs.push(cx);
    let name = fn_display_name(prog, inst);
    if f.test_name.is_some() {
        el.cxs[0].is_async = true;
    }
    let overridden = el.g.body_override.get(&inst.fn_id).cloned();
    let body = if let Some(b) = overridden.as_ref().or(f.decl.body.as_ref()) {
        if f.decl.is_async {
            let inner = match &ret {
                Ty::Adt(_, a) if a.len() == 1 => a[0].clone(),
                _ => Ty::Error,
            };
            let bexpr = ae(ast::ExprKind::Block(b.clone()), b.span);
            el.future_of(&bexpr, Some(inner), b.span)
        } else {
            let e = el.block(b, Some(&ret));
            el.coerce(e, &ret)
        }
    } else {
        Expr { kind: ExprKind::Unreachable, ty: Ty::Never, span: f.span }
    };
    let cx = el.cxs.pop().unwrap();
    let mut func = ir::Func {
        name,
        params,
        locals: cx.locals,
        ret,
        body,
        is_closure: false,
        export: f.export.clone(),
        extern_: f.extern_.clone(),
    };
    el.finalize(&mut func);
    let closures = std::mem::take(&mut el.closures);
    for (idx, mut cf) in closures {
        el.finalize(&mut cf);
        el.g.funcs[idx] = Some(cf);
    }
    func
}

pub fn fn_display_name(prog: &Program, inst: &FnInst) -> String {
    let f = &prog.fns[inst.fn_id];
    let mut s = String::new();
    match f.owner {
        FnOwner::Impl(iid) => {
            let imp = &prog.impls[iid];
            s.push_str(&prog.ty_str(&imp.self_ty.subst(&inst.targs)));
            if let Some(tr) = &imp.trait_ref {
                s.push_str(" as ");
                s.push_str(&prog.traits[tr.trait_id].name);
            }
            s.push('.');
        }
        FnOwner::Trait(tid) => {
            if let Some(t) = inst.targs.first() {
                s.push_str(&prog.ty_str(t));
                s.push_str(" as ");
            }
            s.push_str(&prog.traits[tid].name);
            s.push('.');
        }
        FnOwner::Free => {
            let m = &prog.modules[f.module];
            if m.pkg.is_source() && m.path != "main" && !m.path.is_empty() {
                s.push_str(&m.path);
                s.push('.');
            }
        }
    }
    s.push_str(&f.name);
    let own = &inst.targs[f.n_outer.min(inst.targs.len())..];
    if !own.is_empty() {
        s.push('<');
        s.push_str(&own.iter().map(|t| prog.ty_str(t)).collect::<Vec<_>>().join(", "));
        s.push('>');
    }
    s
}

enum PathRes {
    Module(ModId),
    Type(Ty),
    Def(Def, Span),
}

fn mk(kind: ExprKind, ty: Ty, span: Span) -> Expr {
    Expr { kind, ty, span }
}

fn unit(span: Span) -> Expr {
    mk(ExprKind::Lit(Lit::Unit), Ty::Unit, span)
}

fn ae(kind: ast::ExprKind, span: Span) -> ast::Expr {
    ast::Expr { kind, span }
}

fn aname(n: &str, span: Span) -> ast::Expr {
    ae(ast::ExprKind::Name(ast::Ident { name: n.to_string(), span }, Vec::new()), span)
}

fn aident(n: &str, span: Span) -> ast::Ident {
    ast::Ident { name: n.to_string(), span }
}

fn acall_method(recv: ast::Expr, m: &str, args: Vec<ast::Expr>, span: Span) -> ast::Expr {
    let f = ae(ast::ExprKind::Field(Box::new(recv), aident(m, span), Vec::new()), span);
    ae(ast::ExprKind::Call(Box::new(f), args), span)
}

fn abind(n: &str, span: Span) -> ast::Pattern {
    ast::Pattern { kind: ast::PatKind::Bind(aident(n, span)), span }
}

fn get_target(base: &str, idx: &str, span: Span) -> ast::Expr {
    ae(ast::ExprKind::Index(Box::new(aname(base, span)), Box::new(aname(idx, span))), span)
}

fn ablock(stmts: Vec<ast::Stmt>, tail: Option<ast::Expr>, span: Span) -> ast::Block {
    ast::Block { stmts, tail: tail.map(Box::new), span }
}

fn alet(mutable: bool, n: &str, init: ast::Expr, span: Span) -> ast::Stmt {
    ast::Stmt::Let { mutable, pat: abind(n, span), ty: None, init, else_block: None, span }
}

fn pat_binds(p: &ast::Pattern, out: &mut Vec<ast::Ident>) {
    match &p.kind {
        ast::PatKind::Bind(id) => {
            if !out.iter().any(|o| o.name == id.name) {
                out.push(id.clone())
            }
        }
        ast::PatKind::Tuple(ps) | ast::PatKind::TupleStruct(_, ps) => ps.iter().for_each(|p| pat_binds(p, out)),
        ast::PatKind::Struct(_, fs, _) => {
            for (n, p) in fs {
                match p {
                    Some(p) => pat_binds(p, out),
                    None => out.push(n.clone()),
                }
            }
        }
        ast::PatKind::Or(ps) => {
            if let Some(p) = ps.first() {
                pat_binds(p, out)
            }
        }
        ast::PatKind::List(ps, rest) => {
            ps.iter().for_each(|p| pat_binds(p, out));
            if let Some(Some(r)) = rest {
                out.push(r.clone());
            }
        }
        _ => {}
    }
}

fn binop_method(op: BinOp) -> Option<(&'static str, &'static str)> {
    Some(match op {
        BinOp::Add => ("Add", "add"),
        BinOp::Sub => ("Sub", "sub"),
        BinOp::Mul => ("Mul", "mul"),
        BinOp::Div => ("Div", "div"),
        BinOp::Rem => ("Rem", "rem"),
        BinOp::Eq => ("Eq", "eq"),
        BinOp::Ne => ("Eq", "ne"),
        BinOp::Lt => ("Ord", "lt"),
        BinOp::Le => ("Ord", "le"),
        BinOp::Gt => ("Ord", "gt"),
        BinOp::Ge => ("Ord", "ge"),
        _ => return None,
    })
}

fn prim_of(op: BinOp) -> PrimOp {
    match op {
        BinOp::Add => PrimOp::Add,
        BinOp::Sub => PrimOp::Sub,
        BinOp::Mul => PrimOp::Mul,
        BinOp::Div => PrimOp::Div,
        BinOp::Rem => PrimOp::Rem,
        BinOp::Shl => PrimOp::Shl,
        BinOp::Shr => PrimOp::Shr,
        BinOp::BitAnd => PrimOp::BitAnd,
        BinOp::BitOr => PrimOp::BitOr,
        BinOp::BitXor => PrimOp::BitXor,
        BinOp::Eq => PrimOp::Eq,
        BinOp::Ne => PrimOp::Ne,
        BinOp::Lt => PrimOp::Lt,
        BinOp::Le => PrimOp::Le,
        BinOp::Gt => PrimOp::Gt,
        BinOp::Ge => PrimOp::Ge,
        BinOp::And | BinOp::Or => unreachable!(),
    }
}

impl<'g, 'p> Elab<'g, 'p> {
    // ---------------- diagnostics & types ----------------
    fn err(&mut self, span: Span, msg: impl Into<String>) {
        self.g.error(Diag::new(span, msg));
    }

    fn warn_local_name(&mut self, id: &ast::Ident) {
        if self.prog.modules[self.module].pkg.is_source() {
            if let Some(warning) = Naming::Snake.warning(id) {
                self.g.warn(warning);
            }
        }
    }

    fn tys(&self, t: &Ty) -> String {
        let z = self.zonk(t);
        self.prog.ty_str(&z)
    }

    fn fresh(&mut self) -> Ty {
        self.vars.push((None, VarKind::General));
        Ty::Var((self.vars.len() - 1) as u32)
    }

    fn fresh_kind(&mut self, k: VarKind) -> Ty {
        self.vars.push((None, k));
        Ty::Var((self.vars.len() - 1) as u32)
    }

    fn resolve(&self, t: &Ty) -> Ty {
        let mut t = t.clone();
        while let Ty::Var(v) = t {
            match &self.vars[v as usize].0 {
                Some(b) => t = b.clone(),
                None => return t,
            }
        }
        t
    }

    fn var_kind(&self, t: &Ty) -> Option<VarKind> {
        match self.resolve(t) {
            Ty::Var(v) => Some(self.vars[v as usize].1),
            _ => None,
        }
    }

    fn zonk(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| self.zonk(t)).collect()),
            Ty::Adt(id, ts) => Ty::Adt(id, ts.iter().map(|t| self.zonk(t)).collect()),
            Ty::Array(t) => Ty::Array(Box::new(self.zonk(&t))),
            Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(|t| self.zonk(t)).collect(), Box::new(self.zonk(&r))),
            Ty::Dyn(id, ts, a) => Ty::Dyn(id, ts.iter().map(|t| self.zonk(t)).collect(), a.iter().map(|(n, t)| (n.clone(), self.zonk(t))).collect()),
            Ty::Proj(b, n) => {
                let b = self.zonk(&b);
                self.prog.normalize_proj(Ty::Proj(Box::new(b), n))
            }
            other => other,
        }
    }

    /// Zonk with defaults applied for literal variables.
    fn zonk_default(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Var(v) => match self.vars[v as usize].1 {
                VarKind::Int => INT,
                VarKind::Float => Ty::Float(FloatTy::F64),
                VarKind::General => Ty::Var(v),
            },
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| self.zonk_default(t)).collect()),
            Ty::Adt(id, ts) => Ty::Adt(id, ts.iter().map(|t| self.zonk_default(t)).collect()),
            Ty::Array(t) => Ty::Array(Box::new(self.zonk_default(&t))),
            Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(|t| self.zonk_default(t)).collect(), Box::new(self.zonk_default(&r))),
            Ty::Dyn(id, ts, a) => Ty::Dyn(id, ts.iter().map(|t| self.zonk_default(t)).collect(), a.iter().map(|(n, t)| (n.clone(), self.zonk_default(t))).collect()),
            Ty::Proj(b, n) => {
                let b = self.zonk_default(&b);
                self.prog.normalize_proj(Ty::Proj(Box::new(b), n))
            }
            other => other,
        }
    }

    fn occurs(&self, v: u32, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(w) => v == w,
            Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(|t| self.occurs(v, t)),
            Ty::Array(t) => self.occurs(v, &t),
            Ty::Fn(ps, r) => ps.iter().any(|t| self.occurs(v, t)) || self.occurs(v, &r),
            Ty::Dyn(_, ts, a) => ts.iter().any(|t| self.occurs(v, t)) || a.iter().any(|(_, t)| self.occurs(v, t)),
            _ => false,
        }
    }

    fn unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (&a, &b) {
            (Ty::Error, _) | (_, Ty::Error) => true,
            (Ty::Never, _) | (_, Ty::Never) => true,
            (Ty::Var(x), Ty::Var(y)) if x == y => true,
            (Ty::Var(x), Ty::Var(y)) => {
                let kx = self.vars[*x as usize].1;
                let ky = self.vars[*y as usize].1;
                let k = match (kx, ky) {
                    (VarKind::General, k) | (k, VarKind::General) => k,
                    (VarKind::Float, _) | (_, VarKind::Float) => VarKind::Float,
                    _ => VarKind::Int,
                };
                self.vars[*y as usize].1 = k;
                self.vars[*x as usize].0 = Some(b.clone());
                true
            }
            (Ty::Var(x), t) | (t, Ty::Var(x)) => {
                let k = self.vars[*x as usize].1;
                let ok = match k {
                    VarKind::General => true,
                    VarKind::Int => t.is_numeric(),
                    VarKind::Float => matches!(t, Ty::Float(_)),
                };
                if !ok || self.occurs(*x, t) {
                    return false;
                }
                self.vars[*x as usize].0 = Some(t.clone());
                true
            }
            (Ty::Tuple(x), Ty::Tuple(y)) => x.len() == y.len() && x.clone().iter().zip(y.clone().iter()).all(|(p, q)| self.unify(p, q)),
            (Ty::Adt(i, x), Ty::Adt(j, y)) => i == j && x.clone().iter().zip(y.clone().iter()).all(|(p, q)| self.unify(p, q)),
            (Ty::Array(x), Ty::Array(y)) => {
                let (x, y) = (x.clone(), y.clone());
                self.unify(&x, &y)
            }
            (Ty::Fn(px, rx), Ty::Fn(py, ry)) => {
                let (px, rx, py, ry) = (px.clone(), rx.clone(), py.clone(), ry.clone());
                px.len() == py.len() && px.iter().zip(py.iter()).all(|(p, q)| self.unify(p, q)) && self.unify(&rx, &ry)
            }
            (Ty::Dyn(i, x, ax), Ty::Dyn(j, y, ay)) => {
                let (x, y, ax, ay) = (x.clone(), y.clone(), ax.clone(), ay.clone());
                i == j && x.iter().zip(y.iter()).all(|(p, q)| self.unify(p, q)) && ax.len() == ay.len() && ax.iter().zip(ay.iter()).all(|(p, q)| p.0 == q.0 && self.unify(&p.1, &q.1))
            }
            _ => a == b,
        }
    }

    fn try_unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let saved = self.vars.clone();
        if self.unify(a, b) {
            true
        } else {
            self.vars = saved;
            false
        }
    }

    fn mismatch(&mut self, span: Span, expected: &Ty, found: &Ty) {
        let e = self.prog.ty_str(&self.zonk_default(expected));
        let f = self.prog.ty_str(&self.zonk_default(found));
        self.err(span, format!("mismatched types: expected `{e}`, found `{f}`"));
    }

    fn resolve_ty(&mut self, t: &ast::TypeExpr) -> Ty {
        let cx = TyCx { module: self.module, generics: &self.gen_names, self_ty: self.self_ty.clone(), self_impl: self.self_impl };
        match self.prog.resolve_ty(&cx, t) {
            Ok(ty) => self.prog.normalize_proj(ty.subst(&self.targs)),
            Err(d) => {
                self.g.error(d);
                Ty::Error
            }
        }
    }

    /// Coerce an expression to an expected type (widening, dyn, views).
    fn coerce(&mut self, e: Expr, expected: &Ty) -> Expr {
        let actual = self.resolve(&e.ty);
        let exp = self.resolve(expected);
        if matches!(actual, Ty::Never | Ty::Error) || matches!(exp, Ty::Error) {
            return e;
        }
        let actual = if matches!(exp, Ty::Dyn(..)) && matches!(self.var_kind(&actual), Some(VarKind::Int | VarKind::Float)) { self.default_var(&actual) } else { actual };
        if let Ty::Dyn(tid, targs, assoc) = &exp {
            if !matches!(actual, Ty::Dyn(..) | Ty::Var(_)) {
                let concrete = self.zonk_default(&actual);
                if let Err(why) = self.prog.dyn_compatible(*tid) {
                    self.err(e.span, format!("trait `{}` cannot be used as `dyn {}`: {why}", self.prog.traits[*tid].name, self.prog.traits[*tid].name));
                    return e;
                }
                let tr = TraitRef { trait_id: *tid, args: targs.iter().map(|t| self.zonk(t)).collect() };
                if !self.prog.implements(&concrete, &tr, 0) {
                    let ts = self.tys(&concrete);
                    self.err(e.span, format!("`{ts}` does not implement `{}`", self.prog.trait_ref_str(&tr)));
                    return e;
                }
                for (n, at) in assoc {
                    let actual_assoc = self.prog.normalize_proj(Ty::Proj(Box::new(concrete.clone()), n.clone()));
                    if !self.unify(&actual_assoc, at) {
                        self.err(e.span, format!("associated type `{n}` does not match"));
                    }
                }
                let span = e.span;
                return mk(ExprKind::DynNew(Box::new(e), tr), exp.clone(), span);
            }
        }
        if actual.is_numeric() && exp.is_numeric() && actual != exp && widens_to(&actual, &exp) {
            let span = e.span;
            return mk(ExprKind::Cast(Box::new(e)), exp, span);
        }
        if let (Ty::Adt(a, aargs), Ty::Adt(b, bargs)) = (&actual, &exp) {
            if a != b {
                let pairs = [("List", "ListView"), ("Map", "MapView"), ("Set", "SetView")];
                for (from, to) in pairs {
                    if self.prog.known.get(from).is_some() && *a == self.prog.known_adt(from) && *b == self.prog.known_adt(to) {
                        let (aargs, bargs) = (aargs.clone(), bargs.clone());
                        for (x, y) in aargs.iter().zip(bargs.iter()) {
                            self.unify(x, y);
                        }
                        let span = e.span;
                        return self.method_call(e, "view", &[], Vec::new(), span, Some(&exp));
                    }
                }
            }
        }
        if !self.unify(&actual, &exp) {
            self.mismatch(e.span, &exp, &actual);
        }
        e
    }

    // ---------------- scopes ----------------
    fn cx(&mut self) -> &mut FnCx {
        self.cxs.last_mut().unwrap()
    }

    fn push_scope(&mut self) {
        self.cx().scopes.push(Vec::new());
    }

    fn pop_scope(&mut self) {
        self.cx().scopes.pop();
    }

    fn new_local(&mut self, name: &str, ty: Ty, mutable: bool) -> LocalId {
        let cx = self.cx();
        let id = cx.locals.len();
        cx.locals.push(LocalInfo { name: name.to_string(), ty, mutable, boxed: false, is_param: false, capture: None });
        id
    }

    fn bind_local(&mut self, name: &str, id: LocalId) {
        self.cx().scopes.last_mut().unwrap().push((name.to_string(), id));
    }

    fn tmp_name(&mut self, base: &str) -> String {
        self.next_tmp += 1;
        format!("${base}{}", self.next_tmp)
    }

    fn lookup_local(&mut self, name: &str) -> Option<LocalId> {
        let n = self.cxs.len();
        for depth in (0..n).rev() {
            let found = self.cxs[depth].scopes.iter().rev().find_map(|s| s.iter().rev().find(|(nm, _)| nm == name).map(|(_, id)| *id));
            if let Some(mut id) = found {
                for level in depth + 1..n {
                    id = self.capture_into(level, id);
                }
                return Some(id);
            }
        }
        None
    }

    fn capture_into(&mut self, level: usize, parent: LocalId) -> LocalId {
        if let Some((_, inner)) = self.cxs[level].captures.iter().find(|(p, _)| *p == parent) {
            return *inner;
        }
        let pinfo = self.cxs[level - 1].locals[parent].clone();
        if pinfo.mutable {
            self.cxs[level - 1].locals[parent].boxed = true;
        }
        let cx = &mut self.cxs[level];
        let idx = cx.captures.len();
        let id = cx.locals.len();
        cx.locals.push(LocalInfo { name: pinfo.name.clone(), ty: pinfo.ty.clone(), mutable: pinfo.mutable, boxed: pinfo.mutable, is_param: false, capture: Some(idx) });
        cx.captures.push((parent, id));
        id
    }

    fn local_ty(&self, id: LocalId) -> Ty {
        self.cxs.last().unwrap().locals[id].ty.clone()
    }

    fn local_expr(&self, id: LocalId, span: Span) -> Expr {
        mk(ExprKind::Local(id), self.local_ty(id), span)
    }

    // ---------------- blocks & statements ----------------
    fn block(&mut self, b: &ast::Block, expect: Option<&Ty>) -> Expr {
        self.push_scope();
        let mut stmts = Vec::new();
        let mut diverges = false;
        for s in &b.stmts {
            match s {
                ast::Stmt::Let { mutable, pat, ty, init, else_block, span } => {
                    if let Some(eb) = else_block {
                        self.let_else(*mutable, pat, ty.as_ref(), init, eb, *span, &mut stmts);
                        continue;
                    }
                    let st = self.let_stmt(*mutable, pat, ty.as_ref(), init);
                    if let Stmt::Let(_, e) = &st {
                        if matches!(self.resolve(&e.ty), Ty::Never) {
                            diverges = true;
                        }
                    }
                    stmts.push(st);
                }
                ast::Stmt::Expr(e) => {
                    let ie = self.expr(e, None);
                    if matches!(self.resolve(&ie.ty), Ty::Never) {
                        diverges = true;
                    }
                    stmts.push(Stmt::Expr(ie));
                }
            }
        }
        let (tail, ty) = match &b.tail {
            Some(t) => {
                if matches!(expect.map(|t| self.resolve(t)), Some(Ty::Unit)) {
                    let e = self.expr(t, None);
                    let rt = self.resolve(&e.ty);
                    if matches!(rt, Ty::Unit | Ty::Never) {
                        let ty = e.ty.clone();
                        (Some(Box::new(e)), ty)
                    } else {
                        let span = e.span;
                        (Some(Box::new(mk(ExprKind::Discard(Box::new(e)), Ty::Unit, span))), Ty::Unit)
                    }
                } else {
                    let e = self.expr(t, expect);
                    let ty = e.ty.clone();
                    (Some(Box::new(e)), ty)
                }
            }
            None => (None, if diverges { Ty::Never } else { Ty::Unit }),
        };
        self.pop_scope();
        mk(ExprKind::Block(stmts, tail), ty, b.span)
    }

    fn let_stmt(&mut self, mutable: bool, pat: &ast::Pattern, ty: Option<&ast::TypeExpr>, init: &ast::Expr) -> Stmt {
        let ann = ty.map(|t| self.resolve_ty(t));
        let init_e = match &ann {
            Some(t) => {
                let e = self.expr(init, Some(t));
                self.coerce(e, t)
            }
            None => self.expr(init, None),
        };
        let pty = ann.unwrap_or_else(|| init_e.ty.clone());
        let mut binds = Vec::new();
        let p = self.pattern(pat, &pty, mutable, &mut binds, None);
        for (n, id) in binds {
            self.bind_local(&n, id);
        }
        Stmt::Let(p, init_e)
    }

    fn let_else(&mut self, mutable: bool, pat: &ast::Pattern, ty: Option<&ast::TypeExpr>, init: &ast::Expr, eb: &ast::Block, span: Span, stmts: &mut Vec<Stmt>) {
        // let PAT = INIT else { ELSE }  ==>  let (a, b) = match INIT { PAT -> (a, b), _ -> ELSE }
        let mut names = Vec::new();
        pat_binds(pat, &mut names);
        let tuple = if names.len() == 1 {
            aname(&names[0].name, span)
        } else if names.is_empty() {
            ae(ast::ExprKind::Unit, span)
        } else {
            ae(ast::ExprKind::Tuple(names.iter().map(|n| aname(&n.name, n.span)).collect()), span)
        };
        let init = match ty {
            Some(t) => {
                let tmp = self.tmp_name("le");
                let st = self.let_stmt(false, &abind(&tmp, span), Some(t), init);
                stmts.push(st);
                aname(&tmp, span)
            }
            None => init.clone(),
        };
        let else_expr = ae(ast::ExprKind::Block(eb.clone()), eb.span);
        let m = ae(
            ast::ExprKind::Match {
                scrut: Box::new(init),
                arms: vec![
                    ast::Arm { pat: pat.clone(), guard: None, body: tuple, span },
                    ast::Arm { pat: ast::Pattern { kind: ast::PatKind::Wild, span }, guard: None, body: else_expr, span: eb.span },
                ],
            },
            span,
        );
        // check else diverges
        let lhs = if names.len() == 1 {
            abind(&names[0].name, span)
        } else if names.is_empty() {
            ast::Pattern { kind: ast::PatKind::Wild, span }
        } else {
            ast::Pattern { kind: ast::PatKind::Tuple(names.iter().map(|n| abind(&n.name, n.span)).collect()), span }
        };
        let st = self.let_stmt(mutable, &lhs, None, &m);
        if let Stmt::Let(_, ir::Expr { kind: ExprKind::Match(_, arms), .. }) = &st {
            if let Some(last) = arms.last() {
                if !matches!(self.resolve(&last.body.ty), Ty::Never) {
                    self.err(eb.span, "the `else` block of `let ... else` must not fall through (use `return`, `break`, `continue` or `panic`)");
                }
            }
        }
        stmts.push(st);
    }

    // ---------------- expressions ----------------
    fn expr_coerce(&mut self, e: &ast::Expr, expected: &Ty) -> Expr {
        let ie = self.expr(e, Some(expected));
        self.coerce(ie, expected)
    }

    fn expr(&mut self, e: &ast::Expr, expect: Option<&Ty>) -> Expr {
        let span = e.span;
        match &e.kind {
            ast::ExprKind::Int(n) => {
                let ty = match expect.map(|t| self.resolve(t)) {
                    Some(t @ (Ty::Int(_) | Ty::Float(_))) => t,
                    _ => self.fresh_kind(VarKind::Int),
                };
                mk(ExprKind::Lit(Lit::Int(*n as i128)), ty, span)
            }
            ast::ExprKind::Float(f) => {
                let ty = match expect.map(|t| self.resolve(t)) {
                    Some(t @ Ty::Float(_)) => t,
                    _ => self.fresh_kind(VarKind::Float),
                };
                mk(ExprKind::Lit(Lit::Float(*f)), ty, span)
            }
            ast::ExprKind::Bool(b) => mk(ExprKind::Lit(Lit::Bool(*b)), Ty::Bool, span),
            ast::ExprKind::Char(c) => mk(ExprKind::Lit(Lit::Char(*c)), Ty::Char, span),
            ast::ExprKind::Unit => unit(span),
            ast::ExprKind::Str(pieces) => self.string(pieces, span),
            ast::ExprKind::Name(id, targs) => self.name_expr(id, targs, span, expect),
            ast::ExprKind::SelfValue => match self.lookup_local("self") {
                Some(id) => self.local_expr(id, span),
                None => {
                    self.err(span, "`self` is only available in methods");
                    mk(ExprKind::Unreachable, Ty::Error, span)
                }
            },
            ast::ExprKind::SelfType => {
                self.err(span, "`Self` is a type, not a value");
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
            ast::ExprKind::Field(base, name, targs) => self.field_expr(base, name, targs, span, expect),
            ast::ExprKind::TupleField(base, idx) => {
                let b = self.expr(base, None);
                let bt = self.resolve(&b.ty);
                match bt {
                    Ty::Tuple(ts) if (*idx as usize) < ts.len() => {
                        let t = ts[*idx as usize].clone();
                        mk(ExprKind::Field(Box::new(b), None, *idx as usize), t, span)
                    }
                    Ty::Error => mk(ExprKind::Unreachable, Ty::Error, span),
                    _ => {
                        let s = self.tys(&bt);
                        self.err(span, format!("no field `{idx}` on type `{s}`"));
                        mk(ExprKind::Unreachable, Ty::Error, span)
                    }
                }
            }
            ast::ExprKind::Call(callee, args) => self.call_expr(callee, args, span, expect),
            ast::ExprKind::Index(base, idx) => {
                let b = self.expr(base, None);
                if let Some(elem) = self.list_elem(&b.ty) {
                    return self.list_access(b, elem, idx, None, span);
                }
                self.method_call(b, "index", &[], vec![(**idx).clone()], span, expect)
            }
            ast::ExprKind::Try(inner) => self.try_expr(inner, span),
            ast::ExprKind::Await(inner) => {
                if !self.cxs.last().unwrap().is_async {
                    self.err(span, "`.await` is only allowed inside `async` functions, `async` closures and tests");
                }
                let e = self.expr(inner, None);
                let t = self.resolve(&e.ty);
                let ok = match &t {
                    Ty::Adt(id, _) => {
                        let n = self.prog.adts[*id].name.as_str();
                        self.prog.adts[*id].pkg == Pkg::Prelude && (n == "Future" || n == "Task")
                    }
                    Ty::Error => true,
                    _ => false,
                };
                if !ok {
                    let s = self.tys(&t);
                    self.err(span, format!("`.await` needs a future, found `{s}`"));
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                }
                self.method_call(e, "__await", &[], Vec::new(), span, expect)
            }
            ast::ExprKind::Unary(op, inner) => self.unary(*op, inner, span, expect),
            ast::ExprKind::Binary(op, l, r) => self.binary(*op, l, r, span, expect),
            ast::ExprKind::Assign(op, l, r) => self.assign(*op, l, r, span),
            ast::ExprKind::Range(a, b, inclusive) => {
                let elem = match expect.map(|t| self.resolve(t)) {
                    Some(Ty::Adt(id, args)) if self.prog.known.contains_key("Range") && id == self.prog.known_adt("Range") => args[0].clone(),
                    _ => self.fresh_kind(VarKind::Int),
                };
                let ea = self.expr_coerce(a, &elem);
                let eb = self.expr_coerce(b, &elem);
                let rid = self.prog.known_adt("Range");
                mk(ExprKind::StructNew(vec![ea, eb, mk(ExprKind::Lit(Lit::Bool(*inclusive)), Ty::Bool, span)]), Ty::Adt(rid, vec![elem]), span)
            }
            ast::ExprKind::Tuple(items) => {
                let exp_items = match expect.map(|t| self.resolve(t)) {
                    Some(Ty::Tuple(ts)) if ts.len() == items.len() => Some(ts),
                    _ => None,
                };
                let mut es = Vec::new();
                for (i, it) in items.iter().enumerate() {
                    let ie = match &exp_items {
                        Some(ts) => self.expr_coerce(it, &ts[i]),
                        None => self.expr(it, None),
                    };
                    es.push(ie);
                }
                let ty = Ty::Tuple(es.iter().map(|e| e.ty.clone()).collect());
                mk(ExprKind::TupleNew(es), ty, span)
            }
            ast::ExprKind::List(items) => self.list_lit(items, span, expect),
            ast::ExprKind::Map(entries) => {
                let mut stmts = Vec::new();
                let tmp = self.tmp_name("map");
                let map_ty = ae(ast::ExprKind::Name(aident("Map", span), Vec::new()), span);
                stmts.push(alet(false, &tmp, acall_method(map_ty, "new", Vec::new(), span), span));
                for (k, v) in entries {
                    stmts.push(ast::Stmt::Expr(acall_method(aname(&tmp, span), "insert", vec![k.clone(), v.clone()], span)));
                }
                let b = ablock(stmts, Some(aname(&tmp, span)), span);
                self.block(&b, expect)
            }
            ast::ExprKind::Struct { path, args, fields, base } => self.struct_lit(path, args, fields, base.as_deref(), span, expect),
            ast::ExprKind::Block(b) => self.block(b, expect),
            ast::ExprKind::If { cond, then, els } => self.if_expr(cond, then, els.as_deref(), span, expect),
            ast::ExprKind::Match { scrut, arms } => self.match_expr(scrut, arms, span, expect),
            ast::ExprKind::Loop(b) => {
                let label = self.next_label;
                self.next_label += 1;
                let bt = self.fresh();
                self.cx().loops.push(LoopCx { label, break_ty: bt.clone(), allows_value: true, has_break: false });
                let body = self.block(b, Some(&Ty::Unit));
                let lc = self.cx().loops.pop().unwrap();
                let ty = if lc.has_break { bt } else { Ty::Never };
                mk(ExprKind::Loop(label, Box::new(body)), ty, span)
            }
            ast::ExprKind::While(cond, body) => self.while_expr(cond, body, span),
            ast::ExprKind::For(pat, iter, body) => self.for_expr(pat, iter, body, span),
            ast::ExprKind::Closure { is_async, params, ret, body } => {
                if *is_async {
                    self.async_closure(params, ret.as_ref(), body, span, expect)
                } else {
                    self.closure(params, ret.as_ref(), body, span, expect)
                }
            }
            ast::ExprKind::Return(v) => {
                let ret = self.cx().ret.clone();
                let val = match v {
                    Some(v) => self.expr_coerce(v, &ret),
                    None => {
                        if !self.unify(&ret, &Ty::Unit) {
                            let r = self.tys(&ret);
                            self.err(span, format!("`return` without a value in a function returning `{r}`"));
                        }
                        unit(span)
                    }
                };
                mk(ExprKind::Return(Box::new(val)), Ty::Never, span)
            }
            ast::ExprKind::Break(v) => {
                let Some(lc) = self.cx().loops.last() else {
                    self.err(span, "`break` outside of a loop");
                    return mk(ExprKind::Unreachable, Ty::Never, span);
                };
                let (label, bt, allows) = (lc.label, lc.break_ty.clone(), lc.allows_value);
                self.cx().loops.last_mut().unwrap().has_break = true;
                let val = match v {
                    Some(v) => {
                        if !allows {
                            self.err(span, "`break` with a value is only allowed inside `loop`");
                        }
                        Some(Box::new(self.expr_coerce(v, &bt)))
                    }
                    None => {
                        if !self.unify(&bt, &Ty::Unit) {
                            self.err(span, "this `loop` breaks with a value elsewhere; `break` needs a value here too");
                        }
                        None
                    }
                };
                mk(ExprKind::Break(label, val), Ty::Never, span)
            }
            ast::ExprKind::Continue => {
                let Some(lc) = self.cx().loops.last() else {
                    self.err(span, "`continue` outside of a loop");
                    return mk(ExprKind::Unreachable, Ty::Never, span);
                };
                mk(ExprKind::Continue(lc.label), Ty::Never, span)
            }
        }
    }

    fn string(&mut self, pieces: &[ast::StrPiece], span: Span) -> Expr {
        if pieces.len() == 1 {
            if let ast::StrPiece::Lit(s) = &pieces[0] {
                return mk(ExprKind::Lit(Lit::Str(s.clone())), Ty::Str, span);
            }
        }
        let mut parts = Vec::new();
        for p in pieces {
            match p {
                ast::StrPiece::Lit(s) => {
                    if !s.is_empty() {
                        parts.push(mk(ExprKind::Lit(Lit::Str(s.clone())), Ty::Str, span));
                    }
                }
                ast::StrPiece::Expr(e) => {
                    let ie = self.expr(e, None);
                    parts.push(self.to_str(ie));
                }
            }
        }
        mk(ExprKind::StrConcat(parts), Ty::Str, span)
    }

    fn to_str(&mut self, e: Expr) -> Expr {
        let t = self.resolve(&e.ty);
        if t == Ty::Str {
            return e;
        }
        let span = e.span;
        let show = self.prog.known_trait("Show");
        let t2 = self.default_var(&t);
        if !matches!(t2, Ty::Error | Ty::Var(_)) && !self.prog.implements(&self.zonk(&t2), &TraitRef { trait_id: show, args: vec![] }, 0) {
            let s = self.tys(&t2);
            self.err(span, format!("`{s}` does not implement `Show`, so it cannot be interpolated into a string"));
            return mk(ExprKind::Unreachable, Ty::Str, span);
        }
        self.method_call(e, "show", &[], Vec::new(), span, Some(&Ty::Str))
    }

    fn default_var(&mut self, t: &Ty) -> Ty {
        let t = self.resolve(t);
        match self.var_kind(&t) {
            Some(VarKind::Int) => {
                self.unify(&t, &INT);
                INT
            }
            Some(VarKind::Float) => {
                let f = Ty::Float(FloatTy::F64);
                self.unify(&t, &f);
                f
            }
            _ => t,
        }
    }

    fn list_lit(&mut self, items: &[ast::Expr], span: Span, expect: Option<&Ty>) -> Expr {
        let list_id = self.prog.known_adt("List");
        let elem = match expect.map(|t| self.resolve(t)) {
            Some(Ty::Adt(id, args)) if id == list_id => args[0].clone(),
            Some(Ty::Adt(id, args)) if self.prog.known.contains_key("ListView") && id == self.prog.known_adt("ListView") => args[0].clone(),
            _ => self.fresh(),
        };
        let mut es = Vec::new();
        for it in items {
            let ie = self.expr_coerce(it, &elem);
            es.push(ie);
        }
        let n = es.len() as i128;
        let fields = self.prog.struct_fields(list_id);
        let len_idx = fields.iter().position(|f| f.name == "len").unwrap_or(0);
        let mut vals = vec![
            mk(ExprKind::Lit(Lit::Int(n)), INT, span),
            mk(ExprKind::ArrayLit(es), Ty::Array(Box::new(elem.clone())), span),
        ];
        if len_idx == 1 {
            vals.swap(0, 1);
        }
        mk(ExprKind::StructNew(vals), Ty::Adt(list_id, vec![elem]), span)
    }

    /// Resolve a path-like expression that does not start with a local.
    fn try_path(&mut self, e: &ast::Expr) -> Option<PathRes> {
        match &e.kind {
            ast::ExprKind::SelfType => match &self.self_ty {
                Some(t) => Some(PathRes::Type(t.clone())),
                None => None,
            },
            ast::ExprKind::Name(id, targs) => {
                if self.lookup_local_peek(&id.name) {
                    return None;
                }
                // generic parameters are concrete here (generics are monomorphized)
                if let Some(i) = self.gen_names.iter().position(|g| g == &id.name) {
                    if let Some(t) = self.targs.get(i) {
                        return Some(PathRes::Type(t.clone()));
                    }
                }
                let def = self.prog.lookup(self.module, &id.name)?;
                Some(self.def_res(def, targs, id))
            }
            ast::ExprKind::Field(base, name, targs) => {
                let b = self.try_path(base)?;
                match b {
                    PathRes::Module(m) => match self.prog.module_member(m, &name.name, self.module, name.span) {
                        Ok(def) => Some(self.def_res(def, targs, name)),
                        Err(d) => {
                            self.g.error(d);
                            Some(PathRes::Def(Def::Builtin(Ty::Error), name.span))
                        }
                    },
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn lookup_local_peek(&self, name: &str) -> bool {
        self.cxs.iter().any(|cx| cx.scopes.iter().any(|s| s.iter().any(|(n, _)| n == name)))
    }

    fn def_res(&mut self, def: Def, targs: &[ast::TypeExpr], id: &ast::Ident) -> PathRes {
        match def {
            Def::Module(m) => PathRes::Module(m),
            Def::Adt(_) | Def::Builtin(_) | Def::Alias(_) => {
                let ts: Vec<Ty> = targs.iter().map(|t| self.resolve_ty(t)).collect();
                let ts = if ts.is_empty() {
                    match &def {
                        Def::Adt(aid) => (0..self.prog.adts[*aid].generics.len()).map(|_| self.fresh()).collect(),
                        Def::Builtin(Ty::Array(_)) => vec![self.fresh()],
                        _ => ts,
                    }
                } else {
                    ts
                };
                match self.prog.def_to_ty(def, ts, id.span, id) {
                    Ok(t) => PathRes::Type(t),
                    Err(d) => {
                        self.g.error(d);
                        PathRes::Type(Ty::Error)
                    }
                }
            }
            other => PathRes::Def(other, id.span),
        }
    }

    fn name_expr(&mut self, id: &ast::Ident, targs: &[ast::TypeExpr], span: Span, expect: Option<&Ty>) -> Expr {
        if let Some(l) = self.lookup_local(&id.name) {
            return self.local_expr(l, span);
        }
        match self.prog.lookup(self.module, &id.name) {
            Some(def) => self.def_value(def, targs, span, expect, &id.name),
            None => {
                self.err(id.span, format!("cannot find value `{}` in this scope", id.name));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    fn def_value(&mut self, def: Def, targs: &[ast::TypeExpr], span: Span, expect: Option<&Ty>, name: &str) -> Expr {
        match def {
            Def::Fn(fid) => {
                let f = &self.prog.fns[fid];
                if f.intrinsic.is_some() {
                    self.err(span, format!("intrinsic `{name}` cannot be used as a value"));
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                }
                let explicit: Vec<Ty> = targs.iter().map(|t| self.resolve_ty(t)).collect();
                let targs = self.make_targs(fid, Vec::new(), explicit, span);
                let ps: Vec<Ty> = f.params.iter().map(|(_, t)| self.prog.normalize_proj(t.subst(&targs))).collect();
                let r = self.prog.normalize_proj(f.ret.subst(&targs));
                let ty = Ty::Fn(ps, Box::new(r));
                if let Some(e) = expect {
                    self.try_unify(&ty, e);
                }
                mk(ExprKind::FnValue(FnInst { fn_id: fid, targs }), ty, span)
            }
            Def::Const(cid) => self.const_value(cid, span),
            Def::Variant(aid, vi) => self.variant_value(aid, None, vi, span, expect),
            Def::Adt(_) | Def::Builtin(_) | Def::Alias(_) => {
                self.err(span, format!("`{name}` is a type, not a value"));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
            Def::Trait(_) => {
                self.err(span, format!("`{name}` is a trait, not a value"));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
            Def::Module(_) => {
                self.err(span, format!("`{name}` is a module, not a value"));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    fn const_value(&mut self, cid: usize, span: Span) -> Expr {
        let c = &self.prog.consts[cid];
        if self.const_stack.contains(&cid) {
            self.err(span, "cyclic constant initializer");
            return mk(ExprKind::Unreachable, Ty::Error, span);
        }
        self.const_stack.push(cid);
        let saved_mod = self.module;
        self.module = c.module;
        let value = c.value.clone();
        if !is_const_expr(self.prog, self.module, &value) {
            self.err(c.value.span, "constant initializers must be constant expressions (literals, other constants, operators and constructors)");
        }
        let cx = TyCx { module: c.module, generics: &[], self_ty: None, self_impl: None };
        let decl_ty = self.prog_const_ty(cid, &cx);
        let saved_targs = std::mem::take(&mut self.targs);
        let saved_gen = std::mem::take(&mut self.gen_names);
        let mut e = self.expr_coerce(&value, &decl_ty);
        self.targs = saved_targs;
        self.gen_names = saved_gen;
        self.module = saved_mod;
        self.const_stack.pop();
        e.span = span;
        e
    }

    fn prog_const_ty(&mut self, cid: usize, cx: &TyCx) -> Ty {
        // const types are resolved lazily from the AST type expression stored in the item
        let _ = cx;
        self.prog.consts[cid].ty.clone()
    }

    fn variant_value(&mut self, aid: AdtId, adt_args: Option<Vec<Ty>>, vi: usize, span: Span, expect: Option<&Ty>) -> Expr {
        let adt = &self.prog.adts[aid];
        let AdtKind::Enum(vs) = &adt.kind else { unreachable!() };
        let v = &vs[vi];
        let args = adt_args.unwrap_or_else(|| (0..adt.generics.len()).map(|_| self.fresh()).collect());
        let ty = Ty::Adt(aid, args.clone());
        if let Some(e) = expect {
            self.try_unify(&ty, e);
        }
        if v.shape != Shape::Unit {
            let vname = v.name.clone();
            self.err(span, format!("variant `{vname}` has fields; call it like `{vname}(...)` or use `{vname} {{ ... }}`"));
            return mk(ExprKind::Unreachable, ty, span);
        }
        mk(ExprKind::EnumNew(vi, Vec::new()), ty, span)
    }

    fn make_targs(&mut self, fid: FnId, prefix: Vec<Ty>, explicit: Vec<Ty>, span: Span) -> Vec<Ty> {
        let f = &self.prog.fns[fid];
        let mut targs = prefix;
        while targs.len() < f.n_outer {
            targs.push(self.fresh());
        }
        let own = f.generics.len() - f.n_outer;
        if !explicit.is_empty() {
            if explicit.len() != own {
                self.err(span, format!("`{}` expects {own} type argument(s), found {}", f.name, explicit.len()));
            }
            for (i, t) in explicit.into_iter().enumerate() {
                if i < own {
                    targs.push(t);
                }
            }
        }
        while targs.len() < f.generics.len() {
            targs.push(self.fresh());
        }
        targs
    }

    fn field_expr(&mut self, base: &ast::Expr, name: &ast::Ident, targs: &[ast::TypeExpr], span: Span, expect: Option<&Ty>) -> Expr {
        if let Some(res) = self.try_path(base) {
            match res {
                PathRes::Module(m) => match self.prog.module_member(m, &name.name, self.module, name.span) {
                    Ok(def) => return self.def_value(def, targs, span, expect, &name.name),
                    Err(d) => {
                        self.g.error(d);
                        return mk(ExprKind::Unreachable, Ty::Error, span);
                    }
                },
                PathRes::Type(t) => return self.assoc_value(t, name, targs, span, expect),
                PathRes::Def(..) => {}
            }
        }
        let b = self.expr(base, None);
        self.field_of(b, name, span)
    }

    fn field_of(&mut self, b: Expr, name: &ast::Ident, span: Span) -> Expr {
        let bt = self.resolve(&b.ty);
        match &bt {
            Ty::Adt(id, args) => {
                if let AdtKind::Struct(fields) = &self.prog.adts[*id].kind {
                    if let Some(i) = fields.iter().position(|f| f.name == name.name) {
                        let f = &fields[i];
                        if !f.public && self.prog.adts[*id].module != self.module && self.prog.adts[*id].pkg != Pkg::Std {
                            self.err(name.span, format!("field `{}` of `{}` is private", name.name, self.prog.adts[*id].name));
                        }
                        let t = self.prog.normalize_proj(f.ty.subst(args));
                        return mk(ExprKind::Field(Box::new(b), None, i), t, span);
                    }
                }
                let s = self.tys(&bt);
                self.err(name.span, format!("no field `{}` on type `{s}`", name.name));
            }
            Ty::Error => {}
            Ty::Var(_) => self.err(span, "the type of this value must be known here; add a type annotation"),
            _ => {
                let s = self.tys(&bt);
                self.err(name.span, format!("no field `{}` on type `{s}`", name.name));
            }
        }
        mk(ExprKind::Unreachable, Ty::Error, span)
    }

    /// `Type.name` used as a value: unit variant or associated function.
    fn assoc_value(&mut self, t: Ty, name: &ast::Ident, targs: &[ast::TypeExpr], span: Span, expect: Option<&Ty>) -> Expr {
        if let Ty::Adt(aid, args) = &t {
            if let AdtKind::Enum(vs) = &self.prog.adts[*aid].kind {
                if let Some(vi) = vs.iter().position(|v| v.name == name.name) {
                    return self.variant_value(*aid, Some(args.clone()), vi, span, expect);
                }
            }
        }
        match self.lookup_assoc_fn(&t, &name.name, span) {
            Some((fid, prefix)) => {
                let explicit: Vec<Ty> = targs.iter().map(|t| self.resolve_ty(t)).collect();
                let targs = self.make_targs(fid, prefix, explicit, span);
                let f = &self.prog.fns[fid];
                let ps: Vec<Ty> = f.params.iter().map(|(_, t)| self.prog.normalize_proj(t.subst(&targs))).collect();
                let r = self.prog.normalize_proj(f.ret.subst(&targs));
                mk(ExprKind::FnValue(FnInst { fn_id: fid, targs }), Ty::Fn(ps, Box::new(r)), span)
            }
            None => {
                let s = self.tys(&t);
                self.err(name.span, format!("no associated item `{}` on type `{s}`", name.name));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    // ---------------- calls ----------------
    fn call_expr(&mut self, callee: &ast::Expr, args: &[ast::Expr], span: Span, expect: Option<&Ty>) -> Expr {
        match &callee.kind {
            ast::ExprKind::Field(base, name, targs) => {
                if let Some(res) = self.try_path(base) {
                    match res {
                        PathRes::Module(m) => match self.prog.module_member(m, &name.name, self.module, name.span) {
                            Ok(def) => return self.call_def(def, targs, args, span, expect, name),
                            Err(d) => {
                                self.g.error(d);
                                return mk(ExprKind::Unreachable, Ty::Error, span);
                            }
                        },
                        PathRes::Type(t) => return self.static_call(t, name, targs, args, span, expect),
                        PathRes::Def(..) => {}
                    }
                }
                let recv = self.expr(base, None);
                let explicit: Vec<Ty> = targs.iter().map(|t| self.resolve_ty(t)).collect();
                self.method_call(recv, &name.name, &explicit, args.to_vec(), span, expect)
            }
            ast::ExprKind::Name(id, targs) if !self.lookup_local_peek(&id.name) => match self.prog.lookup(self.module, &id.name) {
                Some(def) => self.call_def(def, targs, args, span, expect, id),
                None => {
                    self.err(id.span, format!("cannot find function `{}` in this scope", id.name));
                    for a in args {
                        self.expr(a, None);
                    }
                    mk(ExprKind::Unreachable, Ty::Error, span)
                }
            },
            _ => {
                let f = self.expr(callee, None);
                self.call_value(f, args, span)
            }
        }
    }

    fn call_value(&mut self, f: Expr, args: &[ast::Expr], span: Span) -> Expr {
        let ft = self.resolve(&f.ty);
        match ft {
            Ty::Fn(ps, r) => {
                if ps.len() != args.len() {
                    self.err(span, format!("this function takes {} argument(s) but {} were supplied", ps.len(), args.len()));
                }
                let mut es = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let e = match ps.get(i) {
                        Some(p) => self.expr_coerce(a, p),
                        None => self.expr(a, None),
                    };
                    es.push(e);
                }
                mk(ExprKind::CallIndirect(Box::new(f), es), *r, span)
            }
            Ty::Error => mk(ExprKind::Unreachable, Ty::Error, span),
            Ty::Var(_) => {
                // infer a function type from the call
                let ps: Vec<Ty> = args.iter().map(|_| self.fresh()).collect();
                let r = self.fresh();
                self.unify(&ft, &Ty::Fn(ps.clone(), Box::new(r.clone())));
                let mut es = Vec::new();
                for (a, p) in args.iter().zip(&ps) {
                    es.push(self.expr_coerce(a, p));
                }
                mk(ExprKind::CallIndirect(Box::new(f), es), r, span)
            }
            other => {
                let s = self.tys(&other);
                self.err(span, format!("cannot call a value of type `{s}`"));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    fn call_def(&mut self, def: Def, targs: &[ast::TypeExpr], args: &[ast::Expr], span: Span, expect: Option<&Ty>, name: &ast::Ident) -> Expr {
        match def {
            Def::Fn(fid) => {
                let explicit: Vec<Ty> = targs.iter().map(|t| self.resolve_ty(t)).collect();
                self.call_fn(fid, Vec::new(), explicit, None, args.to_vec(), span, expect)
            }
            Def::Variant(aid, vi) => self.construct_variant(aid, None, vi, args, span, expect),
            Def::Const(_) => {
                let f = self.def_value(def, targs, span, expect, &name.name);
                self.call_value(f, args, span)
            }
            _ => {
                self.err(name.span, format!("`{}` is not a function", name.name));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    fn construct_variant(&mut self, aid: AdtId, adt_args: Option<Vec<Ty>>, vi: usize, args: &[ast::Expr], span: Span, expect: Option<&Ty>) -> Expr {
        let adt = &self.prog.adts[aid];
        let AdtKind::Enum(vs) = &adt.kind else { unreachable!() };
        let v = vs[vi].clone();
        let targs = adt_args.unwrap_or_else(|| (0..adt.generics.len()).map(|_| self.fresh()).collect());
        let ty = Ty::Adt(aid, targs.clone());
        if let Some(e) = expect {
            self.try_unify(&ty, e);
        }
        if v.shape != Shape::Tuple {
            if v.shape == Shape::Unit {
                self.err(span, format!("variant `{}` has no fields", v.name));
            } else {
                self.err(span, format!("variant `{}` has named fields; use `{} {{ ... }}`", v.name, v.name));
            }
            return mk(ExprKind::Unreachable, ty, span);
        }
        if v.fields.len() != args.len() {
            self.err(span, format!("variant `{}` has {} field(s) but {} were supplied", v.name, v.fields.len(), args.len()));
        }
        let mut es = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let e = match v.fields.get(i) {
                Some(f) => {
                    let ft = self.prog.normalize_proj(f.ty.subst(&targs));
                    self.expr_coerce(a, &ft)
                }
                None => self.expr(a, None),
            };
            es.push(e);
        }
        mk(ExprKind::EnumNew(vi, es), ty, span)
    }

    fn static_call(&mut self, t: Ty, name: &ast::Ident, targs: &[ast::TypeExpr], args: &[ast::Expr], span: Span, expect: Option<&Ty>) -> Expr {
        if let Ty::Adt(aid, adt_args) = &t {
            if let AdtKind::Enum(vs) = &self.prog.adts[*aid].kind {
                if let Some(vi) = vs.iter().position(|v| v.name == name.name) {
                    return self.construct_variant(*aid, Some(adt_args.clone()), vi, args, span, expect);
                }
            }
        }
        match self.lookup_assoc_fn(&t, &name.name, span) {
            Some((fid, prefix)) => {
                let explicit: Vec<Ty> = targs.iter().map(|t| self.resolve_ty(t)).collect();
                self.call_fn(fid, prefix, explicit, None, args.to_vec(), span, expect)
            }
            None => {
                let s = self.tys(&t);
                self.err(name.span, format!("no function or variant named `{}` on type `{s}`", name.name));
                for a in args {
                    self.expr(a, None);
                }
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    /// Find `name` among the impls (inherent first, then trait) of a type used in
    /// path position. Returns fn id and the outer type arguments.
    fn lookup_assoc_fn(&mut self, t: &Ty, name: &str, span: Span) -> Option<(FnId, Vec<Ty>)> {
        let found = self.find_method(t, name, span)?;
        Some(found)
    }

    #[allow(clippy::too_many_arguments)]
    fn call_fn(&mut self, fid: FnId, prefix: Vec<Ty>, explicit: Vec<Ty>, recv: Option<Expr>, args: Vec<ast::Expr>, span: Span, expect: Option<&Ty>) -> Expr {
        let f = &self.prog.fns[fid];
        if let Some(msg) = &f.deprecated {
            let m = if msg.is_empty() { String::new() } else { format!(": {msg}") };
            self.g.warn(Diag::new(span, format!("`{}` is deprecated{m}", f.name)));
        }
        if f.module != self.module && !f.is_pub && f.pkg.is_source() {
            self.err(span, format!("`{}` is private", f.name));
        }
        let targs = self.make_targs(fid, prefix, explicit, span);
        let ps: Vec<Ty> = f.params.iter().map(|(_, t)| self.prog.normalize_proj(t.subst(&targs))).collect();
        let ret = self.prog.normalize_proj(f.ret.subst(&targs));
        if let Some(e) = expect {
            if ret.has_vars() {
                let e = e.clone();
                self.try_unify(&ret, &e);
            }
        }
        let nrecv = if recv.is_some() { 1 } else { 0 };
        if ps.len() != args.len() + nrecv {
            let shown = ps.len().saturating_sub(nrecv);
            self.err(span, format!("`{}` takes {shown} argument(s) but {} were supplied", f.name, args.len()));
        }
        let mut es = Vec::new();
        if let Some(r) = recv {
            let r = self.coerce(r, &ps[0]);
            es.push(r);
        }
        for (i, a) in args.iter().enumerate() {
            let e = match ps.get(i + nrecv) {
                Some(p) => self.expr_coerce(a, p),
                None => self.expr(a, None),
            };
            es.push(e);
        }
        if let Some(name) = &f.intrinsic {
            // questions about a type argument, answered here so that `if __is_int<T>()`
            // elaborates only the branch for the actual type
            if matches!(name.as_str(), "is_int" | "int_bits" | "int_signed") {
                let it = match targs.first().map(|t| self.resolve(t)) {
                    Some(Ty::Int(it)) => Some(it),
                    _ => None,
                };
                return match name.as_str() {
                    "is_int" => mk(ExprKind::Lit(Lit::Bool(it.is_some())), Ty::Bool, span),
                    "int_bits" => mk(ExprKind::Lit(Lit::Int(it.map_or(0, |i| i.bits() as i128))), INT, span),
                    _ => mk(ExprKind::Lit(Lit::Bool(it.is_some_and(|i| i.signed()))), Ty::Bool, span),
                };
            }
            return mk(ExprKind::Intrinsic(name.clone(), targs, es), ret, span);
        }
        mk(ExprKind::Call(FnInst { fn_id: fid, targs }, es), ret, span)
    }

    /// Resolve a method on a receiver type. Returns (fn id, outer targs).
    fn find_method(&mut self, rt: &Ty, name: &str, span: Span) -> Option<(FnId, Vec<Ty>)> {
        let prog = self.prog;
        // inherent impls
        let cands = prog.candidate_impls(rt);
        for &iid in &cands {
            let imp = &prog.impls[iid];
            if imp.trait_ref.is_some() {
                continue;
            }
            let Some(&fid) = imp.methods.get(name) else { continue };
            let mut binds = vec![None; imp.generics.len()];
            if prog.match_ty(&imp.self_ty, rt, &mut binds) {
                let mut prefix = Vec::new();
                for b in binds {
                    prefix.push(match b {
                        Some(t) => t,
                        None => self.fresh(),
                    });
                }
                let st = imp.self_ty.subst(&prefix);
                if !self.try_unify(&st, rt) {
                    continue;
                }
                return Some((fid, prefix));
            }
        }
        // trait impls
        let mut found: Vec<(FnId, Vec<Ty>, ImplId)> = Vec::new();
        for &iid in &cands {
            let imp = &prog.impls[iid];
            let Some(tr) = &imp.trait_ref else { continue };
            let td = &prog.traits[tr.trait_id];
            let Some((_, tfid)) = td.methods.iter().find(|(n, _)| n == name) else { continue };
            let mut binds = vec![None; imp.generics.len()];
            if !prog.match_ty(&imp.self_ty, rt, &mut binds) {
                continue;
            }
            // bounds of blanket impls
            let concrete_binds: Vec<Ty> = binds.iter().map(|b| b.clone().unwrap_or(Ty::Var(u32::MAX))).collect();
            let ok = imp.generics.iter().enumerate().all(|(i, g)| {
                g.bounds.iter().all(|b| {
                    let bt = TraitRef { trait_id: b.trait_id, args: b.args.iter().map(|a| a.subst(&concrete_binds)).collect() };
                    matches!(concrete_binds[i], Ty::Var(_)) || prog.implements(&self.zonk(&concrete_binds[i]), &bt, 0)
                })
            });
            if !ok {
                continue;
            }
            let mut prefix = Vec::new();
            for b in binds {
                prefix.push(match b {
                    Some(t) => t,
                    None => self.fresh(),
                });
            }
            match imp.methods.get(name) {
                Some(&fid) => found.push((fid, prefix, iid)),
                None => {
                    let mut p = vec![rt.clone()];
                    p.extend(tr.args.iter().map(|a| a.subst(&prefix)));
                    found.push((*tfid, p, iid));
                }
            }
        }
        if found.len() > 1 {
            // prefer impls whose trait args are fully determined; otherwise ambiguous
            let names: Vec<String> = found.iter().map(|(_, _, iid)| prog.trait_ref_str(prog.impls[*iid].trait_ref.as_ref().unwrap())).collect();
            let same_trait = found.iter().all(|(_, _, iid)| prog.impls[*iid].trait_ref.as_ref().unwrap().trait_id == prog.impls[found[0].2].trait_ref.as_ref().unwrap().trait_id);
            if !same_trait {
                let s = self.tys(rt);
                self.err(span, format!("method `{name}` on `{s}` is ambiguous: it is provided by {}", names.join(" and ")));
            }
        }
        if let Some((fid, prefix, iid)) = found.into_iter().next() {
            let imp = &prog.impls[iid];
            if prog.fns[fid].owner == FnOwner::Impl(iid) {
                let st = imp.self_ty.subst(&prefix);
                self.unify(&st, rt);
            }
            return Some((fid, prefix));
        }
        None
    }

    /// `s.worker(f)`: `f` must name a top-level async function taking a
    /// `worker.Port<In, Out>`; the worker instance runs it by index.
    fn worker_call(&mut self, recv: Expr, arg: &ast::Expr, span: Span) -> Expr {
        let f = self.expr(arg, None);
        let ExprKind::FnValue(inst) = &f.kind else {
            self.err(arg.span, "`worker` takes the name of a top-level async function, not a closure or other value");
            return mk(ExprKind::Unreachable, Ty::Error, span);
        };
        let fd = &self.prog.fns[inst.fn_id];
        if !matches!(fd.owner, FnOwner::Free) || !fd.decl.is_async {
            self.err(arg.span, "`worker` takes the name of a top-level `async fn`");
            return mk(ExprKind::Unreachable, Ty::Error, span);
        }
        let ft = self.resolve(&f.ty);
        let ports = match &ft {
            Ty::Fn(ps, r) if ps.len() == 1 => match (self.resolve(&ps[0]), self.resolve(r)) {
                (Ty::Adt(pid, ta), Ty::Adt(_, ra)) if self.prog.adts[pid].name == "__Port" && ta.len() == 2 && ra.len() == 1 && self.resolve(&ra[0]) == Ty::Unit => Some((ta[0].clone(), ta[1].clone())),
                _ => None,
            },
            _ => None,
        };
        let Some((i, o)) = ports else {
            let s = self.tys(&ft);
            self.err(arg.span, format!("a worker function must have the signature `async fn(worker.Port<In, Out>)`, found `{s}`"));
            return mk(ExprKind::Unreachable, Ty::Error, span);
        };
        let Some(Def::Fn(wm)) = self.prog.lookup(self.prog.prelude, "__worker_main") else {
            self.err(span, "internal error: missing `__worker_main` in the prelude");
            return mk(ExprKind::Unreachable, Ty::Error, span);
        };
        let idx = self.g.reserve();
        let body = mk(ExprKind::Call(FnInst { fn_id: wm, targs: vec![i.clone(), o.clone()] }, vec![f]), Ty::Unit, span);
        let func = ir::Func { name: format!("worker_entry{idx}"), params: Vec::new(), locals: Vec::new(), ret: Ty::Unit, body, is_closure: false, export: None, extern_: None };
        self.closures.push((idx, func));
        let k = self.g.worker_entries.len();
        self.g.worker_entries.push(idx);
        self.method_call(recv, "__start_worker", &[i, o], vec![ae(ast::ExprKind::Int(k as u128), span)], span, None)
    }

    fn method_call(&mut self, recv: Expr, name: &str, explicit: &[Ty], args: Vec<ast::Expr>, span: Span, expect: Option<&Ty>) -> Expr {
        let rt0 = self.resolve(&recv.ty);
        let rt = match self.var_kind(&rt0) {
            Some(VarKind::Int) | Some(VarKind::Float) => self.default_var(&rt0),
            Some(VarKind::General) => {
                self.err(recv.span, format!("the type of this value must be known to call `.{name}()`; add a type annotation"));
                for a in &args {
                    self.expr(a, None);
                }
                return mk(ExprKind::Unreachable, Ty::Error, span);
            }
            None => rt0,
        };
        if rt == Ty::Error {
            for a in &args {
                self.expr(a, None);
            }
            return mk(ExprKind::Unreachable, Ty::Error, span);
        }
        if let Ty::Dyn(tid, targs, assoc) = &rt {
            return self.dyn_call(recv, *tid, targs.clone(), assoc.clone(), name, args, span);
        }
        if name == "worker" && args.len() == 1 && matches!(&rt, Ty::Adt(id, _) if self.prog.adts[*id].name == "Scope" && self.prog.adts[*id].pkg == Pkg::Prelude) {
            return self.worker_call(recv, &args[0], span);
        }
        if let Some((fid, prefix)) = self.find_method(&rt, name, span) {
            if !self.prog.fns[fid].has_self {
                let s = self.tys(&rt);
                self.err(span, format!("`{name}` is an associated function of `{s}`, not a method; call it as `{s}.{name}(...)`"));
            }
            return self.call_fn(fid, prefix, explicit.to_vec(), Some(recv), args, span, expect);
        }
        // a field holding a function
        if let Ty::Adt(id, _) = &rt {
            if let AdtKind::Struct(fields) = &self.prog.adts[*id].kind {
                if fields.iter().any(|f| f.name == name) {
                    let fe = self.field_of(recv, &aident(name, span), span);
                    if matches!(self.resolve(&fe.ty), Ty::Fn(..)) {
                        return self.call_value(fe, &args, span);
                    }
                    self.err(span, format!("field `{name}` is not a function"));
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                }
            }
        }
        let s = self.tys(&rt);
        self.err(span, format!("no method named `{name}` found for type `{s}`"));
        for a in &args {
            self.expr(a, None);
        }
        mk(ExprKind::Unreachable, Ty::Error, span)
    }

    #[allow(clippy::too_many_arguments)]
    fn dyn_call(&mut self, recv: Expr, tid: TraitId, targs: Vec<Ty>, assoc: Vec<(String, Ty)>, name: &str, args: Vec<ast::Expr>, span: Span) -> Expr {
        let prog = self.prog;
        for t in prog.trait_closure(tid) {
            if let Some((_, fid)) = prog.traits[t].methods.iter().find(|(n, _)| n == name) {
                if let Err(why) = prog.vtable_ok(*fid) {
                    self.err(span, format!("method `{name}` cannot be called on `dyn {}`: it {why}", prog.traits[tid].name));
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                }
                let f = &prog.fns[*fid];
                // map: Param(0)=dyn type, Param(1..)=trait args (for supertraits, use their args)
                let tr_args = if t == tid {
                    targs.clone()
                } else {
                    prog.traits[tid].supertraits.iter().find(|s| s.trait_id == t).map(|s| {
                        let mut m = vec![recv.ty.clone()];
                        m.extend(targs.iter().cloned());
                        s.args.iter().map(|a| a.subst(&m)).collect()
                    }).unwrap_or_default()
                };
                let mut m = vec![recv.ty.clone()];
                m.extend(tr_args.iter().cloned());
                let fix = |ty: &Ty| -> Ty {
                    let s = ty.subst(&m);
                    replace_proj_dyn(&s, &assoc)
                };
                let ps: Vec<Ty> = f.params.iter().skip(1).map(|(_, t)| fix(t)).collect();
                let ret = fix(&f.ret);
                if ps.len() != args.len() {
                    self.err(span, format!("`{name}` takes {} argument(s) but {} were supplied", ps.len(), args.len()));
                }
                let mut es = Vec::new();
                for (a, p) in args.iter().zip(&ps) {
                    es.push(self.expr_coerce(a, p));
                }
                let tr = TraitRef { trait_id: tid, args: targs.clone() };
                return mk(ExprKind::DynCall { recv: Box::new(recv), trait_ref: tr, method: name.to_string(), args: es }, ret, span);
            }
        }
        self.err(span, format!("no method named `{name}` on `dyn {}`", prog.traits[tid].name));
        mk(ExprKind::Unreachable, Ty::Error, span)
    }

    // ---------------- operators ----------------
    fn unary(&mut self, op: UnOp, inner: &ast::Expr, span: Span, expect: Option<&Ty>) -> Expr {
        if op == UnOp::Neg {
            if let ast::ExprKind::Int(n) = inner.kind {
                let ty = match expect.map(|t| self.resolve(t)) {
                    Some(t @ (Ty::Int(_) | Ty::Float(_))) => t,
                    _ => self.fresh_kind(VarKind::Int),
                };
                return mk(ExprKind::Lit(Lit::Int(-(n as i128))), ty, span);
            }
            if let ast::ExprKind::Float(f) = inner.kind {
                let ty = match expect.map(|t| self.resolve(t)) {
                    Some(t @ Ty::Float(_)) => t,
                    _ => self.fresh_kind(VarKind::Float),
                };
                return mk(ExprKind::Lit(Lit::Float(-f)), ty, span);
            }
        }
        let e = self.expr(inner, expect);
        let t = self.resolve(&e.ty);
        let numeric_var = matches!(self.var_kind(&t), Some(VarKind::Int | VarKind::Float));
        match op {
            UnOp::Neg => {
                if t.is_numeric() || numeric_var {
                    if let Ty::Int(i) = &t {
                        if !i.signed() {
                            let s = self.tys(&t);
                            self.err(span, format!("cannot negate a value of unsigned type `{s}`"));
                        }
                    }
                    let ty = e.ty.clone();
                    return mk(ExprKind::Prim(PrimOp::Neg, ty.clone(), vec![e]), ty, span);
                }
                if matches!(t, Ty::Adt(..)) {
                    return self.method_call(e, "neg", &[], Vec::new(), span, expect);
                }
                let s = self.tys(&t);
                self.err(span, format!("cannot apply `-` to `{s}`"));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
            UnOp::Not => {
                if t == Ty::Bool || matches!(t, Ty::Int(_)) || matches!(self.var_kind(&t), Some(VarKind::Int)) {
                    let ty = e.ty.clone();
                    return mk(ExprKind::Prim(PrimOp::Not, ty.clone(), vec![e]), ty, span);
                }
                if matches!(t, Ty::Adt(..)) {
                    return self.method_call(e, "not", &[], Vec::new(), span, expect);
                }
                if t == Ty::Error {
                    return e;
                }
                let s = self.tys(&t);
                self.err(span, format!("cannot apply `!` to `{s}`"));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    fn is_numericish(&self, t: &Ty) -> bool {
        let t = self.resolve(t);
        t.is_numeric() || matches!(self.var_kind(&t), Some(VarKind::Int | VarKind::Float))
    }

    fn binary(&mut self, op: BinOp, l: &ast::Expr, r: &ast::Expr, span: Span, expect: Option<&Ty>) -> Expr {
        if op == BinOp::And || op == BinOp::Or {
            let a = self.expr_coerce(l, &Ty::Bool);
            let b = self.expr_coerce(r, &Ty::Bool);
            let (then, els) = if op == BinOp::And { (b, mk(ExprKind::Lit(Lit::Bool(false)), Ty::Bool, span)) } else { (mk(ExprKind::Lit(Lit::Bool(true)), Ty::Bool, span), b) };
            return mk(ExprKind::If(Box::new(a), Box::new(then), Box::new(els)), Ty::Bool, span);
        }
        let is_cmp = matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
        let arith_expect = if is_cmp { None } else { expect.filter(|t| self.resolve(t).is_numeric()) };
        let a = self.expr(l, arith_expect);
        let inferred_rhs = if self.var_kind(&a.ty) == Some(VarKind::General) {
            let b = self.expr(r, arith_expect);
            if !self.is_numericish(&b.ty) {
                self.err(a.span, "the type of this value must be known here; add a type annotation");
                return mk(ExprKind::Unreachable, Ty::Error, span);
            }
            self.unify(&a.ty, &b.ty);
            Some(b)
        } else {
            None
        };
        let at = self.resolve(&a.ty);
        if self.is_numericish(&at) {
            let b = inferred_rhs.unwrap_or_else(|| self.expr(r, at.is_numeric().then_some(&at)));
            if self.var_kind(&b.ty) == Some(VarKind::General) {
                self.unify(&b.ty, &at);
            }
            let bt = self.resolve(&b.ty);
            if !self.is_numericish(&bt) {
                if bt != Ty::Error && bt != Ty::Never {
                    let (x, y) = (self.tys(&at), self.tys(&bt));
                    self.err(span, format!("cannot apply `{}` to `{x}` and `{y}`", op.text()));
                }
                return mk(ExprKind::Unreachable, if is_cmp { Ty::Bool } else { Ty::Error }, span);
            }
            let (a, b, ty) = self.unify_numeric(a, b, span, op, arith_expect);
            if matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr) {
                let rt = self.resolve(&ty);
                if matches!(rt, Ty::Float(_)) || matches!(self.var_kind(&rt), Some(VarKind::Float)) {
                    self.err(span, format!("`{}` is not defined for floating-point numbers", op.text()));
                } else if let Some(VarKind::Int) = self.var_kind(&rt) {
                    // keep as int var
                }
            }
            if matches!(op, BinOp::Rem) {
                // fine for floats too
            }
            let rty = if is_cmp { Ty::Bool } else { ty.clone() };
            return mk(ExprKind::Prim(prim_of(op), ty, vec![a, b]), rty, span);
        }
        match &at {
            Ty::Bool | Ty::Char | Ty::Unit => {
                let b = self.expr_coerce(r, &at);
                let allowed = match at {
                    Ty::Bool => matches!(op, BinOp::Eq | BinOp::Ne | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor),
                    Ty::Char => is_cmp,
                    _ => matches!(op, BinOp::Eq | BinOp::Ne),
                };
                if !allowed {
                    let s = self.tys(&at);
                    self.err(span, format!("cannot apply `{}` to `{s}`", op.text()));
                }
                let rty = if is_cmp { Ty::Bool } else { at.clone() };
                mk(ExprKind::Prim(prim_of(op), at.clone(), vec![a, b]), rty, span)
            }
            Ty::Error | Ty::Never => {
                self.expr(r, None);
                mk(ExprKind::Unreachable, if is_cmp { Ty::Bool } else { Ty::Error }, span)
            }
            Ty::Var(_) => {
                self.err(a.span, "the type of this value must be known here; add a type annotation");
                self.expr(r, None);
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
            _ => {
                let Some((tname, mname)) = binop_method(op) else {
                    let s = self.tys(&at);
                    self.err(span, format!("cannot apply `{}` to `{s}`", op.text()));
                    self.expr(r, None);
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                };
                let tid = self.prog.known_trait(tname);
                let zt = self.zonk(&at);
                if !zt.has_vars() && !self.prog.implements(&zt, &TraitRef { trait_id: tid, args: vec![] }, 0) {
                    let s = self.tys(&at);
                    self.err(span, format!("`{s}` does not implement `{tname}`, so `{}` cannot be used on it", op.text()));
                    self.expr(r, None);
                    return mk(ExprKind::Unreachable, if is_cmp { Ty::Bool } else { Ty::Error }, span);
                }
                self.method_call(a, mname, &[], vec![r.clone()], span, expect)
            }
        }
    }

    /// Bring two numeric operands to a common type.
    fn unify_numeric(&mut self, a: Expr, b: Expr, span: Span, op: BinOp, expect: Option<&Ty>) -> (Expr, Expr, Ty) {
        let at = self.resolve(&a.ty);
        let bt = self.resolve(&b.ty);
        // A float literal cannot take its type from a concrete integer operand.
        let (at, bt) = match (&at, &bt) {
            (Ty::Int(_), Ty::Var(_)) if self.var_kind(&bt) == Some(VarKind::Float) => {
                let bt = self.resolve_float_operand(&bt, expect);
                (at, bt)
            }
            (Ty::Var(_), Ty::Int(_)) if self.var_kind(&at) == Some(VarKind::Float) => {
                let at = self.resolve_float_operand(&at, expect);
                (at, bt)
            }
            _ => (at, bt),
        };
        if at.is_numeric() && bt.is_numeric() && at != bt {
            if matches!(op, BinOp::Shl | BinOp::Shr) {
                // shift amount takes the left operand's type when it widens
            }
            match common_numeric(&at, &bt) {
                Some(c) => {
                    let a = self.coerce(a, &c);
                    let b = self.coerce(b, &c);
                    return (a, b, c);
                }
                None => {
                    let (x, y) = (self.tys(&at), self.tys(&bt));
                    self.err(span, format!("cannot apply `{}` to `{x}` and `{y}`: no type holds both without loss", op.text()));
                    return (a, b, at);
                }
            }
        }
        if !self.unify(&at, &bt) {
            let (x, y) = (self.tys(&at), self.tys(&bt));
            self.err(span, format!("cannot apply `{}` to `{x}` and `{y}`", op.text()));
        }
        (a, b, at)
    }

    fn resolve_float_operand(&mut self, literal: &Ty, expect: Option<&Ty>) -> Ty {
        if let Some(ty @ Ty::Float(_)) = expect.map(|t| self.resolve(t)) {
            self.unify(literal, &ty);
            ty
        } else {
            self.default_var(literal)
        }
    }

    fn assign(&mut self, op: Option<BinOp>, l: &ast::Expr, r: &ast::Expr, span: Span) -> Expr {
        match &l.kind {
            ast::ExprKind::Name(id, _) => {
                let Some(lid) = self.lookup_local(&id.name) else {
                    if self.prog.lookup(self.module, &id.name).is_some() {
                        self.err(l.span, format!("cannot assign to `{}`", id.name));
                    } else {
                        self.err(l.span, format!("cannot find value `{}` in this scope", id.name));
                    }
                    self.expr(r, None);
                    return unit(span);
                };
                let info = self.cxs.last().unwrap().locals[lid].clone();
                if !info.mutable {
                    let kind = if info.is_param { "a parameter" } else { "declared with `let`" };
                    self.g.error(Diag::new(l.span, format!("cannot assign twice to `{}`: it is {kind}", id.name)).note("declare it with `var` to allow reassignment"));
                }
                let rhs = match op {
                    None => self.expr_coerce(r, &info.ty),
                    Some(op) => {
                        let e = self.binary(op, l, r, span, Some(&info.ty));
                        self.coerce(e, &info.ty)
                    }
                };
                mk(ExprKind::SetLocal(lid, Box::new(rhs)), Ty::Unit, span)
            }
            ast::ExprKind::Field(base, name, _) => {
                let b = self.expr(base, None);
                let bt = self.resolve(&b.ty);
                let (idx, fty) = match &bt {
                    Ty::Adt(id, args) => match &self.prog.adts[*id].kind {
                        AdtKind::Struct(fields) => match fields.iter().position(|f| f.name == name.name) {
                            Some(i) => {
                                let f = &fields[i];
                                if !f.mutable {
                                    self.g.error(Diag::new(name.span, format!("cannot assign to field `{}`: it is immutable", name.name)).note("declare the field with `var` in the struct to allow assignment"));
                                }
                                if !f.public && self.prog.adts[*id].module != self.module {
                                    self.err(name.span, format!("field `{}` is private", name.name));
                                }
                                (i, self.prog.normalize_proj(f.ty.subst(args)))
                            }
                            None => {
                                let s = self.tys(&bt);
                                self.err(name.span, format!("no field `{}` on type `{s}`", name.name));
                                (0, Ty::Error)
                            }
                        },
                        _ => {
                            let s = self.tys(&bt);
                            self.err(name.span, format!("cannot assign to a field of enum `{s}`"));
                            (0, Ty::Error)
                        }
                    },
                    Ty::Error => (0, Ty::Error),
                    _ => {
                        let s = self.tys(&bt);
                        self.err(name.span, format!("no field `{}` on type `{s}`", name.name));
                        (0, Ty::Error)
                    }
                };
                match op {
                    None => {
                        let rhs = self.expr_coerce(r, &fty);
                        mk(ExprKind::SetField(Box::new(b), idx, Box::new(rhs)), Ty::Unit, span)
                    }
                    Some(op) => {
                        // tmp = base; tmp.f = tmp.f op rhs
                        let tmp = self.tmp_name("asg");
                        self.push_scope();
                        let bty = b.ty.clone();
                        let lid = self.new_local(&tmp, bty.clone(), false);
                        self.bind_local(&tmp, lid);
                        let lhs_ast = ae(ast::ExprKind::Field(Box::new(aname(&tmp, l.span)), name.clone(), Vec::new()), l.span);
                        let e = self.binary(op, &lhs_ast, r, span, Some(&fty));
                        let rhs = self.coerce(e, &fty);
                        self.pop_scope();
                        let set = mk(ExprKind::SetField(Box::new(self.local_expr(lid, span)), idx, Box::new(rhs)), Ty::Unit, span);
                        let pat = Pat { kind: PatKind::Bind(lid, None), ty: bty, span };
                        mk(ExprKind::Block(vec![Stmt::Let(pat, b)], Some(Box::new(set))), Ty::Unit, span)
                    }
                }
            }
            ast::ExprKind::Index(base, idx) => {
                let b = self.expr(base, None);
                match op {
                    None => match self.list_elem(&b.ty) {
                        Some(elem) => self.list_access(b, elem, idx, Some(r), span),
                        None => self.method_call(b, "set_index", &[], vec![(**idx).clone(), r.clone()], span, None),
                    },
                    Some(op) => {
                        let tb = self.tmp_name("ib");
                        let ti = self.tmp_name("ii");
                        self.push_scope();
                        let bl = self.new_local(&tb, b.ty.clone(), false);
                        self.bind_local(&tb, bl);
                        let ie = self.expr(idx, None);
                        let il = self.new_local(&ti, ie.ty.clone(), false);
                        self.bind_local(&ti, il);
                        let get = ae(ast::ExprKind::Index(Box::new(aname(&tb, span)), Box::new(aname(&ti, span))), span);
                        let newv = ae(ast::ExprKind::Binary(op, Box::new(get), Box::new(r.clone())), span);
                        let set = ae(ast::ExprKind::Assign(None, Box::new(get_target(&tb, &ti, span)), Box::new(newv)), span);
                        let s = self.expr(&set, None);
                        self.pop_scope();
                        let bty = b.ty.clone();
                        let ity = ie.ty.clone();
                        mk(
                            ExprKind::Block(
                                vec![Stmt::Let(Pat { kind: PatKind::Bind(bl, None), ty: bty, span }, b), Stmt::Let(Pat { kind: PatKind::Bind(il, None), ty: ity, span }, ie)],
                                Some(Box::new(s)),
                            ),
                            Ty::Unit,
                            span,
                        )
                    }
                }
            }
            _ => {
                self.err(l.span, "invalid left-hand side of assignment");
                self.expr(r, None);
                unit(span)
            }
        }
    }

    // ---------------- control flow ----------------
    fn if_expr(&mut self, cond: &ast::Cond, then: &ast::Block, els: Option<&ast::Expr>, span: Span, expect: Option<&Ty>) -> Expr {
        if let ast::Cond::Let(pat, scrut) = cond {
            // if let P = E { A } else { B }  ==>  match E { P -> A, _ -> B }
            let then_e = ae(ast::ExprKind::Block(then.clone()), then.span);
            let else_e = match els {
                Some(e) => e.clone(),
                None => ae(ast::ExprKind::Unit, span),
            };
            let arms = vec![
                ast::Arm { pat: pat.clone(), guard: None, body: then_e, span: then.span },
                ast::Arm { pat: ast::Pattern { kind: ast::PatKind::Wild, span }, guard: None, body: else_e, span },
            ];
            let unit_ctx = els.is_none();
            return self.match_inner(scrut, &arms, span, if unit_ctx { Some(&Ty::Unit) } else { expect });
        }
        let ast::Cond::Expr(c) = cond else { unreachable!() };
        let static_test = matches!(&c.kind, ast::ExprKind::Call(f, _) if matches!(&f.kind, ast::ExprKind::Name(id, _) if id.name == "__is_int"));
        let c = self.expr_coerce(c, &Ty::Bool);
        if let (true, ExprKind::Lit(Lit::Bool(b))) = (static_test, &c.kind) {
            // only the branch for this instantiation's type is elaborated
            return match (*b, els) {
                (true, None) => {
                    let t = self.block(then, Some(&Ty::Unit));
                    self.coerce(t, &Ty::Unit)
                }
                (false, None) => unit(span),
                (true, Some(_)) => {
                    let t = self.block(then, expect);
                    match expect {
                        Some(x) => self.coerce(t, x),
                        None => t,
                    }
                }
                (false, Some(e)) => match expect {
                    Some(x) => self.expr_coerce(e, x),
                    None => self.expr(e, None),
                },
            };
        }
        match els {
            None => {
                let t = self.block(then, Some(&Ty::Unit));
                let t = self.coerce(t, &Ty::Unit);
                mk(ExprKind::If(Box::new(c), Box::new(t), Box::new(unit(span))), Ty::Unit, span)
            }
            Some(e) => {
                let t = self.block(then, expect);
                let (t, el, ty) = self.join2(t, e, expect);
                mk(ExprKind::If(Box::new(c), Box::new(t), Box::new(el)), ty, span)
            }
        }
    }

    /// Elaborate a second branch and join both branch types.
    fn join2(&mut self, t: Expr, e: &ast::Expr, expect: Option<&Ty>) -> (Expr, Expr, Ty) {
        if let Some(x) = expect {
            let x = x.clone();
            let t = self.coerce(t, &x);
            let el = self.expr_coerce(e, &x);
            if matches!(self.resolve(&x), Ty::Unit) {
                return (t, el, Ty::Unit);
            }
            let ty = if matches!(self.resolve(&t.ty), Ty::Never) && matches!(self.resolve(&el.ty), Ty::Never) { Ty::Never } else { x };
            return (t, el, ty);
        }
        let tt = self.resolve(&t.ty);
        if matches!(tt, Ty::Never) {
            let el = self.expr(e, None);
            let ty = el.ty.clone();
            return (t, el, ty);
        }
        let el = self.expr(e, Some(&tt));
        let et = self.resolve(&el.ty);
        if et.is_numeric() && tt.is_numeric() && et != tt {
            if let Some(c) = common_numeric(&tt, &et) {
                let t = self.coerce(t, &c);
                let el = self.coerce(el, &c);
                return (t, el, c);
            }
        }
        let el = self.coerce(el, &tt);
        (t, el, tt)
    }

    fn match_expr(&mut self, scrut: &ast::Expr, arms: &[ast::Arm], span: Span, expect: Option<&Ty>) -> Expr {
        self.match_inner(scrut, arms, span, expect)
    }

    fn match_inner(&mut self, scrut: &ast::Expr, arms: &[ast::Arm], span: Span, expect: Option<&Ty>) -> Expr {
        let s = self.expr(scrut, None);
        let st = s.ty.clone();
        let mut out = Vec::new();
        let mut result_ty: Option<Ty> = expect.cloned();
        for arm in arms {
            self.push_scope();
            let mut binds = Vec::new();
            let p = self.pattern(&arm.pat, &st, false, &mut binds, None);
            for (n, id) in binds {
                self.bind_local(&n, id);
            }
            let guard = arm.guard.as_ref().map(|g| self.expr_coerce(g, &Ty::Bool));
            let body = match &result_ty {
                Some(t) => {
                    let t = t.clone();
                    if matches!(self.resolve(&t), Ty::Unit) {
                        let b = self.expr(&arm.body, None);
                        let bt = self.resolve(&b.ty);
                        if matches!(bt, Ty::Unit | Ty::Never) || expect.is_none() {
                            self.coerce(b, &t)
                        } else {
                            let sp = b.span;
                            mk(ExprKind::Discard(Box::new(b)), Ty::Unit, sp)
                        }
                    } else {
                        let b = self.expr(&arm.body, Some(&t));
                        // numeric widening across arms
                        let bt = self.resolve(&b.ty);
                        let rt = self.resolve(&t);
                        if expect.is_none() && bt.is_numeric() && rt.is_numeric() && bt != rt && !widens_to(&bt, &rt) {
                            if let Some(c) = common_numeric(&rt, &bt) {
                                result_ty = Some(c.clone());
                                for a in out.iter_mut() {
                                    let a: &mut ir::Arm = a;
                                    let body = std::mem::replace(&mut a.body, unit(span));
                                    a.body = self.coerce(body, &c);
                                }
                                let b = self.coerce(b, &c);
                                self.pop_scope();
                                out.push(ir::Arm { pat: p, guard, body: b, span: arm.span });
                                continue;
                            }
                        }
                        self.coerce(b, &t)
                    }
                }
                None => {
                    let b = self.expr(&arm.body, None);
                    if !matches!(self.resolve(&b.ty), Ty::Never) {
                        result_ty = Some(b.ty.clone());
                    }
                    b
                }
            };
            self.pop_scope();
            out.push(ir::Arm { pat: p, guard, body, span: arm.span });
        }
        let all_never = out.iter().all(|a| matches!(self.resolve(&a.body.ty), Ty::Never));
        let ty = if all_never { Ty::Never } else { result_ty.unwrap_or(Ty::Never) };
        mk(ExprKind::Match(Box::new(s), out), ty, span)
    }

    fn while_expr(&mut self, cond: &ast::Cond, body: &ast::Block, span: Span) -> Expr {
        if let ast::Cond::Let(pat, scrut) = cond {
            // while let P = E { B }  ==>  loop { match E { P -> B, _ -> break } }
            let brk = ae(ast::ExprKind::Break(None), span);
            let m = ae(
                ast::ExprKind::Match {
                    scrut: scrut.clone(),
                    arms: vec![
                        ast::Arm { pat: pat.clone(), guard: None, body: ae(ast::ExprKind::Block(body.clone()), body.span), span: body.span },
                        ast::Arm { pat: ast::Pattern { kind: ast::PatKind::Wild, span }, guard: None, body: brk, span },
                    ],
                },
                span,
            );
            let lp = ablock(vec![ast::Stmt::Expr(m)], None, span);
            return self.loop_unit(&lp, span, false);
        }
        let ast::Cond::Expr(c) = cond else { unreachable!() };
        let label = self.next_label;
        self.next_label += 1;
        self.cx().loops.push(LoopCx { label, break_ty: Ty::Unit, allows_value: false, has_break: false });
        let c = self.expr_coerce(c, &Ty::Bool);
        let b = self.block(body, Some(&Ty::Unit));
        self.cx().loops.pop();
        let brk = mk(ExprKind::Break(label, None), Ty::Never, span);
        let inner = mk(ExprKind::If(Box::new(c), Box::new(b), Box::new(brk)), Ty::Unit, span);
        mk(ExprKind::Loop(label, Box::new(inner)), Ty::Unit, span)
    }

    fn loop_unit(&mut self, b: &ast::Block, span: Span, allows_value: bool) -> Expr {
        let label = self.next_label;
        self.next_label += 1;
        self.cx().loops.push(LoopCx { label, break_ty: Ty::Unit, allows_value, has_break: false });
        let body = self.block(b, Some(&Ty::Unit));
        self.cx().loops.pop();
        mk(ExprKind::Loop(label, Box::new(body)), Ty::Unit, span)
    }

    fn for_expr(&mut self, pat: &ast::Pattern, iter: &ast::Expr, body: &ast::Block, span: Span) -> Expr {
        let bexpr = ae(ast::ExprKind::Block(body.clone()), body.span);
        if let ast::ExprKind::Range(a, b, inclusive) = &iter.kind {
            let i = self.tmp_name("i");
            let end = self.tmp_name("end");
            let done = self.tmp_name("done");
            let typed = |e: &ast::Expr| e.clone();
            let mut stmts = vec![alet(false, &end, typed(b), span), alet(true, &i, typed(a), span)];
            let bind_stmt = ast::Stmt::Let { mutable: false, pat: pat.clone(), ty: None, init: aname(&i, span), else_block: None, span: pat.span };
            if *inclusive {
                stmts.push(alet(true, &done, ae(ast::ExprKind::Binary(BinOp::Gt, Box::new(aname(&i, span)), Box::new(aname(&end, span))), span), span));
                let cond = ae(ast::ExprKind::Unary(UnOp::Not, Box::new(aname(&done, span))), span);
                let step = ae(
                    ast::ExprKind::If {
                        cond: ast::Cond::Expr(Box::new(ae(ast::ExprKind::Binary(BinOp::Eq, Box::new(aname(&i, span)), Box::new(aname(&end, span))), span))),
                        then: ablock(vec![], Some(ae(ast::ExprKind::Assign(None, Box::new(aname(&done, span)), Box::new(ae(ast::ExprKind::Bool(true), span))), span)), span),
                        els: Some(Box::new(ae(ast::ExprKind::Block(ablock(vec![], Some(ae(ast::ExprKind::Assign(Some(BinOp::Add), Box::new(aname(&i, span)), Box::new(ae(ast::ExprKind::Int(1), span))), span)), span)), span))),
                    },
                    span,
                );
                let wb = ablock(vec![bind_stmt, ast::Stmt::Expr(step)], Some(bexpr), span);
                stmts.push(ast::Stmt::Expr(ae(ast::ExprKind::While(ast::Cond::Expr(Box::new(cond)), wb), span)));
            } else {
                let cond = ae(ast::ExprKind::Binary(BinOp::Lt, Box::new(aname(&i, span)), Box::new(aname(&end, span))), span);
                let step = ae(ast::ExprKind::Assign(Some(BinOp::Add), Box::new(aname(&i, span)), Box::new(ae(ast::ExprKind::Int(1), span))), span);
                let wb = ablock(vec![bind_stmt, ast::Stmt::Expr(step)], Some(bexpr), span);
                stmts.push(ast::Stmt::Expr(ae(ast::ExprKind::While(ast::Cond::Expr(Box::new(cond)), wb), span)));
            }
            let blk = ablock(stmts, None, span);
            let e = self.block(&blk, Some(&Ty::Unit));
            return e;
        }
        // the iterable is elaborated once and held in a hidden local, so its type can pick the loop shape
        self.push_scope();
        let src = self.expr(iter, None);
        let src_ty = self.resolve(&src.ty);
        let src_name = self.tmp_name("src");
        let src_id = self.new_local(&src_name, src_ty.clone(), false);
        self.bind_local(&src_name, src_id);
        let list = self.prog.known_adt("List");
        let blk = if matches!(&src_ty, Ty::Adt(id, _) if *id == list) {
            // List: var i = 0; while i < src.len() { let pat = src[i]; i += 1; body }
            // (the same order as ListIter, without allocating an Option per element)
            let i = self.tmp_name("i");
            let cond = ae(ast::ExprKind::Binary(BinOp::Lt, Box::new(aname(&i, span)), Box::new(acall_method(aname(&src_name, span), "len", vec![], span))), span);
            let elem = ae(ast::ExprKind::Index(Box::new(aname(&src_name, span)), Box::new(aname(&i, span))), span);
            let bind_stmt = ast::Stmt::Let { mutable: false, pat: pat.clone(), ty: None, init: elem, else_block: None, span: pat.span };
            let step = ae(ast::ExprKind::Assign(Some(BinOp::Add), Box::new(aname(&i, span)), Box::new(ae(ast::ExprKind::Int(1), span))), span);
            let wb = ablock(vec![bind_stmt, ast::Stmt::Expr(step)], Some(bexpr), span);
            ablock(vec![alet(true, &i, ae(ast::ExprKind::Int(0), span), span), ast::Stmt::Expr(ae(ast::ExprKind::While(ast::Cond::Expr(Box::new(cond)), wb), span))], None, span)
        } else {
            // general: let it = src.iter(); while let Some(pat) = it.next() { body }
            let it = self.tmp_name("it");
            let init = acall_method(aname(&src_name, span), "iter", vec![], iter.span);
            let some_pat = ast::Pattern { kind: ast::PatKind::TupleStruct(vec![aident("Some", pat.span)], vec![pat.clone()]), span: pat.span };
            let next = acall_method(aname(&it, span), "next", vec![], span);
            let wl = ae(ast::ExprKind::While(ast::Cond::Let(some_pat, Box::new(next)), body.clone()), span);
            ablock(vec![alet(false, &it, init, span), ast::Stmt::Expr(wl)], None, span)
        };
        let inner = self.block(&blk, Some(&Ty::Unit));
        self.pop_scope();
        let bind = Pat { kind: PatKind::Bind(src_id, None), ty: src_ty, span };
        mk(ExprKind::Block(vec![Stmt::Let(bind, src)], Some(Box::new(inner))), Ty::Unit, span)
    }

    /// The element type when `t` is a `List`.
    fn list_elem(&mut self, t: &Ty) -> Option<Ty> {
        let list = self.prog.known_adt("List");
        match self.resolve(t) {
            Ty::Adt(id, args) if id == list => Some(args[0].clone()),
            _ => None,
        }
    }

    /// `list[i]` and `list[i] = v` without calling `Index`: one unsigned comparison against
    /// the length (the out-of-bounds panic is out of line), then the array access. Same
    /// behaviour and evaluation order as `List`'s `Index` impl (list, index, value, check).
    fn list_access(&mut self, b: Expr, elem: Ty, idx: &ast::Expr, val: Option<&ast::Expr>, span: Span) -> Expr {
        let int = Ty::Int(IntTy::I32);
        let u32t = Ty::Int(IntTy::U32);
        let lty = b.ty.clone();
        let bl = self.new_local("$lb", lty.clone(), false);
        let i = self.expr_coerce(idx, &int);
        let il = self.new_local("$li", int.clone(), false);
        let mut stmts = vec![Stmt::Let(Pat { kind: PatKind::Bind(bl, None), ty: lty, span }, b), Stmt::Let(Pat { kind: PatKind::Bind(il, None), ty: int.clone(), span }, i)];
        let v = val.map(|v| {
            let e = self.expr_coerce(v, &elem);
            let vl = self.new_local("$lv", elem.clone(), false);
            stmts.push(Stmt::Let(Pat { kind: PatKind::Bind(vl, None), ty: elem.clone(), span }, e));
            self.local_expr(vl, span)
        });
        let lv = self.local_expr(bl, span);
        let iv = self.local_expr(il, span);
        let len = mk(ExprKind::Field(Box::new(lv.clone()), None, 0), int.clone(), span);
        let data = mk(ExprKind::Field(Box::new(lv), None, 1), Ty::Array(Box::new(elem.clone())), span);
        let as_u32 = |e: Expr| mk(ExprKind::Cast(Box::new(e)), u32t.clone(), span);
        let cond = mk(ExprKind::Prim(PrimOp::Ge, u32t.clone(), vec![as_u32(iv.clone()), as_u32(len.clone())]), Ty::Bool, span);
        let oob = mk(ExprKind::Call(FnInst { fn_id: self.prog.known_fn("__list_oob"), targs: vec![] }, vec![iv.clone(), len]), Ty::Never, span);
        let unit = mk(ExprKind::Block(vec![], None), Ty::Unit, span);
        stmts.push(Stmt::Expr(mk(ExprKind::If(Box::new(cond), Box::new(oob), Box::new(unit)), Ty::Unit, span)));
        let access = match v {
            None => mk(ExprKind::Intrinsic("array_get".into(), vec![elem.clone()], vec![data, iv]), elem, span),
            Some(v) => mk(ExprKind::Intrinsic("array_set".into(), vec![elem], vec![data, iv, v]), Ty::Unit, span),
        };
        let ty = access.ty.clone();
        mk(ExprKind::Block(stmts, Some(Box::new(access))), ty, span)
    }

    fn try_expr(&mut self, inner: &ast::Expr, span: Span) -> Expr {
        let e = self.expr(inner, None);
        let t = self.resolve(&e.ty);
        let opt = self.prog.known_adt("Option");
        let res = self.prog.known_adt("Result");
        let ret = self.cx().ret.clone();
        match &t {
            Ty::Adt(id, args) if *id == res => {
                let (ok_t, err_t) = (args[0].clone(), args[1].clone());
                let mut rr = self.resolve(&ret);
                if let Ty::Var(_) = rr {
                    let v = self.fresh();
                    let r = Ty::Adt(res, vec![v, err_t.clone()]);
                    self.unify(&rr, &r);
                    rr = r;
                }
                let Ty::Adt(rid, rargs) = &rr else {
                    let s = self.tys(&rr);
                    self.err(span, format!("the `?` operator on a `Result` can only be used in a function that returns `Result`, not `{s}`"));
                    return mk(ExprKind::Unreachable, ok_t, span);
                };
                if *rid != res {
                    let s = self.tys(&rr);
                    self.err(span, format!("the `?` operator on a `Result` can only be used in a function that returns `Result`, not `{s}`"));
                    return mk(ExprKind::Unreachable, ok_t, span);
                }
                let target_err = rargs[1].clone();
                let v = self.new_local("$ok", ok_t.clone(), false);
                let er = self.new_local("$err", err_t.clone(), false);
                let err_val = self.local_expr(er, span);
                let conv = self.convert_err(err_val, &err_t, &target_err, span);
                let ret_val = mk(ExprKind::EnumNew(1, vec![conv]), rr.clone(), span);
                let arms = vec![
                    ir::Arm { pat: Pat { kind: PatKind::Variant(0, vec![(0, Pat { kind: PatKind::Bind(v, None), ty: ok_t.clone(), span })]), ty: t.clone(), span }, guard: None, body: self.local_expr(v, span), span },
                    ir::Arm {
                        pat: Pat { kind: PatKind::Variant(1, vec![(0, Pat { kind: PatKind::Bind(er, None), ty: err_t.clone(), span })]), ty: t.clone(), span },
                        guard: None,
                        body: mk(ExprKind::Return(Box::new(ret_val)), Ty::Never, span),
                        span,
                    },
                ];
                mk(ExprKind::Match(Box::new(e), arms), ok_t, span)
            }
            Ty::Adt(id, args) if *id == opt => {
                let inner_t = args[0].clone();
                let mut rr = self.resolve(&ret);
                if let Ty::Var(_) = rr {
                    let v = self.fresh();
                    let r = Ty::Adt(opt, vec![v]);
                    self.unify(&rr, &r);
                    rr = r;
                }
                if !matches!(&rr, Ty::Adt(rid, _) if *rid == opt) {
                    let s = self.tys(&rr);
                    self.err(span, format!("the `?` operator on an `Option` can only be used in a function that returns `Option`, not `{s}`"));
                    return mk(ExprKind::Unreachable, inner_t, span);
                }
                let v = self.new_local("$some", inner_t.clone(), false);
                let arms = vec![
                    ir::Arm { pat: Pat { kind: PatKind::Variant(0, vec![(0, Pat { kind: PatKind::Bind(v, None), ty: inner_t.clone(), span })]), ty: t.clone(), span }, guard: None, body: self.local_expr(v, span), span },
                    ir::Arm {
                        pat: Pat { kind: PatKind::Variant(1, vec![]), ty: t.clone(), span },
                        guard: None,
                        body: mk(ExprKind::Return(Box::new(mk(ExprKind::EnumNew(1, vec![]), rr.clone(), span))), Ty::Never, span),
                        span,
                    },
                ];
                mk(ExprKind::Match(Box::new(e), arms), inner_t, span)
            }
            Ty::Error => e,
            _ => {
                let s = self.tys(&t);
                self.err(span, format!("the `?` operator can only be applied to `Result` or `Option`, not `{s}`"));
                mk(ExprKind::Unreachable, Ty::Error, span)
            }
        }
    }

    fn convert_err(&mut self, val: Expr, from: &Ty, to: &Ty, span: Span) -> Expr {
        if self.try_unify(from, to) {
            return val;
        }
        let from_trait = self.prog.known_trait("From");
        let zto = self.zonk_default(to);
        let zfrom = self.zonk_default(from);
        match self.prog.find_trait_impl(&zto, from_trait, Some(std::slice::from_ref(&zfrom)), 0) {
            Some((iid, binds)) => {
                let imp = &self.prog.impls[iid];
                let fid = imp.methods["from"];
                let ret = self.prog.normalize_proj(self.prog.fns[fid].ret.subst(&binds));
                mk(ExprKind::Call(FnInst { fn_id: fid, targs: binds }, vec![val]), ret, span)
            }
            None => {
                let (f, t) = (self.tys(&zfrom), self.tys(&zto));
                self.g.error(Diag::new(span, format!("`?` cannot convert the error type `{f}` into `{t}`")).note(format!("implement `From<{f}>` for `{t}`, or convert with `.map_err(...)`")));
                val
            }
        }
    }

    /// Build a lazy `Future<T>` whose body runs in an async context.
    fn future_of(&mut self, body: &ast::Expr, inner_ret: Option<Ty>, span: Span) -> Expr {
        let rty = inner_ret.unwrap_or_else(|| self.fresh());
        let idx = self.g.reserve();
        let mut cx = FnCx::new(rty.clone());
        cx.is_async = true;
        self.cxs.push(cx);
        let mut b = self.expr(body, Some(&rty));
        if matches!(self.resolve(&rty), Ty::Unit) && !matches!(self.resolve(&b.ty), Ty::Unit | Ty::Never) {
            let sp = b.span;
            b = mk(ExprKind::Discard(Box::new(b)), Ty::Unit, sp);
        }
        let b = self.coerce(b, &rty);
        let cx = self.cxs.pop().unwrap();
        let captures: Vec<LocalId> = cx.captures.iter().map(|(p, _)| *p).collect();
        let func = ir::Func { name: format!("async{idx}"), params: Vec::new(), locals: cx.locals, ret: rty.clone(), body: b, is_closure: true, export: None, extern_: None };
        self.closures.push((idx, func));
        let clo = mk(ExprKind::Closure { func: idx, captures }, Ty::Fn(Vec::new(), Box::new(rty.clone())), span);
        let Some(Def::Fn(fid)) = self.prog.lookup(self.prog.prelude, "__future_new") else {
            self.err(span, "internal error: missing `__future_new` in the prelude");
            return mk(ExprKind::Unreachable, Ty::Error, span);
        };
        let fty = self.prog.future_ty(rty.clone());
        mk(ExprKind::Call(FnInst { fn_id: fid, targs: vec![rty] }, vec![clo]), fty, span)
    }

    /// `async |p| body` is a closure returning a lazy future.
    fn async_closure(&mut self, params: &[(ast::Pattern, Option<ast::TypeExpr>)], ret: Option<&ast::TypeExpr>, body: &ast::Expr, span: Span, expect: Option<&Ty>) -> Expr {
        let inner_ret = match ret {
            Some(r) => Some(self.resolve_ty(r)),
            None => match expect.map(|t| self.resolve(t)) {
                Some(Ty::Fn(_, r)) => match self.resolve(&r) {
                    Ty::Adt(_, a) if a.len() == 1 => Some(a[0].clone()),
                    _ => None,
                },
                _ => None,
            },
        };
        let inner_ret = inner_ret.unwrap_or_else(|| self.fresh());
        self.closure_impl(params, None, body, span, expect, Some(inner_ret))
    }

    fn closure(&mut self, params: &[(ast::Pattern, Option<ast::TypeExpr>)], ret: Option<&ast::TypeExpr>, body: &ast::Expr, span: Span, expect: Option<&Ty>) -> Expr {
        self.closure_impl(params, ret, body, span, expect, None)
    }

    fn closure_impl(&mut self, params: &[(ast::Pattern, Option<ast::TypeExpr>)], ret: Option<&ast::TypeExpr>, body: &ast::Expr, span: Span, expect: Option<&Ty>, async_inner: Option<Ty>) -> Expr {
        let (exp_ps, exp_r) = match expect.map(|t| self.resolve(t)) {
            Some(Ty::Fn(ps, r)) if ps.len() == params.len() => (Some(ps), Some(*r)),
            _ => (None, None),
        };
        let mut ptys = Vec::new();
        for (i, (_, ann)) in params.iter().enumerate() {
            let t = match ann {
                Some(a) => {
                    let t = self.resolve_ty(a);
                    if let Some(ps) = &exp_ps {
                        self.unify(&t, &ps[i]);
                    }
                    t
                }
                None => match &exp_ps {
                    Some(ps) => ps[i].clone(),
                    None => self.fresh(),
                },
            };
            ptys.push(t);
        }
        let rty = match (&async_inner, ret) {
            (Some(i), _) => {
                let f = self.prog.future_ty(i.clone());
                if let Some(r) = &exp_r {
                    self.unify(&f, r);
                }
                f
            }
            (None, Some(r)) => self.resolve_ty(r),
            (None, None) => exp_r.unwrap_or_else(|| self.fresh()),
        };
        let idx = self.g.reserve();
        self.cxs.push(FnCx::new(rty.clone()));
        let mut param_ids = Vec::new();
        let mut destructure = Vec::new();
        for (i, (p, _)) in params.iter().enumerate() {
            let pid = match &p.kind {
                ast::PatKind::Bind(id) if self.prog.lookup(self.module, &id.name).map(|d| !matches!(d, Def::Variant(..))).unwrap_or(true) => {
                    self.warn_local_name(id);
                    let l = self.new_local(&id.name, ptys[i].clone(), false);
                    self.cx().locals[l].is_param = true;
                    self.bind_local(&id.name, l);
                    l
                }
                _ => {
                    let l = self.new_local(&format!("$p{i}"), ptys[i].clone(), false);
                    self.cx().locals[l].is_param = true;
                    destructure.push((l, p.clone()));
                    l
                }
            };
            param_ids.push(pid);
        }
        let mut stmts = Vec::new();
        for (l, p) in destructure {
            let mut binds = Vec::new();
            let ty = self.local_ty(l);
            let pat = self.pattern(&p, &ty, false, &mut binds, None);
            for (n, id) in binds {
                self.bind_local(&n, id);
            }
            stmts.push(Stmt::Let(pat, self.local_expr(l, p.span)));
        }
        let mut b = match &async_inner {
            Some(i) => self.future_of(body, Some(i.clone()), span),
            None => self.expr(body, Some(&rty)),
        };
        if matches!(self.resolve(&rty), Ty::Unit) && !matches!(self.resolve(&b.ty), Ty::Unit | Ty::Never) {
            let sp = b.span;
            b = mk(ExprKind::Discard(Box::new(b)), Ty::Unit, sp);
        }
        let b = self.coerce(b, &rty);
        let body = if stmts.is_empty() { b } else { mk(ExprKind::Block(stmts, Some(Box::new(b))), rty.clone(), span) };
        let cx = self.cxs.pop().unwrap();
        let captures: Vec<LocalId> = cx.captures.iter().map(|(p, _)| *p).collect();
        let func = ir::Func { name: format!("closure{idx}"), params: param_ids, locals: cx.locals, ret: rty.clone(), body, is_closure: true, export: None, extern_: None };
        self.closures.push((idx, func));
        mk(ExprKind::Closure { func: idx, captures }, Ty::Fn(ptys, Box::new(rty)), span)
    }

    // ---------------- struct literals ----------------
    #[allow(clippy::too_many_arguments)]
    fn struct_lit(&mut self, path: &[ast::Ident], targs: &[ast::TypeExpr], fields: &[(ast::Ident, Option<ast::Expr>)], base: Option<&ast::Expr>, span: Span, expect: Option<&Ty>) -> Expr {
        // resolve the path to a struct type or a record variant
        let (aid, variant) = if path.len() == 1 && path[0].name == "Self" {
            match &self.self_ty {
                Some(Ty::Adt(id, _)) => (*id, None),
                _ => {
                    self.err(span, "`Self` is not a struct here");
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                }
            }
        } else {
            let res = if path[0].name == "Self" {
                match &self.self_ty {
                    Some(Ty::Adt(id, _)) => match &self.prog.adts[*id].kind {
                        AdtKind::Enum(vs) => vs.iter().position(|v| v.name == path[1].name).map(|i| Def::Variant(*id, i)).ok_or_else(|| Diag::new(path[1].span, "no such variant")),
                        _ => Err(Diag::new(span, "invalid path")),
                    },
                    _ => Err(Diag::new(span, "invalid path")),
                }
            } else {
                self.prog.resolve_path_def(self.module, path)
            };
            match res {
                Ok(Def::Adt(id)) if matches!(self.prog.adts[id].kind, AdtKind::Struct(_)) => (id, None),
                Ok(Def::Variant(id, vi)) => (id, Some(vi)),
                Ok(Def::Alias(al)) => match self.prog.aliases[al].resolved.clone() {
                    Some(Ty::Adt(id, _)) => (id, None),
                    _ => {
                        self.err(span, "type alias does not name a struct");
                        return mk(ExprKind::Unreachable, Ty::Error, span);
                    }
                },
                Ok(_) => {
                    self.err(span, format!("`{}` is not a struct or a variant with named fields", path.last().unwrap().name));
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                }
                Err(d) => {
                    self.g.error(d);
                    for (_, v) in fields {
                        if let Some(v) = v {
                            self.expr(v, None);
                        }
                    }
                    return mk(ExprKind::Unreachable, Ty::Error, span);
                }
            }
        };
        let adt = &self.prog.adts[aid];
        let adt_args: Vec<Ty> = if !targs.is_empty() {
            targs.iter().map(|t| self.resolve_ty(t)).collect()
        } else if path[0].name == "Self" {
            match &self.self_ty {
                Some(Ty::Adt(_, a)) => a.clone(),
                _ => Vec::new(),
            }
        } else {
            (0..adt.generics.len()).map(|_| self.fresh()).collect()
        };
        let ty = Ty::Adt(aid, adt_args.clone());
        if let Some(e) = expect {
            self.try_unify(&ty, e);
        }
        let defs: Vec<FieldDef> = match (&adt.kind, variant) {
            (AdtKind::Struct(fs), None) => fs.clone(),
            (AdtKind::Enum(vs), Some(vi)) => {
                if vs[vi].shape != Shape::Record {
                    self.err(span, format!("variant `{}` does not have named fields", vs[vi].name));
                    return mk(ExprKind::Unreachable, ty, span);
                }
                vs[vi].fields.clone()
            }
            _ => unreachable!(),
        };
        let foreign = adt.module != self.module && adt.pkg.is_source();
        let mut slots: Vec<Option<Expr>> = vec![None; defs.len()];
        let mut order = Vec::new();
        for (name, val) in fields {
            let Some(i) = defs.iter().position(|f| f.name == name.name) else {
                let s = self.tys(&ty);
                self.err(name.span, format!("`{s}` has no field named `{}`", name.name));
                if let Some(v) = val {
                    self.expr(v, None);
                }
                continue;
            };
            if variant.is_none() && foreign && !defs[i].public {
                self.err(name.span, format!("field `{}` is private", name.name));
            }
            if slots[i].is_some() {
                self.err(name.span, format!("field `{}` is specified more than once", name.name));
            }
            let fty = self.prog.normalize_proj(defs[i].ty.subst(&adt_args));
            let e = match val {
                Some(v) => self.expr_coerce(v, &fty),
                None => {
                    let ne = self.name_expr(name, &[], name.span, Some(&fty));
                    self.coerce(ne, &fty)
                }
            };
            order.push(i);
            slots[i] = Some(e);
        }
        let mut prelude_stmts = Vec::new();
        let base_local = match base {
            Some(b) => {
                if variant.is_some() {
                    self.err(b.span, "struct update syntax is only allowed for structs");
                }
                let be = self.expr_coerce(b, &ty);
                let l = self.new_local("$base", ty.clone(), false);
                prelude_stmts.push(Stmt::Let(Pat { kind: PatKind::Bind(l, None), ty: ty.clone(), span }, be));
                Some(l)
            }
            None => None,
        };
        let mut vals = Vec::new();
        let mut missing = Vec::new();
        for (i, s) in slots.into_iter().enumerate() {
            match s {
                Some(e) => vals.push(e),
                None => match base_local {
                    Some(l) => {
                        let fty = self.prog.normalize_proj(defs[i].ty.subst(&adt_args));
                        vals.push(mk(ExprKind::Field(Box::new(self.local_expr(l, span)), None, i), fty, span));
                    }
                    None => {
                        missing.push(defs[i].name.clone());
                        vals.push(mk(ExprKind::Unreachable, Ty::Error, span));
                    }
                },
            }
        }
        if !missing.is_empty() {
            let s = self.tys(&ty);
            self.err(span, format!("missing field(s) {} in initializer of `{s}`", missing.iter().map(|m| format!("`{m}`")).collect::<Vec<_>>().join(", ")));
        }
        // preserve source evaluation order when it differs from declaration order
        let in_order = order.windows(2).all(|w| w[0] < w[1]);
        if !in_order && base_local.is_none() {
            let mut tmps = vec![None; vals.len()];
            for &i in &order {
                let v = std::mem::replace(&mut vals[i], unit(span));
                let vt = v.ty.clone();
                let l = self.new_local("$f", vt.clone(), false);
                prelude_stmts.push(Stmt::Let(Pat { kind: PatKind::Bind(l, None), ty: vt, span }, v));
                tmps[i] = Some(l);
            }
            for (i, t) in tmps.into_iter().enumerate() {
                if let Some(l) = t {
                    vals[i] = self.local_expr(l, span);
                }
            }
        }
        let new = match variant {
            Some(vi) => mk(ExprKind::EnumNew(vi, vals), ty.clone(), span),
            None => mk(ExprKind::StructNew(vals), ty.clone(), span),
        };
        if prelude_stmts.is_empty() {
            new
        } else {
            mk(ExprKind::Block(prelude_stmts, Some(Box::new(new))), ty, span)
        }
    }

    // ---------------- patterns ----------------
    fn pattern(&mut self, p: &ast::Pattern, expected: &Ty, mutable: bool, binds: &mut Vec<(String, LocalId)>, reuse: Option<&HashMap<String, LocalId>>) -> Pat {
        let span = p.span;
        let ety = expected.clone();
        let mkp = |kind: PatKind, ty: Ty| Pat { kind, ty, span };
        match &p.kind {
            ast::PatKind::Wild => mkp(PatKind::Wild, ety),
            ast::PatKind::Bind(id) => {
                // a bare name may refer to a unit variant or constant
                if let Some(def) = self.prog.lookup(self.module, &id.name) {
                    if let Def::Variant(aid, vi) = def {
                        return self.variant_pattern(aid, vi, None, &[], &[], false, expected, span, mutable, binds, reuse, Shape::Unit);
                    }
                    if let Def::Const(cid) = def {
                        let v = self.const_value(cid, span);
                        if let ExprKind::Lit(l) = v.kind {
                            if !self.unify(&v.ty, expected) {
                                self.mismatch(span, expected, &v.ty);
                            }
                            return mkp(PatKind::Lit(l), ety);
                        }
                        self.err(span, "only constants with literal values can be used as patterns");
                        return mkp(PatKind::Wild, ety);
                    }
                }
                self.warn_local_name(id);
                if binds.iter().any(|(n, _)| *n == id.name) {
                    self.err(id.span, format!("identifier `{}` is bound more than once in the same pattern", id.name));
                }
                let lid = match reuse {
                    Some(m) => match m.get(&id.name) {
                        Some(&l) => {
                            let lt = self.local_ty(l);
                            if !self.unify(&lt, expected) {
                                self.mismatch(span, &lt, expected);
                            }
                            l
                        }
                        None => {
                            self.err(id.span, format!("variable `{}` is not bound in all alternatives of this pattern", id.name));
                            self.new_local(&id.name, ety.clone(), mutable)
                        }
                    },
                    None => self.new_local(&id.name, ety.clone(), mutable),
                };
                binds.push((id.name.clone(), lid));
                mkp(PatKind::Bind(lid, None), ety)
            }
            ast::PatKind::Lit(l) => {
                let lit = self.lit_pat(l, expected, span);
                mkp(PatKind::Lit(lit), ety)
            }
            ast::PatKind::Range(a, b, inc) => {
                let la = self.lit_pat(a, expected, span);
                let lb = self.lit_pat(b, expected, span);
                if matches!(la, Lit::Str(_) | Lit::Bool(_)) {
                    self.err(span, "range patterns need numbers or characters");
                }
                mkp(PatKind::Range(la, lb, *inc), ety)
            }
            ast::PatKind::Tuple(ps) => {
                let et = self.resolve(expected);
                let tys: Vec<Ty> = match &et {
                    Ty::Tuple(ts) if ts.len() == ps.len() => ts.clone(),
                    Ty::Var(_) => {
                        let ts: Vec<Ty> = ps.iter().map(|_| self.fresh()).collect();
                        self.unify(&et, &Ty::Tuple(ts.clone()));
                        ts
                    }
                    Ty::Error => ps.iter().map(|_| Ty::Error).collect(),
                    _ => {
                        let s = self.tys(&et);
                        self.err(span, format!("tuple pattern with {} element(s) cannot match `{s}`", ps.len()));
                        ps.iter().map(|_| Ty::Error).collect()
                    }
                };
                let subs = ps.iter().zip(&tys).map(|(p, t)| self.pattern(p, t, mutable, binds, reuse)).collect();
                mkp(PatKind::Tuple(subs), ety)
            }
            ast::PatKind::Path(segs) => match self.pat_path(segs) {
                Some((aid, vi)) => self.variant_pattern(aid, vi, None, &[], &[], false, expected, span, mutable, binds, reuse, Shape::Unit),
                None => mkp(PatKind::Wild, ety),
            },
            ast::PatKind::TupleStruct(segs, ps) => match self.pat_path(segs) {
                Some((aid, vi)) => self.variant_pattern(aid, vi, None, ps, &[], false, expected, span, mutable, binds, reuse, Shape::Tuple),
                None => {
                    for sp in ps {
                        self.pattern(sp, &Ty::Error, mutable, binds, reuse);
                    }
                    mkp(PatKind::Wild, ety)
                }
            },
            ast::PatKind::Struct(segs, fields, rest) => {
                let def = if segs.len() == 1 && segs[0].name == "Self" {
                    match &self.self_ty {
                        Some(Ty::Adt(id, _)) => Ok(Def::Adt(*id)),
                        _ => Err(Diag::new(span, "`Self` is not a struct here")),
                    }
                } else {
                    self.prog.resolve_path_def(self.module, segs)
                };
                match def {
                    Ok(Def::Variant(aid, vi)) => self.variant_pattern(aid, vi, None, &[], fields, *rest, expected, span, mutable, binds, reuse, Shape::Record),
                    Ok(Def::Adt(aid)) if matches!(self.prog.adts[aid].kind, AdtKind::Struct(_)) => {
                        let args: Vec<Ty> = (0..self.prog.adts[aid].generics.len()).map(|_| self.fresh()).collect();
                        let ty = Ty::Adt(aid, args.clone());
                        if !self.unify(&ty, expected) {
                            self.mismatch(span, expected, &ty);
                        }
                        let defs = self.prog.struct_fields(aid).to_vec();
                        let subs = self.field_pats(&defs, &args, fields, *rest, span, mutable, binds, reuse);
                        mkp(PatKind::Struct(subs), ety)
                    }
                    Ok(_) => {
                        self.err(span, "expected a struct or an enum variant with named fields");
                        mkp(PatKind::Wild, ety)
                    }
                    Err(d) => {
                        self.g.error(d);
                        mkp(PatKind::Wild, ety)
                    }
                }
            }
            ast::PatKind::Or(alts) => {
                let mut first_binds = Vec::new();
                let first = self.pattern(&alts[0], expected, mutable, &mut first_binds, reuse);
                let map: HashMap<String, LocalId> = first_binds.iter().cloned().collect();
                let mut outs = vec![first];
                for a in &alts[1..] {
                    let mut bs = Vec::new();
                    outs.push(self.pattern(a, expected, mutable, &mut bs, Some(&map)));
                    for (n, _) in &first_binds {
                        if !bs.iter().any(|(m, _)| m == n) {
                            self.err(a.span, format!("variable `{n}` is not bound in all alternatives of this pattern"));
                        }
                    }
                }
                binds.extend(first_binds);
                mkp(PatKind::Or(outs), ety)
            }
            ast::PatKind::List(ps, rest) => {
                let list_id = self.prog.known_adt("List");
                let et = self.resolve(expected);
                let elem = match &et {
                    Ty::Adt(id, a) if *id == list_id => a[0].clone(),
                    Ty::Var(_) => {
                        let v = self.fresh();
                        self.unify(&et, &Ty::Adt(list_id, vec![v.clone()]));
                        v
                    }
                    Ty::Error => Ty::Error,
                    _ => {
                        let s = self.tys(&et);
                        self.err(span, format!("list pattern cannot match `{s}`"));
                        Ty::Error
                    }
                };
                let subs = ps.iter().map(|p| self.pattern(p, &elem, mutable, binds, reuse)).collect();
                let r = rest.as_ref().map(|r| {
                    r.as_ref().map(|id| {
                        let lt = Ty::Adt(list_id, vec![elem.clone()]);
                        let l = match reuse.and_then(|m| m.get(&id.name)) {
                            Some(&l) => l,
                            None => self.new_local(&id.name, lt, mutable),
                        };
                        binds.push((id.name.clone(), l));
                        l
                    })
                });
                mkp(PatKind::List(subs, r), ety)
            }
        }
    }

    fn pat_path(&mut self, segs: &[ast::Ident]) -> Option<(AdtId, usize)> {
        let def = if segs[0].name == "Self" && segs.len() == 2 {
            match &self.self_ty {
                Some(Ty::Adt(id, _)) => match &self.prog.adts[*id].kind {
                    AdtKind::Enum(vs) => vs.iter().position(|v| v.name == segs[1].name).map(|i| Def::Variant(*id, i)).ok_or_else(|| Diag::new(segs[1].span, "no such variant")),
                    _ => Err(Diag::new(segs[0].span, "`Self` is not an enum")),
                },
                _ => Err(Diag::new(segs[0].span, "`Self` is not available here")),
            }
        } else {
            self.prog.resolve_path_def(self.module, segs)
        };
        match def {
            Ok(Def::Variant(aid, vi)) => Some((aid, vi)),
            Ok(_) => {
                let n = segs.iter().map(|s| s.name.as_str()).collect::<Vec<_>>().join(".");
                self.err(segs[0].span.to(segs.last().unwrap().span), format!("`{n}` is not an enum variant"));
                None
            }
            Err(d) => {
                self.g.error(d);
                None
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn variant_pattern(
        &mut self,
        aid: AdtId,
        vi: usize,
        _adt_args: Option<Vec<Ty>>,
        tuple_pats: &[ast::Pattern],
        field_pats: &[(ast::Ident, Option<ast::Pattern>)],
        rest: bool,
        expected: &Ty,
        span: Span,
        mutable: bool,
        binds: &mut Vec<(String, LocalId)>,
        reuse: Option<&HashMap<String, LocalId>>,
        used_shape: Shape,
    ) -> Pat {
        let adt = &self.prog.adts[aid];
        let AdtKind::Enum(vs) = &adt.kind else { unreachable!() };
        let v = vs[vi].clone();
        let args: Vec<Ty> = (0..adt.generics.len()).map(|_| self.fresh()).collect();
        let ty = Ty::Adt(aid, args.clone());
        if !self.unify(&ty, expected) {
            self.mismatch(span, expected, &ty);
        }
        if v.shape != used_shape {
            let want = match v.shape {
                Shape::Unit => format!("`{}`", v.name),
                Shape::Tuple => format!("`{}(...)`", v.name),
                Shape::Record => format!("`{} {{ ... }}`", v.name),
            };
            self.err(span, format!("variant `{}` must be matched as {want}", v.name));
            return Pat { kind: PatKind::Wild, ty: expected.clone(), span };
        }
        let subs = match v.shape {
            Shape::Unit => Vec::new(),
            Shape::Tuple => {
                if tuple_pats.len() != v.fields.len() {
                    self.err(span, format!("variant `{}` has {} field(s), but the pattern has {}", v.name, v.fields.len(), tuple_pats.len()));
                }
                tuple_pats
                    .iter()
                    .enumerate()
                    .filter_map(|(i, p)| {
                        let ft = v.fields.get(i).map(|f| self.prog.normalize_proj(f.ty.subst(&args))).unwrap_or(Ty::Error);
                        let sp = self.pattern(p, &ft, mutable, binds, reuse);
                        if i < v.fields.len() { Some((i, sp)) } else { None }
                    })
                    .collect()
            }
            Shape::Record => self.field_pats(&v.fields, &args, field_pats, rest, span, mutable, binds, reuse),
        };
        Pat { kind: PatKind::Variant(vi, subs), ty: expected.clone(), span }
    }

    #[allow(clippy::too_many_arguments)]
    fn field_pats(&mut self, defs: &[FieldDef], args: &[Ty], fields: &[(ast::Ident, Option<ast::Pattern>)], rest: bool, span: Span, mutable: bool, binds: &mut Vec<(String, LocalId)>, reuse: Option<&HashMap<String, LocalId>>) -> Vec<(usize, Pat)> {
        let mut out = Vec::new();
        let mut seen = vec![false; defs.len()];
        for (name, p) in fields {
            let Some(i) = defs.iter().position(|f| f.name == name.name) else {
                self.err(name.span, format!("no field named `{}`", name.name));
                continue;
            };
            seen[i] = true;
            let ft = self.prog.normalize_proj(defs[i].ty.subst(args));
            let sp = match p {
                Some(p) => self.pattern(p, &ft, mutable, binds, reuse),
                None => self.pattern(&abind(&name.name, name.span), &ft, mutable, binds, reuse),
            };
            out.push((i, sp));
        }
        if !rest {
            let missing: Vec<String> = defs.iter().zip(&seen).filter(|(_, s)| !**s).map(|(f, _)| format!("`{}`", f.name)).collect();
            if !missing.is_empty() {
                self.err(span, format!("pattern does not mention field(s) {}; add them or use `..`", missing.join(", ")));
            }
        }
        out
    }

    fn lit_pat(&mut self, l: &ast::LitPat, expected: &Ty, span: Span) -> Lit {
        let (lit, ty) = match l {
            ast::LitPat::Int(v) => (Lit::Int(*v), self.fresh_kind(VarKind::Int)),
            ast::LitPat::Float(f) => (Lit::Float(*f), self.fresh_kind(VarKind::Float)),
            ast::LitPat::Bool(b) => (Lit::Bool(*b), Ty::Bool),
            ast::LitPat::Char(c) => (Lit::Char(*c), Ty::Char),
            ast::LitPat::Str(s) => (Lit::Str(s.clone()), Ty::Str),
        };
        if !self.unify(&ty, expected) {
            self.mismatch(span, expected, &ty);
        }
        lit
    }

    // ---------------- finalization ----------------
    fn finalize(&mut self, f: &mut ir::Func) {
        for l in f.locals.iter_mut() {
            l.ty = self.zonk_default(&l.ty);
        }
        f.ret = self.zonk_default(&f.ret);
        let mut body = std::mem::replace(&mut f.body, unit(Span::default()));
        let mut reported = false;
        self.fin_expr(&mut body, &f.locals, &mut reported);
        f.body = body;
        for l in &f.locals {
            if l.ty.has_vars() && !reported {
                reported = true;
                self.err(f.body.span, format!("cannot infer the type of `{}`; add a type annotation", l.name));
            }
        }
    }

    fn fin_ty(&mut self, t: &mut Ty, span: Span, reported: &mut bool) {
        *t = self.zonk_default(t);
        if t.has_vars() {
            if !*reported {
                *reported = true;
                self.err(span, "cannot infer a type here; add a type annotation");
            }
            *t = replace_vars(t);
        }
    }

    fn fin_pat(&mut self, p: &mut Pat, reported: &mut bool) {
        self.fin_ty(&mut p.ty, p.span, reported);
        match &mut p.kind {
            PatKind::Bind(_, Some(sub)) => self.fin_pat(sub, reported),
            PatKind::Tuple(ps) | PatKind::Or(ps) => ps.iter_mut().for_each(|p| self.fin_pat(p, reported)),
            PatKind::Struct(fs) | PatKind::Variant(_, fs) => fs.iter_mut().for_each(|(_, p)| self.fin_pat(p, reported)),
            PatKind::List(ps, _) => ps.iter_mut().for_each(|p| self.fin_pat(p, reported)),
            PatKind::Lit(l) => self.check_lit(l, &p.ty.clone(), p.span),
            PatKind::Range(a, b, _) => {
                let t = p.ty.clone();
                self.check_lit(a, &t, p.span);
                self.check_lit(b, &t, p.span);
            }
            _ => {}
        }
    }

    fn check_lit(&mut self, l: &mut Lit, ty: &Ty, span: Span) {
        if let Lit::Int(v) = l {
            match ty {
                Ty::Int(it) => {
                    if *v < IntTy::min(*it) || *v > IntTy::max(*it) {
                        self.err(span, format!("integer literal `{v}` does not fit in `{}` (range {}..={})", it.name(), IntTy::min(*it), IntTy::max(*it)));
                    }
                }
                Ty::Float(_) => {
                    *l = Lit::Float(*v as f64);
                }
                _ => {}
            }
        }
    }

    fn fin_expr(&mut self, e: &mut Expr, locals: &[LocalInfo], reported: &mut bool) {
        let span = e.span;
        self.fin_ty(&mut e.ty, span, reported);
        let ety = e.ty.clone();
        match &mut e.kind {
            ExprKind::Lit(l) => self.check_lit(l, &ety, span),
            ExprKind::Local(_) | ExprKind::Unreachable | ExprKind::Continue(_) => {}
            ExprKind::SetLocal(_, v) | ExprKind::Return(v) | ExprKind::Cast(v) | ExprKind::Discard(v) | ExprKind::Loop(_, v) => self.fin_expr(v, locals, reported),
            ExprKind::Break(_, v) => {
                if let Some(v) = v {
                    self.fin_expr(v, locals, reported)
                }
            }
            ExprKind::Call(inst, args) => {
                for t in inst.targs.iter_mut() {
                    self.fin_ty(t, span, reported);
                }
                for a in args.iter_mut() {
                    self.fin_expr(a, locals, reported);
                }
                let inst = inst.clone();
                self.check_bounds(&inst, span);
                self.g.request(inst);
            }
            ExprKind::FnValue(inst) => {
                for t in inst.targs.iter_mut() {
                    self.fin_ty(t, span, reported);
                }
                let inst = inst.clone();
                self.check_bounds(&inst, span);
                self.g.request(inst);
            }
            ExprKind::Intrinsic(_, targs, args) => {
                for t in targs.iter_mut() {
                    self.fin_ty(t, span, reported);
                }
                for a in args.iter_mut() {
                    self.fin_expr(a, locals, reported);
                }
            }
            ExprKind::CallIndirect(f, args) => {
                self.fin_expr(f, locals, reported);
                for a in args.iter_mut() {
                    self.fin_expr(a, locals, reported);
                }
            }
            ExprKind::Closure { .. } => {}
            ExprKind::StructNew(vs) | ExprKind::EnumNew(_, vs) | ExprKind::TupleNew(vs) | ExprKind::ArrayLit(vs) | ExprKind::StrConcat(vs) => {
                for v in vs.iter_mut() {
                    self.fin_expr(v, locals, reported);
                }
            }
            ExprKind::Field(b, _, _) => self.fin_expr(b, locals, reported),
            ExprKind::SetField(b, _, v) => {
                self.fin_expr(b, locals, reported);
                self.fin_expr(v, locals, reported);
            }
            ExprKind::Block(stmts, tail) => {
                for s in stmts.iter_mut() {
                    match s {
                        Stmt::Let(p, init) => {
                            self.fin_expr(init, locals, reported);
                            self.fin_pat(p, reported);
                            if !crate::exhaust::irrefutable(self.prog, p) {
                                self.err(p.span, "refutable pattern in `let`; use `let ... else { ... }` or `match`");
                            }
                        }
                        Stmt::Expr(x) => self.fin_expr(x, locals, reported),
                    }
                }
                if let Some(t) = tail {
                    self.fin_expr(t, locals, reported);
                }
            }
            ExprKind::If(c, t, el) => {
                self.fin_expr(c, locals, reported);
                self.fin_expr(t, locals, reported);
                self.fin_expr(el, locals, reported);
            }
            ExprKind::Match(s, arms) => {
                self.fin_expr(s, locals, reported);
                for a in arms.iter_mut() {
                    self.fin_pat(&mut a.pat, reported);
                    if let Some(g) = &mut a.guard {
                        self.fin_expr(g, locals, reported);
                    }
                    self.fin_expr(&mut a.body, locals, reported);
                }
                if !*reported {
                    let sty = s.ty.clone();
                    if let Err(witness) = crate::exhaust::check_match(self.prog, &sty, arms) {
                        self.g.error(Diag::new(span, format!("non-exhaustive match: pattern `{witness}` is not covered")).note("add an arm for it, or a wildcard arm `_ -> ...`"));
                    }
                }
            }
            ExprKind::Prim(_, t, args) => {
                self.fin_ty(t, span, reported);
                for a in args.iter_mut() {
                    self.fin_expr(a, locals, reported);
                }
            }
            ExprKind::DynNew(v, tr) => {
                self.fin_expr(v, locals, reported);
                for t in tr.args.iter_mut() {
                    self.fin_ty(t, span, reported);
                }
                let concrete = v.ty.clone();
                let tr = tr.clone();
                self.request_vtable(concrete, tr, span);
            }
            ExprKind::DynCall { recv, trait_ref, args, .. } => {
                self.fin_expr(recv, locals, reported);
                for t in trait_ref.args.iter_mut() {
                    self.fin_ty(t, span, reported);
                }
                for a in args.iter_mut() {
                    self.fin_expr(a, locals, reported);
                }
            }
        }
    }

    fn check_bounds(&mut self, inst: &FnInst, span: Span) {
        let f = &self.prog.fns[inst.fn_id];
        for (i, g) in f.generics.iter().enumerate() {
            let Some(t) = inst.targs.get(i) else { continue };
            if matches!(f.owner, FnOwner::Trait(_)) && i == 0 {
                continue;
            }
            for b in &g.bounds {
                let bt = TraitRef { trait_id: b.trait_id, args: b.args.iter().map(|a| a.subst(&inst.targs)).collect() };
                if !self.prog.implements(t, &bt, 0) {
                    let ts = self.prog.ty_str(t);
                    self.g.error(Diag::new(span, format!("`{ts}` does not implement `{}`", self.prog.trait_ref_str(&bt))).note(format!("required by the bound `{}: {}` on `{}`", g.name, self.prog.traits[b.trait_id].name, f.name)));
                }
            }
        }
    }

    fn request_vtable(&mut self, concrete: Ty, tr: TraitRef, span: Span) {
        let key = (concrete.clone(), tr.clone());
        if self.g.vtables.contains_key(&key) {
            return;
        }
        let prog = self.prog;
        let mut methods = Vec::new();
        for t in prog.trait_closure(tr.trait_id) {
            for (name, mfid) in &prog.traits[t].methods {
                if prog.vtable_ok(*mfid).is_err() {
                    continue;
                }
                match self.find_method(&concrete, name, span) {
                    Some((fid, prefix)) => {
                        let mut targs: Vec<Ty> = prefix.iter().map(|t| self.zonk_default(t)).collect();
                        let f = &prog.fns[fid];
                        while targs.len() < f.generics.len() {
                            targs.push(Ty::Error);
                        }
                        let inst = FnInst { fn_id: fid, targs };
                        self.g.request(inst.clone());
                        methods.push((name.clone(), inst));
                    }
                    None => {
                        let s = prog.ty_str(&concrete);
                        self.err(span, format!("`{s}` has no method `{name}` required by `dyn {}`", prog.traits[tr.trait_id].name));
                    }
                }
            }
        }
        self.g.vtables.insert(key.clone(), methods);
        self.g.vtable_order.push(key);
    }
}

fn replace_vars(t: &Ty) -> Ty {
    match t {
        Ty::Var(_) => Ty::Error,
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(replace_vars).collect()),
        Ty::Adt(id, ts) => Ty::Adt(*id, ts.iter().map(replace_vars).collect()),
        Ty::Array(t) => Ty::Array(Box::new(replace_vars(t))),
        Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(replace_vars).collect(), Box::new(replace_vars(r))),
        other => other.clone(),
    }
}

pub fn replace_proj_dyn(t: &Ty, assoc: &[(String, Ty)]) -> Ty {
    match t {
        Ty::Proj(_, n) => assoc.iter().find(|(m, _)| m == n).map(|(_, t)| t.clone()).unwrap_or(Ty::Error),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| replace_proj_dyn(t, assoc)).collect()),
        Ty::Adt(id, ts) => Ty::Adt(*id, ts.iter().map(|t| replace_proj_dyn(t, assoc)).collect()),
        Ty::Array(t) => Ty::Array(Box::new(replace_proj_dyn(t, assoc))),
        Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(|t| replace_proj_dyn(t, assoc)).collect(), Box::new(replace_proj_dyn(r, assoc))),
        other => other.clone(),
    }
}

fn is_const_expr(prog: &Program, module: ModId, e: &ast::Expr) -> bool {
    let check = |e: &ast::Expr| is_const_expr(prog, module, e);
    match &e.kind {
        ast::ExprKind::Int(_) | ast::ExprKind::Float(_) | ast::ExprKind::Bool(_) | ast::ExprKind::Char(_) | ast::ExprKind::Unit | ast::ExprKind::Name(..) => true,
        ast::ExprKind::Str(ps) => ps.iter().all(|p| matches!(p, ast::StrPiece::Lit(_))),
        ast::ExprKind::Field(b, _, _) => check(b),
        ast::ExprKind::Unary(_, x) => check(x),
        ast::ExprKind::Binary(_, a, b) => check(a) && check(b),
        ast::ExprKind::Tuple(xs) | ast::ExprKind::List(xs) => xs.iter().all(check),
        ast::ExprKind::Struct { fields, base, .. } => base.is_none() && fields.iter().all(|(_, v)| v.as_ref().is_none_or(check)),
        ast::ExprKind::Call(f, args) => args.iter().all(check) && const_constructor(prog, module, f),
        _ => false,
    }
}

fn const_constructor(prog: &Program, module: ModId, f: &ast::Expr) -> bool {
    let mut path = Vec::new();
    let mut current = f;
    loop {
        match &current.kind {
            ast::ExprKind::Field(base, id, _) => {
                path.push(id.clone());
                current = base;
            }
            ast::ExprKind::Name(id, _) => {
                path.push(id.clone());
                break;
            }
            _ => return false,
        }
    }
    path.reverse();
    if matches!(prog.resolve_path_def(module, &path), Ok(Def::Variant(..))) {
        return true;
    }
    let Some((variant, base)) = path.split_last() else { return false };
    if base.is_empty() { return false }
    let Ok(Def::Alias(alias)) = prog.resolve_path_def(module, base) else { return false };
    let Some(Ty::Adt(id, _)) = &prog.aliases[alias].resolved else { return false };
    matches!(&prog.adts[*id].kind, AdtKind::Enum(variants) if variants.iter().any(|v| v.name == variant.name))
}
