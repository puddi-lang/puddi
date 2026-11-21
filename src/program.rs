//! Item collection, name resolution and signature resolution.

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use crate::ast::{self, TypeArg, TypeExpr};
use crate::diag::{Diag, Span};
use crate::ir::TraitRef;
use crate::types::*;

#[derive(Clone, Copy)]
pub enum Naming {
    Snake,
    Camel,
    Constant,
}

impl Naming {
    pub fn warning(self, id: &ast::Ident) -> Option<Diag> {
        let name = id.name.trim_matches('_');
        if name.is_empty() || name.starts_with('$') {
            return None;
        }
        let (valid, style) = match self {
            Self::Snake => (
                name.chars().all(|c| c == '_' || c.is_alphanumeric() && !c.is_uppercase()),
                "snake_case",
            ),
            Self::Camel => (
                name.starts_with(char::is_uppercase) && !name.contains('_'),
                "UpperCamelCase",
            ),
            Self::Constant => (!name.chars().any(char::is_lowercase), "SCREAMING_SNAKE_CASE"),
        };
        if valid {
            return None;
        }
        let mut warning = Diag::new(id.span, format!("name `{}` should use {style}", id.name));
        warning.warning = true;
        Some(warning)
    }
}

fn item_names(item: &ast::Item, warnings: &mut Vec<Diag>) {
    use ast::{ItemKind::*, VariantKind};
    use Naming::*;

    fn function_names(f: &ast::FnDecl, warnings: &mut Vec<Diag>) {
        warnings.extend(Snake.warning(&f.name));
        warnings.extend(f.params.iter().filter_map(|p| Snake.warning(&p.name)));
    }

    match &item.kind {
        Struct(item) => {
            warnings.extend(Camel.warning(&item.name));
            warnings.extend(item.fields.iter().filter_map(|f| Snake.warning(&f.name)));
        }
        Enum(item) => {
            warnings.extend(Camel.warning(&item.name));
            for variant in &item.variants {
                warnings.extend(Camel.warning(&variant.name));
                if let VariantKind::Record(fields) = &variant.kind {
                    warnings.extend(fields.iter().filter_map(|f| Snake.warning(&f.name)));
                }
            }
        }
        Trait(item) => {
            warnings.extend(Camel.warning(&item.name));
            warnings.extend(item.assoc_types.iter().filter_map(|id| Camel.warning(id)));
            for method in &item.methods {
                function_names(method, warnings);
            }
        }
        Impl(item) => {
            for method in &item.methods {
                function_names(method, warnings);
            }
        }
        TypeAlias { name, .. } => warnings.extend(Camel.warning(name)),
        Const { name, .. } => warnings.extend(Constant.warning(name)),
        Fn(f) => function_names(f, warnings),
        Test { .. } => {}
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pkg {
    Prelude,
    Std,
    User,
    /// A dependency package.
    Dep(u16),
}

impl Pkg {
    /// Packages compiled from user-written source (the root package and its dependencies).
    pub fn is_source(self) -> bool {
        matches!(self, Pkg::User | Pkg::Dep(_))
    }
}

#[derive(Clone, Debug)]
pub enum Def {
    Adt(AdtId),
    Trait(TraitId),
    Fn(FnId),
    Const(usize),
    Alias(usize),
    Module(ModId),
    Builtin(Ty),
    Variant(AdtId, usize),
}

pub struct ModuleInfo {
    pub path: String,
    pub pkg: Pkg,
    /// File ID of the author-written source, before synthetic items are added.
    pub source_file: Option<u32>,
    pub items: HashMap<String, (Def, bool)>,
    pub imports: HashMap<String, (Def, Span)>,
}

#[derive(Clone, Debug)]
pub struct GenericDef {
    pub name: String,
    pub bounds: Vec<TraitRef>,
}

fn generic_names(params: &[ast::GenericParam]) -> Vec<GenericDef> {
    params.iter().map(|p| GenericDef { name: p.name.name.clone(), bounds: Vec::new() }).collect()
}

#[derive(Clone, Debug)]
pub struct FieldDef {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    pub public: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    Unit,
    Tuple,
    Record,
}

#[derive(Clone, Debug)]
pub struct VariantDef {
    pub name: String,
    pub fields: Vec<FieldDef>,
    pub shape: Shape,
}

#[derive(Clone, Debug)]
pub enum AdtKind {
    Struct(Vec<FieldDef>),
    Enum(Vec<VariantDef>),
}

pub struct AdtDef {
    pub name: String,
    pub module: ModId,
    pub generics: Vec<GenericDef>,
    pub kind: AdtKind,
    pub span: Span,
    pub pkg: Pkg,
}

pub struct TraitDef {
    pub name: String,
    pub module: ModId,
    /// Trait's own generics; in method signatures Param(0) is Self and
    /// Param(1 + i) is the i-th trait generic.
    pub generics: Vec<GenericDef>,
    pub supertraits: Vec<TraitRef>,
    pub assoc: Vec<String>,
    pub methods: Vec<(String, FnId)>,
    pub span: Span,
    pub pkg: Pkg,
}

pub struct ImplDef {
    pub module: ModId,
    pub generics: Vec<GenericDef>,
    pub trait_ref: Option<TraitRef>,
    pub self_ty: Ty,
    pub methods: HashMap<String, FnId>,
    pub assoc: HashMap<String, Ty>,
    pub span: Span,
    pub pkg: Pkg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FnOwner {
    Free,
    Impl(ImplId),
    Trait(TraitId),
}

impl FnOwner {
    pub fn impl_id(self) -> Option<ImplId> {
        match self {
            Self::Impl(id) => Some(id),
            _ => None,
        }
    }
}

pub struct FnDef {
    pub name: String,
    pub module: ModId,
    pub generics: Vec<GenericDef>,
    /// Number of leading generics that come from the enclosing impl/trait.
    pub n_outer: usize,
    pub params: Vec<(String, Ty)>,
    pub has_self: bool,
    pub self_ty: Option<Ty>,
    pub ret: Ty,
    pub decl: Arc<ast::FnDecl>,
    pub owner: FnOwner,
    pub is_pub: bool,
    pub span: Span,
    pub intrinsic: Option<String>,
    pub extern_: Option<(String, String)>,
    pub export: Option<String>,
    pub deprecated: Option<String>,
    pub test_name: Option<String>,
    pub pkg: Pkg,
}

pub struct ConstDef {
    pub name: String,
    pub module: ModId,
    pub ty: Ty,
    pub ty_expr: ast::TypeExpr,
    pub value: ast::Expr,
    pub span: Span,
}

pub struct AliasDef {
    pub name: String,
    pub module: ModId,
    pub generics: Vec<String>,
    pub ty: ast::TypeExpr,
    pub resolved: Option<Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Str,
    Unit,
    Tuple(usize),
    Adt(AdtId),
    Array,
    Fn,
    Dyn(TraitId),
    Any,
}

pub fn head_of(t: &Ty) -> Option<Head> {
    Some(match t {
        Ty::Int(i) => Head::Int(*i),
        Ty::Float(f) => Head::Float(*f),
        Ty::Bool => Head::Bool,
        Ty::Char => Head::Char,
        Ty::Str => Head::Str,
        Ty::Unit => Head::Unit,
        Ty::Tuple(ts) => Head::Tuple(ts.len()),
        Ty::Adt(id, _) => Head::Adt(*id),
        Ty::Array(_) => Head::Array,
        Ty::Fn(..) => Head::Fn,
        Ty::Dyn(id, ..) => Head::Dyn(*id),
        Ty::Param(_) => Head::Any,
        _ => return None,
    })
}

pub struct Program {
    pub modules: Vec<ModuleInfo>,
    pub adts: Vec<AdtDef>,
    pub traits: Vec<TraitDef>,
    pub impls: Vec<ImplDef>,
    pub fns: Vec<FnDef>,
    pub consts: Vec<ConstDef>,
    pub aliases: Vec<AliasDef>,
    pub impls_by_head: HashMap<Head, Vec<ImplId>>,
    pub prelude: ModId,
    pub target: String,
    pub warnings: Vec<Diag>,
    /// Well-known prelude items.
    pub known: HashMap<&'static str, Def>,
}

pub struct ModSource {
    pub path: String,
    pub pkg: Pkg,
    pub ast: ast::Module,
    pub source_file: Option<u32>,
    /// Module path prefix of the package ("" for the root package).
    pub prefix: String,
    /// Dependency import names of the package -> their module path prefixes.
    pub aliases: HashMap<String, String>,
}

/// Context for resolving type expressions.
#[derive(Clone)]
pub struct TyCx<'a> {
    pub module: ModId,
    pub generics: &'a [String],
    pub self_ty: Option<Ty>,
    pub self_impl: Option<ImplId>,
}

const PORTABLE: &[&str] = &["browser", "wasi", "plugin"];

macro_rules! std_modules {
    ($($name:literal => $targets:expr),* $(,)?) => {
        pub const STD_MODULES: &[(&str, &str, &[&str])] = &[
            $((concat!("std.", $name), include_str!(concat!("../std/", $name, ".pud")), $targets)),*
        ];
    };
}

std_modules! {
    "math" => PORTABLE,
    "log" => PORTABLE,
    "time" => &["browser", "wasi"],
    "random" => &["browser", "wasi"],
    "io" => &["wasi"],
    "fs" => &["wasi"],
    "env" => &["wasi"],
    "json" => PORTABLE,
    "http" => &["browser", "wasi"],
    "worker" => &["browser", "wasi"],
    "dom" => &["browser"],
    "bytes" => PORTABLE,
    "collections" => PORTABLE,
    "csv" => PORTABLE,
    "date" => PORTABLE,
    "encoding" => PORTABLE,
    "fmt" => PORTABLE,
    "iter" => PORTABLE,
    "path" => PORTABLE,
    "stats" => PORTABLE,
    "text" => PORTABLE,
}

thread_local! {
    /// Modules a plugin's world provides through its imports (SPEC 10.2 "host").
    static HOST_MODULES: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Sets the modules the current plugin world provides.
pub fn set_host_modules(m: Vec<String>) {
    HOST_MODULES.with(|h| *h.borrow_mut() = m);
}

pub fn std_available(path: &str, target: &str) -> Option<bool> {
    if target == "plugin" && HOST_MODULES.with(|h| h.borrow().iter().any(|m| m == path)) {
        return Some(true);
    }
    STD_MODULES.iter().find(|(p, _, _)| *p == path).map(|(_, _, ts)| ts.contains(&target))
}

impl Program {
    pub fn adt_name(&self, id: AdtId) -> String {
        self.adts[id].name.clone()
    }

    pub fn ty_str(&self, t: &Ty) -> String {
        self.ty_str_p(t, &[])
    }

    pub fn ty_str_p(&self, t: &Ty, params: &[String]) -> String {
        let an = |id: AdtId| self.adts[id].name.clone();
        let tn = |id: TraitId| self.traits[id].name.clone();
        TyDisplay { ty: t, adt_names: &an, trait_names: &tn, param_names: params }.to_string()
    }

    pub fn trait_ref_str(&self, tr: &TraitRef) -> String {
        let mut s = self.traits[tr.trait_id].name.clone();
        if !tr.args.is_empty() {
            s.push('<');
            s.push_str(&tr.args.iter().map(|t| self.ty_str(t)).collect::<Vec<_>>().join(", "));
            s.push('>');
        }
        s
    }

    pub fn known_adt(&self, name: &str) -> AdtId {
        match self.known.get(name) {
            Some(Def::Adt(id)) => *id,
            _ => panic!("prelude type {name} missing"),
        }
    }

    pub fn known_trait(&self, name: &str) -> TraitId {
        match self.known.get(name) {
            Some(Def::Trait(id)) => *id,
            _ => panic!("prelude trait {name} missing"),
        }
    }

    pub fn known_fn(&self, name: &str) -> FnId {
        match self.known.get(name) {
            Some(Def::Fn(id)) => *id,
            _ => panic!("prelude fn {name} missing"),
        }
    }

    pub fn future_ty(&self, t: Ty) -> Ty {
        match self.known.get("Future") {
            Some(Def::Adt(id)) => Ty::Adt(*id, vec![t]),
            _ => t,
        }
    }

    pub fn option_ty(&self, t: Ty) -> Ty {
        Ty::Adt(self.known_adt("Option"), vec![t])
    }

    pub fn list_ty(&self, t: Ty) -> Ty {
        Ty::Adt(self.known_adt("List"), vec![t])
    }

    /// Look up a name visible in a module (items, imports, prelude).
    pub fn lookup(&self, module: ModId, name: &str) -> Option<Def> {
        let m = &self.modules[module];
        if let Some((d, _)) = m.items.get(name) {
            return Some(d.clone());
        }
        if let Some((d, _)) = m.imports.get(name) {
            return Some(d.clone());
        }
        if let Some((d, _)) = self.modules[self.prelude].items.get(name) {
            return Some(d.clone());
        }
        None
    }

    /// Look up a member of a module, checking visibility from `from`.
    pub fn module_member(&self, module: ModId, name: &str, from: ModId, span: Span) -> Result<Def, Diag> {
        let m = &self.modules[module];
        match m.items.get(name) {
            Some((d, is_pub)) => {
                if !*is_pub && module != from && m.pkg.is_source() {
                    return Err(Diag::new(span, format!("`{name}` is private to module `{}`", m.path)).note("mark it `pub` to use it from other modules"));
                }
                Ok(d.clone())
            }
            None => Err(Diag::new(span, format!("module `{}` has no item named `{name}`", m.path.strip_suffix(".lib").unwrap_or(&m.path)))),
        }
    }

    pub fn resolve_path_def(&self, module: ModId, segs: &[ast::Ident]) -> Result<Def, Diag> {
        let first = &segs[0];
        let mut def = self.lookup(module, &first.name).ok_or_else(|| Diag::new(first.span, format!("cannot find `{}` in this scope", first.name)))?;
        for seg in &segs[1..] {
            def = match def {
                Def::Module(m) => self.module_member(m, &seg.name, module, seg.span)?,
                Def::Adt(id) => match &self.adts[id].kind {
                    AdtKind::Enum(vs) => match vs.iter().position(|v| v.name == seg.name) {
                        Some(i) => Def::Variant(id, i),
                        None => return Err(Diag::new(seg.span, format!("enum `{}` has no variant `{}`", self.adts[id].name, seg.name))),
                    },
                    _ => return Err(Diag::new(seg.span, format!("`{}` is a struct, not a module or enum", self.adts[id].name))),
                },
                _ => return Err(Diag::new(seg.span, format!("`{}` is not a module", seg.name))),
            };
        }
        Ok(def)
    }

    pub fn resolve_ty(&self, cx: &TyCx, t: &TypeExpr) -> Result<Ty, Diag> {
        match t {
            TypeExpr::Tuple(ts, _) => {
                if ts.is_empty() {
                    return Ok(Ty::Unit);
                }
                Ok(Ty::Tuple(ts.iter().map(|t| self.resolve_ty(cx, t)).collect::<Result<_, _>>()?))
            }
            TypeExpr::Fn { is_async, params, ret, span } => {
                let _ = span;
                let ps = params.iter().map(|t| self.resolve_ty(cx, t)).collect::<Result<_, _>>()?;
                let mut r = match ret {
                    Some(r) => self.resolve_ty(cx, r)?,
                    None => Ty::Unit,
                };
                if *is_async {
                    r = self.future_ty(r);
                }
                Ok(Ty::Fn(ps, Box::new(r)))
            }
            TypeExpr::SelfTy(span) => cx.self_ty.clone().ok_or_else(|| Diag::new(*span, "`Self` is only available inside traits and impls")),
            TypeExpr::Dyn { segs, args, span } => {
                let def = self.resolve_path_def(cx.module, segs)?;
                let Def::Trait(tid) = def else {
                    return Err(Diag::new(*span, "`dyn` must be followed by a trait"));
                };
                let mut targs = Vec::new();
                let mut assoc = Vec::new();
                for a in args {
                    match a {
                        TypeArg::Type(t) => targs.push(self.resolve_ty(cx, t)?),
                        TypeArg::Assoc(n, t) => {
                            if !self.traits[tid].assoc.contains(&n.name) {
                                return Err(Diag::new(n.span, format!("trait `{}` has no associated type `{}`", self.traits[tid].name, n.name)));
                            }
                            assoc.push((n.name.clone(), self.resolve_ty(cx, t)?));
                        }
                    }
                }
                if targs.len() != self.traits[tid].generics.len() {
                    return Err(Diag::new(*span, format!("trait `{}` expects {} type argument(s), found {}", self.traits[tid].name, self.traits[tid].generics.len(), targs.len())));
                }
                assoc.sort_by(|a, b| a.0.cmp(&b.0));
                Ok(Ty::Dyn(tid, targs, assoc))
            }
            TypeExpr::Path { segs, args, span } => {
                let mut targs = Vec::new();
                for a in args {
                    match a {
                        TypeArg::Type(t) => targs.push(self.resolve_ty(cx, t)?),
                        TypeArg::Assoc(n, _) => return Err(Diag::new(n.span, "associated type bindings are only allowed on `dyn` types")),
                    }
                }
                // generic parameter or projection
                if let Some(i) = cx.generics.iter().position(|g| *g == segs[0].name) {
                    if segs.len() == 1 {
                        if !targs.is_empty() {
                            return Err(Diag::new(*span, "type parameters cannot take type arguments"));
                        }
                        return Ok(Ty::Param(i as u32));
                    }
                    if segs.len() == 2 {
                        return Ok(Ty::Proj(Box::new(Ty::Param(i as u32)), segs[1].name.clone()));
                    }
                }
                if segs[0].name == "Self" {
                    let st = cx.self_ty.clone().ok_or_else(|| Diag::new(*span, "`Self` is only available inside traits and impls"))?;
                    if segs.len() == 2 {
                        if let Some(ty) = cx.self_impl.and_then(|id| self.impls[id].assoc.get(&segs[1].name)) {
                            return Ok(ty.clone());
                        }
                        return Ok(self.normalize_proj(Ty::Proj(Box::new(st), segs[1].name.clone())));
                    }
                }
                let def = self.resolve_path_def(cx.module, segs)?;
                self.def_to_ty(def, targs, *span, segs.last().unwrap())
            }
        }
    }

    pub fn def_to_ty(&self, def: Def, targs: Vec<Ty>, span: Span, name: &ast::Ident) -> Result<Ty, Diag> {
        match def {
            Def::Builtin(t) => {
                if let Ty::Array(_) = t {
                    if targs.len() != 1 {
                        return Err(Diag::new(span, "`Array` expects 1 type argument"));
                    }
                    return Ok(Ty::Array(Box::new(targs.into_iter().next().unwrap())));
                }
                if !targs.is_empty() {
                    return Err(Diag::new(span, format!("`{}` does not take type arguments", name.name)));
                }
                Ok(t)
            }
            Def::Adt(id) => {
                let n = self.adts[id].generics.len();
                if targs.len() != n {
                    return Err(Diag::new(span, format!("`{}` expects {} type argument(s), found {}", self.adts[id].name, n, targs.len())));
                }
                Ok(Ty::Adt(id, targs))
            }
            Def::Alias(id) => {
                let a = &self.aliases[id];
                if targs.len() != a.generics.len() {
                    return Err(Diag::new(span, format!("type alias `{}` expects {} type argument(s), found {}", a.name, a.generics.len(), targs.len())));
                }
                match &a.resolved {
                    Some(base) => Ok(base.subst(&targs)),
                    None => Err(Diag::new(span, format!("type alias `{}` has not been resolved", a.name))),
                }
            }
            Def::Trait(_) => Err(Diag::new(span, format!("`{}` is a trait; use `dyn {}` for a trait object type", name.name, name.name))),
            _ => Err(Diag::new(span, format!("`{}` is not a type", name.name))),
        }
    }

    pub fn resolve_trait_ref(&self, cx: &TyCx, t: &TypeExpr) -> Result<TraitRef, Diag> {
        let TypeExpr::Path { segs, args, span } = t else {
            return Err(Diag::new(t.span(), "expected a trait"));
        };
        let def = self.resolve_path_def(cx.module, segs)?;
        let Def::Trait(tid) = def else {
            return Err(Diag::new(*span, format!("`{}` is not a trait", segs.last().unwrap().name)));
        };
        let mut targs = Vec::new();
        for a in args {
            match a {
                TypeArg::Type(t) => targs.push(self.resolve_ty(cx, t)?),
                TypeArg::Assoc(n, _) => return Err(Diag::new(n.span, "associated type bindings are not allowed here")),
            }
        }
        if targs.len() != self.traits[tid].generics.len() {
            return Err(Diag::new(*span, format!("trait `{}` expects {} type argument(s), found {}", self.traits[tid].name, self.traits[tid].generics.len(), targs.len())));
        }
        Ok(TraitRef { trait_id: tid, args: targs })
    }

    fn resolve_aliases(&mut self, errors: &mut Vec<Diag>) {
        let mut remaining = vec![0; self.aliases.len()];
        let mut dependents = vec![Vec::new(); self.aliases.len()];
        for (id, alias) in self.aliases.iter().enumerate() {
            let mut dependencies = Vec::new();
            self.alias_dependencies(alias, &alias.ty, &mut dependencies);
            dependencies.sort_unstable();
            dependencies.dedup();
            remaining[id] = dependencies.len();
            for dependency in dependencies {
                dependents[dependency].push(id);
            }
        }
        let mut ready: VecDeque<_> = (0..self.aliases.len()).filter(|&id| remaining[id] == 0).collect();
        while let Some(id) = ready.pop_front() {
            let a = &self.aliases[id];
            let cx = TyCx { module: a.module, generics: &a.generics, self_ty: None, self_impl: None };
            let resolved = self.resolve_ty(&cx, &a.ty).unwrap_or_else(|e| {
                errors.push(e);
                Ty::Error
            });
            self.aliases[id].resolved = Some(resolved);
            for &dependent in &dependents[id] {
                remaining[dependent] -= 1;
                if remaining[dependent] == 0 {
                    ready.push_back(dependent);
                }
            }
        }
        for alias in &mut self.aliases {
            if alias.resolved.is_none() {
                errors.push(Diag::new(alias.ty.span(), format!("type alias `{}` has a cyclic dependency", alias.name)));
                alias.resolved = Some(Ty::Error);
            }
        }
    }

    fn alias_dependencies(&self, alias: &AliasDef, ty: &TypeExpr, out: &mut Vec<usize>) {
        let args = match ty {
            TypeExpr::Path { segs, args, .. } => {
                let head = &segs[0].name;
                let generic = segs.len() <= 2 && alias.generics.contains(head);
                if !generic && head != "Self" {
                    if let Ok(Def::Alias(id)) = self.resolve_path_def(alias.module, segs) {
                        out.push(id);
                    }
                }
                args
            }
            TypeExpr::Dyn { args, .. } => args,
            TypeExpr::Tuple(items, _) => {
                for item in items {
                    self.alias_dependencies(alias, item, out);
                }
                return;
            }
            TypeExpr::Fn { params, ret, .. } => {
                for param in params {
                    self.alias_dependencies(alias, param, out);
                }
                if let Some(ret) = ret {
                    self.alias_dependencies(alias, ret, out);
                }
                return;
            }
            TypeExpr::SelfTy(_) => return,
        };
        for arg in args {
            match arg {
                TypeArg::Type(ty) | TypeArg::Assoc(_, ty) => self.alias_dependencies(alias, ty, out),
            }
        }
    }

    // ---------- impl matching ----------

    /// Match an impl-side pattern type (with Params) against a concrete type.
    pub fn match_ty(&self, pat: &Ty, actual: &Ty, binds: &mut Vec<Option<Ty>>) -> bool {
        match (pat, actual) {
            (Ty::Param(i), _) => {
                let i = *i as usize;
                if i >= binds.len() {
                    return false;
                }
                match &binds[i] {
                    Some(b) => b == actual || matches!(actual, Ty::Var(_)) || matches!(b, Ty::Var(_)),
                    None => {
                        binds[i] = Some(actual.clone());
                        true
                    }
                }
            }
            (_, Ty::Var(_)) | (_, Ty::Error) => true,
            (Ty::Tuple(a), Ty::Tuple(b)) => a.len() == b.len() && a.iter().zip(b).all(|(x, y)| self.match_ty(x, y, binds)),
            (Ty::Adt(i, a), Ty::Adt(j, b)) => i == j && a.iter().zip(b).all(|(x, y)| self.match_ty(x, y, binds)),
            (Ty::Array(a), Ty::Array(b)) => self.match_ty(a, b, binds),
            (Ty::Fn(pa, ra), Ty::Fn(pb, rb)) => pa.len() == pb.len() && pa.iter().zip(pb).all(|(x, y)| self.match_ty(x, y, binds)) && self.match_ty(ra, rb, binds),
            (Ty::Dyn(i, a, aa), Ty::Dyn(j, b, ab)) => {
                i == j && a.iter().zip(b).all(|(x, y)| self.match_ty(x, y, binds)) && aa.len() == ab.len() && aa.iter().zip(ab).all(|(x, y)| x.0 == y.0 && self.match_ty(&x.1, &y.1, binds))
            }
            (a, b) => a == b,
        }
    }

    pub fn candidate_impls(&self, t: &Ty) -> Vec<ImplId> {
        let mut out = Vec::new();
        if let Some(h) = head_of(t) {
            if let Some(v) = self.impls_by_head.get(&h) {
                out.extend(v.iter().copied());
            }
        }
        if let Some(v) = self.impls_by_head.get(&Head::Any) {
            out.extend(v.iter().copied());
        }
        out
    }

    fn impls_overlap(&self, left: &ImplDef, right: &ImplDef) -> bool {
        let (Some(a), Some(b)) = (&left.trait_ref, &right.trait_ref) else { return false };
        if a.trait_id != b.trait_id {
            return false;
        }
        let split = left.generics.len() as u32;
        let end = split + right.generics.len() as u32;
        let left_args: Vec<_> = (0..split).map(Ty::Var).collect();
        let right_args: Vec<_> = (split..end).map(Ty::Var).collect();
        let header = std::iter::once((&left.self_ty, &right.self_ty)).chain(a.args.iter().zip(&b.args));
        let pairs = header.map(|(x, y)| (x.subst(&left_args), y.subst(&right_args))).collect();
        let Some(bindings) = unify_headers(pairs, end) else { return false };
        let (left_args, right_args) = bindings.split_at(split as usize);
        self.impl_bounds_may_hold(left, left_args) && self.impl_bounds_may_hold(right, right_args)
    }

    fn impl_bounds_may_hold(&self, imp: &ImplDef, args: &[Ty]) -> bool {
        imp.generics.iter().zip(args).all(|(g, ty)| {
            let ty = self.normalize_proj(ty.clone());
            g.bounds.iter().all(|bound| {
                let tr = TraitRef {
                    trait_id: bound.trait_id,
                    args: bound.args.iter().map(|t| self.normalize_proj(t.subst(args))).collect(),
                };
                if matches!(ty, Ty::Var(_) | Ty::Proj(..)) {
                    true
                } else if ty.has_vars() || tr.args.iter().any(Ty::has_vars) {
                    self.candidate_impls(&ty).iter().any(|id| {
                        self.impls[*id].trait_ref.as_ref().is_some_and(|candidate| candidate.trait_id == tr.trait_id)
                    })
                } else {
                    self.implements(&ty, &tr, 0)
                }
            })
        })
    }

    /// Find an impl of `tr` for `t`. Returns impl id and impl generic bindings.
    pub fn find_trait_impl(&self, t: &Ty, trait_id: TraitId, targs: Option<&[Ty]>, depth: u32) -> Option<(ImplId, Vec<Ty>)> {
        if depth > 16 {
            return None;
        }
        for iid in self.candidate_impls(t) {
            let imp = &self.impls[iid];
            let Some(tr) = &imp.trait_ref else { continue };
            if tr.trait_id != trait_id {
                continue;
            }
            let mut binds = vec![None; imp.generics.len()];
            if !self.match_ty(&imp.self_ty, t, &mut binds) {
                continue;
            }
            if let Some(targs) = targs {
                if !tr.args.iter().zip(targs).all(|(p, a)| self.match_ty(p, a, &mut binds)) {
                    continue;
                }
            }
            let binds: Vec<Ty> = binds.into_iter().map(|b| b.unwrap_or(Ty::Error)).collect();
            // check bounds
            let ok = imp.generics.iter().enumerate().all(|(i, g)| {
                g.bounds.iter().all(|b| {
                    let bt = TraitRef { trait_id: b.trait_id, args: b.args.iter().map(|a| a.subst(&binds)).collect() };
                    self.implements(&binds[i], &bt, depth + 1)
                })
            });
            if ok {
                return Some((iid, binds));
            }
        }
        None
    }

    pub fn implements(&self, t: &Ty, tr: &TraitRef, depth: u32) -> bool {
        match t {
            Ty::Error | Ty::Never => return true,
            Ty::Var(_) => return true,
            Ty::Dyn(tid, _, _) => {
                if self.trait_has_super(*tid, tr.trait_id) {
                    return true;
                }
            }
            _ => {}
        }
        self.find_trait_impl(t, tr.trait_id, Some(&tr.args), depth).is_some()
    }

    pub fn trait_has_super(&self, tid: TraitId, target: TraitId) -> bool {
        self.trait_closure(tid).contains(&target)
    }

    /// All traits in the supertrait closure (including tid), in order.
    pub fn trait_closure(&self, tid: TraitId) -> Vec<TraitId> {
        let mut out = vec![tid];
        let mut i = 0;
        while i < out.len() {
            let t = out[i];
            for s in &self.traits[t].supertraits {
                if !out.contains(&s.trait_id) {
                    out.push(s.trait_id);
                }
            }
            i += 1;
        }
        out
    }

    /// Resolve projections in a type whose params have been substituted.
    pub fn normalize_proj(&self, t: Ty) -> Ty {
        match t {
            Ty::Proj(base, name) => {
                let base = self.normalize_proj(*base);
                if let Ty::Dyn(_, _, assoc) = &base {
                    if let Some((_, t)) = assoc.iter().find(|(n, _)| *n == name) {
                        return t.clone();
                    }
                }
                if base.has_params() || matches!(base, Ty::Var(_)) {
                    return Ty::Proj(Box::new(base), name);
                }
                let has_vars = base.has_vars();
                for iid in self.candidate_impls(&base) {
                    let imp = &self.impls[iid];
                    let Some(tr) = &imp.trait_ref else { continue };
                    if let Some(at) = imp.assoc.get(&name) {
                        let mut binds = vec![None; imp.generics.len()];
                        if self.match_ty(&imp.self_ty, &base, &mut binds) {
                            if matches!(imp.self_ty, Ty::Param(_)) {
                                // blanket impl: check its bounds
                                let b0: Vec<Ty> = binds.iter().map(|b| b.clone().unwrap_or(Ty::Error)).collect();
                                let ok = imp.generics.iter().enumerate().all(|(i, g)| {
                                    g.bounds.iter().all(|b| self.implements(&b0[i], &TraitRef { trait_id: b.trait_id, args: b.args.iter().map(|a| a.subst(&b0)).collect() }, 1))
                                });
                                if !ok {
                                    continue;
                                }
                            }
                            let _ = tr;
                            let binds: Vec<Ty> = binds.into_iter().map(|b| b.unwrap_or(Ty::Error)).collect();
                            return self.normalize_proj(at.subst(&binds));
                        }
                    }
                }
                if has_vars {
                    return Ty::Proj(Box::new(base), name);
                }
                Ty::Error
            }
            Ty::Tuple(ts) => Ty::Tuple(ts.into_iter().map(|t| self.normalize_proj(t)).collect()),
            Ty::Adt(id, ts) => Ty::Adt(id, ts.into_iter().map(|t| self.normalize_proj(t)).collect()),
            Ty::Array(t) => Ty::Array(Box::new(self.normalize_proj(*t))),
            Ty::Fn(ps, r) => Ty::Fn(ps.into_iter().map(|t| self.normalize_proj(t)).collect(), Box::new(self.normalize_proj(*r))),
            Ty::Dyn(id, ts, a) => Ty::Dyn(id, ts.into_iter().map(|t| self.normalize_proj(t)).collect(), a.into_iter().map(|(n, t)| (n, self.normalize_proj(t))).collect()),
            other => other,
        }
    }

    pub fn struct_fields(&self, id: AdtId) -> &[FieldDef] {
        match &self.adts[id].kind {
            AdtKind::Struct(f) => f,
            _ => &[],
        }
    }

    /// Whether a trait can be used as `dyn Trait`.
    pub fn dyn_compatible(&self, tid: TraitId) -> Result<(), String> {
        for t in self.trait_closure(tid) {
            for (name, fid) in &self.traits[t].methods {
                let f = &self.fns[*fid];
                if let Err(why) = self.vtable_ok(*fid) {
                    // methods with a default body are simply left out of the vtable
                    if f.decl.body.is_none() {
                        return Err(format!("method `{name}` {why}"));
                    }
                }
            }
        }
        Ok(())
    }

    /// Whether a trait method can be called through a vtable.
    pub fn vtable_ok(&self, fid: FnId) -> Result<(), &'static str> {
        let f = &self.fns[fid];
        if !f.has_self {
            return Err("has no `self` receiver");
        }
        if f.generics.len() > f.n_outer {
            return Err("has its own type parameters");
        }
        if f.params.iter().skip(1).any(|(_, t)| mentions_param0(t)) || mentions_param0(&f.ret) {
            return Err("mentions `Self` outside the receiver");
        }
        Ok(())
    }
}

fn mentions_param0(t: &Ty) -> bool {
    match t {
        Ty::Param(0) => true,
        Ty::Proj(..) => false,
        Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(mentions_param0),
        Ty::Array(t) => mentions_param0(t),
        Ty::Fn(ps, r) => ps.iter().any(mentions_param0) || mentions_param0(r),
        Ty::Dyn(_, ts, a) => ts.iter().any(mentions_param0) || a.iter().any(|(_, t)| mentions_param0(t)),
        _ => false,
    }
}

fn attr_str(a: &ast::Attribute, i: usize) -> Option<String> {
    match a.args.get(i) {
        Some(ast::AttrArg::Str(s, _)) => Some(s.clone()),
        Some(ast::AttrArg::Ident(id)) => Some(id.name.clone()),
        None => None,
    }
}

fn target_matches(attrs: &[ast::Attribute], target: &str) -> bool {
    for a in attrs {
        if a.name.name == "target" {
            return a.args.iter().any(|arg| matches!(arg, ast::AttrArg::Ident(id) if id.name == target));
        }
    }
    true
}

struct PendingImpl {
    module: ModId,
    decl: ast::ImplDecl,
    span: Span,
    pkg: Pkg,
}

pub fn build(sources: Vec<ModSource>, target: &str) -> Result<Program, Vec<Diag>> {
    let mut errs: Vec<Diag> = Vec::new();
    let mut p = Program {
        modules: Vec::new(),
        adts: Vec::new(),
        traits: Vec::new(),
        impls: Vec::new(),
        fns: Vec::new(),
        consts: Vec::new(),
        aliases: Vec::new(),
        impls_by_head: HashMap::new(),
        prelude: 0,
        target: target.to_string(),
        warnings: Vec::new(),
        known: HashMap::new(),
    };
    // 1. modules
    for s in &sources {
        p.modules.push(ModuleInfo {
            path: s.path.clone(), pkg: s.pkg, source_file: s.source_file,
            items: HashMap::new(), imports: HashMap::new(),
        });
    }
    p.prelude = sources.iter().position(|s| s.pkg == Pkg::Prelude).unwrap_or(0);
    {
        let pm = &mut p.modules[p.prelude];
        use IntTy::*;
        let builtins: Vec<(&str, Ty)> = vec![
            ("Int", Ty::Int(I32)),
            ("I8", Ty::Int(I8)),
            ("I16", Ty::Int(I16)),
            ("I32", Ty::Int(I32)),
            ("I64", Ty::Int(I64)),
            ("U8", Ty::Int(U8)),
            ("U16", Ty::Int(U16)),
            ("U32", Ty::Int(U32)),
            ("U64", Ty::Int(U64)),
            ("Float", Ty::Float(FloatTy::F64)),
            ("F32", Ty::Float(FloatTy::F32)),
            ("F64", Ty::Float(FloatTy::F64)),
            ("Bool", Ty::Bool),
            ("Char", Ty::Char),
            ("Str", Ty::Str),
            ("Array", Ty::Array(Box::new(Ty::Error))),
            ("Never", Ty::Never),
        ];
        for (n, t) in builtins {
            pm.items.insert(n.to_string(), (Def::Builtin(t), true));
        }
    }

    // 2. register items
    let mut pending_impls: Vec<PendingImpl> = Vec::new();
    let mut fn_items: Vec<(ModId, ast::Item)> = Vec::new();
    let mut adt_items: Vec<(AdtId, ast::Item)> = Vec::new();
    let mut trait_items: Vec<(TraitId, ast::Item)> = Vec::new();
    for (mid, s) in sources.iter().enumerate() {
        if let Some(file) = s.source_file {
            let path = s.path.strip_prefix(&format!("{}.", s.prefix)).unwrap_or(&s.path);
            for name in path.split('.') {
                p.warnings.extend(Naming::Snake.warning(&ast::Ident {
                    name: name.into(), span: Span::new(file, 0, 0),
                }));
            }
        }
        for item in &s.ast.items {
            if !target_matches(&item.attrs, target) {
                continue;
            }
            if s.source_file == Some(item.span.file) {
                item_names(item, &mut p.warnings);
            }
            let is_pub = item.vis != ast::Vis::Private;
            let register = |p: &mut Program, name: &ast::Ident, def: Def, errs: &mut Vec<Diag>| {
                if p.modules[mid].items.contains_key(&name.name) && s.pkg != Pkg::Prelude {
                    errs.push(Diag::new(name.span, format!("`{}` is defined more than once in this module", name.name)));
                }
                p.modules[mid].items.insert(name.name.clone(), (def, is_pub));
            };
            match &item.kind {
                ast::ItemKind::Struct(sd) => {
                    let id = p.adts.len();
                    p.adts.push(AdtDef { name: sd.name.name.clone(), module: mid, generics: generic_names(&sd.generics), kind: AdtKind::Struct(Vec::new()), span: sd.name.span, pkg: s.pkg });
                    register(&mut p, &sd.name, Def::Adt(id), &mut errs);
                    adt_items.push((id, item.clone()));
                }
                ast::ItemKind::Enum(ed) => {
                    let id = p.adts.len();
                    p.adts.push(AdtDef { name: ed.name.name.clone(), module: mid, generics: generic_names(&ed.generics), kind: AdtKind::Enum(Vec::new()), span: ed.name.span, pkg: s.pkg });
                    register(&mut p, &ed.name, Def::Adt(id), &mut errs);
                    adt_items.push((id, item.clone()));
                }
                ast::ItemKind::Trait(td) => {
                    let id = p.traits.len();
                    p.traits.push(TraitDef {
                        name: td.name.name.clone(),
                        module: mid,
                        generics: generic_names(&td.generics),
                        supertraits: Vec::new(),
                        assoc: td.assoc_types.iter().map(|a| a.name.clone()).collect(),
                        methods: Vec::new(),
                        span: td.name.span,
                        pkg: s.pkg,
                    });
                    register(&mut p, &td.name, Def::Trait(id), &mut errs);
                    trait_items.push((id, item.clone()));
                }
                ast::ItemKind::Fn(fd) => {
                    let id = p.fns.len();
                    // placeholder; signature resolved later
                    p.fns.push(placeholder_fn(fd, mid, s.pkg));
                    register(&mut p, &fd.name, Def::Fn(id), &mut errs);
                    fn_items.push((mid, item.clone()));
                    let _ = id;
                }
                ast::ItemKind::Const { name, value, ty } => {
                    let id = p.consts.len();
                    p.consts.push(ConstDef { name: name.name.clone(), module: mid, ty: Ty::Error, ty_expr: ty.clone(), value: value.clone(), span: name.span });
                    register(&mut p, name, Def::Const(id), &mut errs);
                }
                ast::ItemKind::TypeAlias { name, generics, ty } => {
                    let id = p.aliases.len();
                    p.aliases.push(AliasDef { name: name.name.clone(), module: mid, generics: generics.iter().map(|g| g.name.name.clone()).collect(), ty: ty.clone(), resolved: None });
                    register(&mut p, name, Def::Alias(id), &mut errs);
                }
                ast::ItemKind::Impl(id) => pending_impls.push(PendingImpl { module: mid, decl: id.clone(), span: item.span, pkg: s.pkg }),
                ast::ItemKind::Test { name, body } => {
                    let fd = Arc::new(ast::FnDecl {
                        name: ast::Ident { name: format!("$test{}", p.fns.len()), span: item.span },
                        is_async: false,
                        generics: Vec::new(),
                        has_self: false,
                        params: Vec::new(),
                        ret: None,
                        body: Some(body.clone()),
                        attrs: Vec::new(),
                        is_pub: false,
                        span: item.span,
                    });
                    let mut f = placeholder_fn(&fd, mid, s.pkg);
                    f.test_name = Some(name.clone());
                    f.ret = Ty::Unit;
                    p.fns.push(f);
                }
            }
        }
    }
    // prelude variants
    for (name, adt, idx) in [("Some", "Option", 0usize), ("None", "Option", 1), ("Ok", "Result", 0), ("Err", "Result", 1)] {
        if let Some((Def::Adt(id), _)) = p.modules[p.prelude].items.get(adt).cloned() {
            p.modules[p.prelude].items.insert(name.to_string(), (Def::Variant(id, idx), true));
        }
    }
    for name in [
        "Option", "Result", "List", "Map", "Set", "Ordering", "Range", "ListView", "MapView", "SetView", "AnyErr", "StrIndex", "Show", "Eq", "Ord", "Hash", "From",
        "Error", "Add", "Sub", "Mul", "Div", "Rem", "Neg", "Not", "Index", "Transfer", "Iterator", "Future", "__list_oob",
    ] {
        if let Some((d, _)) = p.modules[p.prelude].items.get(name).cloned() {
            p.known.insert(name, d);
        }
    }

    // 3. imports
    for (mid, s) in sources.iter().enumerate() {
        for imp in &s.ast.imports {
            let wit_path;
            let path: Vec<&str> = if let Some(w) = &imp.wit {
                let Some(mp) = crate::wit::module_path_for_name(w) else {
                    errs.push(Diag::new(imp.span, format!("invalid WIT import `{w}`; expected `namespace:package/interface`")));
                    continue;
                };
                if !p.modules.iter().any(|m| m.path == mp) {
                    let note = if target == "browser" { "WIT interfaces are imported on the `wasi` and `plugin` targets, which build components" } else { "the interface must be part of the bundled WASI 0.3 packages or of the package's wit/ directory" };
                    errs.push(Diag::new(imp.span, format!("cannot find WIT interface `{w}`")).note(note));
                    continue;
                }
                wit_path = mp;
                wit_path.split('.').collect()
            } else {
                imp.path.iter().map(|i| i.name.as_str()).collect()
            };
            let full = path.join(".");
            if (full.starts_with("std.") || full == "std") && !full.starts_with("std.__") {
                match std_available(&full, target) {
                    None => {
                        errs.push(Diag::new(imp.span, format!("standard library module `{full}` is not available in this implementation")));
                        continue;
                    }
                    Some(false) => {
                        let need = match full.as_str() {
                            "std.time" => Some("wasi:clocks/monotonic-clock and wasi:clocks/system-clock"),
                            "std.random" => Some("wasi:random/random"),
                            "std.http" => Some("wasi:http/types and wasi:http/client"),
                            "std.worker" => Some("puddi:runtime/workers and puddi:runtime/port"),
                            _ => None,
                        };
                        let mut d = Diag::new(imp.span, format!("`{full}` is not available on target `{target}`"));
                        if let (Some(n), "plugin") = (need, target) {
                            d = d.note(&format!("a plugin gets this module when its world imports {n}"));
                        }
                        errs.push(d);
                        continue;
                    }
                    Some(true) => {}
                }
            }
            let own = if s.prefix.is_empty() { full.clone() } else { format!("{}.{full}", s.prefix) };
            let mut target_mod = p.modules.iter().position(|m| m.path == own && m.pkg == s.pkg);
            if target_mod.is_none() && full.starts_with("std") {
                target_mod = p.modules.iter().position(|m| m.path == full && m.pkg == Pkg::Std);
            }
            if target_mod.is_none() {
                if let Some(pre) = s.aliases.get(path[0]) {
                    let mut dep_path = pre.clone();
                    let rest = &path[1..];
                    if rest.is_empty() {
                        dep_path.push_str(".lib");
                    }
                    for r in rest {
                        dep_path.push('.');
                        dep_path.push_str(r);
                    }
                    target_mod = p.modules.iter().position(|m| m.path == dep_path && matches!(m.pkg, Pkg::Dep(_)));
                }
            }
            let Some(tm) = target_mod else {
                let note = if s.aliases.is_empty() { "modules are files under src/, and dependencies are listed under [deps] in pud.toml" } else { "modules are files under src/; dependencies are imported by their name in [deps]" };
                errs.push(Diag::new(imp.span, format!("cannot find module `{full}`")).note(note));
                continue;
            };
            if let Some(names) = &imp.names {
                for n in names {
                    match p.module_member(tm, &n.name, mid, n.span) {
                        Ok(d) => {
                            p.modules[mid].imports.insert(n.name.clone(), (d, n.span));
                        }
                        Err(e) => errs.push(e),
                    }
                }
            } else {
                let bind = imp.alias.as_ref().map(|a| a.name.clone()).unwrap_or_else(|| path.last().unwrap().to_string());
                p.modules[mid].imports.insert(bind, (Def::Module(tm), imp.span));
            }
        }
    }

    // 4. Aliases only need declaration names and generic arity.
    p.resolve_aliases(&mut errs);

    // 5. Resolve ADT bounds and fields.
    for (id, item) in &adt_items {
        let gens = match &item.kind {
            ast::ItemKind::Struct(sd) => &sd.generics,
            ast::ItemKind::Enum(ed) => &ed.generics,
            _ => unreachable!(),
        };
        let names: Vec<String> = gens.iter().map(|g| g.name.name.clone()).collect();
        let cx = TyCx { module: p.adts[*id].module, generics: &names, self_ty: None, self_impl: None };
        let mut gdefs = Vec::new();
        for g in gens {
            let mut bounds = Vec::new();
            for b in &g.bounds {
                match p.resolve_trait_ref(&cx, b) {
                    Ok(tr) => bounds.push(tr),
                    Err(e) => errs.push(e),
                }
            }
            gdefs.push(GenericDef { name: g.name.name.clone(), bounds });
        }
        p.adts[*id].generics = gdefs;
    }
    for (id, item) in &adt_items {
        let names: Vec<String> = p.adts[*id].generics.iter().map(|g| g.name.clone()).collect();
        let self_ty = Ty::Adt(*id, (0..names.len() as u32).map(Ty::Param).collect());
        let cx = TyCx { module: p.adts[*id].module, generics: &names, self_ty: Some(self_ty), self_impl: None };
        let resolve_fields = |p: &Program, fields: &[ast::Field], errs: &mut Vec<Diag>| -> Vec<FieldDef> {
            let mut out: Vec<FieldDef> = Vec::new();
            for f in fields {
                if out.iter().any(|o| o.name == f.name.name) {
                    errs.push(Diag::new(f.name.span, format!("field `{}` is declared more than once", f.name.name)));
                }
                let ty = p.resolve_ty(&cx, &f.ty).unwrap_or_else(|e| {
                    errs.push(e);
                    Ty::Error
                });
                out.push(FieldDef { name: f.name.name.clone(), ty, mutable: f.mutable, public: f.public });
            }
            out
        };
        match &item.kind {
            ast::ItemKind::Struct(sd) => {
                let fs = resolve_fields(&p, &sd.fields, &mut errs);
                p.adts[*id].kind = AdtKind::Struct(fs);
            }
            ast::ItemKind::Enum(ed) => {
                let mut vs: Vec<VariantDef> = Vec::new();
                for v in &ed.variants {
                    if vs.iter().any(|o| o.name == v.name.name) {
                        errs.push(Diag::new(v.name.span, format!("variant `{}` is declared more than once", v.name.name)));
                    }
                    let (fields, shape) = match &v.kind {
                        ast::VariantKind::Unit => (Vec::new(), Shape::Unit),
                        ast::VariantKind::Tuple(ts) => (
                            ts.iter()
                                .enumerate()
                                .map(|(i, t)| FieldDef {
                                    name: i.to_string(),
                                    ty: p.resolve_ty(&cx, t).unwrap_or_else(|e| {
                                        errs.push(e);
                                        Ty::Error
                                    }),
                                    mutable: false,
                                    public: true,
                                })
                                .collect(),
                            Shape::Tuple,
                        ),
                        ast::VariantKind::Record(fs) => {
                            let mut fs = resolve_fields(&p, fs, &mut errs);
                            for f in &mut fs {
                                f.public = true;
                                if f.mutable {
                                    errs.push(Diag::new(v.name.span, "enum variant fields cannot be `var`"));
                                }
                            }
                            (fs, Shape::Record)
                        }
                    };
                    vs.push(VariantDef { name: v.name.name.clone(), fields, shape });
                }
                p.adts[*id].kind = AdtKind::Enum(vs);
            }
            _ => {}
        }
    }

    // 6. traits
    for (tid, item) in &trait_items {
        let ast::ItemKind::Trait(td) = &item.kind else { unreachable!() };
        let mut names = vec!["Self".to_string()];
        names.extend(td.generics.iter().map(|g| g.name.name.clone()));
        let cx = TyCx { module: p.traits[*tid].module, generics: &names, self_ty: Some(Ty::Param(0)), self_impl: None };
        let mut gdefs = Vec::new();
        for g in &td.generics {
            let mut bounds = Vec::new();
            for b in &g.bounds {
                match p.resolve_trait_ref(&cx, b) {
                    Ok(tr) => bounds.push(tr),
                    Err(e) => errs.push(e),
                }
            }
            gdefs.push(GenericDef { name: g.name.name.clone(), bounds });
        }
        let mut sups = Vec::new();
        for s in &td.supertraits {
            match p.resolve_trait_ref(&cx, s) {
                Ok(tr) => sups.push(tr),
                Err(e) => errs.push(e),
            }
        }
        p.traits[*tid].generics = gdefs;
        p.traits[*tid].supertraits = sups;
    }
    for (tid, _) in &trait_items {
        let td = &p.traits[*tid];
        if td.supertraits.iter().any(|sup| p.trait_has_super(sup.trait_id, *tid)) {
            errs.push(Diag::new(td.span, format!("cyclic supertraits for `{}`", td.name)));
        }
    }
    for (tid, item) in &trait_items {
        let ast::ItemKind::Trait(td) = &item.kind else { unreachable!() };
        let mut outer = vec![GenericDef { name: "Self".into(), bounds: vec![TraitRef { trait_id: *tid, args: (1..=td.generics.len() as u32).map(Ty::Param).collect() }] }];
        outer.extend(p.traits[*tid].generics.clone());
        let mut methods = Vec::new();
        for m in &td.methods {
            let fid = p.fns.len();
            match resolve_fn(&p, m, p.traits[*tid].module, &outer, Some(Ty::Param(0)), FnOwner::Trait(*tid), true, p.traits[*tid].pkg) {
                Ok(f) => p.fns.push(f),
                Err(e) => {
                    errs.push(e);
                    p.fns.push(placeholder_fn(m, p.traits[*tid].module, p.traits[*tid].pkg));
                }
            }
            methods.push((m.name.name.clone(), fid));
        }
        p.traits[*tid].methods = methods;
    }

    // 7. free functions
    {
        let mut fid = 0;
        for (mid, item) in &fn_items {
            // find the placeholder id registered earlier
            let ast::ItemKind::Fn(fd) = &item.kind else { unreachable!() };
            while fid < p.fns.len() && !(p.fns[fid].module == *mid && p.fns[fid].name == fd.name.name && p.fns[fid].span == fd.span && p.fns[fid].test_name.is_none()) {
                fid += 1;
            }
            if fid >= p.fns.len() {
                break;
            }
            let pkg = p.fns[fid].pkg;
            match resolve_fn(&p, fd, *mid, &[], None, FnOwner::Free, item.vis != ast::Vis::Private, pkg) {
                Ok(mut f) => {
                    if item.vis == ast::Vis::Export && f.export.is_none() {
                        f.export = Some(fd.name.name.clone());
                    }
                    p.fns[fid] = f;
                }
                Err(e) => errs.push(e),
            }
            fid += 1;
        }
    }

    // 8. impls
    for pi in pending_impls {
        let names: Vec<String> = pi.decl.generics.iter().map(|g| g.name.name.clone()).collect();
        let cx0 = TyCx { module: pi.module, generics: &names, self_ty: None, self_impl: None };
        let self_ty = match p.resolve_ty(&cx0, &pi.decl.self_ty) {
            Ok(t) => t,
            Err(e) => {
                errs.push(e);
                continue;
            }
        };
        let cx = TyCx { module: pi.module, generics: &names, self_ty: Some(self_ty.clone()), self_impl: None };
        let mut gdefs = Vec::new();
        for g in &pi.decl.generics {
            let mut bounds = Vec::new();
            for b in &g.bounds {
                match p.resolve_trait_ref(&cx, b) {
                    Ok(tr) => bounds.push(tr),
                    Err(e) => errs.push(e),
                }
            }
            gdefs.push(GenericDef { name: g.name.name.clone(), bounds });
        }
        let trait_ref = match &pi.decl.trait_ref {
            Some(t) => match p.resolve_trait_ref(&cx, t) {
                Ok(tr) => Some(tr),
                Err(e) => {
                    errs.push(e);
                    continue;
                }
            },
            None => None,
        };
        // orphan rule
        if pi.pkg.is_source() {
            match &trait_ref {
                Some(tr) => {
                    let trait_local = p.traits[tr.trait_id].pkg == pi.pkg;
                    let type_local = matches!(&self_ty, Ty::Adt(id, _) if p.adts[*id].pkg == pi.pkg);
                    if !trait_local && !type_local {
                        errs.push(Diag::new(pi.span, format!("cannot implement `{}` for `{}`: either the trait or the type must be defined in this package", p.trait_ref_str(tr), p.ty_str_p(&self_ty, &names))));
                        continue;
                    }
                }
                None => {
                    let type_local = matches!(&self_ty, Ty::Adt(id, _) if p.adts[*id].pkg == pi.pkg);
                    if !type_local {
                        errs.push(Diag::new(pi.span, format!("inherent impls are only allowed for types defined in this package, not `{}`", p.ty_str_p(&self_ty, &names))));
                        continue;
                    }
                }
            }
        }
        let iid = p.impls.len();
        let mut assoc = HashMap::new();
        for (n, t) in &pi.decl.assoc_types {
            match p.resolve_ty(&cx, t) {
                Ok(t) => {
                    assoc.insert(n.name.clone(), t);
                }
                Err(e) => errs.push(e),
            }
        }
        p.impls.push(ImplDef { module: pi.module, generics: gdefs.clone(), trait_ref: trait_ref.clone(), self_ty: self_ty.clone(), methods: HashMap::new(), assoc, span: pi.span, pkg: pi.pkg });
        let mut methods = HashMap::new();
        for m in &pi.decl.methods {
            let fid = p.fns.len();
            let is_pub = m.is_pub || trait_ref.is_some();
            match resolve_fn(&p, m, pi.module, &gdefs, Some(self_ty.clone()), FnOwner::Impl(iid), is_pub, pi.pkg) {
                Ok(f) => p.fns.push(f),
                Err(e) => {
                    errs.push(e);
                    p.fns.push(placeholder_fn(m, pi.module, pi.pkg));
                }
            }
            if methods.insert(m.name.name.clone(), fid).is_some() {
                errs.push(Diag::new(m.name.span, format!("method `{}` is defined more than once in this impl", m.name.name)));
            }
        }
        p.impls[iid].methods = methods;
        let h = head_of(&self_ty).unwrap_or(Head::Any);
        p.impls_by_head.entry(h).or_default().push(iid);
    }

    // 9. trait impl completeness and signature checks
    for iid in 0..p.impls.len() {
        let Some(tr) = p.impls[iid].trait_ref.clone() else { continue };
        let td = &p.traits[tr.trait_id];
        let imp = &p.impls[iid];
        let candidates = if matches!(head_of(&imp.self_ty), None | Some(Head::Any)) {
            (0..iid).collect()
        } else {
            p.candidate_impls(&imp.self_ty)
        };
        if candidates.into_iter().any(|other| other < iid && p.impls_overlap(imp, &p.impls[other])) {
            let names: Vec<_> = imp.generics.iter().map(|g| g.name.clone()).collect();
            errs.push(Diag::new(imp.span, format!("overlapping implementations of `{}` for `{}`",
                p.trait_ref_str(&tr), p.ty_str_p(&imp.self_ty, &names))));
        }
        for a in &td.assoc {
            if !imp.assoc.contains_key(a) {
                errs.push(Diag::new(imp.span, format!("missing associated type `{a}` in impl of `{}`", td.name)));
            }
        }
        for (name, _) in &imp.methods {
            if !td.methods.iter().any(|(n, _)| n == name) {
                let f = &p.fns[imp.methods[name]];
                errs.push(Diag::new(f.decl.name.span, format!("method `{name}` is not a member of trait `{}`", td.name)));
            }
        }
        for (name, tfid) in &td.methods {
            let tf = &p.fns[*tfid];
            match imp.methods.get(name) {
                None => {
                    if tf.decl.body.is_none() {
                        errs.push(Diag::new(imp.span, format!("missing method `{name}` in impl of `{}` for `{}`", td.name, p.ty_str(&imp.self_ty))));
                    }
                }
                Some(ifid) => {
                    let f = &p.fns[*ifid];
                    if f.has_self != tf.has_self || f.params.len() != tf.params.len() {
                        errs.push(Diag::new(f.decl.name.span, format!("method `{name}` has a different signature than in trait `{}`", td.name)));
                        continue;
                    }
                    // compare types: map trait params to impl context
                    let n_impl = imp.generics.len();
                    let n_trait_outer = tf.n_outer;
                    let mut map: Vec<Ty> = vec![imp.self_ty.clone()];
                    map.extend(tr.args.iter().cloned());
                    while map.len() < n_trait_outer {
                        map.push(Ty::Error);
                    }
                    for j in 0..(tf.generics.len() - n_trait_outer) {
                        map.push(Ty::Param((n_impl + j) as u32));
                    }
                    let norm = |t: &Ty| -> Ty { resolve_self_proj(&p, t, iid) };
                    for (k, ((_, pt), (_, it))) in tf.params.iter().zip(&f.params).enumerate() {
                        let want = norm(&pt.subst(&map));
                        if want != norm(it) {
                            let gnames: Vec<String> = f.generics.iter().map(|g| g.name.clone()).collect();
                            errs.push(Diag::new(f.decl.params[k].ty.span(), format!("parameter type mismatch with trait `{}`: expected `{}`, found `{}`", td.name, p.ty_str_p(&want, &gnames), p.ty_str_p(it, &gnames))));
                        }
                    }
                    let want = norm(&tf.ret.subst(&map));
                    if want != norm(&f.ret) {
                        let gnames: Vec<String> = f.generics.iter().map(|g| g.name.clone()).collect();
                        errs.push(Diag::new(f.decl.name.span, format!("return type mismatch with trait `{}`: expected `{}`, found `{}`", td.name, p.ty_str_p(&want, &gnames), p.ty_str_p(&f.ret, &gnames))));
                    }
                }
            }
        }
        // supertrait impls must exist (checked lazily for generic impls)
        if imp.generics.is_empty() {
            for s in &td.supertraits {
                let st = TraitRef { trait_id: s.trait_id, args: s.args.iter().map(|a| a.subst(&{
                    let mut m = vec![imp.self_ty.clone()];
                    m.extend(tr.args.iter().cloned());
                    m
                })).collect() };
                if !p.implements(&imp.self_ty, &st, 0) {
                    errs.push(Diag::new(imp.span, format!("`{}` must also implement supertrait `{}`", p.ty_str(&imp.self_ty), p.trait_ref_str(&st))));
                }
            }
        }
    }

    // 10. consts
    for i in 0..p.consts.len() {
        let cx = TyCx { module: p.consts[i].module, generics: &[], self_ty: None, self_impl: None };
        match p.resolve_ty(&cx, &p.consts[i].ty_expr.clone()) {
            Ok(t) => p.consts[i].ty = t,
            Err(e) => errs.push(e),
        }
    }

    if errs.is_empty() { Ok(p) } else { Err(errs) }
}

fn resolve_self_proj(p: &Program, t: &Ty, iid: ImplId) -> Ty {
    let imp = &p.impls[iid];
    match t {
        Ty::Proj(base, name) if **base == imp.self_ty || **base == Ty::Param(0) => imp.assoc.get(name).cloned().unwrap_or(Ty::Error),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| resolve_self_proj(p, t, iid)).collect()),
        Ty::Adt(id, ts) => Ty::Adt(*id, ts.iter().map(|t| resolve_self_proj(p, t, iid)).collect()),
        Ty::Array(t) => Ty::Array(Box::new(resolve_self_proj(p, t, iid))),
        Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(|t| resolve_self_proj(p, t, iid)).collect(), Box::new(resolve_self_proj(p, r, iid))),
        other => other.clone(),
    }
}

fn placeholder_fn(fd: &Arc<ast::FnDecl>, module: ModId, pkg: Pkg) -> FnDef {
    FnDef {
        name: fd.name.name.clone(),
        module,
        generics: Vec::new(),
        n_outer: 0,
        params: Vec::new(),
        has_self: fd.has_self,
        self_ty: None,
        ret: Ty::Error,
        decl: fd.clone(),
        owner: FnOwner::Free,
        is_pub: fd.is_pub,
        span: fd.span,
        intrinsic: None,
        extern_: None,
        export: None,
        deprecated: None,
        test_name: None,
        pkg,
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_fn(p: &Program, fd: &Arc<ast::FnDecl>, module: ModId, outer: &[GenericDef], self_ty: Option<Ty>, owner: FnOwner, is_pub: bool, pkg: Pkg) -> Result<FnDef, Diag> {
    let mut names: Vec<String> = outer.iter().map(|g| g.name.clone()).collect();
    for g in &fd.generics {
        if names.contains(&g.name.name) {
            return Err(Diag::new(g.name.span, format!("type parameter `{}` shadows an outer type parameter", g.name.name)));
        }
        names.push(g.name.name.clone());
    }
    let cx = TyCx { module, generics: &names, self_ty: self_ty.clone(), self_impl: owner.impl_id() };
    let mut generics: Vec<GenericDef> = outer.to_vec();
    for g in &fd.generics {
        let mut bounds = Vec::new();
        for b in &g.bounds {
            bounds.push(p.resolve_trait_ref(&cx, b)?);
        }
        generics.push(GenericDef { name: g.name.name.clone(), bounds });
    }
    let mut params = Vec::new();
    if fd.has_self {
        let Some(st) = &self_ty else {
            return Err(Diag::new(fd.name.span, "`self` parameter is only allowed in methods"));
        };
        params.push(("self".to_string(), st.clone()));
    }
    for prm in &fd.params {
        params.push((prm.name.name.clone(), p.resolve_ty(&cx, &prm.ty)?));
    }
    let mut ret = match &fd.ret {
        Some(t) => p.resolve_ty(&cx, t)?,
        None => Ty::Unit,
    };
    if fd.is_async {
        ret = p.future_ty(ret);
    }
    let mut intrinsic = None;
    let mut extern_ = None;
    let mut export = None;
    let mut deprecated = None;
    for a in &fd.attrs {
        match a.name.name.as_str() {
            "intrinsic" => intrinsic = Some(attr_str(a, 0).unwrap_or_else(|| fd.name.name.clone())),
            "extern" => {
                let m = attr_str(a, 0).ok_or_else(|| Diag::new(a.span, "`@extern` needs a module name and a function name"))?;
                let n = attr_str(a, 1).ok_or_else(|| Diag::new(a.span, "`@extern` needs a module name and a function name"))?;
                extern_ = Some((m, n));
            }
            "export" => export = Some(attr_str(a, 0).unwrap_or_else(|| fd.name.name.clone())),
            "deprecated" => deprecated = Some(attr_str(a, 0).unwrap_or_default()),
            "target" | "derive" => {}
            other => return Err(Diag::new(a.name.span, format!("unknown attribute `@{other}`"))),
        }
    }
    if fd.body.is_none() && intrinsic.is_none() && extern_.is_none() && !matches!(owner, FnOwner::Trait(_)) {
        return Err(Diag::new(fd.name.span, format!("function `{}` has no body", fd.name.name)));
    }
    if fd.body.is_some() && extern_.is_some() {
        return Err(Diag::new(fd.name.span, "`@extern` functions cannot have a body"));
    }
    if extern_.is_some() || export.is_some() {
        for (n, t) in &params {
            if !(t.is_numeric() || matches!(t, Ty::Bool | Ty::Char) || (extern_.is_some() && *t == Ty::Str)) {
                return Err(Diag::new(fd.name.span, format!("parameter `{n}` of type `{}` cannot cross the raw WebAssembly boundary", p.ty_str_p(t, &names))));
            }
        }
        if !(ret.is_numeric() || matches!(ret, Ty::Bool | Ty::Char | Ty::Unit)) {
            return Err(Diag::new(fd.name.span, format!("return type `{}` cannot cross the raw WebAssembly boundary", p.ty_str_p(&ret, &names))));
        }
        if !fd.generics.is_empty() || self_ty.is_some() {
            return Err(Diag::new(fd.name.span, "raw imports and exports must be non-generic free functions"));
        }
    }
    Ok(FnDef {
        name: fd.name.name.clone(),
        module,
        n_outer: outer.len(),
        generics,
        params,
        has_self: fd.has_self,
        self_ty,
        ret,
        decl: fd.clone(),
        owner,
        is_pub,
        span: fd.span,
        intrinsic,
        extern_,
        export,
        deprecated,
        test_name: None,
        pkg,
    })
}
