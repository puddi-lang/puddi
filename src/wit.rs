//! Component Model support: loading WIT worlds, generating Puddi bindings
//! for imported interfaces (canonical ABI lowering and lifting written as
//! Puddi source), export wrappers, and component encoding.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::path::Path;

use wit_parser::abi::{AbiVariant, WasmType};
use wit_parser::{Function, FunctionKind, Handle, InterfaceId, Int, Resolve, SizeAlign, Type, TypeDefKind, TypeId, TypeOwner, WorldId, WorldItem, WorldKey};

/// WASI 0.3 packages bundled with the toolchain, in dependency order.
pub const WASI: &[(&str, &[(&str, &str)])] = &[
    (
        "clocks",
        &[
            ("monotonic-clock.wit", include_str!("../wit/wasi/clocks/monotonic-clock.wit")),
            ("system-clock.wit", include_str!("../wit/wasi/clocks/system-clock.wit")),
            ("timezone.wit", include_str!("../wit/wasi/clocks/timezone.wit")),
            ("types.wit", include_str!("../wit/wasi/clocks/types.wit")),
            ("world.wit", include_str!("../wit/wasi/clocks/world.wit")),
        ],
    ),
    (
        "random",
        &[
            ("insecure-seed.wit", include_str!("../wit/wasi/random/insecure-seed.wit")),
            ("insecure.wit", include_str!("../wit/wasi/random/insecure.wit")),
            ("random.wit", include_str!("../wit/wasi/random/random.wit")),
            ("world.wit", include_str!("../wit/wasi/random/world.wit")),
        ],
    ),
    (
        "filesystem",
        &[
            ("preopens.wit", include_str!("../wit/wasi/filesystem/preopens.wit")),
            ("types.wit", include_str!("../wit/wasi/filesystem/types.wit")),
            ("world.wit", include_str!("../wit/wasi/filesystem/world.wit")),
        ],
    ),
    (
        "sockets",
        &[
            ("ip-name-lookup.wit", include_str!("../wit/wasi/sockets/ip-name-lookup.wit")),
            ("types.wit", include_str!("../wit/wasi/sockets/types.wit")),
            ("world.wit", include_str!("../wit/wasi/sockets/world.wit")),
        ],
    ),
    (
        "cli",
        &[
            ("command.wit", include_str!("../wit/wasi/cli/command.wit")),
            ("environment.wit", include_str!("../wit/wasi/cli/environment.wit")),
            ("exit.wit", include_str!("../wit/wasi/cli/exit.wit")),
            ("imports.wit", include_str!("../wit/wasi/cli/imports.wit")),
            ("run.wit", include_str!("../wit/wasi/cli/run.wit")),
            ("stdio.wit", include_str!("../wit/wasi/cli/stdio.wit")),
            ("terminal.wit", include_str!("../wit/wasi/cli/terminal.wit")),
        ],
    ),
    ("http", &[("types.wit", include_str!("../wit/wasi/http/types.wit")), ("worlds.wit", include_str!("../wit/wasi/http/worlds.wit"))]),
    ("logging", &[("logging.wit", include_str!("../wit/wasi/logging/logging.wit"))]),
    ("puddi-runtime", &[("runtime.wit", include_str!("../wit/puddi/runtime.wit"))]),
];

const KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "dyn", "else", "enum", "export", "false", "fn", "for", "if", "impl", "import", "in", "let", "loop", "match", "pub", "return", "self", "Self", "struct", "test", "trait", "true", "type", "var", "while",
];

/// `kebab-case` to `snake_case`, escaping keywords with a trailing underscore.
pub fn snake(s: &str) -> String {
    let mut out = s.replace('-', "_");
    if KEYWORDS.contains(&out.as_str()) {
        out.push('_');
    }
    out
}

/// `kebab-case` to `PascalCase`.
pub fn pascal(s: &str) -> String {
    s.split('-').map(|w| {
        let mut c = w.chars();
        match c.next() {
            Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
            None => String::new(),
        }
    }).collect()
}

pub struct Wit {
    pub resolve: Resolve,
    pub world: WorldId,
    pub sizes: SizeAlign,
}

fn push_package(resolve: &mut Resolve, name: &str, files: &[(&str, &str)]) -> Result<wit_parser::PackageId, String> {
    let mut sm = wit_parser::SourceMap::new();
    for (f, text) in files {
        sm.push_str(&format!("<wasi>/{name}/{f}"), *text);
    }
    let group = sm.parse().map_err(|(_, e)| format!("{e}"))?;
    resolve.push_group(group).map_err(|e| format!("{e}"))
}

impl Wit {
    /// Load the bundled WASI packages and the package's own `wit/` directory.
    pub fn new(pkg_dir: Option<&Path>) -> Result<(Resolve, Option<wit_parser::PackageId>), String> {
        let mut resolve = Resolve::new();
        for (name, files) in WASI {
            push_package(&mut resolve, name, files).map_err(|e| format!("bundled WASI WIT failed to load: {e}"))?;
        }
        let mut own = None;
        if let Some(d) = pkg_dir {
            let wd = d.join("wit");
            if wd.is_dir() {
                let id = resolve.push_dir(&wd).map_err(|e| format!("cannot load {}: {e:#}", wd.display()))?;
                own = Some(id.0);
            }
        }
        Ok((resolve, own))
    }

    /// Find an interface named like `wasi:cli/stdout` (the highest version wins).
    pub fn find_interface(resolve: &Resolve, name: &str) -> Option<InterfaceId> {
        let (pkg, iface) = name.split_once('/')?;
        let (ns, pname) = pkg.split_once(':')?;
        let iface = iface.split('@').next()?;
        let mut best: Option<(Option<semver::Version>, InterfaceId)> = None;
        for (_, p) in resolve.packages.iter() {
            if p.name.namespace == ns && p.name.name == pname {
                if let Some(&id) = p.interfaces.get(iface) {
                    if best.as_ref().map(|(v, _)| p.name.version > *v).unwrap_or(true) {
                        best = Some((p.name.version.clone(), id));
                    }
                }
            }
        }
        best.map(|b| b.1)
    }

    /// Select the target world and add `extra` interface imports to it.
    pub fn load(pkg_dir: Option<&Path>, world_spec: &str, extra_names: &[String], extra_exports: &[String]) -> Result<Wit, String> {
        let (resolve, own) = Wit::new(pkg_dir)?;
        Wit::load_with(resolve, own, world_spec, extra_names, extra_exports)
    }

    /// `load` on packages already loaded by `Wit::new`.
    pub fn load_with(mut resolve: Resolve, own: Option<wit_parser::PackageId>, world_spec: &str, extra_names: &[String], extra_exports: &[String]) -> Result<Wit, String> {
        let base = Wit::select(&resolve, own, world_spec)?;
        let have: BTreeSet<InterfaceId> = resolve.worlds[base].imports.values().filter_map(|it| match it {
            WorldItem::Interface { id, .. } => Some(*id),
            _ => None,
        }).collect();
        let mut extra = Vec::new();
        for n in extra_names {
            let i = Wit::find_interface(&resolve, n).ok_or_else(|| format!("cannot find WIT interface `{n}`"))?;
            if !have.contains(&i) && !extra.contains(&i) {
                extra.push(i);
            }
        }
        let base_id = {
            let w = &resolve.worlds[base];
            let p = &resolve.packages[w.package.unwrap()];
            let v = p.name.version.as_ref().map(|v| format!("@{v}")).unwrap_or_default();
            format!("{}:{}/{}{v}", p.name.namespace, p.name.name, w.name)
        };
        let mut text = format!("package puddi:app;\n\nworld app {{\n  include {base_id};\n");
        for &i in &extra {
            if let Some(id) = resolve.id_of(i) {
                let _ = writeln!(text, "  import {id};");
            }
        }
        for n in extra_exports {
            let i = Wit::find_interface(&resolve, n).ok_or_else(|| format!("cannot find WIT interface `{n}`"))?;
            if let Some(id) = resolve.id_of(i) {
                let _ = writeln!(text, "  export {id};");
            }
        }
        text.push_str("}\n");
        let mut sm = wit_parser::SourceMap::new();
        sm.push_str("<puddi app world>", text);
        let group = sm.parse().map_err(|(_, e)| format!("{e}"))?;
        let pkg = resolve.push_group(group).map_err(|e| format!("{e}"))?;
        let world = resolve.select_world(&[pkg], Some("app")).map_err(|e| format!("{e:#}"))?;
        let mut sizes = SizeAlign::default();
        sizes.fill(&resolve).map_err(|e| format!("{e:#}"))?;
        Ok(Wit { resolve, world, sizes })
    }

    fn select(resolve: &Resolve, own: Option<wit_parser::PackageId>, spec: &str) -> Result<WorldId, String> {
        if let Some((_, world)) = spec.split_once('#') {
            let pkgs: Vec<_> = own.into_iter().collect();
            if pkgs.is_empty() {
                return Err(format!("world `{spec}` needs a wit/ directory in the package"));
            }
            return resolve.select_world(&pkgs, Some(world)).map_err(|e| format!("cannot find world `{spec}`: {e:#}"));
        }
        let (pkg, wname) = spec.split_once('/').ok_or_else(|| format!("invalid world `{spec}`; expected `namespace:package/world` or `wit/file.wit#world`"))?;
        let (ns, pname) = pkg.split_once(':').ok_or_else(|| format!("invalid world `{spec}`"))?;
        let wname = wname.split('@').next().unwrap();
        let mut best: Option<(Option<semver::Version>, WorldId)> = None;
        for (_, p) in resolve.packages.iter() {
            if p.name.namespace == ns && p.name.name == pname {
                if let Some(&id) = p.worlds.get(wname) {
                    if best.as_ref().map(|(v, _)| p.name.version > *v).unwrap_or(true) {
                        best = Some((p.name.version.clone(), id));
                    }
                }
            }
        }
        best.map(|b| b.1).ok_or_else(|| format!("cannot find world `{spec}`"))
    }

    /// Interfaces imported by the world.
    pub fn imported_interfaces(&self) -> BTreeSet<InterfaceId> {
        self.resolve.worlds[self.world].imports.iter().filter_map(|(_, it)| match it {
            WorldItem::Interface { id, .. } => Some(*id),
            _ => None,
        }).collect()
    }

    pub fn interface_name(&self, i: InterfaceId) -> String {
        self.resolve.id_of(i).unwrap_or_else(|| "<anonymous interface>".into())
    }

    /// Encode a core module as a component of the target world.
    pub fn encode(&self, core: &[u8]) -> Result<Vec<u8>, String> {
        let mut module = core.to_vec();
        wit_component::embed_component_metadata(&mut module, &self.resolve, self.world, wit_component::StringEncoding::UTF8, false).map_err(|e| format!("{e:#}"))?;
        let mut enc = wit_component::ComponentEncoder::default();
        enc.module(&module).map_err(|e| format!("{e:#}"))?;
        enc.validate(true);
        enc.encode().map_err(|e| format!("{e:#}"))
    }
}

/// Module path of the generated bindings for an interface.
pub fn module_path(resolve: &Resolve, i: InterfaceId) -> String {
    let iface = &resolve.interfaces[i];
    let p = &resolve.packages[iface.package.unwrap()];
    format!("std.__wit.{}.{}.{}", snake(&p.name.namespace), snake(&p.name.name), snake(iface.name.as_deref().unwrap_or("anon")))
}

/// Puddi module path for a WIT import written as `ns:pkg/iface`.
pub fn module_path_for_name(name: &str) -> Option<String> {
    let (pkg, iface) = name.split_once('/')?;
    let (ns, pname) = pkg.split_once(':')?;
    let iface = iface.split('@').next()?;
    Some(format!("std.__wit.{}.{}.{}", snake(ns), snake(pname), snake(iface)))
}

fn wt(t: WasmType) -> &'static str {
    match t {
        WasmType::I32 | WasmType::Pointer | WasmType::Length => "I32",
        WasmType::I64 | WasmType::PointerOrI64 => "I64",
        WasmType::F32 => "F32",
        WasmType::F64 => "Float",
    }
}

fn norm(t: WasmType) -> WasmType {
    match t {
        WasmType::Pointer | WasmType::Length => WasmType::I32,
        WasmType::PointerOrI64 => WasmType::I64,
        t => t,
    }
}

/// Generates Puddi source with canonical ABI glue.
pub struct Gen<'a> {
    pub w: &'a Wit,
    /// Interface the generated code lives in (None for export wrappers).
    pub home: Option<InterfaceId>,
    pub imports: BTreeMap<InterfaceId, String>,
    buf: Vec<String>,
    tmp: usize,
    /// The exported Puddi function is async: await its future.
    pub await_call: bool,
}

impl<'a> Gen<'a> {
    pub fn new(w: &'a Wit, home: Option<InterfaceId>) -> Gen<'a> {
        Gen { w, home, imports: BTreeMap::new(), buf: Vec::new(), tmp: 0, await_call: false }
    }

    fn r(&self) -> &'a Resolve {
        &self.w.resolve
    }

    fn t(&mut self) -> String {
        self.tmp += 1;
        format!("__t{}", self.tmp)
    }

    fn emit(&mut self, s: String) {
        self.buf.push(s);
    }

    fn bind(&mut self, ty: &str, e: String) -> String {
        let t = self.t();
        self.emit(format!("let {t}: {ty} = {e}"));
        t
    }

    fn bindt(&mut self, t: &Type, e: String) -> String {
        let ty = self.ty(t);
        self.bind(&ty, e)
    }

    fn block(&mut self, f: impl FnOnce(&mut Self) -> String) -> String {
        let saved = std::mem::take(&mut self.buf);
        let e = f(self);
        let inner = std::mem::replace(&mut self.buf, saved);
        if inner.is_empty() { format!("{{ {e} }}") } else { format!("{{\n{}\n{e}\n}}", inner.join("\n")) }
    }

    pub fn alias_for(&mut self, i: InterfaceId) -> String {
        if let Some(a) = self.imports.get(&i) {
            return a.clone();
        }
        let p = module_path(self.r(), i);
        let a = format!("__w_{}", p.trim_start_matches("std.__wit.").replace('.', "_"));
        self.imports.insert(i, a.clone());
        a
    }

    /// Name of a named type as seen from the home module.
    pub fn named(&mut self, id: TypeId) -> String {
        let td = &self.r().types[id];
        let n = pascal(td.name.as_deref().unwrap_or("Anon"));
        match td.owner {
            TypeOwner::Interface(i) if Some(i) != self.home => format!("{}.{n}", self.alias_for(i)),
            _ => n,
        }
    }

    /// The Puddi type for a WIT type.
    pub fn ty(&mut self, t: &Type) -> String {
        match t {
            Type::Bool => "Bool".into(),
            Type::U8 => "U8".into(),
            Type::U16 => "U16".into(),
            Type::U32 => "U32".into(),
            Type::U64 => "U64".into(),
            Type::S8 => "I8".into(),
            Type::S16 => "I16".into(),
            Type::S32 => "I32".into(),
            Type::S64 => "I64".into(),
            Type::F32 => "F32".into(),
            Type::F64 => "Float".into(),
            Type::Char => "Char".into(),
            Type::String => "Str".into(),
            Type::ErrorContext => "I32".into(),
            Type::Id(id) => {
                let td = &self.r().types[*id];
                // A world-level `use` is an alias. Only interface bindings
                // declare named Puddi types, so follow the alias to its owner.
                if td.name.is_some() && !matches!(td.owner, TypeOwner::World(_))
                    && !matches!(td.kind, TypeDefKind::Handle(_)) {
                    return self.named(*id);
                }
                self.ty_structural(*id)
            }
        }
    }

    /// The Puddi type for a type definition, ignoring its name.
    fn ty_structural(&mut self, id: TypeId) -> String {
        let td = &self.r().types[id];
        {
            {
                match &td.kind {
                    TypeDefKind::Type(t) => self.ty(t),
                    TypeDefKind::List(e) => format!("List<{}>", self.ty(e)),
                    TypeDefKind::Option(e) => format!("Option<{}>", self.ty(e)),
                    TypeDefKind::Result(r) => {
                        let ok = r.ok.as_ref().map(|t| self.ty(t)).unwrap_or_else(|| "()".into());
                        let err = r.err.as_ref().map(|t| self.ty(t)).unwrap_or_else(|| "()".into());
                        format!("Result<{ok}, {err}>")
                    }
                    TypeDefKind::Tuple(tu) => {
                        let parts: Vec<String> = tu.types.iter().map(|t| self.ty(t)).collect();
                        format!("({})", parts.join(", "))
                    }
                    TypeDefKind::Handle(Handle::Own(r) | Handle::Borrow(r)) => self.named(*r),
                    TypeDefKind::Future(_) => "__WitFuture".into(),
                    TypeDefKind::Stream(_) => "__WitStream".into(),
                    _ => "()".into(),
                }
            }
        }
    }

    fn kind(&self, t: &Type) -> Option<&'a TypeDefKind> {
        match t {
            Type::Id(id) => {
                let k = &self.r().types[*id].kind;
                match k {
                    TypeDefKind::Type(inner) => self.kind(inner).or(Some(k)),
                    _ => Some(k),
                }
            }
            _ => None,
        }
    }

    fn resolve_alias(&self, t: &Type) -> Type {
        match t {
            Type::Id(id) => match &self.r().types[*id].kind {
                TypeDefKind::Type(inner) => self.resolve_alias(inner),
                _ => *t,
            },
            _ => *t,
        }
    }

    pub fn flat(&self, t: &Type) -> Vec<WasmType> {
        let mut storage = [WasmType::I32; 256];
        let mut ft = wit_parser::abi::FlatTypes::new(&mut storage);
        self.r().push_flat(t, &mut ft);
        ft.to_vec().into_iter().map(norm).collect()
    }

    fn size(&self, t: &Type) -> usize {
        self.w.sizes.size(t).size_wasm32()
    }

    fn align(&self, t: &Type) -> usize {
        self.w.sizes.align(t).align_wasm32()
    }

    /// Cases of a variant-like type: (case pattern prefix, payload type).
    fn cases(&mut self, t: &Type) -> Option<(Int, Vec<(String, Option<Type>)>)> {
        let t = self.resolve_alias(t);
        let Type::Id(id) = t else { return None };
        match &self.r().types[id].kind {
            TypeDefKind::Option(p) => Some((Int::U8, vec![("None".into(), None), ("Some".into(), Some(*p))])),
            TypeDefKind::Result(r) => Some((Int::U8, vec![("Ok".into(), r.ok), ("Err".into(), r.err)])),
            TypeDefKind::Variant(v) => {
                let n = self.named(id);
                Some((v.tag(), v.cases.iter().map(|c| (format!("{n}.{}", pascal(&c.name)), c.ty)).collect()))
            }
            _ => None,
        }
    }

    fn is_result_unit(&self, t: &Type, ok: bool) -> bool {
        match self.kind(t) {
            Some(TypeDefKind::Result(r)) => if ok { r.ok.is_none() } else { r.err.is_none() },
            _ => false,
        }
    }

    fn join_conv(v: &str, from: WasmType, to: WasmType) -> String {
        match (from, to) {
            (a, b) if a == b => v.to_string(),
            (WasmType::I32, WasmType::I64) => format!("__cast<U32, I64>(__cast<I32, U32>({v}))"),
            (WasmType::F32, WasmType::I32) => format!("__reinterpret<F32, I32>({v})"),
            (WasmType::F32, WasmType::I64) => format!("__cast<U32, I64>(__cast<I32, U32>(__reinterpret<F32, I32>({v})))"),
            (WasmType::F64, WasmType::I64) => format!("__reinterpret<Float, I64>({v})"),
            _ => v.to_string(),
        }
    }

    fn unjoin_conv(v: &str, from: WasmType, to: WasmType) -> String {
        match (from, to) {
            (a, b) if a == b => v.to_string(),
            (WasmType::I64, WasmType::I32) => format!("__cast<I64, I32>({v})"),
            (WasmType::I32, WasmType::F32) => format!("__reinterpret<I32, F32>({v})"),
            (WasmType::I64, WasmType::F32) => format!("__reinterpret<I32, F32>(__cast<I64, I32>({v}))"),
            (WasmType::I64, WasmType::F64) => format!("__reinterpret<I64, Float>({v})"),
            _ => v.to_string(),
        }
    }

    fn zero(t: WasmType) -> &'static str {
        match t {
            WasmType::F32 | WasmType::F64 => "0.0",
            _ => "0",
        }
    }

    /// Lower a value to its flat core values.
    pub fn lower_flat(&mut self, t: &Type, v: &str) -> Vec<String> {
        match t {
            Type::Bool => vec![self.bind("I32", format!("if {v} {{ 1 }} else {{ 0 }}"))],
            Type::U8 => vec![format!("__cast<U8, I32>({v})")],
            Type::U16 => vec![format!("__cast<U16, I32>({v})")],
            Type::S8 => vec![format!("__cast<I8, I32>({v})")],
            Type::S16 => vec![format!("__cast<I16, I32>({v})")],
            Type::U32 => vec![format!("__cast<U32, I32>({v})")],
            Type::U64 => vec![format!("__cast<U64, I64>({v})")],
            Type::S32 | Type::S64 | Type::F32 | Type::F64 | Type::ErrorContext => vec![v.to_string()],
            Type::Char => vec![format!("__cast<U32, I32>({v}.to_u32())")],
            Type::String => {
                let s = self.bind("Str", v.to_string());
                let p = self.bind("I32", format!("__str_to_mem({s})"));
                let l = self.bind("I32", format!("__cast<Int, I32>(__str_len({s}))"));
                vec![p, l]
            }
            Type::Id(id) => {
                let kind = &self.r().types[*id].kind;
                match kind {
                    TypeDefKind::Type(inner) => self.lower_flat(inner, v),
                    TypeDefKind::Record(r) => {
                        let s = self.bindt(t, v.to_string());
                        let mut out = Vec::new();
                        for f in &r.fields {
                            out.extend(self.lower_flat(&f.ty, &format!("{s}.{}", snake(&f.name))));
                        }
                        out
                    }
                    TypeDefKind::Tuple(tu) => {
                        let s = self.bindt(t, v.to_string());
                        let mut out = Vec::new();
                        for (i, et) in tu.types.iter().enumerate() {
                            out.extend(self.lower_flat(et, &format!("{s}.{i}")));
                        }
                        out
                    }
                    TypeDefKind::Flags(fl) => {
                        let s = self.bindt(t, v.to_string());
                        let words = fl.flags.len().div_ceil(32).max(1);
                        let mut out = Vec::new();
                        for w in 0..words {
                            let m = self.t();
                            self.emit(format!("var {m}: I32 = 0"));
                            for (i, f) in fl.flags.iter().enumerate().skip(w * 32).take(32) {
                                let bit = 1i64 << (i - w * 32);
                                let bit = if bit >= 1 << 31 { format!("__cast<I64, I32>({bit})") } else { bit.to_string() };
                                self.emit(format!("if {s}.{} {{ {m} = {m} | {bit} }}", snake(&f.name)));
                            }
                            out.push(m);
                        }
                        out
                    }
                    TypeDefKind::Enum(e) => {
                        let n = self.named(*id);
                        let arms: Vec<String> = e.cases.iter().enumerate().map(|(i, c)| format!("{n}.{} -> {i}", pascal(&c.name))).collect();
                        vec![self.bind("I32", format!("match {v} {{\n{}\n}}", arms.join("\n")))]
                    }
                    TypeDefKind::Variant(_) | TypeDefKind::Option(_) | TypeDefKind::Result(_) => {
                        let joined = self.flat(t);
                        let (_, cases) = self.cases(t).unwrap();
                        let slots: Vec<String> = joined.iter().map(|_| self.t()).collect();
                        for (s, jt) in slots.iter().zip(&joined) {
                            self.emit(format!("var {s}: {} = {}", wt(*jt), Self::zero(*jt)));
                        }
                        let mut arms = Vec::new();
                        for (ci, (pat, pt)) in cases.iter().enumerate() {
                            let binder = self.t();
                            let pattern = match pt {
                                Some(_) => format!("{pat}({binder})"),
                                None if pat == "Ok" || pat == "Err" => format!("{pat}(_)"),
                                None => pat.clone(),
                            };
                            let joined2 = joined.clone();
                            let slots2 = slots.clone();
                            let body = self.block(|g| {
                                g.emit(format!("{} = {ci}", slots2[0]));
                                if let Some(pt) = pt {
                                    let vals = g.lower_flat(pt, &binder);
                                    let fts = g.flat(pt);
                                    for (k, (val, ft)) in vals.iter().zip(fts).enumerate() {
                                        g.emit(format!("{} = {}", slots2[k + 1], Self::join_conv(val, ft, joined2[k + 1])));
                                    }
                                }
                                "()".into()
                            });
                            arms.push(format!("{pattern} -> {body}"));
                        }
                        self.emit(format!("match {v} {{\n{}\n}}", arms.join("\n")));
                        slots
                    }
                    TypeDefKind::List(et) => {
                        let et = *et;
                        let xs = self.bindt(t, v.to_string());
                        let n = self.bind("I32", format!("__cast<Int, I32>({xs}.len())"));
                        let size = self.size(&et);
                        let align = self.align(&et);
                        let p = self.bind("I32", format!("__cabi_alloc({n} * {size}, {align})"));
                        let i = self.t();
                        let body = self.block(|g| {
                            g.store(&et, &format!("{xs}[{i}]"), &format!("{p} + __cast<Int, I32>({i}) * {size}"));
                            "()".into()
                        });
                        self.emit(format!("for {i} in 0..{xs}.len() {body}"));
                        vec![p, n]
                    }
                    TypeDefKind::Handle(_) | TypeDefKind::Future(_) | TypeDefKind::Stream(_) => vec![format!("{v}.handle")],
                    _ => vec!["0".into()],
                }
            }
        }
    }

    /// Lift a value from flat core values.
    pub fn lift_flat(&mut self, t: &Type, vals: &mut VecDeque<String>) -> String {
        let mut next = || vals.pop_front().unwrap_or_else(|| "0".into());
        match t {
            Type::Bool => format!("({} != 0)", next()),
            Type::U8 => format!("__cast<I32, U8>({})", next()),
            Type::U16 => format!("__cast<I32, U16>({})", next()),
            Type::S8 => format!("__cast<I32, I8>({})", next()),
            Type::S16 => format!("__cast<I32, I16>({})", next()),
            Type::U32 => format!("__cast<I32, U32>({})", next()),
            Type::U64 => format!("__cast<I64, U64>({})", next()),
            Type::S32 | Type::S64 | Type::F32 | Type::F64 | Type::ErrorContext => next(),
            Type::Char => format!("Char.from_u32(__cast<I32, U32>({})).unwrap()", next()),
            Type::String => {
                let p = next();
                let l = next();
                format!("__str_from_mem({p}, {l})")
            }
            Type::Id(id) => {
                let kind = &self.r().types[*id].kind;
                match kind {
                    TypeDefKind::Type(inner) => self.lift_flat(inner, vals),
                    TypeDefKind::Record(r) => {
                        let n = self.ty(t);
                        let mut parts = Vec::new();
                        for f in &r.fields {
                            let e = self.lift_flat(&f.ty, vals);
                            let b = self.bindt(&f.ty, e);
                            parts.push(format!("{}: {b}", snake(&f.name)));
                        }
                        format!("{n} {{ {} }}", parts.join(", "))
                    }
                    TypeDefKind::Tuple(tu) => {
                        let mut parts = Vec::new();
                        for et in &tu.types {
                            let e = self.lift_flat(et, vals);
                            parts.push(self.bindt(et, e));
                        }
                        format!("({})", parts.join(", "))
                    }
                    TypeDefKind::Flags(fl) => {
                        let n = self.ty(t);
                        let words = fl.flags.len().div_ceil(32).max(1);
                        let ws: Vec<String> = (0..words).map(|_| vals.pop_front().unwrap_or_else(|| "0".into())).collect();
                        let ws: Vec<String> = ws.into_iter().map(|w| self.bind("I32", w)).collect();
                        let parts: Vec<String> = fl.flags.iter().enumerate().map(|(i, f)| {
                            let bit = 1i64 << (i % 32);
                            let bit = if bit >= 1 << 31 { format!("__cast<I64, I32>({bit})") } else { bit.to_string() };
                            format!("{}: ({} & {bit}) != 0", snake(&f.name), ws[i / 32])
                        }).collect();
                        format!("{n} {{ {} }}", parts.join(", "))
                    }
                    TypeDefKind::Enum(e) => {
                        let n = self.named(*id);
                        let d = vals.pop_front().unwrap_or_else(|| "0".into());
                        let arms: Vec<String> = e.cases.iter().enumerate().map(|(i, c)| format!("{i} -> {n}.{}", pascal(&c.name))).collect();
                        format!("match __cast<I32, Int>({d}) {{\n{}\n_ -> panic(\"invalid enum value from the host\")\n}}", arms.join("\n"))
                    }
                    TypeDefKind::Variant(_) | TypeDefKind::Option(_) | TypeDefKind::Result(_) => {
                        let joined = self.flat(t);
                        let mut slots = Vec::new();
                        for jt in &joined {
                            let v = vals.pop_front().unwrap_or_else(|| "0".into());
                            slots.push(self.bind(wt(*jt), v));
                        }
                        let ty_s = self.ty(t);
                        let (_, cases) = self.cases(t).unwrap();
                        let mut arms = Vec::new();
                        for (ci, (pat, pt)) in cases.iter().enumerate() {
                            let joined2 = joined.clone();
                            let slots2 = slots.clone();
                            let unit_payload = (pat == "Ok" && self.is_result_unit(t, true)) || (pat == "Err" && self.is_result_unit(t, false));
                            let body = self.block(|g| match pt {
                                Some(pt) => {
                                    let fts = g.flat(pt);
                                    let mut pv: VecDeque<String> = fts.iter().enumerate().map(|(k, ft)| Self::unjoin_conv(&slots2[k + 1], joined2[k + 1], *ft)).collect();
                                    let e = g.lift_flat(pt, &mut pv);
                                    format!("{pat}({e})")
                                }
                                None if unit_payload => format!("{pat}(())"),
                                None => pat.clone(),
                            });
                            arms.push(format!("{ci} -> {body}"));
                        }
                        let r = self.t();
                        self.emit(format!("let {r}: {ty_s} = match __cast<I32, Int>({}) {{\n{}\n_ -> panic(\"invalid variant from the host\")\n}}", slots[0], arms.join("\n")));
                        r
                    }
                    TypeDefKind::List(et) => {
                        let et = *et;
                        let p = vals.pop_front().unwrap_or_else(|| "0".into());
                        let n = vals.pop_front().unwrap_or_else(|| "0".into());
                        let p = self.bind("I32", p);
                        let n = self.bind("I32", n);
                        let ets = self.ty(&et);
                        let out = self.t();
                        self.emit(format!("let {out}: List<{ets}> = List.with_capacity(__cast<I32, Int>({n}))"));
                        let size = self.size(&et);
                        let i = self.t();
                        let body = self.block(|g| {
                            let e = g.load(&et, &format!("{p} + __cast<Int, I32>({i}) * {size}"));
                            g.emit(format!("{out}.push({e})"));
                            "()".into()
                        });
                        self.emit(format!("for {i} in 0..__cast<I32, Int>({n}) {body}"));
                        out
                    }
                    TypeDefKind::Handle(Handle::Own(r) | Handle::Borrow(r)) => {
                        let n = self.named(*r);
                        format!("{n} {{ handle: {} }}", next())
                    }
                    TypeDefKind::Future(_) => format!("__WitFuture {{ handle: {} }}", next()),
                    TypeDefKind::Stream(_) => format!("__WitStream {{ handle: {} }}", next()),
                    _ => "()".into(),
                }
            }
        }
    }

    fn prim_store(&self, t: &Type) -> Option<&'static str> {
        Some(match t {
            Type::U8 => "U8",
            Type::S8 => "I8",
            Type::U16 => "U16",
            Type::S16 => "I16",
            Type::U32 => "U32",
            Type::S32 => "I32",
            Type::U64 => "U64",
            Type::S64 => "I64",
            Type::F32 => "F32",
            Type::F64 => "Float",
            Type::ErrorContext => "I32",
            _ => return None,
        })
    }

    fn tag_ty(tag: Int) -> &'static str {
        match tag {
            Int::U8 => "U8",
            Int::U16 => "U16",
            Int::U32 => "U32",
            Int::U64 => "U64",
        }
    }

    /// Store a value at a linear memory address (an I32 expression).
    pub fn store(&mut self, t: &Type, v: &str, addr: &str) {
        if let Some(p) = self.prim_store(t) {
            self.emit(format!("__mem_store<{p}>({addr}, {v})"));
            return;
        }
        let a = self.bind("I32", addr.to_string());
        match t {
            Type::Bool => self.emit(format!("__mem_store<U8>({a}, if {v} {{ 1 }} else {{ 0 }})")),
            Type::Char => self.emit(format!("__mem_store<U32>({a}, {v}.to_u32())")),
            Type::String => {
                let vals = self.lower_flat(t, v);
                self.emit(format!("__mem_store<I32>({a}, {})", vals[0]));
                self.emit(format!("__mem_store<I32>({a} + 4, {})", vals[1]));
            }
            Type::Id(id) => {
                let kind = &self.r().types[*id].kind;
                match kind {
                    TypeDefKind::Type(inner) => self.store(inner, v, &a),
                    TypeDefKind::Record(r) => {
                        let s = self.bindt(t, v.to_string());
                        let offs = self.w.sizes.field_offsets(r.fields.iter().map(|f| &f.ty));
                        for ((off, ft), f) in offs.into_iter().zip(&r.fields) {
                            self.store(ft, &format!("{s}.{}", snake(&f.name)), &format!("{a} + {}", off.size_wasm32()));
                        }
                    }
                    TypeDefKind::Tuple(tu) => {
                        let s = self.bindt(t, v.to_string());
                        let offs = self.w.sizes.field_offsets(tu.types.iter());
                        for (i, (off, et)) in offs.into_iter().enumerate() {
                            self.store(et, &format!("{s}.{i}"), &format!("{a} + {}", off.size_wasm32()));
                        }
                    }
                    TypeDefKind::Flags(fl) => {
                        let vals = self.lower_flat(t, v);
                        match fl.repr() {
                            wit_parser::FlagsRepr::U8 => self.emit(format!("__mem_store<U8>({a}, __cast<I32, U8>({}))", vals[0])),
                            wit_parser::FlagsRepr::U16 => self.emit(format!("__mem_store<U16>({a}, __cast<I32, U16>({}))", vals[0])),
                            wit_parser::FlagsRepr::U32(_) => {
                                for (i, w) in vals.iter().enumerate() {
                                    self.emit(format!("__mem_store<I32>({a} + {}, {w})", i * 4));
                                }
                            }
                        }
                    }
                    TypeDefKind::Enum(e) => {
                        let vals = self.lower_flat(t, v);
                        let tt = Self::tag_ty(e.tag());
                        self.emit(format!("__mem_store<{tt}>({a}, __cast<I32, {tt}>({}))", vals[0]));
                    }
                    TypeDefKind::Variant(_) | TypeDefKind::Option(_) | TypeDefKind::Result(_) => {
                        let (tag, cases) = self.cases(t).unwrap();
                        let tt = Self::tag_ty(tag);
                        let off = self.w.sizes.payload_offset(tag, cases.iter().map(|c| c.1.as_ref())).size_wasm32();
                        let mut arms = Vec::new();
                        for (ci, (pat, pt)) in cases.iter().enumerate() {
                            let binder = self.t();
                            let pattern = match pt {
                                Some(_) => format!("{pat}({binder})"),
                                None if pat == "Ok" || pat == "Err" => format!("{pat}(_)"),
                                None => pat.clone(),
                            };
                            let a2 = a.clone();
                            let body = self.block(|g| {
                                g.emit(format!("__mem_store<{tt}>({a2}, {ci})"));
                                if let Some(pt) = pt {
                                    g.store(pt, &binder, &format!("{a2} + {off}"));
                                }
                                "()".into()
                            });
                            arms.push(format!("{pattern} -> {body}"));
                        }
                        self.emit(format!("match {v} {{\n{}\n}}", arms.join("\n")));
                    }
                    TypeDefKind::List(_) => {
                        let vals = self.lower_flat(t, v);
                        self.emit(format!("__mem_store<I32>({a}, {})", vals[0]));
                        self.emit(format!("__mem_store<I32>({a} + 4, {})", vals[1]));
                    }
                    TypeDefKind::Handle(_) | TypeDefKind::Future(_) | TypeDefKind::Stream(_) => self.emit(format!("__mem_store<I32>({a}, {v}.handle)")),
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Load a value from a linear memory address.
    pub fn load(&mut self, t: &Type, addr: &str) -> String {
        if let Some(p) = self.prim_store(t) {
            return format!("__mem_load<{p}>({addr})");
        }
        let a = self.bind("I32", addr.to_string());
        match t {
            Type::Bool => format!("(__mem_load<U8>({a}) != 0)"),
            Type::Char => format!("Char.from_u32(__mem_load<U32>({a})).unwrap()"),
            Type::String => format!("__str_from_mem(__mem_load<I32>({a}), __mem_load<I32>({a} + 4))"),
            Type::Id(id) => {
                let kind = &self.r().types[*id].kind;
                match kind {
                    TypeDefKind::Type(inner) => self.load(inner, &a),
                    TypeDefKind::Record(r) => {
                        let n = self.ty(t);
                        let offs = self.w.sizes.field_offsets(r.fields.iter().map(|f| &f.ty));
                        let mut parts = Vec::new();
                        for ((off, ft), f) in offs.into_iter().zip(&r.fields) {
                            let e = self.load(ft, &format!("{a} + {}", off.size_wasm32()));
                            let b = self.bindt(ft, e);
                            parts.push(format!("{}: {b}", snake(&f.name)));
                        }
                        format!("{n} {{ {} }}", parts.join(", "))
                    }
                    TypeDefKind::Tuple(tu) => {
                        let offs = self.w.sizes.field_offsets(tu.types.iter());
                        let mut parts = Vec::new();
                        for (off, et) in offs {
                            let e = self.load(et, &format!("{a} + {}", off.size_wasm32()));
                            parts.push(self.bindt(et, e));
                        }
                        format!("({})", parts.join(", "))
                    }
                    TypeDefKind::Flags(fl) => {
                        let mut vals: VecDeque<String> = match fl.repr() {
                            wit_parser::FlagsRepr::U8 => vec![format!("__cast<U8, I32>(__mem_load<U8>({a}))")].into(),
                            wit_parser::FlagsRepr::U16 => vec![format!("__cast<U16, I32>(__mem_load<U16>({a}))")].into(),
                            wit_parser::FlagsRepr::U32(n) => (0..n).map(|i| format!("__mem_load<I32>({a} + {})", i * 4)).collect(),
                        };
                        self.lift_flat(t, &mut vals)
                    }
                    TypeDefKind::Enum(e) => {
                        let tt = Self::tag_ty(e.tag());
                        let mut vals: VecDeque<String> = vec![format!("__cast<{tt}, I32>(__mem_load<{tt}>({a}))")].into();
                        self.lift_flat(t, &mut vals)
                    }
                    TypeDefKind::Variant(_) | TypeDefKind::Option(_) | TypeDefKind::Result(_) => {
                        let (tag, cases) = self.cases(t).unwrap();
                        let tt = Self::tag_ty(tag);
                        let off = self.w.sizes.payload_offset(tag, cases.iter().map(|c| c.1.as_ref())).size_wasm32();
                        let ty_s = self.ty(t);
                        let d = self.bind("Int", format!("__cast<{tt}, Int>(__mem_load<{tt}>({a}))"));
                        let mut arms = Vec::new();
                        for (ci, (pat, pt)) in cases.iter().enumerate() {
                            let unit_payload = (pat == "Ok" && self.is_result_unit(t, true)) || (pat == "Err" && self.is_result_unit(t, false));
                            let a2 = a.clone();
                            let body = self.block(|g| match pt {
                                Some(pt) => {
                                    let e = g.load(pt, &format!("{a2} + {off}"));
                                    format!("{pat}({e})")
                                }
                                None if unit_payload => format!("{pat}(())"),
                                None => pat.clone(),
                            });
                            arms.push(format!("{ci} -> {body}"));
                        }
                        let r = self.t();
                        self.emit(format!("let {r}: {ty_s} = match {d} {{\n{}\n_ -> panic(\"invalid variant in memory\")\n}}", arms.join("\n")));
                        r
                    }
                    TypeDefKind::List(_) => {
                        let mut vals: VecDeque<String> = vec![format!("__mem_load<I32>({a})"), format!("__mem_load<I32>({a} + 4)")].into();
                        self.lift_flat(t, &mut vals)
                    }
                    TypeDefKind::Handle(_) | TypeDefKind::Future(_) | TypeDefKind::Stream(_) => {
                        let mut vals: VecDeque<String> = vec![format!("__mem_load<I32>({a})")].into();
                        self.lift_flat(t, &mut vals)
                    }
                    _ => "()".into(),
                }
            }
            _ => "()".into(),
        }
    }

    fn take(&mut self) -> Vec<String> {
        std::mem::take(&mut self.buf)
    }

    /// Generate the Puddi module for an imported interface.
    pub fn interface_module(&mut self, i: InterfaceId) -> Result<String, String> {
        let r = self.r();
        let iface = &r.interfaces[i];
        let module = self.w.interface_name(i);
        let mut items = String::new();
        // types
        for (name, &tid) in &iface.types {
            let td = &r.types[tid];
            let n = pascal(name);
            match &td.kind {
                TypeDefKind::Record(rec) => {
                    let _ = writeln!(items, "@derive(Eq, Show)\npub struct {n} {{");
                    for f in &rec.fields {
                        let ft = self.ty(&f.ty);
                        let _ = writeln!(items, "    pub {}: {ft}", snake(&f.name));
                    }
                    items.push_str("}\n\n");
                }
                TypeDefKind::Variant(v) => {
                    let _ = writeln!(items, "@derive(Eq, Show)\npub enum {n} {{");
                    for c in &v.cases {
                        match &c.ty {
                            Some(t) => {
                                let ct = self.ty(t);
                                let _ = writeln!(items, "    {}({ct})", pascal(&c.name));
                            }
                            None => {
                                let _ = writeln!(items, "    {}", pascal(&c.name));
                            }
                        }
                    }
                    items.push_str("}\n\n");
                }
                TypeDefKind::Enum(e) => {
                    let _ = writeln!(items, "@derive(Eq, Show)\npub enum {n} {{");
                    for c in &e.cases {
                        let _ = writeln!(items, "    {}", pascal(&c.name));
                    }
                    items.push_str("}\n\n");
                }
                TypeDefKind::Flags(fl) => {
                    let _ = writeln!(items, "@derive(Eq, Show)\npub struct {n} {{");
                    for f in &fl.flags {
                        let _ = writeln!(items, "    pub {}: Bool", snake(&f.name));
                    }
                    items.push_str("}\n\n");
                    let all: Vec<String> = fl.flags.iter().map(|f| format!("{}: false", snake(&f.name))).collect();
                    let _ = writeln!(items, "impl {n} {{\n    /// No flags set.\n    pub fn empty() -> {n} {{ {n} {{ {} }} }}\n}}\n", all.join(", "));
                }
                TypeDefKind::Resource => {
                    let _ = writeln!(items, "/// A handle to a host resource.\n@derive(Eq, Show)\npub struct {n} {{\n    pub handle: I32\n}}\n");
                }
                TypeDefKind::Type(t) => {
                    let tt = self.ty(t);
                    if tt != n {
                        let _ = writeln!(items, "pub type {n} = {tt}\n");
                    }
                }
                TypeDefKind::Handle(_) | TypeDefKind::List(_) | TypeDefKind::Option(_) | TypeDefKind::Result(_) | TypeDefKind::Tuple(_) => {
                    let tt = self.ty_structural(tid);
                    let _ = writeln!(items, "pub type {n} = {tt}\n");
                }
                TypeDefKind::Future(_) => {
                    let _ = writeln!(items, "pub type {n} = __WitFuture\n");
                }
                TypeDefKind::Stream(_) => {
                    let _ = writeln!(items, "pub type {n} = __WitStream\n");
                }
                TypeDefKind::Map(..) | TypeDefKind::FixedLengthList(..) | TypeDefKind::Unknown => {
                    return Err(format!("WIT type `{name}` in `{module}` uses a feature this compiler does not support"));
                }
            }
        }
        // functions, grouped by resource
        let mut free = String::new();
        let mut by_res: BTreeMap<TypeId, String> = BTreeMap::new();
        for (k, (_, f)) in iface.functions.iter().enumerate() {
            let code = self.import_fn(f, &module, k)?;
            match f.kind.resource() {
                Some(rid) => by_res.entry(rid).or_default().push_str(&code.1),
                None => free.push_str(&code.1),
            }
            items.push_str(&code.0);
        }
        for (name, &tid) in &iface.types {
            if matches!(r.types[tid].kind, TypeDefKind::Resource) {
                let n = pascal(name);
                let _ = writeln!(items, "@extern({}, \"[resource-drop]{name}\")\nfn __drop_{}(handle: I32)\n", quote(&module), snake(name));
                let methods = by_res.remove(&tid).unwrap_or_default();
                let _ = writeln!(items, "impl {n} {{\n{methods}    /// Releases the resource.\n    pub fn drop(self) {{ __drop_{}(self.handle) }}\n}}\n", snake(name));
            }
        }
        items.push_str(&free);
        // loaders for named types (useful for stream payloads)
        for (name, &tid) in &iface.types {
            if matches!(r.types[tid].kind, TypeDefKind::Record(_) | TypeDefKind::Variant(_) | TypeDefKind::Enum(_)) {
                let n = pascal(name);
                let e = self.load(&Type::Id(tid), "addr");
                let body = self.take();
                let size = self.size(&Type::Id(tid));
                let _ = writeln!(items, "/// Reads a `{n}` stored in linear memory with the canonical ABI layout.\npub fn __load_{}(addr: I32) -> {n} {{\n{}\n{e}\n}}\n", snake(name), body.join("\n"));
                let _ = writeln!(items, "/// Size in bytes of a `{n}` in linear memory.\npub fn __size_{}() -> I32 {{ {size} }}\n", snake(name));
            }
        }
        let mut head = format!("// Generated bindings for the WIT interface `{module}`.\n\n");
        for (iid, alias) in &self.imports {
            let _ = writeln!(head, "import {} as {alias}", module_path(r, *iid));
        }
        head.push('\n');
        Ok(head + &items)
    }

    /// Returns (raw extern declaration, wrapper function text).
    fn import_fn(&mut self, f: &Function, module: &str, k: usize) -> Result<(String, String), String> {
        let r = self.r();
        let sig = r.wasm_signature(AbiVariant::GuestImport, f);
        let raw = format!("__raw{k}_{}", snake(f.item_name()).trim_end_matches('_'));
        let ps: Vec<String> = sig.params.iter().enumerate().map(|(i, t)| format!("p{i}: {}", wt(*t))).collect();
        let ret = sig.results.first().map(|t| format!(" -> {}", wt(*t))).unwrap_or_default();
        let decl = format!("@extern({}, {})\nfn {raw}({}){ret}\n\n", quote(module), quote(&f.name), ps.join(", "));
        let method = matches!(f.kind, FunctionKind::Method(_) | FunctionKind::AsyncMethod(_));
        let mut params = Vec::new();
        let mut vals = Vec::new();
        for (i, p) in f.params.iter().enumerate() {
            if i == 0 && method {
                vals.push("self".to_string());
                continue;
            }
            let pn = snake(&p.name);
            let pt = self.ty(&p.ty);
            params.push(format!("{pn}: {pt}"));
            vals.push(pn);
        }
        let ret_ty = f.result.as_ref().map(|t| self.ty(t));
        self.emit("let __m = __cabi_mark()".into());
        let mut args = Vec::new();
        if sig.indirect_params {
            let info = self.w.sizes.record(f.params.iter().map(|p| &p.ty));
            let p = self.bind("I32", format!("__cabi_alloc({}, {})", info.size.size_wasm32(), info.align.align_wasm32()));
            let offs = self.w.sizes.field_offsets(f.params.iter().map(|p| &p.ty));
            for ((off, pt), v) in offs.into_iter().zip(&vals) {
                self.store(pt, v, &format!("{p} + {}", off.size_wasm32()));
            }
            args.push(p);
        } else {
            for (p, v) in f.params.iter().zip(&vals) {
                args.extend(self.lower_flat(&p.ty, v));
            }
        }
        let mut result = "()".to_string();
        if sig.retptr {
            let t = f.result.unwrap();
            let rp = self.bind("I32", format!("__cabi_alloc({}, {})", self.size(&t), self.align(&t)));
            args.push(rp.clone());
            self.emit(format!("{raw}({})", args.join(", ")));
            let e = self.load(&t, &rp);
            result = self.bind(ret_ty.as_deref().unwrap(), e);
        } else if let Some(t) = &f.result {
            let x = self.bind(wt(sig.results[0]), format!("{raw}({})", args.join(", ")));
            let mut q: VecDeque<String> = vec![x].into();
            let e = self.lift_flat(t, &mut q);
            result = self.bind(ret_ty.as_deref().unwrap(), e);
        } else {
            self.emit(format!("{raw}({})", args.join(", ")));
        }
        self.emit("__cabi_reset(__m)".into());
        let body = self.take();
        let name = match f.kind {
            FunctionKind::Constructor(_) => "new".to_string(),
            _ => snake(f.item_name()),
        };
        let selfp = if method { if params.is_empty() { "self".to_string() } else { "self, ".to_string() } } else { String::new() };
        let rt = ret_ty.map(|t| format!(" -> {t}")).unwrap_or_default();
        let indent = if f.kind.resource().is_some() { "    " } else { "" };
        let mut text = String::new();
        if !f.docs.contents.as_deref().unwrap_or("").is_empty() {
            for l in f.docs.contents.as_deref().unwrap_or("").lines().take(3) {
                let _ = writeln!(text, "{indent}/// {l}");
            }
        }
        let _ = writeln!(text, "{indent}pub fn {name}({selfp}{}){rt} {{", params.join(", "));
        for l in body {
            for ll in l.lines() {
                let _ = writeln!(text, "{indent}    {ll}");
            }
        }
        let _ = writeln!(text, "{indent}    {result}\n{indent}}}\n");
        Ok((decl, text))
    }

    /// Wrapper exporting `target` (a Puddi function) as `f` under the core name `export`.
    /// Async world functions use the stackful async ABI and return through `task.return`.
    pub fn export_fn(&mut self, f: &Function, export: &str, target: &str, k: usize) -> String {
        let r = self.r();
        let is_async = f.kind.is_async();
        let variant = if is_async { AbiVariant::GuestExportAsyncStackful } else { AbiVariant::GuestExport };
        let sig = r.wasm_signature(variant, f);
        let ps: Vec<String> = sig.params.iter().enumerate().map(|(i, t)| format!("p{i}: {}", wt(*t))).collect();
        let ret = sig.results.first().map(|t| format!(" -> {}", wt(*t))).unwrap_or_default();
        let mut args = Vec::new();
        if sig.indirect_params {
            let offs = self.w.sizes.field_offsets(f.params.iter().map(|p| &p.ty));
            for (off, pt) in offs {
                let e = self.load(pt, &format!("p0 + {}", off.size_wasm32()));
                args.push(self.bindt(pt, e));
            }
        } else {
            let mut q: VecDeque<String> = (0..sig.params.len()).map(|i| format!("p{i}")).collect();
            for p in &f.params {
                let e = self.lift_flat(&p.ty, &mut q);
                args.push(self.bindt(&p.ty, e));
            }
        }
        let call = if self.await_call { format!("{target}({}).__await()", args.join(", ")) } else { format!("{target}({})", args.join(", ")) };
        let mut tail = String::new();
        let mut extra = String::new();
        if is_async {
            // results go to the host through `task.return`
            let (module, fname) = match export.split_once('#') {
                Some((iface, fname)) => (format!("[export]{iface}"), fname.to_string()),
                None => ("[export]$root".to_string(), export.to_string()),
            };
            let mut tr_params = Vec::new();
            let mut tr_args = Vec::new();
            if let Some(t) = &f.result {
                let rv = self.bindt(t, call);
                let flat = self.flat(t);
                if flat.len() > 16 {
                    let rp = self.bind("I32", format!("__cabi_alloc({}, {})", self.size(t), self.align(t)));
                    self.store(t, &rv, &rp);
                    tr_params.push("p0: I32".to_string());
                    tr_args.push(rp);
                } else {
                    let vals = self.lower_flat(t, &rv);
                    for (i, (v, ft)) in vals.into_iter().zip(flat).enumerate() {
                        tr_params.push(format!("p{i}: {}", wt(ft)));
                        tr_args.push(v);
                    }
                }
            } else {
                self.emit(call);
            }
            self.emit(format!("__task_return{k}({})", tr_args.join(", ")));
            let _ = writeln!(extra, "@extern({}, {})\nfn __task_return{k}({})\n", quote(&module), quote(&format!("[task-return]{fname}")), tr_params.join(", "));
        } else if let Some(t) = &f.result {
            let rv = self.bindt(t, call);
            if sig.retptr {
                let rp = self.bind("I32", format!("__cabi_alloc({}, {})", self.size(t), self.align(t)));
                self.store(t, &rv, &rp);
                tail = rp;
            } else {
                let vals = self.lower_flat(t, &rv);
                tail = vals[0].clone();
            }
        } else {
            self.emit(call);
        }
        let body = self.take();
        let core_name = if is_async { format!("[async-lift-stackful]{export}") } else { export.to_string() };
        let mut text = extra;
        let _ = writeln!(text, "@export({})\nfn __wit_export{k}({}){ret} {{", quote(&core_name), ps.join(", "));
        for l in body {
            let _ = writeln!(text, "    {l}");
        }
        let _ = writeln!(text, "    {tail}\n}}\n");
        if sig.retptr && !is_async {
            let _ = writeln!(text, "@export({})\nfn __wit_post{k}(p: I32) {{ __cabi_reset(__cabi_base()) }}\n", quote(&format!("cabi_post_{export}")));
        }
        text
    }
}

fn quote(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"").replace('{', "\\{").replace('}', "\\}"))
}

/// Exported functions the world requires: (core export name, function, Puddi name).
pub fn world_exports(w: &Wit) -> Vec<(String, Function, String)> {
    let r = &w.resolve;
    let mut out = Vec::new();
    for (key, item) in &r.worlds[w.world].exports {
        match item {
            WorldItem::Function(f) => out.push((f.name.clone(), f.clone(), snake(&f.name))),
            WorldItem::Interface { id, .. } => {
                let iname = r.name_world_key(key);
                for (fname, f) in &r.interfaces[*id].functions {
                    out.push((format!("{iname}#{fname}"), f.clone(), snake(f.item_name())));
                }
            }
            WorldItem::Type { .. } => {}
        }
    }
    out
}

/// The interface key name of a world export (for messages).
pub fn key_name(r: &Resolve, k: &WorldKey) -> String {
    r.name_world_key(k)
}

/// `name` as a WIT identifier: lowercase kebab-case fragments that start with a letter.
/// `puddi.mjs` has the same function (`witName`).
pub fn wit_name(name: &str) -> String {
    let mut frags: Vec<String> = Vec::new();
    let mut cur = String::new();
    for c in name.chars() {
        if c.is_ascii_alphanumeric() {
            cur.push(c.to_ascii_lowercase());
        } else if !cur.is_empty() {
            frags.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        frags.push(cur);
    }
    if frags.is_empty() {
        frags.push("x".into());
    }
    let s: Vec<String> = frags.into_iter().map(|f| if f.starts_with(|c: char| c.is_ascii_digit()) { format!("x{f}") } else { f }).collect();
    let mut out = s.join("-");
    if KEYWORDS_WIT.contains(&out.as_str()) {
        out = format!("x-{out}");
    }
    out
}

const KEYWORDS_WIT: &[&str] = &[
    "use", "type", "func", "u8", "u16", "u32", "u64", "s8", "s16", "s32", "s64", "f32", "f64", "char", "resource", "record", "flags", "variant", "enum", "bool", "string", "option", "result", "future", "stream", "list", "own", "borrow", "_", "as", "from", "static", "interface", "tuple", "import", "export", "world", "package", "constructor", "include", "with", "async", "error-context", "map", "include", "implements",
];

/// Wraps a browser core module in a component.
///
/// Every core import becomes a world-level function import and every exported
/// function a world export, with WIT signatures derived from the core types
/// (only numbers cross the boundary). The renamed core module carries a
/// `puddi:names` custom section that maps the WIT names back to the names the
/// JavaScript glue uses, and the glue instantiates the core module directly.
pub fn browser_component(core: &[u8]) -> Result<Vec<u8>, String> {
    use wasmparser::{Parser, Payload, TypeRef, ValType};
    let vt = |t: &ValType| -> Result<&'static str, String> {
        Ok(match t {
            ValType::I32 => "s32",
            ValType::I64 => "s64",
            ValType::F32 => "f32",
            ValType::F64 => "f64",
            _ => return Err("a browser import or export uses a reference type".into()),
        })
    };
    // function types, imported function types and exports
    let mut types: Vec<Option<wasmparser::FuncType>> = Vec::new();
    let mut func_types: Vec<u32> = Vec::new();
    let mut sections: Vec<(u8, std::ops::Range<usize>)> = Vec::new();
    let mut imports: Vec<(String, String, u32)> = Vec::new();
    let mut exports: Vec<(String, wasmparser::ExternalKind, u32)> = Vec::new();
    for p in Parser::new(0).parse_all(core) {
        let p = p.map_err(|e| e.to_string())?;
        if let Some((id, range)) = p_section(&p) {
            sections.push((id, range));
        }
        match p {
            Payload::TypeSection(r) => {
                for g in r {
                    for st in g.map_err(|e| e.to_string())?.into_types() {
                        types.push(match &st.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => Some(f.clone()),
                            _ => None,
                        });
                    }
                }
            }
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    let imp = imp.map_err(|e| e.to_string())?;
                    match imp.ty {
                        TypeRef::Func(t) => {
                            func_types.push(t);
                            imports.push((imp.module.to_string(), imp.name.to_string(), t));
                        }
                        _ => return Err("browser modules import only functions".into()),
                    }
                }
            }
            Payload::FunctionSection(r) => {
                for t in r {
                    func_types.push(t.map_err(|e| e.to_string())?);
                }
            }
            Payload::ExportSection(r) => {
                for e in r {
                    let e = e.map_err(|e| e.to_string())?;
                    exports.push((e.name.to_string(), e.kind, e.index));
                }
            }
            _ => {}
        }
    }
    let sig = |t: u32| -> Result<String, String> {
        let f = types.get(t as usize).and_then(|x| x.as_ref()).ok_or("bad function type")?;
        let ps: Vec<String> = f.params().iter().enumerate().map(|(i, p)| Ok(format!("p{i}: {}", vt(p)?))).collect::<Result<_, String>>()?;
        let r = match f.results() {
            [] => String::new(),
            [r] => format!(" -> {}", vt(r)?),
            _ => return Err("multiple results".into()),
        };
        Ok(format!("func({}){r}", ps.join(", ")))
    };
    let mut wit = String::from("package puddi:browser-app;\n\nworld app {\n");
    let mut names = Vec::new();
    let mut used = BTreeSet::new();
    let mut new_imports = wasm_encoder::ImportSection::new();
    for (m, f, t) in &imports {
        let n = if m == "puddi" { wit_name(f) } else { wit_name(&format!("{m}-{f}")) };
        if !used.insert(n.clone()) {
            return Err(format!("imports `{m}` `{f}` collide as WIT name `{n}`"));
        }
        let _ = writeln!(wit, "  import {n}: {};", sig(*t)?);
        names.push(format!("[\"i\",{},{},{}]", json(&n), json(m), json(f)));
        new_imports.import("$root", &n, wasm_encoder::EntityType::Function(*t));
    }
    let mut new_exports = wasm_encoder::ExportSection::new();
    for (e, kind, idx) in &exports {
        match kind {
            wasmparser::ExternalKind::Func => {
                let n = wit_name(e);
                if !used.insert(n.clone()) {
                    return Err(format!("export `{e}` collides as WIT name `{n}`"));
                }
                let _ = writeln!(wit, "  export {n}: {};", sig(func_types[*idx as usize])?);
                names.push(format!("[\"e\",{},{}]", json(&n), json(e)));
                new_exports.export(&n, wasm_encoder::ExportKind::Func, *idx);
            }
            wasmparser::ExternalKind::Memory => {
                new_exports.export(e, wasm_encoder::ExportKind::Memory, *idx);
            }
            _ => return Err(format!("unsupported export `{e}`")),
        }
    }
    wit.push_str("}\n");
    // re-emit the module with the renamed import and export sections
    let mut module = wasm_encoder::Module::new();
    for (id, range) in &sections {
        match id {
            2 => {
                module.section(&new_imports);
            }
            7 => {
                module.section(&new_exports);
            }
            _ => {
                module.section(&wasm_encoder::RawSection { id: *id, data: &core[range.clone()] });
            }
        }
    }
    module.section(&wasm_encoder::CustomSection { name: "puddi:names".into(), data: format!("[{}]", names.join(",")).into_bytes().into() });
    let mut bytes = module.finish();
    let mut resolve = Resolve::new();
    let mut sm = wit_parser::SourceMap::new();
    sm.push_str("<browser world>", wit);
    let group = sm.parse().map_err(|(_, e)| format!("{e}"))?;
    let pkg = resolve.push_group(group).map_err(|e| format!("{e}"))?;
    let world = resolve.select_world(&[pkg], Some("app")).map_err(|e| format!("{e:#}"))?;
    wit_component::embed_component_metadata(&mut bytes, &resolve, world, wit_component::StringEncoding::UTF8, false).map_err(|e| format!("{e:#}"))?;
    let mut enc = wit_component::ComponentEncoder::default();
    enc.module(&bytes).map_err(|e| format!("{e:#}"))?;
    enc.validate(true);
    enc.encode().map_err(|e| format!("{e:#}"))
}

/// Section id and content range of a top-level payload, for copying sections verbatim.
fn p_section(p: &wasmparser::Payload) -> Option<(u8, std::ops::Range<usize>)> {
    use wasmparser::Payload::*;
    let (id, r): (u8, std::ops::Range<u64>) = match p {
        TypeSection(r) => (1, r.range()),
        ImportSection(r) => (2, r.range()),
        FunctionSection(r) => (3, r.range()),
        TableSection(r) => (4, r.range()),
        MemorySection(r) => (5, r.range()),
        TagSection(r) => (13, r.range()),
        GlobalSection(r) => (6, r.range()),
        ExportSection(r) => (7, r.range()),
        StartSection { range, .. } => (8, range.start as u64..range.end as u64),
        ElementSection(r) => (9, r.range()),
        DataCountSection { range, .. } => (12, range.start as u64..range.end as u64),
        DataSection(r) => (11, r.range()),
        CodeSectionStart { unchecked_range, .. } => (10, unchecked_range.clone()),
        _ => return None,
    };
    Some((id, r.start as usize..r.end as usize))
}

fn json(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}
