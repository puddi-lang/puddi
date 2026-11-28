//! Code generation: IR to WebAssembly text (WasmGC), assembled to binary.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use crate::elab::{replace_proj_dyn, Global};
use crate::ir::*;
use crate::program::{AdtKind, Program};
use crate::types::*;

pub struct Output {
    pub wat: String,
    pub wasm: Vec<u8>,
    pub tests: Vec<(String, String)>,
}

/// Code generation state. The vectors `types`, `funcs`, `data`, `globals`, `imports` and
/// `new_refs` collect output; the maps and sets remember what was already defined, so that
/// several copies of the state can generate functions in parallel and their outputs can be
/// merged afterwards (see `generate`).
#[derive(Clone)]
struct Cg<'a> {
    tail: String,
    component: bool,
    prog: &'a Program,
    g: &'a Global<'a>,
    /// (name, definition)
    types: Vec<(String, String)>,
    type_names: HashMap<String, String>,
    defined: HashSet<String>,
    funcs: Vec<String>,
    /// (name, bytes)
    data: Vec<(String, Vec<u8>)>,
    data_map: HashMap<Vec<u8>, String>,
    data_names: HashSet<String>,
    refs: HashSet<String>,
    new_refs: Vec<String>,
    imports: Vec<String>,
    globals: Vec<String>,
    exports: Vec<String>,
    global_names: HashSet<String>,
    shims: HashMap<FnInst, String>,
    vtable_globals: HashMap<(Ty, TraitRef), String>,
    /// one shared instance per payload-less enum variant, so `None` or `Ordering.Less` never allocates
    unit_variants: HashMap<String, String>,
    func_names: Vec<String>,
}

struct FnState {
    out: String,
    indent: usize,
    locals: Vec<LocalInfo>,
    local_names: Vec<String>,
    temps: Vec<(String, String)>,
    label: u32,
    loop_types: HashMap<LabelId, Ty>,
    /// scratch locals (a, b, result) for inline overflow checks; never live across them
    ovf_tmps: Option<(String, String, String)>,
    /// known value ranges of integer locals, to leave out overflow checks that cannot fail
    ranges: crate::ranges::Ranges,
}

impl FnState {
    fn emit(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }
    fn label(&mut self) -> String {
        self.label += 1;
        format!("$L{}", self.label)
    }
}

fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '.' | '<' | '>' | '|' | '#' | ':' | '+' | '-' | '*' | '/' | '!' | '?' | '@' | '^' | '~' | '=' => c,
            _ => '_',
        })
        .collect()
}

pub fn is_ref(t: &Ty) -> bool {
    matches!(t, Ty::Str | Ty::Adt(..) | Ty::Tuple(_) | Ty::Array(_) | Ty::Fn(..) | Ty::Dyn(..))
}

fn wat_str(bytes: &[u8]) -> String {
    let mut s = String::from("\"");
    for &b in bytes {
        if b.is_ascii_graphic() && b != b'"' && b != b'\\' || b == b' ' {
            s.push(b as char);
        } else {
            let _ = write!(s, "\\{b:02x}");
        }
    }
    s.push('"');
    s
}

/// Assembles the generated text with `asm`, or with the `wat` crate when `asm` does not
/// understand it (`PUD_WAT=1` always uses `wat`; `PUD_ASM_CHECK=1` assembles with both and
/// fails unless the results agree).
fn assemble(text: &str) -> Result<Vec<u8>, String> {
    let wat = || wat::parse_str(text).map_err(|e| format!("internal error: generated WAT failed to assemble: {e}"));
    if std::env::var_os("PUD_WAT").is_some() {
        return wat();
    }
    let check = std::env::var_os("PUD_ASM_CHECK").is_some();
    match crate::asm::assemble(text) {
        Ok(w) => {
            if check {
                if let Some(d) = crate::asm::compare(&w, &wat()?) {
                    return Err(format!("internal error: assembler output differs from wat: {d}"));
                }
            }
            Ok(w)
        }
        Err(e) if check => Err(format!("internal error: assembler: {e}")),
        Err(_) => wat(),
    }
}

fn f64_lit(v: f64) -> String {
    if v.is_nan() {
        "nan".into()
    } else if v.is_infinite() {
        if v > 0.0 { "inf".into() } else { "-inf".into() }
    } else {
        format!("{v:e}")
    }
}

impl<'a> Cg<'a> {
    // ---------------- types ----------------
    fn mangle(&self, t: &Ty) -> String {
        match t {
            Ty::Int(i) => i.name().to_string(),
            Ty::Float(FloatTy::F64) => "Float".into(),
            Ty::Float(FloatTy::F32) => "F32".into(),
            Ty::Bool => "Bool".into(),
            Ty::Char => "Char".into(),
            Ty::Str => "Str".into(),
            Ty::Unit => "U".into(),
            Ty::Never => "N".into(),
            Ty::Tuple(ts) => format!("T<{}>", ts.iter().map(|t| self.mangle(t)).collect::<Vec<_>>().join("|")),
            Ty::Adt(id, ts) => {
                let a = &self.prog.adts[*id];
                let m = &self.prog.modules[a.module];
                let base = if m.pkg == crate::program::Pkg::Prelude || m.path == "main" { a.name.clone() } else { format!("{}.{}", m.path, a.name) };
                if ts.is_empty() { base } else { format!("{base}<{}>", ts.iter().map(|t| self.mangle(t)).collect::<Vec<_>>().join("|")) }
            }
            Ty::Array(t) => format!("Array<{}>", self.mangle(t)),
            Ty::Fn(ps, r) => format!("Fn<{}>{}", ps.iter().map(|t| self.mangle(t)).collect::<Vec<_>>().join("|"), self.mangle(r)),
            Ty::Dyn(id, ts, a) => {
                let mut s = format!("dyn.{}", self.prog.traits[*id].name);
                if !ts.is_empty() || !a.is_empty() {
                    s.push('<');
                    let mut parts: Vec<String> = ts.iter().map(|t| self.mangle(t)).collect();
                    parts.extend(a.iter().map(|(n, t)| format!("{n}={}", self.mangle(t))));
                    s.push_str(&parts.join("|"));
                    s.push('>');
                }
                s
            }
            _ => "E".into(),
        }
    }

    fn vt(&mut self, t: &Ty) -> String {
        match t {
            Ty::Int(i) if i.is64() => "i64".into(),
            Ty::Int(_) | Ty::Bool | Ty::Char | Ty::Unit | Ty::Never | Ty::Error | Ty::Var(_) | Ty::Param(_) | Ty::Proj(..) => "i32".into(),
            Ty::Float(FloatTy::F64) => "f64".into(),
            Ty::Float(FloatTy::F32) => "f32".into(),
            _ => format!("(ref {})", self.tname(t)),
        }
    }

    fn vt_null(&mut self, t: &Ty) -> String {
        if is_ref(t) { format!("(ref null {})", self.tname(t)) } else { self.vt(t) }
    }

    fn storage(&mut self, t: &Ty) -> String {
        match t {
            Ty::Int(IntTy::I8 | IntTy::U8) | Ty::Bool => "i8".into(),
            Ty::Int(IntTy::I16 | IntTy::U16) => "i16".into(),
            _ => self.vt_null(t),
        }
    }

    fn add_type(&mut self, name: &str, def: String) {
        if self.defined.insert(name.to_string()) {
            self.types.push((name.to_string(), format!("(type {name} {def})")));
        }
    }

    /// Name of the wasm type for a reference type (defining it on first use).
    fn tname(&mut self, t: &Ty) -> String {
        let key = self.mangle(t);
        if let Some(n) = self.type_names.get(&key) {
            return n.clone();
        }
        let name = format!("${}", sanitize(&key));
        self.type_names.insert(key, name.clone());
        match t {
            Ty::Str => {
                self.add_type(&name, "(array (mut i8))".into());
            }
            Ty::Tuple(ts) => {
                let fields: Vec<String> = ts.iter().map(|t| format!("(field {})", self.vt(t))).collect();
                self.add_type(&name, format!("(struct {})", fields.join(" ")));
            }
            Ty::Array(e) => {
                let s = self.storage(e);
                self.add_type(&name, format!("(array (mut {s}))"));
            }
            Ty::Fn(ps, r) => {
                let ft = self.fn_type(ps, r, "(ref null struct)");
                self.add_type(&name, format!("(struct (field (ref {ft})) (field (ref null struct)))"));
            }
            Ty::Dyn(tid, targs, assoc) => {
                let vt_name = format!("$vt.{}", sanitize(&self.mangle(t)));
                let sigs = self.dyn_sigs(*tid, targs, assoc, t);
                let mut fields = Vec::new();
                for (_, ps, r) in &sigs {
                    let ft = self.fn_type(ps, r, "anyref");
                    fields.push(format!("(field (ref {ft}))"));
                }
                self.add_type(&vt_name, format!("(struct {})", fields.join(" ")));
                self.add_type(&name, format!("(struct (field anyref) (field (ref {vt_name})))"));
            }
            Ty::Adt(id, args) => {
                let adt = &self.prog.adts[*id];
                match &adt.kind {
                    AdtKind::Struct(fields) => {
                        let fields = fields.clone();
                        let fs: Vec<String> = fields
                            .iter()
                            .map(|f| {
                                let ft = self.prog.normalize_proj(f.ty.subst(args));
                                let v = self.vt(&ft);
                                if f.mutable { format!("(field (mut {v}))") } else { format!("(field {v})") }
                            })
                            .collect();
                        self.add_type(&name, format!("(struct {})", fs.join(" ")));
                    }
                    AdtKind::Enum(vs) => {
                        let vs = vs.clone();
                        self.add_type(&name, "(sub (struct (field i32)))".into());
                        for (i, v) in vs.iter().enumerate() {
                            let mut fs = vec!["(field i32)".to_string()];
                            for f in &v.fields {
                                let ft = self.prog.normalize_proj(f.ty.subst(args));
                                fs.push(format!("(field {})", self.vt(&ft)));
                            }
                            self.add_type(&format!("{name}#{i}"), format!("(sub final {name} (struct {}))", fs.join(" ")));
                        }
                    }
                }
            }
            _ => {}
        }
        name
    }

    fn fn_type(&mut self, ps: &[Ty], r: &Ty, first: &str) -> String {
        let mut params: Vec<String> = Vec::new();
        if !first.is_empty() {
            params.push(first.to_string());
        }
        for p in ps {
            params.push(self.vt(p));
        }
        let rv = self.vt(r);
        let key = format!("{}->{}", params.join(","), rv);
        let name = format!("$ft.{}", sanitize(&key.replace(['(', ')', ' ', ','], "_")));
        let name = if name.len() > 120 {
            let mut h: u64 = 1469598103934665603;
            for b in key.bytes() {
                h = (h ^ b as u64).wrapping_mul(1099511628211);
            }
            format!("$ft.h{h:x}")
        } else {
            name
        };
        let def = format!("(func{}{})", params.iter().map(|p| format!(" (param {p})")).collect::<String>(), format!(" (result {rv})"));
        self.add_type(&name, def);
        name
    }

    fn box_type(&mut self, t: &Ty) -> String {
        let v = self.vt(t);
        let name = format!("$box.{}", sanitize(&self.mangle(t)));
        self.add_type(&name, format!("(struct (field (mut {v})))"));
        name
    }

    fn pbox_type(&mut self, t: &Ty) -> String {
        let v = self.vt(t);
        let name = format!("$pbox.{}", sanitize(&self.mangle(t)));
        self.add_type(&name, format!("(struct (field {v}))"));
        name
    }

    fn env_type(&mut self, func: usize) -> String {
        let name = format!("$env{func}");
        if self.defined.contains(&name) {
            return name;
        }
        let f = self.g.funcs[func].as_ref().unwrap();
        let caps: Vec<LocalInfo> = {
            let mut v: Vec<&LocalInfo> = f.locals.iter().filter(|l| l.capture.is_some()).collect();
            v.sort_by_key(|l| l.capture.unwrap());
            v.into_iter().cloned().collect()
        };
        let mut fs = Vec::new();
        for c in &caps {
            let t = if c.boxed { format!("(ref {})", self.box_type(&c.ty)) } else { self.vt(&c.ty) };
            fs.push(format!("(field {t})"));
        }
        self.add_type(&name, format!("(struct {})", fs.join(" ")));
        name
    }

    /// Methods of a dyn type in vtable order: (name, param types without self, ret).
    fn dyn_sigs(&self, tid: TraitId, targs: &[Ty], assoc: &[(String, Ty)], dyn_ty: &Ty) -> Vec<(String, Vec<Ty>, Ty)> {
        let mut out: Vec<(String, Vec<Ty>, Ty)> = Vec::new();
        for t in self.prog.trait_closure(tid) {
            let tr_args: Vec<Ty> = if t == tid {
                targs.to_vec()
            } else {
                self.prog.traits[tid]
                    .supertraits
                    .iter()
                    .find(|s| s.trait_id == t)
                    .map(|s| {
                        let mut m = vec![dyn_ty.clone()];
                        m.extend(targs.iter().cloned());
                        s.args.iter().map(|a| a.subst(&m)).collect()
                    })
                    .unwrap_or_default()
            };
            let mut m = vec![dyn_ty.clone()];
            m.extend(tr_args);
            for (name, fid) in &self.prog.traits[t].methods {
                if out.iter().any(|(n, _, _)| n == name) || self.prog.vtable_ok(*fid).is_err() {
                    continue;
                }
                let f = &self.prog.fns[*fid];
                let ps = f.params.iter().skip(1).map(|(_, t)| replace_proj_dyn(&t.subst(&m), assoc)).collect();
                let r = replace_proj_dyn(&f.ret.subst(&m), assoc);
                out.push((name.clone(), ps, r));
            }
        }
        out
    }

    /// The name of a passive data segment holding `bytes`. Names come from the contents,
    /// so that functions generated in parallel agree on them.
    fn data_seg(&mut self, bytes: &[u8]) -> String {
        if let Some(n) = self.data_map.get(bytes) {
            return n.clone();
        }
        use std::hash::{Hash, Hasher};
        let mut name = String::from("$d.");
        for salt in [0u8, 1] {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            (salt, bytes).hash(&mut h);
            let _ = write!(name, "{:016x}", h.finish());
        }
        while !self.data_names.insert(name.clone()) {
            name.push('x');
        }
        self.data.push((name.clone(), bytes.to_vec()));
        self.data_map.insert(bytes.to_vec(), name.clone());
        name
    }

    fn add_ref(&mut self, f: String) {
        if !self.refs.contains(&f) {
            self.refs.insert(f.clone());
            self.new_refs.push(f);
        }
    }

    fn str_lit(&mut self, st: &mut FnState, s: &str) {
        let d = self.data_seg(s.as_bytes());
        let sn = self.tname(&Ty::Str);
        st.emit(&format!("i32.const 0 i32.const {} array.new_data {sn} {d}", s.len()));
    }

    fn fname(&self, inst: &FnInst) -> String {
        let idx = self.g.insts[inst];
        self.func_names[idx].clone()
    }

    // ---------------- functions ----------------
    fn gen_func(&mut self, idx: usize, f: &Func) {
        let name = self.func_names[idx].clone();
        if let Some((m, n)) = &f.extern_ {
            self.gen_extern(&name, f, m, n);
            return;
        }
        let mut st = FnState { out: String::new(), indent: 1, locals: f.locals.clone(), local_names: Vec::new(), temps: Vec::new(), label: 0, loop_types: HashMap::new(), ovf_tmps: None, ranges: Default::default() };
        for (i, l) in f.locals.iter().enumerate() {
            st.local_names.push(format!("$l{i}.{}", sanitize(&l.name)));
        }
        let mut header = format!("(func {name}");
        if f.is_closure {
            let ps: Vec<Ty> = f.params.iter().map(|&p| f.locals[p].ty.clone()).collect();
            let ft = self.fn_type(&ps, &f.ret, "(ref null struct)");
            let _ = write!(header, " (type {ft})");
            header.push_str(" (param $env (ref null struct))");
        }
        for &p in &f.params {
            let t = self.vt(&f.locals[p].ty);
            let _ = write!(header, " (param {} {t})", st.local_names[p]);
        }
        let rv = self.vt(&f.ret);
        let _ = write!(header, " (result {rv})");
        // closure captures
        if f.is_closure {
            let env = self.env_type(idx);
            let has_caps = f.locals.iter().any(|l| l.capture.is_some());
            if has_caps {
                st.emit(&format!("local.get $env ref.cast (ref {env}) local.set $envc"));
                st.temps.push(("$envc".into(), format!("(ref null {env})")));
                for (i, l) in f.locals.iter().enumerate() {
                    if let Some(k) = l.capture {
                        st.emit(&format!("local.get $envc struct.get {env} {k} local.set {}", st.local_names[i]));
                    }
                }
            }
        }
        self.gen_expr(&mut st, &f.body);
        let mut out = header;
        out.push('\n');
        for (i, l) in f.locals.iter().enumerate() {
            if l.is_param {
                continue;
            }
            let t = if l.boxed { format!("(ref null {})", self.box_type(&l.ty)) } else { self.vt_null(&l.ty) };
            let _ = writeln!(out, "  (local {} {t})", st.local_names[i]);
        }
        for (n, t) in &st.temps {
            let _ = writeln!(out, "  (local {n} {t})");
        }
        out.push_str(&st.out);
        out.push_str(")\n");
        self.funcs.push(out);
        if let Some(e) = &f.export {
            // components export only the canonical ABI wrappers generated from the world
            if !self.component || f.name.starts_with("__wit_") {
                self.gen_export_wrapper(&name, f, e);
            }
        }
    }

    fn funcs_tail(&mut self) -> &mut String {
        &mut self.tail
    }

    fn raw_vt(&mut self, t: &Ty) -> Option<String> {
        match t {
            Ty::Unit => None,
            _ => Some(self.vt(t)),
        }
    }

    fn gen_export_wrapper(&mut self, name: &str, f: &Func, export: &str) {
        let mut s = format!("(func $export.{}", sanitize(export));
        let _ = write!(s, " (export {})", wat_str(export.as_bytes()));
        for (i, &p) in f.params.iter().enumerate() {
            let t = self.vt(&f.locals[p].ty);
            let _ = write!(s, " (param $p{i} {t})");
        }
        let rv = self.raw_vt(&f.ret);
        if let Some(r) = &rv {
            let _ = write!(s, " (result {r})");
        }
        s.push('\n');
        for i in 0..f.params.len() {
            let _ = writeln!(s, "  local.get $p{i}");
        }
        let _ = writeln!(s, "  call {name}");
        if rv.is_none() {
            s.push_str("  drop\n");
        }
        s.push_str(")\n");
        self.funcs.push(s);
    }

    fn gen_extern(&mut self, name: &str, f: &Func, module: &str, field: &str) {
        let imp_name = format!("$ext.{}", &name[1..]);
        let mut ip = Vec::new();
        for &p in &f.params {
            let t = &f.locals[p].ty;
            if *t == Ty::Str {
                ip.push("i32".to_string());
                ip.push("i32".to_string());
            } else {
                ip.push(self.vt(t));
            }
        }
        let rv = self.raw_vt(&f.ret);
        self.imports.push(format!(
            "(import {} {} (func {imp_name}{}{}))",
            wat_str(module.as_bytes()),
            wat_str(field.as_bytes()),
            ip.iter().map(|p| format!(" (param {p})")).collect::<String>(),
            rv.as_ref().map(|r| format!(" (result {r})")).unwrap_or_default()
        ));
        let mut s = format!("(func {name}");
        for (i, &p) in f.params.iter().enumerate() {
            let t = self.vt(&f.locals[p].ty);
            let _ = write!(s, " (param $p{i} {t})");
        }
        let full_rv = self.vt(&f.ret);
        let _ = write!(s, " (result {full_rv})\n  (local $off i32) (local $n i32)\n");
        for (i, &p) in f.params.iter().enumerate() {
            if f.locals[p].ty == Ty::Str {
                let _ = writeln!(s, "  local.get $off local.get $p{i} local.get $off call $rt_to_mem_at local.tee $n local.get $off local.get $n i32.add local.set $off");
                // stack: off, n
            } else {
                let _ = writeln!(s, "  local.get $p{i}");
            }
        }
        let _ = writeln!(s, "  call {imp_name}");
        if rv.is_none() {
            s.push_str("  i32.const 0\n");
        }
        s.push_str(")\n");
        self.funcs.push(s);
    }

    fn temp(&mut self, st: &mut FnState, t: &Ty) -> String {
        let n = format!("$t{}", st.temps.len());
        let ty = self.vt_null(t);
        st.temps.push((n.clone(), ty));
        n
    }

    fn temp_raw(&mut self, st: &mut FnState, ty: &str) -> String {
        let n = format!("$t{}", st.temps.len());
        st.temps.push((n.clone(), ty.to_string()));
        n
    }

    fn get_temp(&mut self, st: &mut FnState, n: &str, t: &Ty) {
        if is_ref(t) {
            st.emit(&format!("local.get {n} ref.as_non_null"));
        } else {
            st.emit(&format!("local.get {n}"));
        }
    }

    fn read_local(&mut self, st: &mut FnState, id: LocalId) {
        let l = st.locals[id].clone();
        let n = st.local_names[id].clone();
        if l.boxed {
            let b = self.box_type(&l.ty);
            st.emit(&format!("local.get {n} ref.as_non_null struct.get {b} 0"));
        } else if l.is_param || !is_ref(&l.ty) {
            st.emit(&format!("local.get {n}"));
        } else {
            st.emit(&format!("local.get {n} ref.as_non_null"));
        }
    }

    /// Store the value on the stack into a local (initializing a box if needed).
    fn init_local(&mut self, st: &mut FnState, id: LocalId) {
        let l = st.locals[id].clone();
        let n = st.local_names[id].clone();
        if l.boxed {
            let b = self.box_type(&l.ty);
            st.emit(&format!("struct.new {b} local.set {n}"));
        } else {
            st.emit(&format!("local.set {n}"));
        }
    }

    fn gen_expr(&mut self, st: &mut FnState, e: &Expr) {
        self.gen_expr_inner(st, e);
        if e.ty == Ty::Never && !matches!(e.kind, ExprKind::Unreachable | ExprKind::Return(_) | ExprKind::Break(..) | ExprKind::Continue(_)) {
            st.emit("unreachable");
        }
    }

    fn gen_expr_inner(&mut self, st: &mut FnState, e: &Expr) {
        match &e.kind {
            ExprKind::Lit(l) => self.gen_lit(st, l, &e.ty),
            ExprKind::Local(id) => self.read_local(st, *id),
            ExprKind::SetLocal(id, v) => {
                let l = st.locals[*id].clone();
                let n = st.local_names[*id].clone();
                if l.boxed {
                    let b = self.box_type(&l.ty);
                    st.emit(&format!("local.get {n} ref.as_non_null"));
                    self.gen_expr(st, v);
                    st.emit(&format!("struct.set {b} 0"));
                } else {
                    self.gen_expr(st, v);
                    st.emit(&format!("local.set {n}"));
                }
                st.ranges.kill(*id);
                st.emit("i32.const 0");
            }
            ExprKind::Call(inst, args) => {
                for a in args {
                    self.gen_expr(st, a);
                }
                let n = self.fname(inst);
                st.emit(&format!("call {n}"));
            }
            ExprKind::Intrinsic(name, targs, args) => self.gen_intrinsic(st, name, targs, args, &e.ty),
            ExprKind::ArrayGuard(array, index) => {
                let a = self.temp(st, &array.ty);
                let i = self.temp(st, &index.ty);
                self.gen_expr(st, array);
                st.emit(&format!("local.set {a}"));
                self.gen_expr(st, index);
                st.emit(&format!("local.tee {i} local.get {a} array.len i32.ge_u if"));
                // Take the original Wasm trap on failure. The in-bounds path reads only
                // the array length, and both operands are evaluated exactly once.
                let Ty::Array(elem) = &array.ty else { unreachable!("array guard requires an array") };
                let an = self.tname(&array.ty);
                let op = self.array_get_op(elem, &an);
                st.emit(&format!("  local.get {a} local.get {i} {op} drop"));
                st.emit("end i32.const 0");
            }
            ExprKind::CallIndirect(f, args) => {
                let Ty::Fn(ps, r) = &f.ty else {
                    st.emit("unreachable");
                    return;
                };
                let clo = self.tname(&f.ty);
                let ft = self.fn_type(ps, r, "(ref null struct)");
                let t = self.temp(st, &f.ty);
                self.gen_expr(st, f);
                st.emit(&format!("local.set {t}"));
                st.emit(&format!("local.get {t} ref.as_non_null struct.get {clo} 1"));
                for a in args {
                    self.gen_expr(st, a);
                }
                st.emit(&format!("local.get {t} ref.as_non_null struct.get {clo} 0 call_ref {ft}"));
            }
            ExprKind::FnValue(inst) => {
                let shim = self.fn_shim(inst, &e.ty);
                let clo = self.tname(&e.ty);
                self.add_ref(shim.clone());
                st.emit(&format!("ref.func {shim} ref.null struct struct.new {clo}"));
            }
            ExprKind::Closure { func, captures } => {
                let clo = self.tname(&e.ty);
                let fname = self.func_names[*func].clone();
                self.add_ref(fname.clone());
                st.emit(&format!("ref.func {fname}"));
                if captures.is_empty() {
                    st.emit("ref.null struct");
                } else {
                    for &c in captures {
                        let l = st.locals[c].clone();
                        let n = st.local_names[c].clone();
                        if l.boxed || l.is_param || !is_ref(&l.ty) {
                            st.emit(&format!("local.get {n}"));
                            if l.boxed {
                                st.emit("ref.as_non_null");
                            }
                        } else {
                            st.emit(&format!("local.get {n} ref.as_non_null"));
                        }
                    }
                    let env = self.env_type(*func);
                    st.emit(&format!("struct.new {env}"));
                }
                st.emit(&format!("struct.new {clo}"));
            }
            ExprKind::StructNew(vals) | ExprKind::TupleNew(vals) => {
                for v in vals {
                    self.gen_expr(st, v);
                }
                let n = self.tname(&e.ty);
                st.emit(&format!("struct.new {n}"));
            }
            ExprKind::EnumNew(vi, vals) if vals.is_empty() => {
                let v = format!("{}#{vi}", self.tname(&e.ty));
                let next = self.unit_variants.len();
                let g = self.unit_variants.entry(v.clone()).or_insert_with(|| format!("$unitv.{}", &v[1..])).clone();
                if self.unit_variants.len() > next {
                    self.globals.push(format!("(global {g} (ref {v}) (struct.new {v} (i32.const {vi})))"));
                }
                st.emit(&format!("global.get {g}"));
            }
            ExprKind::EnumNew(vi, vals) => {
                let n = self.tname(&e.ty);
                st.emit(&format!("i32.const {vi}"));
                for v in vals {
                    self.gen_expr(st, v);
                }
                st.emit(&format!("struct.new {n}#{vi}"));
            }
            ExprKind::ArrayLit(vals) => {
                for v in vals {
                    self.gen_expr(st, v);
                }
                let n = self.tname(&e.ty);
                st.emit(&format!("array.new_fixed {n} {}", vals.len()));
            }
            ExprKind::Field(b, _, i) => {
                self.gen_expr(st, b);
                let n = self.tname(&b.ty);
                st.emit(&format!("struct.get {n} {i}"));
            }
            ExprKind::SetField(b, i, v) => {
                self.gen_expr(st, b);
                self.gen_expr(st, v);
                let n = self.tname(&b.ty);
                st.emit(&format!("struct.set {n} {i}"));
                st.emit("i32.const 0");
            }
            ExprKind::Block(stmts, tail) => {
                for s in stmts {
                    match s {
                        Stmt::Expr(x) => {
                            self.gen_expr(st, x);
                            st.emit("drop");
                        }
                        Stmt::Let(p, init) => {
                            if let PatKind::Bind(id, None) = &p.kind {
                                self.gen_expr(st, init);
                                self.init_local(st, *id);
                            } else {
                                let t = self.temp(st, &init.ty);
                                self.gen_expr(st, init);
                                st.emit(&format!("local.set {t}"));
                                let fail = st.label();
                                st.emit(&format!("block {fail}"));
                                st.indent += 1;
                                self.gen_pat(st, p, &t, &fail);
                                st.indent -= 1;
                                st.emit("end");
                            }
                        }
                    }
                }
                match tail {
                    Some(t) => self.gen_expr(st, t),
                    None => {
                        if e.ty == Ty::Never {
                            st.emit("unreachable");
                        } else {
                            st.emit("i32.const 0");
                        }
                    }
                }
            }
            ExprKind::If(c, t, el) => {
                self.gen_expr(st, c);
                let saved = st.ranges.save();
                let rv = self.vt(&e.ty);
                st.emit(&format!("(if (result {rv})"));
                st.indent += 1;
                st.emit("(then");
                st.indent += 1;
                st.ranges.assume(c, true, &st.locals);
                self.gen_expr(st, t);
                st.ranges.restore(&saved);
                st.indent -= 1;
                st.emit(")");
                st.emit("(else");
                st.indent += 1;
                st.ranges.assume(c, false, &st.locals);
                self.gen_expr(st, el);
                st.ranges.restore(&saved);
                st.indent -= 1;
                st.emit(")");
                st.indent -= 1;
                st.emit(")");
            }
            ExprKind::Match(s, arms) => {
                let t = self.temp(st, &s.ty);
                self.gen_expr(st, s);
                st.emit(&format!("local.set {t}"));
                let end = st.label();
                let rv = self.vt(&e.ty);
                st.emit(&format!("block {end} (result {rv})"));
                st.indent += 1;
                for a in arms {
                    let next = st.label();
                    st.emit(&format!("block {next}"));
                    st.indent += 1;
                    self.gen_pat(st, &a.pat, &t, &next);
                    if let Some(g) = &a.guard {
                        self.gen_expr(st, g);
                        st.emit(&format!("i32.eqz br_if {next}"));
                    }
                    self.gen_expr(st, &a.body);
                    st.emit(&format!("br {end}"));
                    st.indent -= 1;
                    st.emit("end");
                }
                st.emit("unreachable");
                st.indent -= 1;
                st.emit("end");
            }
            ExprKind::Loop(label, body) => {
                st.loop_types.insert(*label, e.ty.clone());
                let rv = self.vt(&e.ty);
                st.emit(&format!("block $brk{label} (result {rv})"));
                st.indent += 1;
                st.emit(&format!("loop $cont{label}"));
                st.indent += 1;
                st.ranges.enter_loop(body);
                self.gen_expr(st, body);
                st.emit(&format!("drop br $cont{label}"));
                st.indent -= 1;
                st.emit("end");
                st.emit("unreachable");
                st.indent -= 1;
                st.emit("end");
            }
            ExprKind::Break(label, v) => {
                match v {
                    Some(v) => self.gen_expr(st, v),
                    None => st.emit("i32.const 0"),
                }
                st.emit(&format!("br $brk{label}"));
            }
            ExprKind::Continue(label) => st.emit(&format!("br $cont{label}")),
            ExprKind::Return(v) => {
                self.gen_expr(st, v);
                st.emit("return");
            }
            ExprKind::Prim(op, t, args) => self.gen_prim(st, *op, t, args),
            ExprKind::Cast(v) => {
                self.gen_expr(st, v);
                self.gen_cast(st, &v.ty, &e.ty, false);
            }
            ExprKind::StrConcat(parts) => {
                let sn = self.tname(&Ty::Str);
                let mut temps = Vec::new();
                for p in parts {
                    let t = self.temp(st, &Ty::Str);
                    self.gen_expr(st, p);
                    st.emit(&format!("local.set {t}"));
                    temps.push(t);
                }
                let total = self.temp_raw(st, "i32");
                let off = self.temp_raw(st, "i32");
                let res = self.temp(st, &Ty::Str);
                st.emit("i32.const 0");
                for t in &temps {
                    st.emit(&format!("local.get {t} ref.as_non_null array.len i32.add"));
                }
                st.emit(&format!("local.set {total} local.get {total} array.new_default {sn} local.set {res} i32.const 0 local.set {off}"));
                for t in &temps {
                    st.emit(&format!(
                        "local.get {res} ref.as_non_null local.get {off} local.get {t} ref.as_non_null i32.const 0 local.get {t} ref.as_non_null array.len array.copy {sn} {sn} local.get {off} local.get {t} ref.as_non_null array.len i32.add local.set {off}"
                    ));
                }
                st.emit(&format!("local.get {res} ref.as_non_null"));
            }
            ExprKind::DynNew(v, tr) => {
                self.gen_expr(st, v);
                if !is_ref(&v.ty) {
                    let pb = self.pbox_type(&v.ty);
                    st.emit(&format!("struct.new {pb}"));
                }
                let g = self.vtable_global(&v.ty, tr, &e.ty);
                let dn = self.tname(&e.ty);
                st.emit(&format!("global.get {g} struct.new {dn}"));
            }
            ExprKind::DynCall { recv, method, args, .. } => {
                let Ty::Dyn(tid, targs, assoc) = &recv.ty else {
                    st.emit("unreachable");
                    return;
                };
                let sigs = self.dyn_sigs(*tid, targs, assoc, &recv.ty);
                let k = sigs.iter().position(|(n, _, _)| n == method).unwrap_or(0);
                let (_, ps, r) = sigs[k].clone();
                let ft = self.fn_type(&ps, &r, "anyref");
                let dn = self.tname(&recv.ty);
                let vt_name = format!("$vt.{}", sanitize(&self.mangle(&recv.ty)));
                let t = self.temp(st, &recv.ty);
                self.gen_expr(st, recv);
                st.emit(&format!("local.set {t} local.get {t} ref.as_non_null struct.get {dn} 0"));
                for a in args {
                    self.gen_expr(st, a);
                }
                st.emit(&format!("local.get {t} ref.as_non_null struct.get {dn} 1 struct.get {vt_name} {k} call_ref {ft}"));
            }
            ExprKind::Discard(v) => {
                self.gen_expr(st, v);
                st.emit("drop i32.const 0");
            }
            ExprKind::Unreachable => st.emit("unreachable"),
        }
    }

    fn gen_lit(&mut self, st: &mut FnState, l: &Lit, ty: &Ty) {
        match l {
            Lit::Int(v) => match ty {
                Ty::Int(i) if i.is64() => st.emit(&format!("i64.const {}", *v as i64)),
                Ty::Float(FloatTy::F64) => st.emit(&format!("f64.const {}", f64_lit(*v as f64))),
                Ty::Float(FloatTy::F32) => st.emit(&format!("f32.const {}", f64_lit(*v as f64))),
                _ => st.emit(&format!("i32.const {}", *v as i64 as i32)),
            },
            Lit::Float(f) => match ty {
                Ty::Float(FloatTy::F32) => st.emit(&format!("f32.const {}", f64_lit(*f))),
                _ => st.emit(&format!("f64.const {}", f64_lit(*f))),
            },
            Lit::Bool(b) => st.emit(&format!("i32.const {}", *b as i32)),
            Lit::Char(c) => st.emit(&format!("i32.const {}", *c as u32)),
            Lit::Str(s) => self.str_lit(st, s),
            Lit::Unit => st.emit("i32.const 0"),
        }
    }

    // ---------------- patterns ----------------
    /// Test the value in local `src` against `p`; branch to `fail` on mismatch.
    fn gen_pat(&mut self, st: &mut FnState, p: &Pat, src: &str, fail: &str) {
        match &p.kind {
            PatKind::Wild => {}
            PatKind::Bind(id, sub) => {
                self.get_temp(st, src, &p.ty);
                self.init_local(st, *id);
                if let Some(s) = sub {
                    self.gen_pat(st, s, src, fail);
                }
            }
            PatKind::Lit(l) => {
                self.get_temp(st, src, &p.ty);
                match l {
                    Lit::Str(s) => {
                        self.str_lit(st, s);
                        st.emit(&format!("call $rt_str_eq i32.eqz br_if {fail}"));
                    }
                    _ => {
                        self.gen_lit(st, l, &p.ty);
                        let pre = self.num_prefix(&p.ty);
                        st.emit(&format!("{pre}.ne br_if {fail}"));
                    }
                }
            }
            PatKind::Range(a, b, inc) => {
                let pre = self.num_prefix(&p.ty);
                let signed = match &p.ty {
                    Ty::Int(i) => i.signed(),
                    _ => false,
                };
                let float = matches!(p.ty, Ty::Float(_));
                let sfx = |s: &str| if float { s.to_string() } else if signed { format!("{s}_s") } else { format!("{s}_u") };
                self.get_temp(st, src, &p.ty);
                self.gen_lit(st, a, &p.ty);
                st.emit(&format!("{pre}.{} br_if {fail}", sfx("lt")));
                self.get_temp(st, src, &p.ty);
                self.gen_lit(st, b, &p.ty);
                st.emit(&format!("{pre}.{} br_if {fail}", if *inc { sfx("gt") } else { sfx("ge") }));
            }
            PatKind::Tuple(ps) => {
                let tn = self.tname(&p.ty);
                for (i, sp) in ps.iter().enumerate() {
                    if matches!(sp.kind, PatKind::Wild) {
                        continue;
                    }
                    let t = self.temp(st, &sp.ty);
                    st.emit(&format!("local.get {src} ref.as_non_null struct.get {tn} {i} local.set {t}"));
                    self.gen_pat(st, sp, &t, fail);
                }
            }
            PatKind::Struct(fs) => {
                let tn = self.tname(&p.ty);
                for (i, sp) in fs {
                    if matches!(sp.kind, PatKind::Wild) {
                        continue;
                    }
                    let t = self.temp(st, &sp.ty);
                    st.emit(&format!("local.get {src} ref.as_non_null struct.get {tn} {i} local.set {t}"));
                    self.gen_pat(st, sp, &t, fail);
                }
            }
            PatKind::Variant(vi, fs) => {
                let tn = self.tname(&p.ty);
                st.emit(&format!("local.get {src} ref.as_non_null struct.get {tn} 0 i32.const {vi} i32.ne br_if {fail}"));
                let subs: Vec<&(usize, Pat)> = fs.iter().filter(|(_, sp)| !matches!(sp.kind, PatKind::Wild)).collect();
                if !subs.is_empty() {
                    let vn = format!("{tn}#{vi}");
                    let tv = self.temp_raw(st, &format!("(ref null {vn})"));
                    st.emit(&format!("local.get {src} ref.cast (ref {vn}) local.set {tv}"));
                    for (i, sp) in subs {
                        let t = self.temp(st, &sp.ty);
                        st.emit(&format!("local.get {tv} struct.get {vn} {} local.set {t}", i + 1));
                        self.gen_pat(st, sp, &t, fail);
                    }
                }
            }
            PatKind::Or(alts) => {
                let ok = st.label();
                st.emit(&format!("block {ok}"));
                st.indent += 1;
                for a in alts {
                    let next = st.label();
                    st.emit(&format!("block {next}"));
                    st.indent += 1;
                    self.gen_pat(st, a, src, &next);
                    st.emit(&format!("br {ok}"));
                    st.indent -= 1;
                    st.emit("end");
                }
                st.emit(&format!("br {fail}"));
                st.indent -= 1;
                st.emit("end");
            }
            PatKind::List(ps, rest) => {
                let Ty::Adt(lid, largs) = &p.ty else { return };
                let (len_i, data_i) = self.prog.list_field_indices(*lid);
                let ln = self.tname(&p.ty);
                let elem = largs[0].clone();
                let arr_ty = Ty::Array(Box::new(elem.clone()));
                let an = self.tname(&arr_ty);
                let n = ps.len();
                st.emit(&format!("local.get {src} ref.as_non_null struct.get {ln} {len_i} i32.const {n}"));
                if rest.is_some() {
                    st.emit(&format!("i32.lt_s br_if {fail}"));
                } else {
                    st.emit(&format!("i32.ne br_if {fail}"));
                }
                for (i, sp) in ps.iter().enumerate() {
                    if matches!(sp.kind, PatKind::Wild) {
                        continue;
                    }
                    let t = self.temp(st, &elem);
                    let get = self.array_get_op(&elem, &an);
                    st.emit(&format!("local.get {src} ref.as_non_null struct.get {ln} {data_i} i32.const {i} {get} local.set {t}"));
                    self.gen_pat(st, sp, &t, fail);
                }
                if let Some(Some(rid)) = rest {
                    let newlen = self.temp_raw(st, "i32");
                    let arr = self.temp(st, &arr_ty);
                    st.emit(&format!("local.get {src} ref.as_non_null struct.get {ln} {len_i} i32.const {n} i32.sub local.set {newlen}"));
                    st.emit(&format!("local.get {newlen} array.new_default {an} local.set {arr}"));
                    st.emit(&format!("local.get {arr} ref.as_non_null i32.const 0 local.get {src} ref.as_non_null struct.get {ln} {data_i} i32.const {n} local.get {newlen} array.copy {an} {an}"));
                    if len_i == 0 {
                        st.emit(&format!("local.get {newlen} local.get {arr} ref.as_non_null struct.new {ln}"));
                    } else {
                        st.emit(&format!("local.get {arr} ref.as_non_null local.get {newlen} struct.new {ln}"));
                    }
                    self.init_local(st, *rid);
                }
            }
        }
    }

    fn array_get_op(&mut self, elem: &Ty, an: &str) -> String {
        match elem {
            Ty::Int(IntTy::I8 | IntTy::I16) => format!("array.get_s {an}"),
            Ty::Int(IntTy::U8 | IntTy::U16) | Ty::Bool => format!("array.get_u {an}"),
            t if is_ref(t) => format!("array.get {an} ref.as_non_null"),
            _ => format!("array.get {an}"),
        }
    }

    fn num_prefix(&self, t: &Ty) -> &'static str {
        match t {
            Ty::Int(i) if i.is64() => "i64",
            Ty::Float(FloatTy::F64) => "f64",
            Ty::Float(FloatTy::F32) => "f32",
            _ => "i32",
        }
    }

    // ---------------- primitives ----------------
    fn gen_prim(&mut self, st: &mut FnState, op: PrimOp, t: &Ty, args: &[Expr]) {
        for a in args {
            self.gen_expr(st, a);
        }
        let pre = self.num_prefix(t);
        match t {
            Ty::Float(_) => {
                let s = match op {
                    PrimOp::Add => "add",
                    PrimOp::Sub => "sub",
                    PrimOp::Mul => "mul",
                    PrimOp::Div => "div",
                    PrimOp::Rem => {
                        st.emit(if pre == "f64" { "call $rt_frem64" } else { "call $rt_frem32" });
                        return;
                    }
                    PrimOp::Eq => "eq",
                    PrimOp::Ne => "ne",
                    PrimOp::Lt => "lt",
                    PrimOp::Le => "le",
                    PrimOp::Gt => "gt",
                    PrimOp::Ge => "ge",
                    PrimOp::Neg => "neg",
                    _ => {
                        st.emit("unreachable");
                        return;
                    }
                };
                st.emit(&format!("{pre}.{s}"));
            }
            Ty::Int(it) => {
                let signed = it.signed();
                let su = if signed { "_s" } else { "_u" };
                match op {
                    PrimOp::Add | PrimOp::Sub | PrimOp::Mul => {
                        let o = match op {
                            PrimOp::Add => "add",
                            PrimOp::Sub => "sub",
                            _ => "mul",
                        };
                        if st.ranges.cannot_overflow(op, *it, &args[0], &args[1]) {
                            st.emit(&format!("{pre}.{o}"));
                        } else if *it == IntTy::I32 && o != "mul" {
                            // inline: r = a op b; overflow iff the sign bit of
                            // (a ^ r) & (b ^ r) (add) or (a ^ b) & (a ^ r) (sub) is set
                            let (a, b, r) = match &st.ovf_tmps {
                                Some(t) => t.clone(),
                                None => {
                                    let t = (self.temp_raw(st, "i32"), self.temp_raw(st, "i32"), self.temp_raw(st, "i32"));
                                    st.ovf_tmps = Some(t.clone());
                                    t
                                }
                            };
                            let mix = if o == "add" { format!("local.get {a} local.get {r} i32.xor local.get {b} local.get {r} i32.xor") } else { format!("local.get {a} local.get {b} i32.xor local.get {a} local.get {r} i32.xor") };
                            st.emit(&format!("local.set {b} local.tee {a} local.get {b} i32.{o} local.set {r} {mix} i32.and i32.const 0 i32.lt_s (if (then call $rt_overflow)) local.get {r}"));
                        } else {
                            st.emit(&format!("call $chk_{o}_{}", it.name()));
                        }
                    }
                    PrimOp::Neg => {
                        // 0 - x
                        let tmp = self.temp(st, t);
                        st.emit(&format!("local.set {tmp} {pre}.const 0 local.get {tmp} call $chk_sub_{}", it.name()));
                    }
                    PrimOp::Div => st.emit(&format!("{pre}.div{su}")),
                    PrimOp::Rem => st.emit(&format!("{pre}.rem{su}")),
                    PrimOp::BitAnd => st.emit(&format!("{pre}.and")),
                    PrimOp::BitOr => st.emit(&format!("{pre}.or")),
                    PrimOp::BitXor => st.emit(&format!("{pre}.xor")),
                    PrimOp::Shl => {
                        st.emit(&format!("{pre}.shl"));
                        self.wrap_small(st, *it);
                    }
                    PrimOp::Shr => st.emit(&format!("{pre}.shr{su}")),
                    PrimOp::Not => {
                        match it {
                            IntTy::U8 => st.emit("i32.const 255 i32.xor"),
                            IntTy::U16 => st.emit("i32.const 65535 i32.xor"),
                            _ => st.emit(&format!("{pre}.const -1 {pre}.xor")),
                        }
                    }
                    PrimOp::Eq => st.emit(&format!("{pre}.eq")),
                    PrimOp::Ne => st.emit(&format!("{pre}.ne")),
                    PrimOp::Lt => st.emit(&format!("{pre}.lt{su}")),
                    PrimOp::Le => st.emit(&format!("{pre}.le{su}")),
                    PrimOp::Gt => st.emit(&format!("{pre}.gt{su}")),
                    PrimOp::Ge => st.emit(&format!("{pre}.ge{su}")),
                }
            }
            Ty::Bool => match op {
                PrimOp::Not => st.emit("i32.eqz"),
                PrimOp::Eq => st.emit("i32.eq"),
                PrimOp::Ne => st.emit("i32.ne"),
                PrimOp::BitAnd => st.emit("i32.and"),
                PrimOp::BitOr => st.emit("i32.or"),
                PrimOp::BitXor => st.emit("i32.xor"),
                _ => st.emit("unreachable"),
            },
            Ty::Char => match op {
                PrimOp::Eq => st.emit("i32.eq"),
                PrimOp::Ne => st.emit("i32.ne"),
                PrimOp::Lt => st.emit("i32.lt_u"),
                PrimOp::Le => st.emit("i32.le_u"),
                PrimOp::Gt => st.emit("i32.gt_u"),
                PrimOp::Ge => st.emit("i32.ge_u"),
                _ => st.emit("unreachable"),
            },
            Ty::Unit => match op {
                PrimOp::Eq => st.emit("drop drop i32.const 1"),
                PrimOp::Ne => st.emit("drop drop i32.const 0"),
                _ => st.emit("unreachable"),
            },
            _ => st.emit("unreachable"),
        }
    }

    fn wrap_small(&mut self, st: &mut FnState, it: IntTy) {
        match it {
            IntTy::I8 => st.emit("i32.extend8_s"),
            IntTy::I16 => st.emit("i32.extend16_s"),
            IntTy::U8 => st.emit("i32.const 255 i32.and"),
            IntTy::U16 => st.emit("i32.const 65535 i32.and"),
            _ => {}
        }
    }

    /// Convert the value on the stack from `from` to `to`. `sat` selects
    /// saturating float-to-int truncation (always used).
    fn gen_cast(&mut self, st: &mut FnState, from: &Ty, to: &Ty, _sat: bool) {
        let norm = |t: &Ty| match t {
            Ty::Char => Ty::Int(IntTy::U32),
            Ty::Bool => Ty::Int(IntTy::U8),
            other => other.clone(),
        };
        let (from, to) = (norm(from), norm(to));
        if from == to {
            return;
        }
        match (&from, &to) {
            (Ty::Int(a), Ty::Int(b)) => {
                match (a.is64(), b.is64()) {
                    (false, true) => st.emit(if a.signed() { "i64.extend_i32_s" } else { "i64.extend_i32_u" }),
                    (true, false) => {
                        st.emit("i32.wrap_i64");
                        self.wrap_small(st, *b);
                    }
                    (true, true) => {}
                    (false, false) => {
                        if b.bits() < 32 {
                            self.wrap_small(st, *b);
                        }
                    }
                }
            }
            (Ty::Int(a), Ty::Float(f)) => {
                let fp = if *f == FloatTy::F64 { "f64" } else { "f32" };
                let ip = if a.is64() { "i64" } else { "i32" };
                let s = if a.signed() { "s" } else { "u" };
                st.emit(&format!("{fp}.convert_{ip}_{s}"));
            }
            (Ty::Float(f), Ty::Int(b)) => {
                let fp = if *f == FloatTy::F64 { "f64" } else { "f32" };
                let ip = if b.is64() { "i64" } else { "i32" };
                let s = if b.signed() || b.bits() < 32 { "s" } else { "u" };
                st.emit(&format!("{ip}.trunc_sat_{fp}_{s}"));
                if b.bits() < 32 {
                    // clamp then narrow
                    let (lo, hi) = (IntTy::min(*b), IntTy::max(*b));
                    let t = self.temp_raw(st, "i32");
                    st.emit(&format!("local.set {t} i32.const {lo} local.get {t} i32.const {lo} i32.gt_s select local.set {t} i32.const {hi} local.get {t} local.get {t} i32.const {hi} i32.gt_s select"));
                }
            }
            (Ty::Float(FloatTy::F32), Ty::Float(FloatTy::F64)) => st.emit("f64.promote_f32"),
            (Ty::Float(FloatTy::F64), Ty::Float(FloatTy::F32)) => st.emit("f32.demote_f64"),
            _ => {}
        }
    }

    fn fn_shim(&mut self, inst: &FnInst, fty: &Ty) -> String {
        if let Some(s) = self.shims.get(inst) {
            return s.clone();
        }
        let target = self.fname(inst);
        let name = format!("{target}.shim");
        let Ty::Fn(ps, r) = fty else { return name };
        let ft = self.fn_type(ps, r, "(ref null struct)");
        let mut s = format!("(func {name} (type {ft}) (param $env (ref null struct))");
        for (i, p) in ps.iter().enumerate() {
            let t = self.vt(p);
            let _ = write!(s, " (param $p{i} {t})");
        }
        let rv = self.vt(r);
        let _ = writeln!(s, " (result {rv})");
        for i in 0..ps.len() {
            let _ = writeln!(s, "  local.get $p{i}");
        }
        let _ = writeln!(s, "  call {target})");
        self.funcs.push(s);
        self.shims.insert(inst.clone(), name.clone());
        name
    }

    fn vtable_global(&mut self, concrete: &Ty, tr: &TraitRef, dyn_ty: &Ty) -> String {
        let key = (concrete.clone(), tr.clone());
        if let Some(g) = self.vtable_globals.get(&key) {
            return g.clone();
        }
        // named after the key, so that functions generated in parallel agree on the names
        let vkey = format!("{}.{}", sanitize(&self.mangle(concrete)), sanitize(&self.mangle(dyn_ty)));
        let gname = format!("$vtg.{vkey}");
        let Ty::Dyn(tid, targs, assoc) = dyn_ty else { return gname };
        let sigs = self.dyn_sigs(*tid, targs, assoc, dyn_ty);
        let methods = self.g.vtables.get(&key).cloned().unwrap_or_default();
        let vt_name = format!("$vt.{}", sanitize(&self.mangle(dyn_ty)));
        self.tname(dyn_ty);
        let mut fields = Vec::new();
        for (mi, (mname, ps, r)) in sigs.iter().enumerate() {
            let shim = format!("$vshim.{vkey}.{mi}");
            let ft = self.fn_type(ps, r, "anyref");
            let mut s = format!("(func {shim} (type {ft}) (param $self anyref)");
            for (i, p) in ps.iter().enumerate() {
                let t = self.vt(p);
                let _ = write!(s, " (param $p{i} {t})");
            }
            let rv = self.vt(r);
            let _ = writeln!(s, " (result {rv})");
            if is_ref(concrete) {
                let cn = self.tname(concrete);
                let _ = writeln!(s, "  local.get $self ref.cast (ref {cn})");
            } else {
                let pb = self.pbox_type(concrete);
                let _ = writeln!(s, "  local.get $self ref.cast (ref {pb}) struct.get {pb} 0");
            }
            for i in 0..ps.len() {
                let _ = writeln!(s, "  local.get $p{i}");
            }
            match methods.iter().find(|(n, _)| n == mname) {
                Some((_, inst)) => {
                    let target = self.fname(inst);
                    let _ = writeln!(s, "  call {target})");
                }
                None => {
                    let _ = writeln!(s, "  unreachable)");
                }
            }
            self.funcs.push(s);
            self.add_ref(shim.clone());
            fields.push(format!("(ref.func {shim})"));
        }
        self.globals.push(format!("(global {gname} (ref {vt_name}) (struct.new {vt_name} {}))", fields.join(" ")));
        self.vtable_globals.insert(key, gname.clone());
        gname
    }

    // ---------------- intrinsics ----------------
    fn gen_intrinsic(&mut self, st: &mut FnState, name: &str, targs: &[Ty], args: &[Expr], ret: &Ty) {
        let lit_arg = |i: usize| -> i128 {
            match &args.get(i).map(|a| &a.kind) {
                Some(ExprKind::Lit(Lit::Int(v))) => *v,
                _ => -1,
            }
        };
        match name {
            "array_new" => {
                self.gen_expr(st, &args[0]);
                let an = self.tname(ret);
                st.emit(&format!("array.new_default {an}"));
            }
            "array_len" => {
                self.gen_expr(st, &args[0]);
                st.emit("array.len");
            }
            "array_get" => {
                self.gen_expr(st, &args[0]);
                self.gen_expr(st, &args[1]);
                let at = args[0].ty.clone();
                let Ty::Array(elem) = &at else { st.emit("unreachable"); return };
                let an = self.tname(&at);
                let op = self.array_get_op(elem, &an);
                st.emit(&op);
            }
            "array_set" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                let an = self.tname(&args[0].ty);
                st.emit(&format!("array.set {an} i32.const 0"));
            }
            "array_copy" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                let an = self.tname(&args[0].ty);
                st.emit(&format!("array.copy {an} {an} i32.const 0"));
            }
            "select" => {
                // evaluate in source order, then a branch-free wasm select
                let c = self.temp_raw(st, "i32");
                self.gen_expr(st, &args[0]);
                st.emit(&format!("local.set {c}"));
                self.gen_expr(st, &args[1]);
                self.gen_expr(st, &args[2]);
                let rv = self.vt(ret);
                st.emit(&format!("local.get {c} select (result {rv})"));
            }
            "array_fill" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                let an = self.tname(&args[0].ty);
                st.emit(&format!("array.fill {an} i32.const 0"));
            }
            "bytes_copy_str" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                let an = self.tname(&Ty::Array(Box::new(Ty::Int(IntTy::U8))));
                let sn = self.tname(&Ty::Str);
                st.emit(&format!("array.copy {an} {sn} i32.const 0"));
            }
            "str_len" => {
                self.gen_expr(st, &args[0]);
                st.emit("array.len");
            }
            "str_byte" => {
                self.gen_expr(st, &args[0]);
                self.gen_expr(st, &args[1]);
                let sn = self.tname(&Ty::Str);
                st.emit(&format!("array.get_u {sn}"));
            }
            "str_slice" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                st.emit("call $rt_str_slice");
            }
            "str_from_bytes" => {
                let sn = self.tname(&Ty::Str);
                let an = self.tname(&Ty::Array(Box::new(Ty::Int(IntTy::U8))));
                let a = self.temp_raw(st, &format!("(ref null {an})"));
                let n = self.temp_raw(st, "i32");
                let r = self.temp(st, &Ty::Str);
                self.gen_expr(st, &args[0]);
                st.emit(&format!("local.set {a}"));
                self.gen_expr(st, &args[1]);
                st.emit(&format!("local.set {n} local.get {n} array.new_default {sn} local.set {r}"));
                st.emit(&format!("local.get {r} ref.as_non_null i32.const 0 local.get {a} ref.as_non_null i32.const 0 local.get {n} array.copy {sn} {an} local.get {r} ref.as_non_null"));
            }
            "str_eq" | "str_cmp" | "str_concat" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                st.emit(&format!("call $rt_{name}"));
            }
            "print" | "eprint" => {
                self.gen_expr(st, &args[0]);
                st.emit(&format!("i32.const {} call $rt_print i32.const 0", if name == "print" { 1 } else { 2 }));
            }
            "panic" => {
                self.gen_expr(st, &args[0]);
                st.emit("call $rt_panic unreachable");
            }
            "fmt_f64" | "fmt_f32" => {
                self.gen_expr(st, &args[0]);
                if name == "fmt_f32" {
                    st.emit("f64.promote_f32 i32.const 1");
                } else {
                    st.emit("i32.const 0");
                }
                st.emit("call $rt_fmt_f64");
            }
            "parse_f64" => {
                let t = self.temp(st, &Ty::Str);
                self.gen_expr(st, &args[0]);
                st.emit(&format!("local.set {t} i32.const 0 local.get {t} ref.as_non_null i32.const 0 call $rt_to_mem_at call $host_parse_f64"));
            }
            "host" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                st.emit("call $rt_host");
            }
            "host_ok" => st.emit("call $host_ok"),
            "mem_load" => {
                self.gen_expr(st, &args[0]);
                let ins = match &targs[0] {
                    Ty::Int(IntTy::I8) => "i32.load8_s",
                    Ty::Int(IntTy::U8) | Ty::Bool => "i32.load8_u",
                    Ty::Int(IntTy::I16) => "i32.load16_s",
                    Ty::Int(IntTy::U16) => "i32.load16_u",
                    Ty::Int(it) if it.is64() => "i64.load",
                    Ty::Float(FloatTy::F64) => "f64.load",
                    Ty::Float(FloatTy::F32) => "f32.load",
                    _ => "i32.load",
                };
                st.emit(ins);
            }
            "mem_store" => {
                self.gen_expr(st, &args[0]);
                self.gen_expr(st, &args[1]);
                let ins = match &targs[0] {
                    Ty::Int(IntTy::I8 | IntTy::U8) | Ty::Bool => "i32.store8",
                    Ty::Int(IntTy::I16 | IntTy::U16) => "i32.store16",
                    Ty::Int(it) if it.is64() => "i64.store",
                    Ty::Float(FloatTy::F64) => "f64.store",
                    Ty::Float(FloatTy::F32) => "f32.store",
                    _ => "i32.store",
                };
                st.emit(ins);
                st.emit("i32.const 0");
            }
            "cabi_alloc" => {
                st.emit("i32.const 0 i32.const 0");
                self.gen_expr(st, &args[1]);
                self.gen_expr(st, &args[0]);
                st.emit("call $cabi_realloc");
            }
            "cabi_mark" => st.emit("call $cabi_mark"),
            "cabi_base" => st.emit("i32.const 16777216"),
            "cabi_reset" => {
                self.gen_expr(st, &args[0]);
                st.emit("call $cabi_reset i32.const 0");
            }
            "str_to_mem" => {
                let sty = format!("(ref null {})", self.tname(&Ty::Str));
                let t = self.temp_raw(st, &sty);
                let p = self.temp_raw(st, "i32");
                self.gen_expr(st, &args[0]);
                st.emit(&format!("local.set {t} i32.const 0 i32.const 0 i32.const 1 local.get {t} ref.as_non_null array.len call $cabi_realloc local.set {p}"));
                st.emit(&format!("local.get {t} ref.as_non_null local.get {p} call $rt_to_mem_at drop local.get {p}"));
            }
            "str_from_mem" => {
                self.gen_expr(st, &args[0]);
                self.gen_expr(st, &args[1]);
                st.emit("call $rt_from_mem_at");
            }
            "worker_dispatch" => {
                self.gen_expr(st, &args[0]);
                if self.g.worker_entries.is_empty() {
                    st.emit("drop unreachable");
                } else {
                    st.emit("call $__worker_entry i32.const 0");
                }
            }
            "host_async" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                st.emit("call $rt_host_async");
            }
            "global" => {
                let tn = self.tname(&targs[0]);
                let g = format!("$glob.{}", sanitize(&self.mangle(&targs[0])));
                if self.global_names.insert(g.clone()) {
                    self.globals.push(format!("(global {g} (mut (ref null {tn})) (ref.null {tn}))"));
                }
                st.emit(&format!("global.get {g} ref.is_null"));
                st.emit("(if (then");
                self.gen_expr(st, &args[0]);
                st.emit(&format!("global.set {g}))"));
                st.emit(&format!("global.get {g} ref.as_non_null"));
            }
            "is_err" => {
                let is_result = matches!(&targs[0], Ty::Adt(id, _) if self.prog.adts[*id].name == "Result" && self.prog.adts[*id].pkg == crate::program::Pkg::Prelude);
                if is_result {
                    self.gen_expr(st, &args[0]);
                    let tn = self.tname(&targs[0]);
                    st.emit(&format!("struct.get {tn} 0 i32.const 1 i32.eq"));
                } else {
                    self.gen_expr(st, &args[0]);
                    st.emit("drop");
                    st.emit("i32.const 0");
                }
            }
            "cast" => {
                self.gen_expr(st, &args[0]);
                self.gen_cast(st, &targs[0], &targs[1], true);
            }
            "reinterpret" => {
                self.gen_expr(st, &args[0]);
                match (&targs[0], &targs[1]) {
                    (Ty::Float(FloatTy::F64), Ty::Int(_)) => st.emit("i64.reinterpret_f64"),
                    (Ty::Int(_), Ty::Float(FloatTy::F64)) => st.emit("f64.reinterpret_i64"),
                    (Ty::Float(FloatTy::F32), Ty::Int(_)) => st.emit("i32.reinterpret_f32"),
                    (Ty::Int(_), Ty::Float(FloatTy::F32)) => st.emit("f32.reinterpret_i32"),
                    _ => {}
                }
            }
            "wrapping" => {
                self.gen_expr(st, &args[1]);
                self.gen_expr(st, &args[2]);
                let Ty::Int(it) = &targs[0] else {
                    st.emit("unreachable");
                    return;
                };
                let pre = if it.is64() { "i64" } else { "i32" };
                let o = match lit_arg(0) {
                    0 => "add",
                    1 => "sub",
                    _ => "mul",
                };
                st.emit(&format!("{pre}.{o}"));
                self.wrap_small(st, *it);
            }
            "overflows" => {
                self.gen_expr(st, &args[1]);
                self.gen_expr(st, &args[2]);
                let Ty::Int(it) = &targs[0] else {
                    st.emit("unreachable");
                    return;
                };
                let o = match lit_arg(0) {
                    0 => "add",
                    1 => "sub",
                    _ => "mul",
                };
                st.emit(&format!("call $ovf_{o}_{}", it.name()));
            }
            "fop" => {
                self.gen_expr(st, &args[1]);
                let pre = self.num_prefix(&targs[0]);
                let o = match lit_arg(0) {
                    0 => "sqrt",
                    1 => "floor",
                    2 => "ceil",
                    3 => "trunc",
                    4 => "nearest",
                    5 => "abs",
                    _ => "neg",
                };
                st.emit(&format!("{pre}.{o}"));
            }
            "fminmax" => {
                self.gen_expr(st, &args[1]);
                self.gen_expr(st, &args[2]);
                let pre = self.num_prefix(&targs[0]);
                st.emit(&format!("{pre}.{}", if lit_arg(0) == 0 { "min" } else { "max" }));
            }
            "fmath" => {
                for a in args {
                    self.gen_expr(st, a);
                }
                st.emit("call $host_math");
            }
            "same" => {
                self.gen_expr(st, &args[0]);
                self.gen_expr(st, &args[1]);
                if is_ref(&targs[0]) {
                    st.emit("ref.eq");
                } else {
                    let pre = self.num_prefix(&targs[0]);
                    st.emit(&format!("{pre}.eq"));
                }
            }
            "dyn_is" | "dyn_cast" => {
                self.gen_expr(st, &args[0]);
                let dn = self.tname(&targs[1]);
                st.emit(&format!("struct.get {dn} 0"));
                let target = &targs[0];
                let tn = if is_ref(target) { self.tname(target) } else { self.pbox_type(target) };
                if name == "dyn_is" {
                    st.emit(&format!("ref.test (ref {tn})"));
                } else {
                    st.emit(&format!("ref.cast (ref {tn})"));
                    if !is_ref(target) {
                        st.emit(&format!("struct.get {tn} 0"));
                    }
                }
            }
            "unreachable" => st.emit("unreachable"),
            "char_from_u32" => {
                self.gen_expr(st, &args[0]);
            }
            other => {
                let _ = ret;
                panic!("unknown intrinsic {other}");
            }
        }
    }

    // ---------------- runtime ----------------
    fn runtime(&mut self) -> String {
        let sn = self.tname(&Ty::Str);
        let ovf = self.data_seg(b"integer overflow");
        let mut s = String::new();
        let _ = write!(
            s,
            r#"
(func $rt_ensure_mem (param $n i32)
  (local $have i32)
  memory.size i32.const 16 i32.shl local.set $have
  local.get $n local.get $have i32.gt_u
  (if (then
    local.get $n local.get $have i32.sub i32.const 65535 i32.add i32.const 16 i32.shr_u
    memory.grow drop)))
(func $rt_to_mem_at (param $s (ref {sn})) (param $off i32) (result i32)
  (local $n i32) (local $i i32)
  local.get $s array.len local.set $n
  local.get $off local.get $n i32.add call $rt_ensure_mem
  (block $done (loop $l
    local.get $i local.get $n i32.ge_u br_if $done
    local.get $off local.get $i i32.add
    local.get $s local.get $i array.get_u {sn}
    i32.store8
    local.get $i i32.const 1 i32.add local.set $i
    br $l))
  local.get $n)
(func $rt_from_mem (param $n i32) (result (ref {sn}))
  (local $r (ref null {sn})) (local $i i32)
  local.get $n array.new_default {sn} local.set $r
  (block $done (loop $l
    local.get $i local.get $n i32.ge_u br_if $done
    local.get $r ref.as_non_null local.get $i local.get $i i32.load8_u array.set {sn}
    local.get $i i32.const 1 i32.add local.set $i
    br $l))
  local.get $r ref.as_non_null)
(func $rt_print (param $s (ref {sn})) (param $fd i32)
  local.get $fd i32.const 0 local.get $s i32.const 0 call $rt_to_mem_at call $host_write)
(func $rt_panic (param $s (ref {sn}))
  i32.const 0 local.get $s i32.const 0 call $rt_to_mem_at call $host_panic
  unreachable)
(func $rt_overflow
  i32.const 0 i32.const 16 array.new_data {sn} {ovf} call $rt_panic)
(func $rt_str_eq (param $a (ref {sn})) (param $b (ref {sn})) (result i32)
  (local $n i32) (local $i i32)
  local.get $a local.get $b ref.eq (if (then i32.const 1 return))
  local.get $a array.len local.tee $n local.get $b array.len i32.ne (if (then i32.const 0 return))
  (block $done (loop $l
    local.get $i local.get $n i32.ge_u br_if $done
    local.get $a local.get $i array.get_u {sn} local.get $b local.get $i array.get_u {sn} i32.ne (if (then i32.const 0 return))
    local.get $i i32.const 1 i32.add local.set $i
    br $l))
  i32.const 1)
(func $rt_str_cmp (param $a (ref {sn})) (param $b (ref {sn})) (result i32)
  (local $na i32) (local $nb i32) (local $i i32) (local $x i32) (local $y i32)
  local.get $a array.len local.set $na
  local.get $b array.len local.set $nb
  (block $done (loop $l
    local.get $i local.get $na i32.ge_u br_if $done
    local.get $i local.get $nb i32.ge_u br_if $done
    local.get $a local.get $i array.get_u {sn} local.set $x
    local.get $b local.get $i array.get_u {sn} local.set $y
    local.get $x local.get $y i32.lt_u (if (then i32.const -1 return))
    local.get $x local.get $y i32.gt_u (if (then i32.const 1 return))
    local.get $i i32.const 1 i32.add local.set $i
    br $l))
  local.get $na local.get $nb i32.lt_u (if (then i32.const -1 return))
  local.get $na local.get $nb i32.gt_u (if (then i32.const 1 return))
  i32.const 0)
(func $rt_str_slice (param $s (ref {sn})) (param $a i32) (param $b i32) (result (ref {sn}))
  (local $r (ref null {sn}))
  local.get $b local.get $a i32.sub array.new_default {sn} local.set $r
  local.get $r ref.as_non_null i32.const 0 local.get $s local.get $a local.get $b local.get $a i32.sub array.copy {sn} {sn}
  local.get $r ref.as_non_null)
(func $rt_str_concat (param $a (ref {sn})) (param $b (ref {sn})) (result (ref {sn}))
  (local $r (ref null {sn}))
  local.get $a array.len local.get $b array.len i32.add array.new_default {sn} local.set $r
  local.get $r ref.as_non_null i32.const 0 local.get $a i32.const 0 local.get $a array.len array.copy {sn} {sn}
  local.get $r ref.as_non_null local.get $a array.len local.get $b i32.const 0 local.get $b array.len array.copy {sn} {sn}
  local.get $r ref.as_non_null)
(func $rt_fmt_f64 (param $x f64) (param $is32 i32) (result (ref {sn}))
  i32.const 64 call $rt_ensure_mem
  local.get $x i32.const 0 local.get $is32 call $host_fmt_f64 call $rt_from_mem)
(func $rt_host (param $op i32) (param $s (ref {sn})) (result (ref {sn}))
  (local $n i32)
  local.get $op i32.const 0 local.get $s i32.const 0 call $rt_to_mem_at call $host_op local.tee $n
  i32.const 0 i32.lt_s (if (then i32.const 0 array.new_default {sn} return))
  local.get $n call $rt_ensure_mem
  i32.const 0 call $host_take
  local.get $n call $rt_from_mem)
(func $rt_host_async (param $op i32) (param $s (ref {sn})) (result (ref {sn}))
  (local $n i32)
  local.get $op i32.const 0 local.get $s i32.const 0 call $rt_to_mem_at call $host_async call $host_claim local.tee $n
  i32.const 0 i32.lt_s (if (then i32.const 0 array.new_default {sn} return))
  local.get $n call $rt_ensure_mem
  i32.const 0 call $host_take
  local.get $n call $rt_from_mem)
(global $cabi_top (mut i32) (i32.const 16777216))
(global $cabi_depth (mut i32) (i32.const 0))
(global $cabi_floor (mut i32) (i32.const 16777216))
;; Scratch allocations nest per thread; with concurrent component threads the
;; heap is only rewound once no thread holds a mark.
(func $cabi_mark (result i32)
  global.get $cabi_depth i32.eqz (if (then global.get $cabi_top global.set $cabi_floor))
  global.get $cabi_depth i32.const 1 i32.add global.set $cabi_depth
  global.get $cabi_top)
(func $cabi_reset (param $m i32)
  ;; without an open mark (post-return), rewind to the given address
  global.get $cabi_depth i32.eqz (if (then local.get $m global.set $cabi_top return))
  global.get $cabi_depth i32.const 1 i32.sub global.set $cabi_depth
  global.get $cabi_depth i32.eqz (if (then global.get $cabi_floor global.set $cabi_top)))
(func $cabi_realloc (param $old i32) (param $old_size i32) (param $align i32) (param $new_size i32) (result i32)
  (local $p i32)
  global.get $cabi_top local.get $align i32.const 1 i32.sub i32.add
  i32.const 0 local.get $align i32.sub i32.and local.set $p
  local.get $p local.get $new_size i32.add global.set $cabi_top
  global.get $cabi_top call $rt_ensure_mem
  local.get $old_size (if (then
    local.get $p local.get $old local.get $old_size local.get $new_size i32.lt_u (if (result i32) (then local.get $old_size) (else local.get $new_size)) memory.copy))
  local.get $p)
(func $rt_from_mem_at (param $p i32) (param $n i32) (result (ref {sn}))
  (local $r (ref null {sn})) (local $i i32)
  local.get $n array.new_default {sn} local.set $r
  (block $done (loop $l
    local.get $i local.get $n i32.ge_u br_if $done
    local.get $r ref.as_non_null local.get $i local.get $p local.get $i i32.add i32.load8_u array.set {sn}
    local.get $i i32.const 1 i32.add local.set $i
    br $l))
  local.get $r ref.as_non_null)
(func $rt_frem64 (param $a f64) (param $b f64) (result f64)
  local.get $a local.get $a local.get $b f64.div f64.trunc local.get $b f64.mul f64.sub)
(func $rt_frem32 (param $a f32) (param $b f32) (result f32)
  local.get $a local.get $a local.get $b f32.div f32.trunc local.get $b f32.mul f32.sub)
"#
        );
        for it in IntTy::all() {
            let n = it.name();
            for o in ["add", "sub", "mul"] {
                let (vt, body) = ovf_body(it, o);
                let _ = writeln!(s, "(func $ovf_{o}_{n} (param $a {vt}) (param $b {vt}) (result i32)\n{body})");
                let _ = writeln!(s, "(func $chk_{o}_{n} (param $a {vt}) (param $b {vt}) (result {vt})\n{})", chk_body(it, o));
            }
        }
        s
    }
}

/// Body of `$chk_<op>_<type>`: the checked operation, computed once. Kept to a few
/// instructions so that engines inline it.
fn chk_body(it: IntTy, o: &str) -> String {
    const TRAP: &str = "(if (then call $rt_overflow))";
    match (it, o) {
        (IntTy::I32, "add") => format!("  (local $r i32) local.get $a local.get $b i32.add local.set $r\n  local.get $a local.get $r i32.xor local.get $b local.get $r i32.xor i32.and i32.const 0 i32.lt_s {TRAP}\n  local.get $r"),
        (IntTy::I32, "sub") => format!("  (local $r i32) local.get $a local.get $b i32.sub local.set $r\n  local.get $a local.get $b i32.xor local.get $a local.get $r i32.xor i32.and i32.const 0 i32.lt_s {TRAP}\n  local.get $r"),
        (IntTy::I64, "add") => format!("  (local $r i64) local.get $a local.get $b i64.add local.set $r\n  local.get $a local.get $r i64.xor local.get $b local.get $r i64.xor i64.and i64.const 0 i64.lt_s {TRAP}\n  local.get $r"),
        (IntTy::I64, "sub") => format!("  (local $r i64) local.get $a local.get $b i64.sub local.set $r\n  local.get $a local.get $b i64.xor local.get $a local.get $r i64.xor i64.and i64.const 0 i64.lt_s {TRAP}\n  local.get $r"),
        (IntTy::U32, "add") => format!("  (local $r i32) local.get $a local.get $b i32.add local.tee $r local.get $a i32.lt_u {TRAP}\n  local.get $r"),
        (IntTy::U64, "add") => format!("  (local $r i64) local.get $a local.get $b i64.add local.tee $r local.get $a i64.lt_u {TRAP}\n  local.get $r"),
        (IntTy::U32, "sub") => format!("  local.get $a local.get $b i32.lt_u {TRAP}\n  local.get $a local.get $b i32.sub"),
        (IntTy::U64, "sub") => format!("  local.get $a local.get $b i64.lt_u {TRAP}\n  local.get $a local.get $b i64.sub"),
        (IntTy::I64 | IntTy::U64, _) => format!("  local.get $a local.get $b call $ovf_{o}_{} {TRAP}\n  local.get $a local.get $b i64.{o}", it.name()),
        _ => {
            // narrow types: exact result in i64, range check, then back to i32
            let ext = if it.signed() { "i64.extend_i32_s" } else { "i64.extend_i32_u" };
            let (lo, hi) = (it.min(), it.max());
            format!("  (local $r i64) local.get $a {ext} local.get $b {ext} i64.{o} local.set $r\n  local.get $r i64.const {lo} i64.lt_s local.get $r i64.const {hi} i64.gt_s i32.or {TRAP}\n  local.get $r i32.wrap_i64")
        }
    }
}

fn ovf_body(it: IntTy, o: &str) -> (&'static str, String) {
    if it.is64() {
        let signed = it.signed();
        let body = match (o, signed) {
            ("add", true) => "  (local $r i64) local.get $a local.get $b i64.add local.set $r\n  local.get $a local.get $r i64.xor local.get $b local.get $r i64.xor i64.and i64.const 0 i64.lt_s",
            ("add", false) => "  local.get $a local.get $b i64.add local.get $a i64.lt_u",
            ("sub", true) => "  (local $r i64) local.get $a local.get $b i64.sub local.set $r\n  local.get $a local.get $b i64.xor local.get $a local.get $r i64.xor i64.and i64.const 0 i64.lt_s",
            ("sub", false) => "  local.get $a local.get $b i64.lt_u",
            ("mul", true) => {
                "  local.get $a i64.eqz (if (then i32.const 0 return))\n  local.get $a i64.const -1 i64.eq local.get $b i64.const 0x8000000000000000 i64.eq i32.and (if (then i32.const 1 return))\n  local.get $b i64.const -1 i64.eq local.get $a i64.const 0x8000000000000000 i64.eq i32.and (if (then i32.const 1 return))\n  local.get $a local.get $b i64.mul local.get $a i64.div_s local.get $b i64.ne"
            }
            _ => "  local.get $a i64.eqz (if (then i32.const 0 return))\n  local.get $a local.get $b i64.mul local.get $a i64.div_u local.get $b i64.ne",
        };
        ("i64", body.to_string())
    } else {
        let ext = if it.signed() { "i64.extend_i32_s" } else { "i64.extend_i32_u" };
        let (lo, hi) = (it.min(), it.max());
        let cmp = if it.signed() { ("i64.lt_s", "i64.gt_s") } else { ("i64.lt_s", "i64.gt_u") };
        let body = format!(
            "  (local $r i64) local.get $a {ext} local.get $b {ext} i64.{o} local.set $r\n  local.get $r i64.const {lo} {} local.get $r i64.const {hi} {} i32.or",
            cmp.0, cmp.1
        );
        ("i32", body)
    }
}

/// What generating one function added to a copy of the state.
struct Delta {
    types: Vec<(String, String)>,
    data: Vec<(String, Vec<u8>)>,
    globals: Vec<String>,
    imports: Vec<String>,
    funcs: Vec<String>,
    refs: Vec<String>,
}

/// Generates all functions on several threads, each with its own copy of the state, and
/// merges what each function added in function order. Each thread takes functions in
/// increasing order, so an item appears in the output where the sequential loop would put
/// it: with the first function that uses it. Fails (and changes nothing) when there are
/// too few functions to be worth it, or when two data segments' names collide.
fn gen_parallel(cg: &mut Cg) -> Result<(), ()> {
    let g = cg.g;
    let order: Vec<usize> = (0..g.funcs.len()).filter(|&i| g.funcs[i].is_some()).collect();
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1).min(8).min(order.len() / 64);
    if threads < 2 || std::env::var_os("PUD_SERIAL_CODEGEN").is_some() {
        return Err(());
    }
    let mut base = cg.clone();
    base.types.clear();
    base.data.clear();
    base.globals.clear();
    base.imports.clear();
    base.funcs.clear();
    base.new_refs.clear();
    let base = &base;
    let next = std::sync::atomic::AtomicUsize::new(0);
    let order = &order;
    let mut deltas: Vec<(usize, Delta)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|_| {
                let next = &next;
                sc.spawn(move || {
                    let mut w = base.clone();
                    let mut mine = Vec::new();
                    loop {
                        let k = next.fetch_add(8, std::sync::atomic::Ordering::Relaxed);
                        if k >= order.len() {
                            break;
                        }
                        for (pos, &i) in order.iter().enumerate().skip(k).take(8) {
                            w.gen_func(i, g.funcs[i].as_ref().unwrap());
                            mine.push((
                                pos,
                                Delta {
                                    types: std::mem::take(&mut w.types),
                                    data: std::mem::take(&mut w.data),
                                    globals: std::mem::take(&mut w.globals),
                                    imports: std::mem::take(&mut w.imports),
                                    funcs: std::mem::take(&mut w.funcs),
                                    refs: std::mem::take(&mut w.new_refs),
                                },
                            ));
                        }
                    }
                    mine
                })
            })
            .collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    });
    deltas.sort_by_key(|d| d.0);
    // data names come from contents: refuse a collision instead of merging it
    let mut data_seen: HashMap<String, Vec<u8>> = cg.data.iter().cloned().collect();
    for (_, d) in &deltas {
        for (n, b) in &d.data {
            if let Some(old) = data_seen.get(n) {
                if old != b {
                    return Err(());
                }
            } else {
                data_seen.insert(n.clone(), b.clone());
            }
        }
    }
    let mut globals_seen: HashSet<String> = cg.globals.iter().cloned().collect();
    let mut funcs_seen: HashSet<String> = HashSet::new();
    let mut imports_seen: HashSet<String> = cg.imports.iter().cloned().collect();
    for (_, d) in deltas {
        for (n, t) in d.types {
            if cg.defined.insert(n.clone()) {
                cg.types.push((n, t));
            }
        }
        for (n, b) in d.data {
            if cg.data_names.insert(n.clone()) {
                cg.data_map.insert(b.clone(), n.clone());
                cg.data.push((n, b));
            }
        }
        for x in d.globals {
            if globals_seen.insert(x.clone()) {
                cg.globals.push(x);
            }
        }
        for x in d.imports {
            if imports_seen.insert(x.clone()) {
                cg.imports.push(x);
            }
        }
        for f in d.funcs {
            // shims can be generated by several threads; real functions are unique
            let fname = f.get(6..).and_then(|r| r.split(' ').next()).unwrap_or("");
            if fname.ends_with(".shim") || fname.starts_with("$vshim.") {
                if !funcs_seen.insert(f.clone()) {
                    continue;
                }
            }
            cg.funcs.push(f);
        }
        for r in d.refs {
            cg.refs.insert(r);
        }
    }
    Ok(())
}

/// `plat`: in component builds, the platform functions (in `driver::PLATFORM_FNS` order)
/// that implement the host operations inside the module.
pub fn generate(prog: &Program, g: &Global, entry: Option<usize>, tests: &[(String, usize)], plat: Option<&[usize]>) -> Result<Output, String> {
    let mut cg = Cg {
        prog,
        g,
        types: Vec::new(),
        type_names: HashMap::new(),
        defined: HashSet::new(),
        funcs: Vec::new(),
        data: Vec::new(),
        data_map: HashMap::new(),
        data_names: HashSet::new(),
        refs: HashSet::new(),
        new_refs: Vec::new(),
        imports: Vec::new(),
        globals: Vec::new(),
        exports: Vec::new(),
        global_names: HashSet::new(),
        shims: HashMap::new(),
        vtable_globals: HashMap::new(),
        unit_variants: HashMap::new(),
        func_names: Vec::new(),
        tail: String::new(),
        component: plat.is_some(),
    };
    // function names
    let mut by_idx: Vec<Option<&FnInst>> = vec![None; g.funcs.len()];
    for (inst, &i) in &g.insts {
        by_idx[i] = Some(inst);
    }
    for (i, f) in g.funcs.iter().enumerate() {
        let base = match f {
            Some(f) => sanitize(&f.name),
            None => "missing".into(),
        };
        cg.func_names.push(format!("${base}#{i}"));
    }
    let runtime = cg.runtime();
    if gen_parallel(&mut cg).is_err() {
        for (i, f) in g.funcs.iter().enumerate() {
            if let Some(f) = f {
                cg.gen_func(i, f);
            }
        }
    }
    if let Some(e) = entry {
        let n = cg.func_names[e].clone();
        cg.exports.push(format!("(export \"main\" (func {n}))"));
    }
    if !g.worker_entries.is_empty() {
        let mut w = if cg.component { String::from("(func $__worker_entry (param $k i32)\n") } else { String::from("(func $__worker_entry (export \"__worker_entry\") (param $k i32)\n") };
        for (k, &idx) in g.worker_entries.iter().enumerate() {
            let n = cg.func_names[idx].clone();
            let _ = writeln!(w, "  local.get $k i32.const {k} i32.eq (if (then call {n} drop return))");
        }
        w.push_str("  unreachable)\n");
        cg.funcs.push(w);
    }
    let mut test_exports = Vec::new();
    for (k, (name, idx)) in tests.iter().enumerate() {
        let n = cg.func_names[*idx].clone();
        let ex = format!("test_{k}");
        cg.exports.push(format!("(export \"{ex}\" (func {n}))"));
        test_exports.push((name.clone(), ex));
    }
    let mut out = String::from("(module\n");
    if let Some(pf) = plat {
        let n: Vec<String> = pf.iter().map(|&i| cg.func_names[i].clone()).collect();
        let sn = cg.tname(&Ty::Str);
        let _ = write!(
            cg.funcs_tail(),
            r#"(global $plat_pending (mut (ref null {sn})) (ref.null {sn}))
(func $host_write (param $fd i32) (param $p i32) (param $n i32)
  local.get $fd local.get $p local.get $n call $rt_from_mem_at call {w} drop)
(func $host_panic (param $p i32) (param $n i32)
  local.get $p local.get $n call $rt_from_mem_at call {pa} drop unreachable)
(func $host_fmt_f64 (param $x f64) (param $p i32) (param $is32 i32) (result i32)
  local.get $x local.get $is32 call {fm} local.get $p call $rt_to_mem_at)
(func $host_parse_f64 (param $p i32) (param $n i32) (result f64)
  local.get $p local.get $n call $rt_from_mem_at call {pr})
(func $host_math (param $op i32) (param $x f64) (param $y f64) (result f64)
  local.get $op local.get $x local.get $y call {ma})
(func $host_op (param $op i32) (param $p i32) (param $n i32) (result i32)
  local.get $op local.get $p local.get $n call $rt_from_mem_at call {ho} global.set $plat_pending
  call {st} (if (then throw $cancelled))
  global.get $plat_pending ref.as_non_null array.len)
(func $host_take (param $p i32)
  global.get $plat_pending ref.as_non_null local.get $p call $rt_to_mem_at drop)
(func $host_ok (result i32) call {ok})
(func $host_async (param $op i32) (param $p i32) (param $n i32) (result i32)
  local.get $op local.get $p local.get $n call $rt_from_mem_at call {ha} global.set $plat_pending
  call {st} (if (then throw $cancelled))
  i32.const 0)
(tag $cancelled)
;; entry point of component threads (spawned tasks); a cancelled task unwinds to here
(func $plat_thread_entry (param $id i32)
  (block $out
    (try_table (catch $cancelled $out)
      local.get $id call {tm} drop))
  local.get $id call {td} drop)
(table $__itab (export "__indirect_function_table") 1 funcref)
(elem (table $__itab) (i32.const 0) func $plat_thread_entry)
(func $host_claim (param $t i32) (result i32)
  global.get $plat_pending ref.as_non_null array.len)
(export "cabi_realloc" (func $cabi_realloc))
"#,
            w = n[0], pa = n[1], fm = n[2], pr = n[3], ma = n[4], ho = n[5], ok = n[6], ha = n[7], st = n[8], tm = n[9], td = n[10]
        );
        cg.exports.retain(|e| !e.contains("\"test_"));
    } else {
    out.push_str("(import \"puddi\" \"write\" (func $host_write (param i32 i32 i32)))\n");
    out.push_str("(import \"puddi\" \"panic\" (func $host_panic (param i32 i32)))\n");
    out.push_str("(import \"puddi\" \"fmt_f64\" (func $host_fmt_f64 (param f64 i32 i32) (result i32)))\n");
    out.push_str("(import \"puddi\" \"parse_f64\" (func $host_parse_f64 (param i32 i32) (result f64)))\n");
    out.push_str("(import \"puddi\" \"math\" (func $host_math (param i32 f64 f64) (result f64)))\n");
    out.push_str("(import \"puddi\" \"host\" (func $host_op (param i32 i32 i32) (result i32)))\n");
    out.push_str("(import \"puddi\" \"host_take\" (func $host_take (param i32)))\n");
    out.push_str("(import \"puddi\" \"host_ok\" (func $host_ok (result i32)))\n");
    out.push_str("(import \"puddi\" \"host_async\" (func $host_async (param i32 i32 i32) (result i32)))\n");
    out.push_str("(import \"puddi\" \"host_claim\" (func $host_claim (param i32) (result i32)))\n");
    }
    for i in &cg.imports {
        out.push_str(i);
        out.push('\n');
    }
    out.push_str("(rec\n");
    for (_, t) in &cg.types {
        out.push_str("  ");
        out.push_str(t);
        out.push('\n');
    }
    out.push_str(")\n");
    out.push_str("(memory (export \"memory\") 1)\n");
    for gl in &cg.globals {
        out.push_str(gl);
        out.push('\n');
    }
    if !cg.refs.is_empty() {
        let mut refs: Vec<&String> = cg.refs.iter().collect();
        refs.sort();
        out.push_str("(elem declare func");
        for r in refs {
            out.push(' ');
            out.push_str(r);
        }
        out.push_str(")\n");
    }
    out.push_str(&runtime);
    for f in &cg.funcs {
        out.push_str(f);
    }
    out.push_str(&cg.tail);
    for e in &cg.exports {
        out.push_str(e);
        out.push('\n');
    }
    for (n, d) in &cg.data {
        let _ = writeln!(out, "(data {n} {})", wat_str(d));
    }
    out.push_str(")\n");
    crate::driver::phase("codegen wat");
    let wasm = assemble(&out)?;
    crate::driver::phase("codegen asm");
    let mut features = wasmparser::WasmFeatures::default();
    features.insert(wasmparser::WasmFeatures::GC);
    features.insert(wasmparser::WasmFeatures::FUNCTION_REFERENCES);
    features.insert(wasmparser::WasmFeatures::EXCEPTIONS);
    features.insert(wasmparser::WasmFeatures::REFERENCE_TYPES);
    features.insert(wasmparser::WasmFeatures::BULK_MEMORY);
    features.insert(wasmparser::WasmFeatures::SATURATING_FLOAT_TO_INT);
    features.insert(wasmparser::WasmFeatures::SIGN_EXTENSION);
    let mut v = wasmparser::Validator::new_with_features(features);
    if let Ok(path) = std::env::var("PUDDI_DUMP") {
        let _ = std::fs::write(format!("{path}.wat"), &out);
        let _ = std::fs::write(format!("{path}.wasm"), &wasm);
    }
    if let Err(e) = v.validate_all(&wasm) {
        return Err(format!("internal error: generated module failed validation: {e}"));
    }
    Ok(Output { wat: out, wasm, tests: test_exports })
}
