//! Compilation pipeline: load sources, parse, derive, resolve, elaborate,
//! generate code.

use crate::ast;
use crate::codegen;
use crate::derive;
use crate::diag::{Diag, SourceMap};
use crate::elab::Global;
use crate::ir::FnInst;
use crate::lexer;
use crate::parser;
use crate::program::{self, FnOwner, ModSource, Pkg};

pub const PRELUDE: &str = include_str!("prelude.pud");
pub const SOFT: &str = include_str!("soft.pud");
pub const PLATFORM_WASI: &str = include_str!("platform_wasi.pud");
pub const PLATFORM_CORE: &str = include_str!("platform_core.pud");
pub const PLATFORM_HTTP: &str = include_str!("platform_http.pud");

const PLATFORM_CLOCKS: &str = r#"
fn __plat_clock(op: Int) -> Float {
    if op == 15 {
        let t = __w_wasi_clocks_system_clock.now()
        __cast<I64, Float>(t.seconds) * 1000.0 + __cast<U32, Float>(t.nanoseconds) / 1000000.0
    } else {
        __cast<U64, Float>(__w_wasi_clocks_monotonic_clock.now()) / 1000000.0
    }
}

fn __plat_sleep(ms: Int) {
    if ms > 0 { __w_wasi_clocks_monotonic_clock.wait_for(__cast<Int, U64>(ms) * 1000000) }
}
"#;

const PLATFORM_NO_CLOCKS: &str = r#"
fn __plat_clock(op: Int) -> Float { 0.0 }

fn __plat_sleep(ms: Int) {}
"#;

const PLATFORM_RANDOM: &str = r#"
fn __plat_random() -> Float { __cast<U64, Float>(__w_wasi_random_random.get_random_u64() >> 11) * 1.1102230246251565e-16 }
"#;

const PLATFORM_NO_RANDOM: &str = r#"
fn __plat_random() -> Float { 0.0 }
"#;

const PLATFORM_NO_HTTP: &str = r#"
fn __plat_http(arg: Str) -> Result<Str, Str> { Err("HTTP is not available in this component") }
"#;

const PLATFORM_LOG: &str = r#"
fn __plat_log(level: Str, msg: Str) {
    let l = match level {
        "trace" -> __w_wasi_logging_logging.Level.Trace
        "debug" -> __w_wasi_logging_logging.Level.Debug
        "warn" -> __w_wasi_logging_logging.Level.Warn
        "error" -> __w_wasi_logging_logging.Level.Error
        "critical" -> __w_wasi_logging_logging.Level.Critical
        _ -> __w_wasi_logging_logging.Level.Info
    }
    __w_wasi_logging_logging.log(l, "puddi", msg)
}
"#;

const PLATFORM_NO_LOG: &str = r#"
fn __plat_log(level: Str, msg: Str) {}
"#;
/// Worker operations for `wasi` components, through the puddi:runtime interfaces.
const PLATFORM_WORKERS: &str = r#"
pub fn __plat_worker(op: Int, arg: Str) -> Str {
    let parts = arg.split("\0")
    match op {
        50 -> "{__w_puddi_runtime_workers.start(__cast<Int, U32>(arg.parse_int().unwrap()))}"
        51 -> {
            __w_puddi_runtime_workers.send(__cast<Int, U32>(parts[0].parse_int().unwrap()), parts.slice(1, parts.len()).join("\0"))
            ""
        }
        52 -> {
            __w_puddi_runtime_workers.close(__cast<Int, U32>(arg.parse_int().unwrap()))
            ""
        }
        53 -> {
            __w_puddi_runtime_port.send(arg)
            ""
        }
        54 -> {
            __w_puddi_runtime_port.done()
            ""
        }
        103 -> match __w_puddi_runtime_workers.recv(__cast<Int, U32>(arg.parse_int().unwrap())) {
            Some(m) -> "1" + m
            None -> ""
        }
        104 -> match __w_puddi_runtime_port.recv() {
            Some(m) -> "1" + m
            None -> ""
        }
        _ -> ""
    }
}

pub fn __plat_worker_start(entry: U32) { __worker_dispatch(__cast<U32, Int>(entry)) }
"#;

const PLATFORM_NO_WORKERS: &str = r#"
pub fn __plat_worker(op: Int, arg: Str) -> Str {
    __plat().ok = false
    "workers are not available in this component"
}
"#;

pub const PLATFORM_PLUGIN: &str = include_str!("platform_plugin.pud");

/// WASI interfaces the `wasi` platform layer uses.
const WASI_PLATFORM: &[&str] = &[
    "wasi:cli/stdout",
    "wasi:cli/stderr",
    "wasi:cli/stdin",
    "wasi:cli/environment",
    "wasi:cli/exit",
    "wasi:clocks/monotonic-clock",
    "wasi:clocks/system-clock",
    "wasi:random/random",
    "wasi:filesystem/types",
    "wasi:filesystem/preopens",
    "wasi:http/types",
    "wasi:http/client",
];

/// Functions of the platform layer that replace the JavaScript host imports.
pub const PLATFORM_FNS: &[&str] = &["__plat_write", "__plat_panic", "__plat_fmt", "__plat_parse", "__plat_math", "__plat_host", "__plat_ok", "__plat_host_async", "__plat_should_throw", "__plat_thread_main", "__plat_thread_done"];

/// How to build a component.
pub struct ComponentOpts {
    pub pkg_dir: Option<std::path::PathBuf>,
    /// World spec from pud.toml, e.g. `wasi:cli/command` or `wit/host.wit#plugin`.
    pub world: String,
}

pub struct UserFile {
    /// Module path, e.g. `main` or `net.http`; dependency modules carry their package prefix.
    pub module: String,
    pub pkg: Pkg,
    pub prefix: String,
    pub aliases: std::collections::HashMap<String, String>,
    /// Display path for diagnostics.
    pub display: String,
    pub text: String,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Build,
    Test,
    Check,
}

pub struct Compiled {
    pub wasm: Vec<u8>,
    /// The component, for component builds.
    pub component: Option<Vec<u8>>,
    pub wat: String,
    pub tests: Vec<(String, String)>,
    pub warnings: Vec<Diag>,
    pub has_main: bool,
}

/// Prints the time since the first call when `PUD_TIME` is set (phase profiling).
pub fn phase(name: &str) {
    use std::sync::OnceLock;
    static T0: OnceLock<Option<std::time::Instant>> = OnceLock::new();
    if let Some(t0) = T0.get_or_init(|| std::env::var_os("PUD_TIME").map(|_| std::time::Instant::now())) {
        eprintln!("[time] {name} {:.1} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
}

fn parse_file(sm: &mut SourceMap, display: String, text: String) -> Result<ast::Module, Vec<Diag>> {
    let fid = sm.add(display, text);
    lex_parse(&sm.files[fid as usize].text, fid).map_err(|d| vec![d])
}

/// Lexes and parses one file. A large file is cut at lines holding only `}` into pieces that
/// are lexed and parsed on separate threads; the result is the same as parsing it whole,
/// which is what happens when a cut turns out not to lie between two top-level items.
fn lex_parse(text: &str, fid: u32) -> Result<ast::Module, Diag> {
    const PIECE: usize = 48 * 1024;
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1).min(8);
    let pieces = (text.len() / PIECE).min(threads);
    if pieces < 2 {
        return lexer::lex(text, fid).and_then(parser::parse_module);
    }
    let b = text.as_bytes();
    let mut cuts = vec![0];
    for k in 1..pieces {
        let from = (text.len() * k / pieces).max(*cuts.last().unwrap());
        // just after "\n}\n" (or "\n}\r\n")
        let mut i = from;
        let found = loop {
            match b[i..].iter().position(|&c| c == b'\n') {
                None => break None,
                Some(j) => i += j + 1,
            }
            if b.get(i) == Some(&b'}') {
                match (b.get(i + 1), b.get(i + 2)) {
                    (Some(b'\n'), _) => break Some(i + 2),
                    (Some(b'\r'), Some(b'\n')) => break Some(i + 3),
                    _ => {}
                }
            }
        };
        match found {
            Some(c) if c < text.len() => cuts.push(c),
            _ => break,
        }
    }
    cuts.push(text.len());
    let results: Vec<Result<(Vec<lexer::Token>, bool), Diag>> = std::thread::scope(|sc| {
        let hs: Vec<_> = cuts.windows(2).map(|w| sc.spawn(move || lexer::lex_range(text, fid, w[0], w[1]))).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    use lexer::Tok;
    let item_start = |t: &Tok| matches!(t, Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Trait | Tok::Pub | Tok::Const | Tok::Type | Tok::Test | Tok::Import | Tok::At | Tok::Export | Tok::Async);
    let mut chunks: Vec<Vec<lexer::Token>> = Vec::new();
    for (k, r) in results.into_iter().enumerate() {
        let Ok((toks, closed)) = r else { return lexer::lex(text, fid).and_then(parser::parse_module) };
        let last = k + 2 == cuts.len();
        // a cut is clean when the piece before it ends outside all delimiters with the `}`
        // of an item, and the piece after it starts a new item
        if !last && (!closed || !matches!(toks.iter().rev().find(|t| t.tok != Tok::Newline).map(|t| &t.tok), Some(Tok::RBrace))) {
            return lexer::lex(text, fid).and_then(parser::parse_module);
        }
        if k > 0 && !toks.first().is_none_or(|t| item_start(&t.tok)) {
            return lexer::lex(text, fid).and_then(parser::parse_module);
        }
        chunks.push(toks);
    }
    let end = text.len() as u32;
    let n = chunks.len();
    for (k, c) in chunks.iter_mut().enumerate() {
        let at = c.last().map_or(end, |t| t.span.hi);
        if k + 1 == n && !matches!(c.last().map(|t| &t.tok), None | Some(Tok::Newline) | Some(Tok::LBrace)) {
            c.push(lexer::Token { tok: Tok::Newline, span: crate::diag::Span::new(fid, end, end) });
        }
        let at = if k + 1 == n { end } else { at };
        c.push(lexer::Token { tok: Tok::Eof, span: crate::diag::Span::new(fid, at, at) });
    }
    let parsed: Vec<Result<ast::Module, Diag>> = std::thread::scope(|sc| {
        let hs: Vec<_> = chunks.into_iter().map(|c| sc.spawn(move || parser::parse_module(c))).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut m = ast::Module { imports: Vec::new(), items: Vec::new() };
    for r in parsed {
        let p = r?;
        m.imports.extend(p.imports);
        m.items.extend(p.items);
    }
    Ok(m)
}

/// Lexes and parses the given files on a few threads, largest first.
fn parse_parallel(sm: &SourceMap, fids: &[u32]) -> Vec<Result<ast::Module, Diag>> {
    let mut order: Vec<usize> = (0..fids.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(sm.files[fids[i] as usize].text.len()));
    let next = std::sync::atomic::AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1).clamp(1, 8).min(fids.len().max(1));
    let mut out: Vec<Option<Result<ast::Module, Diag>>> = (0..fids.len()).map(|_| None).collect();
    let done: Vec<Vec<(usize, Result<ast::Module, Diag>)>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|_| {
                sc.spawn(|| {
                    let mut mine = Vec::new();
                    loop {
                        let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(&i) = order.get(k) else { break };
                        let fid = fids[i];
                        mine.push((i, lex_parse(&sm.files[fid as usize].text, fid)));
                    }
                    mine
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for (i, r) in done.into_iter().flatten() {
        out[i] = Some(r);
    }
    out.into_iter().map(|r| r.unwrap()).collect()
}

fn with_derives(sm: &mut SourceMap, module: &mut ast::Module, name: &str) -> Result<(), Vec<Diag>> {
    let src = derive::derive_source(module)?;
    if !src.is_empty() {
        let extra = parse_file(sm, format!("<derive in {name}>"), src)?;
        module.items.extend(extra.items);
    }
    Ok(())
}

fn internal(m: String) -> Vec<Diag> {
    vec![Diag::new(crate::diag::Span::new(u32::MAX, 0, 0), m)]
}

pub fn compile(sm: &mut SourceMap, files: Vec<UserFile>, root: &str, target: &str, mode: Mode, comp: Option<ComponentOpts>) -> Result<Compiled, Vec<Diag>> {
    phase("compile start");
    let mut errs: Vec<Diag> = Vec::new();
    let mut sources: Vec<ModSource> = Vec::new();

    // parse user files first: component builds need their WIT imports
    let mut user_mods = Vec::new();
    for f in files {
        match parse_file(sm, f.display.clone(), f.text.clone()) {
            Ok(m) => user_mods.push((f, m)),
            Err(e) => errs.extend(e),
        }
    }
    if !errs.is_empty() {
        return Err(errs);
    }

    // component setup: world, bindings for imported interfaces, platform layer
    let mut wit_ctx: Option<crate::wit::Wit> = None;
    let mut binding_sources: Vec<(String, String)> = Vec::new();
    let mut platform_imports = String::new();
    let mut platform_text = String::new();
    if let Some(c) = &comp {
        let (base, base_own) = crate::wit::Wit::new(c.pkg_dir.as_deref()).map_err(internal_user)?;
        let mut extra_names: Vec<String> = Vec::new();
        for (_, m) in &user_mods {
            for imp in &m.imports {
                if let Some(w) = &imp.wit {
                    match crate::wit::Wit::find_interface(&base, w) {
                        Some(_) => extra_names.push(w.clone()),
                        None => errs.push(Diag::new(imp.span, format!("cannot find WIT interface `{w}`")).note("the interface must be part of the bundled WASI 0.3 packages or of the package's wit/ directory")),
                    }
                }
            }
        }
        if !errs.is_empty() {
            return Err(errs);
        }
        // `wasi` components always get the WASI platform interfaces; workers
        // need the puddi:runtime worker interfaces from the host
        let uses_workers = target == "wasi" && user_mods.iter().any(|(_, m)| m.imports.iter().any(imports_worker));
        let mut plat: Vec<&str> = if target == "wasi" { WASI_PLATFORM.to_vec() } else { Vec::new() };
        if uses_workers {
            plat.extend(["puddi:runtime/workers", "puddi:runtime/port"]);
        }
        extra_names.extend(plat.iter().map(|s| s.to_string()));
        let mut extra_exports: Vec<String> = if uses_workers { vec!["puddi:runtime/worker-main".into()] } else { Vec::new() };
        let mut w = crate::wit::Wit::load_with(base.clone(), base_own, &c.world, &extra_names, &extra_exports).map_err(internal_user)?;
        // a plugin gets the capabilities its world imports (SPEC 10.2 "host")
        let mut caps = Caps { clocks: target == "wasi", random: target == "wasi", http: target == "wasi", log: false, workers: uses_workers };
        if target == "plugin" {
            let have = w.imported_interfaces();
            let has = |n: &str| crate::wit::Wit::find_interface(&w.resolve, n).map(|i| have.contains(&i)).unwrap_or(false);
            caps.clocks = has("wasi:clocks/monotonic-clock") && has("wasi:clocks/system-clock");
            caps.random = has("wasi:random/random");
            caps.http = has("wasi:http/types") && has("wasi:http/client");
            caps.log = has("wasi:logging/logging");
            caps.workers = has("puddi:runtime/workers") && has("puddi:runtime/port");
            for (on, names) in [
                (caps.clocks, &["wasi:clocks/monotonic-clock", "wasi:clocks/system-clock"][..]),
                (caps.random, &["wasi:random/random"][..]),
                (caps.http, &["wasi:http/types", "wasi:http/client"][..]),
                (caps.log, &["wasi:logging/logging"][..]),
                (caps.workers, &["puddi:runtime/workers", "puddi:runtime/port"][..]),
            ] {
                if on {
                    plat.extend(names.iter().copied());
                    extra_names.extend(names.iter().map(|s| s.to_string()));
                }
            }
            if caps.workers {
                extra_exports.push("puddi:runtime/worker-main".into());
                w = crate::wit::Wit::load_with(base.clone(), base_own, &c.world, &extra_names, &extra_exports).map_err(internal_user)?;
            }
            let mut host = Vec::new();
            for (on, m) in [(caps.clocks, "std.time"), (caps.random, "std.random"), (caps.http, "std.http"), (caps.workers, "std.worker")] {
                if on {
                    host.push(m.to_string());
                }
            }
            program::set_host_modules(host);
        }
        let extra: Vec<wit_parser::InterfaceId> = extra_names.iter().filter_map(|n| crate::wit::Wit::find_interface(&w.resolve, n)).collect();
        // generate binding modules for the needed interfaces and everything they use
        let mut todo: Vec<wit_parser::InterfaceId> = extra.clone();
        let mut done = std::collections::BTreeSet::new();
        while let Some(i) = todo.pop() {
            if !done.insert(i) {
                continue;
            }
            let mut g = crate::wit::Gen::new(&w, Some(i));
            let text = g.interface_module(i).map_err(internal_user)?;
            for dep in g.imports.keys() {
                todo.push(*dep);
            }
            binding_sources.push((crate::wit::module_path(&w.resolve, i), text));
        }
        for p in &plat {
            if let Some(i) = crate::wit::Wit::find_interface(&w.resolve, p) {
                let mp = crate::wit::module_path(&w.resolve, i);
                let alias = format!("__w_{}", mp.trim_start_matches("std.__wit.").replace('.', "_"));
                platform_imports.push_str(&format!("import {mp} as {alias}\n"));
            }
        }
        let pieces = [
            if caps.clocks { PLATFORM_CLOCKS } else { PLATFORM_NO_CLOCKS },
            if caps.random { PLATFORM_RANDOM } else { PLATFORM_NO_RANDOM },
            if caps.http { PLATFORM_HTTP } else { PLATFORM_NO_HTTP },
            if caps.workers { PLATFORM_WORKERS } else { PLATFORM_NO_WORKERS },
        ]
        .join("\n");
        let layer = if target == "wasi" { PLATFORM_WASI.to_string() } else { format!("{PLATFORM_PLUGIN}\n{}", if caps.log { PLATFORM_LOG } else { PLATFORM_NO_LOG }) };
        platform_text = format!("{SOFT}\n{PLATFORM_CORE}\n{layer}\n{pieces}");
        wit_ctx = Some(w);
    }

    phase("wit bindings");
    // prelude, std and the WIT bindings, parsed in parallel (the prelude alone is ~50k tokens)
    let prelude_text = format!("{platform_imports}{PRELUDE}\n{platform_text}\n// ---- generated numeric prelude ----\n{}", crate::numeric::generate());
    // (module path, package, is the prelude, file id)
    let mut jobs: Vec<(String, Pkg, u32)> = vec![("prelude".into(), Pkg::Prelude, sm.add("<prelude>".into(), prelude_text))];
    for (path, text, _) in program::STD_MODULES {
        if program::std_available(path, target) == Some(true) {
            jobs.push((path.to_string(), Pkg::Std, sm.add(format!("<{path}>"), text.to_string())));
        }
    }
    for (path, text) in binding_sources {
        let fid = sm.add(format!("<WIT bindings {path}>"), text);
        jobs.push((path, Pkg::Std, fid));
    }
    let parsed = parse_parallel(sm, &jobs.iter().map(|j| j.2).collect::<Vec<_>>());
    for ((path, pkg, _), res) in jobs.into_iter().zip(parsed) {
        match res {
            Ok(mut m) => {
                if pkg == Pkg::Prelude {
                    sources.push(ModSource { path, pkg, ast: m, prefix: String::new(), aliases: Default::default() });
                    continue;
                }
                if let Err(e) = with_derives(sm, &mut m, &path) {
                    errs.extend(e);
                }
                sources.push(ModSource { path, pkg, ast: m, prefix: "std".into(), aliases: Default::default() });
            }
            Err(e) if pkg == Pkg::Prelude => return Err(vec![e]),
            Err(e) => errs.push(e),
        }
    }
    // user
    let mut has_main = false;
    let mut user_exports: Vec<(String, bool)> = Vec::new();
    for (f, m) in user_mods {
        match Ok::<ast::Module, Vec<Diag>>(m) {
            Ok(mut m) => {
                if f.pkg == Pkg::User && f.module == root {
                    for it in &m.items {
                        if let ast::ItemKind::Fn(fd) = &it.kind {
                            if it.vis == ast::Vis::Export {
                                user_exports.push((fd.name.name.clone(), fd.is_async));
                            }
                        }
                    }
                }
                if let Err(e) = with_derives(sm, &mut m, &f.module) {
                    errs.extend(e);
                }
                if f.module == root && f.pkg == Pkg::User && mode != Mode::Test {
                    let main = m.items.iter().find_map(|it| match &it.kind {
                        ast::ItemKind::Fn(fd) if fd.name.name == "main" => Some(fd.clone()),
                        _ => None,
                    });
                    if let Some(fd) = main {
                        has_main = true;
                        let call = if fd.is_async { "main().__await()" } else { "main()" };
                        let unit_entry = format!("fn __entry() -> Int {{\n    {call}\n    0\n}}\n");
                        let result_entry = format!("fn __entry() -> Int {{\n    match {call} {{\n        Ok(_) -> 0\n        Err(e) -> {{\n            eprint(\"error: {{e}}\")\n            1\n        }}\n    }}\n}}\n");
                        let entry = match &fd.ret {
                            None => Some(unit_entry),
                            Some(ast::TypeExpr::Tuple(ts, _)) if ts.is_empty() => Some(unit_entry),
                            Some(ast::TypeExpr::Path { segs, .. }) if segs.last().map(|s| s.name == "Result").unwrap_or(false) => Some(result_entry),
                            Some(t) => {
                                errs.push(Diag::new(t.span(), "`main` must return `()` or `Result<(), E>`"));
                                None
                            }
                        };
                        if !fd.params.is_empty() {
                            errs.push(Diag::new(fd.name.span, "`main` takes no parameters; use `std.env.args()` for command-line arguments"));
                        }
                        if let Some(src) = entry {
                            match parse_file(sm, "<entry>".into(), src) {
                                Ok(e) => m.items.extend(e.items),
                                Err(e) => errs.extend(e),
                            }
                        }
                    }
                }
                if f.pkg == Pkg::User && f.module == root {
                    if let Some(w) = &wit_ctx {
                        match export_wrappers(w, target, has_main, &user_exports) {
                            Ok(src) => match parse_file(sm, "<component exports>".into(), src) {
                                Ok(e) => {
                                    m.imports.extend(e.imports);
                                    m.items.extend(e.items);
                                }
                                Err(e) => errs.extend(e),
                            },
                            Err(e) => errs.push(Diag::new(crate::diag::Span::new(u32::MAX, 0, 0), e)),
                        }
                    }
                }
                sources.push(ModSource { path: f.module.clone(), pkg: f.pkg, ast: m, prefix: f.prefix.clone(), aliases: f.aliases.clone() });
            }
            Err(e) => errs.extend(e),
        }
    }
    if !errs.is_empty() {
        return Err(errs);
    }

    phase("parse");
    // leaked so that it can be dropped on another thread at the end (see below)
    let prog: &'static program::Program = Box::leak(Box::new(program::build(sources, target)?));
    phase("program");
    let mut g = Global::new(prog);
    let root_mod = prog.modules.iter().position(|m| m.path == root && m.pkg == Pkg::User);
    let mut entry = None;
    let mut tests = Vec::new();
    let mut platform_fns = Vec::new();
    let mut platform_ids = Vec::new();
    if wit_ctx.is_some() {
        for name in PLATFORM_FNS {
            match prog.lookup(prog.prelude, name) {
                Some(program::Def::Fn(fid)) => platform_ids.push(fid),
                _ => return Err(internal(format!("internal error: platform function `{name}` is missing"))),
            }
        }
    }
    for (fid, f) in prog.fns.iter().enumerate() {
        if f.pkg != Pkg::User {
            // runtime entry points the JavaScript host calls (`@export` in the prelude and std)
            if mode != Mode::Check && wit_ctx.is_none() && f.export.is_some() && f.generics.is_empty() && matches!(f.owner, FnOwner::Free) {
                g.request(FnInst { fn_id: fid, targs: Vec::new() });
            }
            continue;
        }
        if let Some(name) = &f.test_name {
            if mode != Mode::Build {
                let idx = g.request(FnInst { fn_id: fid, targs: Vec::new() });
                tests.push((name.clone(), idx));
            }
            continue;
        }
        let generic = !f.generics.is_empty();
        let ok = match f.owner {
            FnOwner::Free => !generic,
            FnOwner::Impl(_) => !generic,
            FnOwner::Trait(_) => false,
        };
        if !ok {
            continue;
        }
        let idx = g.request(FnInst { fn_id: fid, targs: Vec::new() });
        if f.name == "__entry" && Some(f.module) == root_mod {
            entry = Some(idx);
        }
    }
    g.run();
    if wit_ctx.is_some() {
        platform_fns = elaborate_platform(&mut g, &platform_ids);
    }
    phase("elab");
    let mut warnings = prog.warnings.clone();
    warnings.extend(g.warnings.clone());
    if !g.errors.is_empty() {
        let mut errs = g.errors.clone();
        errs.sort_by_key(|d| (d.span.file, d.span.lo));
        return Err(errs);
    }
    if mode == Mode::Check {
        return Ok(Compiled { wasm: Vec::new(), component: None, wat: String::new(), tests: Vec::new(), warnings, has_main });
    }
    crate::opt::run(&mut g);
    phase("opt");
    let plat = if wit_ctx.is_some() { Some(platform_fns.as_slice()) } else { None };
    let out = codegen::generate(&prog, &g, if plat.is_some() { None } else { entry }, &tests, plat).map_err(internal)?;
    phase("codegen");
    let component = match &wit_ctx {
        Some(w) => Some(w.encode(&out.wasm).map_err(|e| internal(format!("internal error: component encoding failed: {e}")))?),
        None => None,
    };
    phase("component");
    // freeing the program, its IR and the WIT resolve takes several milliseconds, which
    // `pud run` would otherwise spend before the program starts
    std::thread::spawn(move || {
        drop(g);
        drop(wit_ctx);
        // SAFETY: `prog` was leaked from a Box above and `g`, its only borrower, is gone
        drop(unsafe { Box::from_raw(prog as *const program::Program as *mut program::Program) });
    });
    Ok(Compiled { wasm: out.wasm, component, wat: out.wat, tests: out.tests, warnings, has_main })
}

/// Elaborates the platform layer once the program is elaborated. The host operation
/// dispatchers (`__plat_host`, `__plat_host_async`) keep only the arms for operation
/// numbers the program uses, so a program that never touches files or HTTP does not
/// carry their bindings. Elaborating the platform layer can reach code that uses more
/// operations; the dispatchers are then elaborated again until the set is stable.
fn elaborate_platform(g: &mut Global, ids: &[crate::types::FnId]) -> Vec<usize> {
    let prog = g.prog;
    let dispatchers: Vec<crate::types::FnId> = ["__plat_host", "__plat_host_async"].iter().filter_map(|n| match prog.lookup(prog.prelude, n) {
        Some(program::Def::Fn(fid)) => Some(fid),
        _ => None,
    }).collect();
    let mut kept: Option<std::collections::BTreeSet<i128>> = None;
    let mut idxs = Vec::new();
    for round in 0..8 {
        let used = host_ops(g);
        if round > 0 && (kept == used || matches!((&kept, &used), (Some(k), Some(u)) if u.is_subset(k))) {
            break;
        }
        g.body_override.clear();
        if let Some(u) = &used {
            for &fid in &dispatchers {
                if let Some(b) = prog.fns[fid].decl.body.as_ref().and_then(|b| prune_ops(b, u)) {
                    g.body_override.insert(fid, b);
                }
            }
        }
        if round == 0 {
            idxs = ids.iter().map(|&fid| g.request(FnInst { fn_id: fid, targs: Vec::new() })).collect();
        } else {
            for &fid in &dispatchers {
                g.reelaborate(FnInst { fn_id: fid, targs: Vec::new() });
            }
        }
        g.run();
        kept = used;
        if kept.is_none() {
            break;
        }
    }
    idxs
}

/// The operation numbers passed to the `host` intrinsics, or None if one is not a literal.
fn host_ops(g: &Global) -> Option<std::collections::BTreeSet<i128>> {
    let mut ops = std::collections::BTreeSet::new();
    let mut all = false;
    for f in g.funcs.iter().flatten() {
        crate::opt::visit(&f.body, &mut |e| {
            if let crate::ir::ExprKind::Intrinsic(name, _, args) = &e.kind {
                if name == "host" || name == "host_async" {
                    match args.first().map(|a| &a.kind) {
                        Some(crate::ir::ExprKind::Lit(crate::ir::Lit::Int(v))) => {
                            ops.insert(*v);
                        }
                        _ => all = true,
                    }
                }
            }
        });
    }
    if all { None } else { Some(ops) }
}

/// The body with the arms of its `match op` that handle unused operations removed.
fn prune_ops(body: &ast::Block, used: &std::collections::BTreeSet<i128>) -> Option<ast::Block> {
    let tail = body.tail.as_ref()?;
    let ast::ExprKind::Match { scrut, arms } = &tail.kind else { return None };
    if !matches!(&scrut.kind, ast::ExprKind::Name(id, _) if id.name == "op") {
        return None;
    }
    fn keep(p: &ast::Pattern, used: &std::collections::BTreeSet<i128>) -> bool {
        match &p.kind {
            ast::PatKind::Lit(ast::LitPat::Int(v)) => used.contains(v),
            ast::PatKind::Or(ps) => ps.iter().any(|p| keep(p, used)),
            _ => true,
        }
    }
    let arms: Vec<ast::Arm> = arms.iter().filter(|a| keep(&a.pat, used)).cloned().collect();
    let mut b = body.clone();
    b.tail = Some(Box::new(ast::Expr { kind: ast::ExprKind::Match { scrut: scrut.clone(), arms }, ..(**tail).clone() }));
    Some(b)
}

fn internal_user(m: String) -> Vec<Diag> {
    vec![Diag::new(crate::diag::Span::new(u32::MAX, 0, 0), m)]
}


/// Export wrappers for the world's exports.
fn export_wrappers(w: &crate::wit::Wit, target: &str, has_main: bool, user_exports: &[(String, bool)]) -> Result<String, String> {
    let mut g = crate::wit::Gen::new(w, None);
    let mut items = String::new();
    let mut missing = Vec::new();
    for (k, (export, f, pname)) in crate::wit::world_exports(w).into_iter().enumerate() {
        let target_fn = if export.starts_with("puddi:runtime/worker-main@") {
            "__plat_worker_start".to_string()
        } else if target == "wasi" && export.starts_with("wasi:cli/run@") {
            if !has_main {
                missing.push("`fn main()` (the world exports `wasi:cli/run`)".to_string());
                continue;
            }
            items.push_str("fn __wasi_run() -> Result<(), ()> {\n    let code = __entry()\n    if code == 0 { return Ok(()) }\n    __plat_host(12, \"{code}\")\n    Err(())\n}\n\n");
            "__wasi_run".to_string()
        } else if let Some((_, is_async)) = user_exports.iter().find(|(n, _)| *n == pname) {
            if *is_async && !f.kind.is_async() {
                missing.push(format!("`{export}` to be an `async func` for `export async fn {pname}` (a synchronous export cannot wait)"));
                continue;
            }
            g.await_call = *is_async;
            pname.clone()
        } else {
            missing.push(format!("`export fn {pname}` for `{export}`"));
            continue;
        };
        items.push_str(&g.export_fn(&f, &export, &target_fn, k));
        g.await_call = false;
    }
    if !missing.is_empty() {
        return Err(format!("the program's exports do not match the target world: it needs {}", missing.join(", ")));
    }
    let mut head = String::new();
    for (iid, alias) in &g.imports {
        head.push_str(&format!("import {} as {alias}\n", crate::wit::module_path(&w.resolve, *iid)));
    }
    Ok(head + &items)
}

/// Whether an import brings in `std.worker`.
fn imports_worker(i: &ast::Import) -> bool {
    let p: Vec<&str> = i.path.iter().map(|x| x.name.as_str()).collect();
    p == ["std", "worker"] || (p == ["std"] && i.names.as_ref().map(|ns| ns.iter().any(|n| n.name == "worker")).unwrap_or(false))
}

/// Runtime capabilities linked into a component.
struct Caps {
    clocks: bool,
    random: bool,
    http: bool,
    log: bool,
    workers: bool,
}
