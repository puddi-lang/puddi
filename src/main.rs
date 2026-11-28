//! `pud`: the Puddi toolchain.

#![allow(dead_code)]

mod asm;
mod ast;
mod codegen;
mod deps;
mod derive;
mod diag;
mod driver;
mod elab;
mod exhaust;
mod ir;
mod lexer;
mod numeric;
mod parser;
mod program;
mod opt;
mod ranges;
#[cfg(feature = "runtime")]
mod runner;
mod tools;
mod types;
mod wit;

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use diag::SourceMap;
use driver::{Mode, UserFile};

const RUNTIME: &str = include_str!("runtime.mjs");
const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(serde::Deserialize)]
struct Manifest {
    package: PackageInfo,
    #[serde(default)]
    deps: toml::Table,
    /// Per-target settings, e.g. `[target.plugin] world = "wit/host.wit#plugin"`.
    #[serde(default)]
    target: toml::Table,
}

#[derive(serde::Deserialize)]
struct PackageInfo {
    name: String,
    #[allow(dead_code)]
    version: Option<String>,
    #[allow(dead_code)]
    puddi: Option<String>,
}

struct Project {
    name: String,
    /// Package directory (None for single-file mode).
    dir: Option<PathBuf>,
    files: Vec<UserFile>,
    root: String,
    targets: toml::Table,
}

impl Project {
    /// The component world for a target, if it builds a component.
    fn world(&self, target: &str) -> Result<Option<String>, String> {
        let configured = self.targets.get(target).and_then(|t| t.get("world")).map(|w| w.as_str().map(|s| s.to_string()).ok_or_else(|| format!("`target.{target}.world` in pud.toml must be a string")));
        match target {
            "wasi" => Ok(Some(configured.transpose()?.unwrap_or_else(|| "wasi:cli/command".into()))),
            "plugin" => match configured.transpose()? {
                Some(w) => Ok(Some(w)),
                None => Err("the plugin target needs a world: add `[target.plugin]` with `world = \"wit/<file>.wit#<world>\"` to pud.toml".into()),
            },
            _ => Ok(None),
        }
    }
}

fn usage() -> &'static str {
    "pud - the Puddi toolchain

usage:
  pud new <name>                 create a package
  pud build [path] [--target t] [--emit-wat] [-o dir]
                                 build a component for browser, wasi (default) or plugin
  pud run [path|file.pud] [-- args...]
                                 build and run (wasi: embedded Wasmtime,
                                 browser: dev server, plugin: `-- <export> [args]`)
  pud test [path|file.pud] [filter]
                                 run test blocks
  pud check [path|file.pud]      type-check without generating code
  pud fmt [files...] [--check]   format sources in the single official style
  pud doc [path]                 write Markdown docs for public items to target/doc
  pud add <repo@version|path> [--name n]
                                 add a dependency to pud.toml and update pud.lock
  pud version                    print the version
"
}

fn fail(msg: impl AsRef<str>) -> ExitCode {
    eprintln!("error: {}", msg.as_ref());
    ExitCode::from(1)
}

fn collect_pud(dir: &Path, base: &Path, out: &mut Vec<(String, PathBuf)>) -> std::io::Result<()> {
    let mut entries: Vec<_> = std::fs::read_dir(dir)?.collect::<Result<_, _>>()?;
    entries.sort_by_key(|e| e.path());
    for e in entries {
        let p = e.path();
        if p.is_dir() {
            collect_pud(&p, base, out)?;
        } else if p.extension().map(|x| x == "pud").unwrap_or(false) {
            let rel = p.strip_prefix(base).unwrap().with_extension("");
            let module = rel.components().map(|c| c.as_os_str().to_string_lossy().to_string()).collect::<Vec<_>>().join(".");
            out.push((module, p));
        }
    }
    Ok(())
}

fn find_manifest(start: &Path) -> Option<PathBuf> {
    let mut d = Some(start.to_path_buf());
    while let Some(dir) = d {
        if dir.join("pud.toml").is_file() {
            return Some(dir);
        }
        d = dir.parent().map(|p| p.to_path_buf());
    }
    None
}

fn load_project(path: Option<&str>) -> Result<Project, String> {
    let p = PathBuf::from(path.unwrap_or("."));
    if p.is_file() {
        if p.file_name().map(|n| n == "pud.toml").unwrap_or(false) {
            return load_project(Some(p.parent().unwrap().to_str().unwrap_or(".")));
        }
        let text = std::fs::read_to_string(&p).map_err(|e| format!("cannot read {}: {e}", p.display()))?;
        let name = p.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_else(|| "main".into());
        return Ok(Project { name, dir: None, files: vec![user_file("main".into(), p.display().to_string(), text)], root: "main".into(), targets: Default::default() });
    }
    let dir = find_manifest(&p).ok_or_else(|| format!("could not find pud.toml in {} or any parent directory", p.display()))?;
    let mtext = std::fs::read_to_string(dir.join("pud.toml")).map_err(|e| format!("cannot read pud.toml: {e}"))?;
    let manifest: Manifest = toml::from_str(&mtext).map_err(|e| format!("invalid pud.toml: {e}"))?;
    let mut root_deps = Vec::new();
    for (k, v) in &manifest.deps {
        root_deps.push((k.clone(), deps::parse_spec(k, v, &dir)?));
    }
    let resolution = if root_deps.is_empty() {
        None
    } else {
        Some(deps::resolve(&root_deps, Some(&dir.join("pud.lock")), true)?)
    };
    let src = dir.join("src");
    let mut found = Vec::new();
    collect_pud(&src, &src, &mut found).map_err(|e| format!("cannot read {}: {e}", src.display()))?;
    let root = if found.iter().any(|(m, _)| m == "main") {
        "main"
    } else if found.iter().any(|(m, _)| m == "lib") {
        "lib"
    } else {
        return Err("package has neither src/main.pud nor src/lib.pud".into());
    };
    let mut files = Vec::new();
    for (module, path) in found {
        let text = std::fs::read_to_string(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        let display = path.strip_prefix(&dir).unwrap_or(&path).display().to_string();
        let mut f = user_file(module, display, text);
        if let Some(r) = &resolution {
            f.aliases = r.root_aliases.clone();
        }
        files.push(f);
    }
    if let Some(r) = resolution {
        for (i, pkg) in r.packages.into_iter().enumerate() {
            for (module, display, text) in pkg.files {
                files.push(UserFile { module: format!("{}.{module}", pkg.prefix), display, text, pkg: program::Pkg::Dep(i as u16), prefix: pkg.prefix.clone(), aliases: pkg.aliases.clone() });
            }
        }
    }
    Ok(Project { name: manifest.package.name, dir: Some(dir), files, root: root.into(), targets: manifest.target })
}

fn user_file(module: String, display: String, text: String) -> UserFile {
    UserFile { module, display, text, pkg: program::Pkg::User, prefix: String::new(), aliases: Default::default() }
}

fn report(sm: &SourceMap, diags: &[diag::Diag]) {
    for d in diags {
        eprint!("{}", sm.render(d));
    }
}

struct BuildResult {
    out_dir: PathBuf,
    /// The core module for the JavaScript host.
    wasm_path: PathBuf,
    /// The component, for `wasi` and `plugin` builds.
    component: Option<(PathBuf, Vec<u8>)>,
}

/// The user's cache directory for `pud` (`PUD_NO_CACHE=1` turns caching off).
fn cache_base() -> Option<PathBuf> {
    if std::env::var_os("PUD_NO_CACHE").is_some() {
        return None;
    }
    let base = if cfg!(windows) {
        std::env::var_os("LOCALAPPDATA").map(PathBuf::from)
    } else if cfg!(target_os = "macos") {
        std::env::var_os("HOME").map(|h| PathBuf::from(h).join("Library/Caches"))
    } else {
        std::env::var_os("XDG_CACHE_HOME").map(PathBuf::from).or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))
    };
    base.map(|b| b.join("pud"))
}

/// Writes `data` to `dir/name` through a temporary file, and keeps the directory to the
/// `keep` most recently written entries.
fn cache_store(dir: &Path, name: &str, data: &[u8], keep: usize) {
    let _ = std::fs::create_dir_all(dir);
    let path = dir.join(name);
    let tmp = dir.join(format!("{name}.{}.tmp", std::process::id()));
    if std::fs::write(&tmp, data).is_ok() && std::fs::rename(&tmp, &path).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    let mut entries: Vec<(std::time::SystemTime, PathBuf)> = rd.flatten().filter_map(|e| Some((e.metadata().ok()?.modified().ok()?, e.path()))).collect();
    if entries.len() > keep {
        entries.sort();
        for (_, p) in &entries[..entries.len() - keep] {
            let _ = std::fs::remove_file(p);
        }
    }
}

/// The cache key of a component build: this `pud` executable, the target, the world, the
/// package's WIT files and every source file.
fn build_key(proj: &Project, target: &str, comp: &driver::ComponentOpts) -> Option<String> {
    use std::hash::{Hash, Hasher};
    cache_base()?;
    let exe = std::env::current_exe().ok()?;
    let meta = std::fs::metadata(&exe).ok()?;
    let mut wit_files: Vec<(PathBuf, Vec<u8>)> = Vec::new();
    if let Some(d) = &comp.pkg_dir {
        let mut todo = vec![d.join("wit")];
        while let Some(dir) = todo.pop() {
            let Ok(rd) = std::fs::read_dir(&dir) else { continue };
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() {
                    todo.push(p);
                } else {
                    wit_files.push((p.clone(), std::fs::read(&p).ok()?));
                }
            }
        }
        wit_files.sort();
    }
    let mut key = String::new();
    for salt in [0u8, 1] {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        (salt, env!("CARGO_PKG_VERSION"), &exe, meta.len(), meta.modified().ok()).hash(&mut h);
        (target, &comp.world, &comp.pkg_dir, &wit_files, std::env::var("PUD_NO_OPT").ok(), &proj.root).hash(&mut h);
        for f in &proj.files {
            let mut aliases: Vec<_> = f.aliases.iter().collect();
            aliases.sort();
            (&f.module, format!("{:?}", f.pkg), &f.prefix, aliases, &f.display, &f.text).hash(&mut h);
        }
        key.push_str(&format!("{:016x}", h.finish()));
    }
    Some(key)
}

fn cache_get(key: &str) -> Option<driver::Compiled> {
    let data = std::fs::read(cache_base()?.join("build").join(key)).ok()?;
    let n = u64::from_le_bytes(data.get(..8)?.try_into().ok()?) as usize;
    let (wasm, component) = data.get(8..)?.split_at_checked(n)?;
    Some(driver::Compiled { wasm: wasm.to_vec(), component: Some(component.to_vec()), wat: String::new(), tests: Vec::new(), warnings: Vec::new(), has_main: true })
}

fn cache_put(key: &str, c: &driver::Compiled) {
    let (Some(dir), Some(comp)) = (cache_base(), &c.component) else { return };
    let mut data = (c.wasm.len() as u64).to_le_bytes().to_vec();
    data.extend_from_slice(&c.wasm);
    data.extend_from_slice(comp);
    cache_store(&dir.join("build"), key, &data, 64);
}

/// `ephemeral`: the component is only run in this process, so nothing is written to disk.
fn build(proj: Project, target: &str, mode: Mode, out: Option<PathBuf>, emit_wat: bool, ephemeral: bool) -> Result<BuildResult, ExitCode> {
    let mut sm = SourceMap::default();
    let name = proj.name.clone();
    // tests run on the JavaScript host; everything else for wasi/plugin is a component
    let node_host = target == "wasi" && std::env::var("PUD_HOST").as_deref() == Ok("node");
    let comp = if mode == Mode::Test || target == "browser" || node_host {
        None
    } else {
        match proj.world(target) {
            Ok(w) => w.map(|world| driver::ComponentOpts { pkg_dir: proj.dir.clone(), world }),
            Err(e) => {
                eprintln!("error: {e}");
                return Err(ExitCode::from(1));
            }
        }
    };
    // a build of exactly the same inputs is reused, as long as it had no warnings to repeat
    let key = match &comp {
        Some(c) if mode == Mode::Build && !emit_wat => build_key(&proj, target, c),
        _ => None,
    };
    let cached = key.as_deref().and_then(cache_get);
    let compiled = match cached {
        Some(c) => c,
        None => {
            let compiled = match driver::compile(&mut sm, proj.files, &proj.root, target, mode, comp) {
                Ok(c) => c,
                Err(errs) => {
                    report(&sm, &errs);
                    let n = errs.iter().filter(|d| !d.warning).count();
                    eprintln!("error: could not compile `{name}` due to {n} previous error{}", if n == 1 { "" } else { "s" });
                    return Err(ExitCode::from(1));
                }
            };
            report(&sm, &compiled.warnings);
            if let Some(k) = &key {
                if compiled.warnings.is_empty() {
                    cache_put(k, &compiled);
                }
            }
            compiled
        }
    };
    if mode == Mode::Check {
        return Ok(BuildResult { out_dir: PathBuf::new(), wasm_path: PathBuf::new(), component: None });
    }
    if ephemeral && !emit_wat {
        if let Some(c) = compiled.component {
            return Ok(BuildResult { out_dir: PathBuf::new(), wasm_path: PathBuf::new(), component: Some((PathBuf::new(), c)) });
        }
    }
    let out_dir = match out {
        Some(o) => o,
        None => match &proj.dir {
            Some(d) => d.join("target").join(if mode == Mode::Test { "test" } else { target }),
            None => std::env::temp_dir().join(format!("puddi-{}-{}", name, std::process::id())),
        },
    };
    if let Err(e) = std::fs::create_dir_all(&out_dir) {
        eprintln!("error: cannot create {}: {e}", out_dir.display());
        return Err(ExitCode::from(1));
    }
    let wasm_path = out_dir.join(if compiled.component.is_some() { format!("{name}.core.wasm") } else { format!("{name}.wasm") });
    let write = |p: PathBuf, data: &[u8]| -> Result<(), ExitCode> {
        std::fs::write(&p, data).map_err(|e| {
            eprintln!("error: cannot write {}: {e}", p.display());
            ExitCode::from(1)
        })
    };
    // browser builds ship a component; puddi.mjs unpacks its core module
    let browser_component = if target == "browser" && mode == Mode::Build {
        match wit::browser_component(&compiled.wasm) {
            Ok(c) => Some(c),
            Err(e) => {
                eprintln!("error: internal error: browser component encoding failed: {e}");
                return Err(ExitCode::from(1));
            }
        }
    } else {
        None
    };
    write(wasm_path.clone(), browser_component.as_deref().unwrap_or(&compiled.wasm))?;
    let component = match compiled.component {
        Some(c) => {
            let p = out_dir.join(format!("{name}.wasm"));
            write(p.clone(), &c)?;
            Some((p, c))
        }
        None => None,
    };
    write(out_dir.join("puddi.mjs"), RUNTIME.as_bytes())?;
    if emit_wat {
        write(out_dir.join(format!("{name}.wat")), compiled.wat.as_bytes())?;
    }
    if mode == Mode::Test {
        let json: Vec<String> = compiled.tests.iter().map(|(n, e)| format!("[{},{}]", json_str(n), json_str(e))).collect();
        write(out_dir.join(format!("{name}.tests.json")), format!("[{}]", json.join(",")).as_bytes())?;
    }
    if target == "browser" && mode == Mode::Build {
        let html = format!(
            "<!doctype html>\n<html>\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>{name}</title>\n<style>body{{font:14px/1.5 ui-monospace,monospace;margin:16px;background:#fafafa;color:#222}}pre{{white-space:pre-wrap}}.err{{color:#b00}}</style>\n</head>\n<body>\n<pre id=\"out\"></pre>\n<script type=\"module\">\nimport {{ load }} from \"./puddi.mjs\";\nconst out = document.getElementById(\"out\");\nconst app = await load(\"./{name}.wasm\", {{ output(fd, line) {{ const s = document.createElement(\"span\"); if (fd === 2) s.className = \"err\"; s.textContent = line + \"\\n\"; out.append(s); (fd === 2 ? console.error : console.log)(line); }} }});\nawait app.run();\n</script>\n</body>\n</html>\n"
        );
        write(out_dir.join("index.html"), html.as_bytes())?;
    }
    Ok(BuildResult { out_dir, wasm_path, component })
}

fn json_str(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn node_run(res: &BuildResult, cmd: &str, args: &[String]) -> ExitCode {
    // V8 has no on-stack replacement for wasm: a loop in a function that runs once (often
    // `main`) stays in Liftoff's baseline code for good. Compiling with TurboFan only makes
    // such loops 2-3x faster for a few milliseconds of start-up.
    let status = Command::new("node").arg("--no-liftoff").arg(res.out_dir.join("puddi.mjs")).arg(cmd).arg(&res.wasm_path).args(args).status();
    match status {
        Ok(s) => match s.code() {
            Some(c) => ExitCode::from(c.clamp(0, 255) as u8),
            None => ExitCode::from(1),
        },
        Err(e) => fail(format!("could not start `node` ({e}); Node.js 22 or newer is needed to run Puddi programs")),
    }
}

#[cfg(feature = "runtime")]
fn run_component(res: &BuildResult, program: &str, args: &[String]) -> ExitCode {
    let (_, bytes) = res.component.as_ref().unwrap();
    ExitCode::from(runner::run(bytes, program, args))
}

#[cfg(feature = "runtime")]
fn invoke_plugin(res: &BuildResult, program: &str, export: &str, args: &[String]) -> ExitCode {
    let (_, bytes) = res.component.as_ref().unwrap();
    ExitCode::from(runner::invoke(bytes, program, export, args))
}

#[cfg(not(feature = "runtime"))]
fn invoke_plugin(res: &BuildResult, _program: &str, _export: &str, _args: &[String]) -> ExitCode {
    fail(format!("this `pud` was built without the embedded runtime; load {} in its host application", res.component.as_ref().unwrap().0.display()))
}

#[cfg(not(feature = "runtime"))]
fn run_component(res: &BuildResult, _program: &str, _args: &[String]) -> ExitCode {
    fail(format!("this `pud` was built without the embedded runtime; run {} with a WASI 0.3 host such as `wasmtime run -Wcomponent-model-async -Wgc`, or set PUD_HOST=node", res.component.as_ref().unwrap().0.display()))
}

fn new_package(name: &str) -> ExitCode {
    let dir = PathBuf::from(name);
    if dir.exists() {
        return fail(format!("`{name}` already exists"));
    }
    let pkg = dir.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_else(|| name.to_string());
    let res = (|| -> std::io::Result<()> {
        std::fs::create_dir_all(dir.join("src"))?;
        std::fs::write(dir.join("pud.toml"), format!("[package]\nname = \"{pkg}\"\nversion = \"0.1.0\"\npuddi = \"0.1\"\n\n[deps]\n"))?;
        std::fs::write(
            dir.join("src/main.pud"),
            "fn greet(name: Str) -> Str {\n    \"Hello, {name}!\"\n}\n\nfn main() {\n    print(greet(\"Puddi\"))\n}\n\ntest \"greet says hello\" {\n    assert_eq(greet(\"you\"), \"Hello, you!\")\n}\n",
        )?;
        std::fs::write(dir.join(".gitignore"), "target/\n")?;
        Ok(())
    })();
    match res {
        Ok(()) => {
            println!("created package `{pkg}` in {}", dir.display());
            ExitCode::SUCCESS
        }
        Err(e) => fail(format!("cannot create package: {e}")),
    }
}

fn main() -> ExitCode {
    driver::phase("main");
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = args.first().cloned() else {
        print!("{}", usage());
        return ExitCode::SUCCESS;
    };
    let rest = &args[1..];
    // split off `-- args`
    let (opts, prog_args): (&[String], &[String]) = match rest.iter().position(|a| a == "--") {
        Some(i) => (&rest[..i], &rest[i + 1..]),
        None => (rest, &[]),
    };
    let mut target = "wasi".to_string();
    let mut emit_wat = false;
    let mut check_only = false;
    let mut name_opt: Option<String> = None;
    let mut out = None;
    let mut positional = Vec::new();
    let mut i = 0;
    while i < opts.len() {
        let inline_target = opts[i].strip_prefix("--target=");
        match opts[i].as_str() {
            s if matches!(s, "--target" | "-t") || inline_target.is_some() => {
                let value = inline_target.or_else(|| {
                    i += 1;
                    opts.get(i).map(String::as_str)
                });
                match value {
                    Some(t) if ["browser", "wasi", "plugin"].contains(&t) => target = t.to_string(),
                    Some(t) => return fail(format!("unknown target `{t}`; expected browser, wasi or plugin")),
                    None => return fail("--target needs a value"),
                }
            }
            "--emit-wat" => emit_wat = true,
            "--check" => check_only = true,
            "--name" => {
                i += 1;
                match opts.get(i) {
                    Some(n) => name_opt = Some(n.clone()),
                    None => return fail("--name needs a value"),
                }
            }
            "-o" | "--out" => {
                i += 1;
                match opts.get(i) {
                    Some(o) => out = Some(PathBuf::from(o)),
                    None => return fail("-o needs a directory"),
                }
            }
            s if s.starts_with('-') && s.len() > 1 => return fail(format!("unknown option `{s}`")),
            s => positional.push(s.to_string()),
        }
        i += 1;
    }
    match cmd.as_str() {
        "new" => match positional.first() {
            Some(n) => new_package(n),
            None => fail("usage: pud new <name>"),
        },
        "build" | "run" | "test" | "check" => {
            let proj = match load_project(positional.first().map(|s| s.as_str())) {
                Ok(p) => p,
                Err(e) => return fail(e),
            };
            let mode = match cmd.as_str() {
                "test" => Mode::Test,
                "check" => Mode::Check,
                _ => Mode::Build,
            };
            let has_dir = proj.dir.is_some();
            let program_name = proj.name.clone();
            // a single file run by the embedded runtime needs no files on disk, and the
            // engine can be created while the program compiles
            let embedded = cmd == "run" && target != "browser" && std::env::var("PUD_HOST").as_deref() != Ok("node") && cfg!(feature = "runtime");
            #[cfg(feature = "runtime")]
            if embedded {
                runner::prewarm();
            }
            let res = match build(proj, &target, mode, out.clone(), emit_wat, embedded && !has_dir && out.is_none()) {
                Ok(r) => r,
                Err(c) => return c,
            };
            driver::phase("built");
            match cmd.as_str() {
                "build" => {
                    println!("built {}", res.component.as_ref().map(|c| &c.0).unwrap_or(&res.wasm_path).display());
                    ExitCode::SUCCESS
                }
                "run" if target == "plugin" => match prog_args.split_first() {
                    Some((export, args)) => invoke_plugin(&res, &program_name, export, args),
                    None => fail("usage: pud run --target plugin [path] -- <export> [args...]"),
                },
                "run" if res.component.is_some() && std::env::var("PUD_HOST").as_deref() != Ok("node") => {
                    let code = run_component(&res, &program_name, prog_args);
                    if !has_dir && !res.out_dir.as_os_str().is_empty() {
                        let _ = std::fs::remove_dir_all(&res.out_dir);
                    }
                    code
                }
                "check" => ExitCode::SUCCESS,
                "run" if target == "browser" && mode == Mode::Build => serve(&res.out_dir, &res.wasm_path),
                "run" => {
                    let code = node_run(&res, "run", prog_args);
                    if !has_dir {
                        let _ = std::fs::remove_dir_all(&res.out_dir);
                    }
                    code
                }
                _ => {
                    let filter: Vec<String> = positional.get(1).cloned().into_iter().collect();
                    let code = node_run(&res, "test", &filter);
                    if !has_dir {
                        let _ = std::fs::remove_dir_all(&res.out_dir);
                    }
                    code
                }
            }
        }
        "fmt" => run_fmt(&positional, check_only),
        "doc" => run_doc(positional.first().map(|s| s.as_str())),
        "add" => run_add(&positional, name_opt.as_deref()),
        "version" | "--version" | "-V" => {
            println!("pud {VERSION}");
            ExitCode::SUCCESS
        }
        "help" | "--help" | "-h" => {
            print!("{}", usage());
            ExitCode::SUCCESS
        }
        other => fail(format!("unknown command `{other}`\n\n{}", usage())),
    }
}

fn fmt_targets(positional: &[String]) -> Result<Vec<PathBuf>, String> {
    if !positional.is_empty() && positional.iter().all(|p| p.ends_with(".pud")) {
        return Ok(positional.iter().map(PathBuf::from).collect());
    }
    let start = PathBuf::from(positional.first().map(|s| s.as_str()).unwrap_or("."));
    let dir = find_manifest(&start).ok_or_else(|| "could not find pud.toml; pass .pud files explicitly".to_string())?;
    let src = dir.join("src");
    let mut found = Vec::new();
    collect_pud(&src, &src, &mut found).map_err(|e| e.to_string())?;
    Ok(found.into_iter().map(|(_, p)| p).collect())
}

fn run_fmt(positional: &[String], check: bool) -> ExitCode {
    let files = match fmt_targets(positional) {
        Ok(f) => f,
        Err(e) => return fail(e),
    };
    let mut changed = 0;
    for f in &files {
        let text = match std::fs::read_to_string(f) {
            Ok(t) => t,
            Err(e) => return fail(format!("cannot read {}: {e}", f.display())),
        };
        let formatted = tools::format(&text);
        if formatted != text {
            changed += 1;
            if check {
                println!("would reformat {}", f.display());
            } else if let Err(e) = std::fs::write(f, formatted) {
                return fail(format!("cannot write {}: {e}", f.display()));
            } else {
                println!("formatted {}", f.display());
            }
        }
    }
    if check && changed > 0 { ExitCode::from(1) } else { ExitCode::SUCCESS }
}

fn run_doc(path: Option<&str>) -> ExitCode {
    let proj = match load_project(path) {
        Ok(p) => p,
        Err(e) => return fail(e),
    };
    let mut page = format!("# {}\n\n", proj.name);
    for f in proj.files.iter().filter(|f| f.pkg == program::Pkg::User) {
        if let Some(d) = tools::doc(&f.module, &f.text) {
            page.push_str(&d);
        }
    }
    let out = match &proj.dir {
        Some(d) => d.join("target").join("doc"),
        None => PathBuf::from("."),
    };
    if let Err(e) = std::fs::create_dir_all(&out) {
        return fail(format!("cannot create {}: {e}", out.display()));
    }
    let file = out.join(format!("{}.md", proj.name));
    match std::fs::write(&file, page) {
        Ok(()) => {
            println!("wrote {}", file.display());
            ExitCode::SUCCESS
        }
        Err(e) => fail(format!("cannot write {}: {e}", file.display())),
    }
}

fn run_add(positional: &[String], name: Option<&str>) -> ExitCode {
    let Some(arg) = positional.first() else {
        return fail("usage: pud add <github.com/user/repo[@version]|path> [--name n]");
    };
    let Some(dir) = find_manifest(Path::new(".")) else {
        return fail("could not find pud.toml in this directory or any parent directory");
    };
    let (n, value) = match deps::add_entry(arg, name, &dir) {
        Ok(x) => x,
        Err(e) => return fail(e),
    };
    let mpath = dir.join("pud.toml");
    let text = match std::fs::read_to_string(&mpath) {
        Ok(t) => t,
        Err(e) => return fail(format!("cannot read pud.toml: {e}")),
    };
    let new_text = deps::edit_manifest(&text, &n, &value);
    if let Err(e) = std::fs::write(&mpath, &new_text) {
        return fail(format!("cannot write pud.toml: {e}"));
    }
    match load_project(Some(dir.to_str().unwrap_or("."))) {
        Ok(_) => {
            println!("added {n} = {value}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            let _ = std::fs::write(&mpath, text);
            fail(e)
        }
    }
}

/// `pud run --target browser`: a development server for the built page.
fn serve(dir: &Path, wasm: &Path) -> ExitCode {
    use std::io::{BufRead, BufReader, Write};
    let port: u16 = std::env::var("PUD_PORT").ok().and_then(|p| p.parse().ok()).unwrap_or(8000);
    let listener = match (port..port + 20).find_map(|p| std::net::TcpListener::bind(("127.0.0.1", p)).ok()) {
        Some(l) => l,
        None => return fail(format!("no free port between {port} and {}", port + 19)),
    };
    let addr = listener.local_addr().unwrap();
    println!("serving {} at http://{addr}/ (press Ctrl-C to stop)", wasm.display());
    for stream in listener.incoming() {
        let Ok(mut stream) = stream else { continue };
        let mut reader = BufReader::new(match stream.try_clone() {
            Ok(s) => s,
            Err(_) => continue,
        });
        let mut line = String::new();
        if reader.read_line(&mut line).is_err() {
            continue;
        }
        loop {
            let mut h = String::new();
            if reader.read_line(&mut h).map(|n| n == 0).unwrap_or(true) || h.trim().is_empty() {
                break;
            }
        }
        let path = line.split_whitespace().nth(1).unwrap_or("/").split('?').next().unwrap_or("/");
        let rel = if path == "/" { "index.html" } else { path.trim_start_matches('/') };
        let file = dir.join(rel);
        let safe = !rel.split('/').any(|c| c == "..");
        let resp = match std::fs::read(&file) {
            Ok(body) if safe => {
                let ct = match file.extension().and_then(|e| e.to_str()) {
                    Some("html") => "text/html; charset=utf-8",
                    Some("mjs") | Some("js") => "text/javascript; charset=utf-8",
                    Some("wasm") => "application/wasm",
                    Some("css") => "text/css; charset=utf-8",
                    Some("json") => "application/json",
                    Some("svg") => "image/svg+xml",
                    Some("png") => "image/png",
                    _ => "application/octet-stream",
                };
                let mut r = format!("HTTP/1.1 200 OK\r\nContent-Type: {ct}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n", body.len()).into_bytes();
                r.extend(body);
                r
            }
            _ => b"HTTP/1.1 404 Not Found\r\nContent-Length: 9\r\nConnection: close\r\n\r\nnot found".to_vec(),
        };
        let _ = stream.write_all(&resp);
    }
    ExitCode::SUCCESS
}
