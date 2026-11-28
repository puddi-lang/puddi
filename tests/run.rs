//! Conformance tests: compile and run every program in tests/run (as a WASI
//! component with the embedded Wasmtime, or with Node.js for programs marked
//! `// host: node`) and compare its output; check that programs in tests/fail are rejected
//! with the expected diagnostics.

use std::path::Path;
use std::process::Command;

fn pud() -> Command {
    Command::new(env!("CARGO_BIN_EXE_pud"))
}

fn sorted(dir: &str, ext: &str) -> Vec<std::path::PathBuf> {
    let mut v: Vec<_> = std::fs::read_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join(dir))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == ext).unwrap_or(false))
        .collect();
    v.sort();
    v
}

#[test]
fn run_programs() {
    let mut failures = Vec::new();
    for src in sorted("tests/run", "pud") {
        let expected_out = src.with_extension("out");
        let is_test = std::fs::read_to_string(&src).unwrap().contains("\ntest \"") && !expected_out.exists();
        let text_src = std::fs::read_to_string(&src).unwrap();
        let mut cmd = pud();
        if text_src.starts_with("// host: node") {
            // needs the concurrent scheduler of the JavaScript host
            cmd.env("PUD_HOST", "node");
        }
        let out = if is_test { cmd.arg("test").arg(&src).output().unwrap() } else { cmd.arg("run").arg(&src).output().unwrap() };
        let code = out.status.code().unwrap_or(-1);
        let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        let want_code: i32 = std::fs::read_to_string(src.with_extension("code")).map(|s| s.trim().parse().unwrap()).unwrap_or(if is_test { 1 } else { 0 });
        if code != want_code {
            failures.push(format!("{}: exit code {code}, expected {want_code}\n{text}", src.display()));
            continue;
        }
        if let Ok(want) = std::fs::read_to_string(&expected_out) {
            if text != want {
                failures.push(format!("{}: output differs\n--- got\n{text}\n--- expected\n{want}", src.display()));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn tape_preserves_array_read_effects() {
    let dir = std::env::temp_dir().join(format!("puddi-tape-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("tape.pud");
    std::fs::write(&src, r#"
fn observe_list(xs: List<U8>) -> List<U8> {
    print("list")
    xs
}

fn observe_index(i: Int) -> Int {
    print("index {i}")
    i
}

fn main() {
    let seed = 123456789
    let relay = seed
    let _dead = relay
    let index = 1
    let forwarded = index
    let values: List<U8> = [3, 4]
    let kept = values[forwarded]
    print("value {kept}")
    let _unused_list = observe_list(values)[observe_index(forwarded)]
    let empty = __array_new<U8>(0)
    let _unused_raw = __array_get(empty, observe_index(-1))
    print("after trap")
}
"#).unwrap();
    let build = pud().env("PUD_HOST", "node").env_remove("PUD_NO_OPT")
        .args(["build", "--emit-wat", "-o"]).arg(&dir).arg(&src).output().unwrap();
    assert!(build.status.success(), "{}", String::from_utf8_lossy(&build.stderr));
    let wat = std::fs::read_to_string(dir.join("tape.wat")).unwrap();
    let result = Command::new("node").arg(dir.join("puddi.mjs")).arg("run").arg(dir.join("tape.wasm")).output().unwrap();
    std::fs::remove_dir_all(&dir).unwrap();

    assert!(!wat.contains("i32.const 123456789"), "the dead binding chain survived");
    let guards: Vec<_> = wat.match_indices("array.len i32.ge_u if\n").collect();
    assert_eq!(guards.len(), 2, "the list and raw read should both have an explicit guard");
    for (offset, guard) in guards {
        let mut failure_path = wat[offset + guard.len()..].lines();
        assert!(failure_path.next().unwrap().contains("array.get_u"));
        assert_eq!(failure_path.next().unwrap().trim(), "end i32.const 0");
    }
    assert_eq!(String::from_utf8_lossy(&result.stdout).lines().collect::<Vec<_>>(), ["value 4", "list", "index 1", "index -1"]);
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert_eq!(result.status.code(), Some(101), "{stderr}");
    assert_eq!(stderr.trim(), "panic: index out of bounds");
}

#[test]
fn reject_programs() {
    let mut failures = Vec::new();
    for src in sorted("tests/fail", "pud") {
        let out = pud().arg("check").arg(&src).output().unwrap();
        let text = String::from_utf8_lossy(&out.stderr).to_string();
        if out.status.success() {
            failures.push(format!("{}: compiled but should have failed", src.display()));
            continue;
        }
        let want = std::fs::read_to_string(src.with_extension("err")).unwrap();
        for line in want.lines().filter(|l| !l.trim().is_empty()) {
            if !text.contains(line) {
                failures.push(format!("{}: missing diagnostic `{line}`\n{text}", src.display()));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn plugin_host_capabilities() {
    // a plugin whose world imports clocks, random, logging, HTTP and the
    // worker interfaces gets std.time, std.random, std.log, std.http and std.worker
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/plugin-host");
    let out = pud().args(["run", "--target", "plugin"]).arg(&dir).args(["--", "run-jobs", "3"]).output().unwrap();
    let text = String::from_utf8_lossy(&out.stdout).to_string();
    assert!(out.status.success(), "{text}{}", String::from_utf8_lossy(&out.stderr));
    // the jobs are timed on their own, then the worker answers
    assert!(text.contains(r#"["job2", "job1", "job0", "concurrent true", "worker Some(49)"]"#), "{text}");
}
