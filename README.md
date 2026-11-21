# Puddi

[![CI](https://github.com/puddi-lang/puddi/actions/workflows/ci.yml/badge.svg)](https://github.com/puddi-lang/puddi/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/puddi-lang/puddi)](https://github.com/puddi-lang/puddi/releases/latest)
[![Docs](https://img.shields.io/badge/docs-puddi--docs-blue)](https://puddi-lang.github.io/puddi-docs/)

A statically typed, expression-oriented language that compiles to WebAssembly. One source language targets the browser, WASI runtimes and plugin hosts, using the engine's garbage collector (WasmGC) and the Component Model.

```puddi
@derive(Eq, Show)
struct Todo {
    title: Str
    var done: Bool
}

fn main() {
    let todos = [Todo { title: "spec", done: true }, Todo { title: "compiler", done: false }]
    let pending = todos.filter(|t| !t.done)
    print("{pending.len()} of {todos.len()} left")
}
```

**[Documentation](https://puddi-lang.github.io/puddi-docs/)** · **[简体中文文档](https://puddi-lang.github.io/puddi-docs/zh-CN/)** · [Language specification](SPEC.md) · [Changelog](CHANGELOG.md) · [Contributing](CONTRIBUTING.md)

## Install

macOS and Linux (x86_64 and arm64):

```sh
curl -fsSL https://raw.githubusercontent.com/puddi-lang/puddi/main/install.sh | sh
```

Windows (PowerShell):

```powershell
irm https://raw.githubusercontent.com/puddi-lang/puddi/main/install.ps1 | iex
```

The scripts download the latest [release](https://github.com/puddi-lang/puddi/releases), verify its SHA-256 checksum, put `pud` in `~/.pud/bin` and add that directory to `PATH`. Set `PUD_VERSION=v0.1.1` to pin a release, `PUD_INSTALL` to change the directory, or `PUD_NO_MODIFY_PATH=1` to leave `PATH` alone. Run the script again to upgrade.

From source (current stable Rust):

```sh
cargo install --locked --git https://github.com/puddi-lang/puddi --tag v0.1.1
```

`pud test` and the browser target also need Node.js 22 or newer.

## Quick start

```sh
pud new hello && cd hello
pud run                        # build src/main.pud as a WASI 0.3 component and run it
pud test                       # run test blocks, each in a fresh instance
pud run --target browser       # build for the browser and serve it on http://127.0.0.1:8000
pud build --target plugin      # build a component for the world in [target.plugin]
pud add github.com/someone/lib@1.2   # add a dependency
pud run some_file.pud          # single-file mode, no package needed
```

| Command | Purpose |
|---|---|
| `pud new <name>` | create a package |
| `pud build [--target browser\|wasi\|plugin] [--emit-wat] [-o dir]` | compile to `target/<target>/<name>.wasm` |
| `pud run [path] [-- args]` | build and run (`wasi`: embedded Wasmtime; `browser`: dev server; `plugin`: `-- <export> [args]` calls an export) |
| `pud test [path] [filter]` | run `test` blocks with Node.js |
| `pud check [path]` | type-check only |
| `pud add <repo@version\|path> [--name n]` | add a dependency to `pud.toml` and update `pud.lock` |
| `pud fmt [files] [--check]` | format in the official style |
| `pud doc [path]` | write Markdown docs for public items to `target/doc` |

The [documentation](https://puddi-lang.github.io/puddi-docs/) has a language guide and covers [targets](https://puddi-lang.github.io/puddi-docs/toolchain/targets.html), [WIT imports](https://puddi-lang.github.io/puddi-docs/interop/wit.html), [plugins](https://puddi-lang.github.io/puddi-docs/interop/plugins.html), [workers](https://puddi-lang.github.io/puddi-docs/guide/workers.html), [dependencies](https://puddi-lang.github.io/puddi-docs/toolchain/dependencies.html) and the [standard library](https://puddi-lang.github.io/puddi-docs/stdlib/prelude.html). Runnable examples are in [examples/](examples).

## Status

Puddi 0.1 is the first release series. The compiler implements the draft 0.1 [specification](SPEC.md), including structs, enums, generics, traits and `dyn Trait`, pattern matching with exhaustiveness checking, `?` and `AnyErr`, `async fn` with structured concurrency, workers, WIT imports and exports, and `test` blocks. The [standard library](SPEC.md#10-standard-library) includes JSON, CSV, binary encodings, collections, text processing, HTTP, files, time, randomness and the DOM.

The [conformance suite](conformance/README.md) checks the toolchain against the specification: every normative section has passing cases, and cases marked `xfail` record the [known gaps](conformance/README.md#known-non-conformance). Other limitations are listed on the [implementation status](https://puddi-lang.github.io/puddi-docs/reference/status.html) page. The language may still change in 0.x releases.

## Development

```sh
cargo build --release          # target/release/pud, with the embedded Wasmtime runtime
cargo build --no-default-features   # much faster, without the embedded runtime
cargo test --release           # regression tests and the conformance suite
node conformance/run.mjs --coverage   # the conformance suite alone, with a per-section report
```

See [CONTRIBUTING.md](CONTRIBUTING.md) for the test suites and how to change the specification, [docs/architecture.md](docs/architecture.md) for a tour of the compiler, and [docs/releasing.md](docs/releasing.md) for the release process.

## Community

- Questions, bugs and proposals: [issues](https://github.com/puddi-lang/puddi/issues)
- Security issues: see [SECURITY.md](SECURITY.md)
- Everyone taking part follows the [code of conduct](CODE_OF_CONDUCT.md)
- The project is run informally by its maintainers for now; [GOVERNANCE.md](GOVERNANCE.md) is a draft of the model it will adopt as the community grows

## License

Copyright (c) 2026 Puddi community

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this project, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
