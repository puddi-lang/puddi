# Changelog

All notable changes to Puddi are recorded here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow [Semantic Versioning](https://semver.org/) as described in [docs/releasing.md](docs/releasing.md).

## [Unreleased]

### Added

- Nine portable standard library modules for browser, WASI and plugins. They provide deques and priority queues, lazy iterator sources, Unicode text helpers, radix formatting, binary readers, hex and Base64 codecs, percent encoding, lexical paths, CSV and descriptive statistics.

## [0.1.1] - 2026-11-21

This release improves the Puddi toolchain for the draft 0.1 language specification.

### Fixed

- `pud` rejects unknown and empty targets in the `--target=<value>` form, matching `--target <value>` and `-t <value>` ([#6](https://github.com/puddi-lang/puddi/pull/6)).

### Performance

Measured with the programs in `bench/` against Rust and MoonBit; see `bench/README.md`.

- `pud run` uses Wasmtime's copying garbage collector instead of deferred reference counting and starts with a 16 MiB GC heap: up to 20x faster on allocation-heavy code
- Compiled machine code is cached per component in the user cache directory, so running an unchanged program again skips Cranelift (`PUD_NO_CACHE=1` turns this off)
- Payload-less enum variants (`None`, `Ordering.Less`, ...) are shared instead of allocated on every use
- Integer overflow checks for `Int` addition and subtraction are emitted inline, and left out where the operands' ranges show they cannot overflow (for example `i += 1` inside `while i < n`)
- `list[i]` compiles to a single unsigned bounds check and an array access instead of calls through `Index`; `for x in list` walks the list by index without allocating an `Option` per element
- Iterator adapters implement `fold` by internal iteration, so chains ending in `fold`, `count`, `collect` or `for_each` allocate nothing per element
- `List.sort` compares with `<` directly instead of through a closure and merges without branches; lists of integers of 256 or more elements are sorted by radix; `List.filled` and `StrBuilder.push` copy in bulk
- A new IR optimizer inlines closures passed to higher-order functions, tiny functions, matches on constructors returned by small functions and one level of small recursive functions: iterator chains run 45x faster on Wasmtime, and `Option` results of `Map.get` or `to_int` are no longer allocated when unwrapped at once (`PUD_NO_OPT=1` turns it off)
- `Map.insert` finds the key or a free slot in one probe
- `PUD_HOST=node pud run` starts Node.js with `--no-liftoff`: V8 cannot move a running wasm loop to optimized code, so loops in `main` stayed in the baseline tier
- `pud run` compiles faster (parallel parsing, shared declarations, only the platform operations a program uses) and starts Wasmtime on another thread while compiling; `PUD_TIME=1` prints the time of each phase
- `pud build` and `pud run` reuse the previous build when the sources, WIT files, target and compiler are unchanged: running an unchanged `hello` takes 25 ms instead of 160 ms
- Wasmtime keeps compiled machine code per function, so after an edit only the changed functions are compiled again; Cranelift's own inliner is off, which makes compiling 1.7x faster at the same speed
- Large source files are lexed and parsed in pieces on several threads
- The generated WebAssembly text is assembled by `src/asm.rs` on several threads instead of the `wat` crate, 10x faster with byte-identical code (`PUD_WAT=1` uses `wat`, `PUD_ASM_CHECK=1` compares both); functions are also turned into WebAssembly text on several threads, with the same result as on one; a 2,000-function program builds in 250 ms instead of 570 ms
- `bench/compile.mjs` compares the edit-compile-run loop with `cargo` and `moon`

### Documentation

- Documentation site at https://puddi-lang.github.io/puddi-docs/ with a language guide, toolchain and standard library pages, built from [puddi-lang/puddi-docs](https://github.com/puddi-lang/puddi-docs)
- Complete [Simplified Chinese documentation](https://puddi-lang.github.io/puddi-docs/zh-CN/)
- Contributing guide, code of conduct, security policy, compiler architecture and release process documents
- Draft governance model in GOVERNANCE.md, not yet in effect

### Known gaps

The [known conformance gaps in 0.1.0](https://github.com/puddi-lang/puddi/blob/v0.1.0/CHANGELOG.md#known-gaps) still apply to this release.

## [0.1.0] - 2026-11-18

First release of Puddi and its `pud` toolchain, implementing the draft 0.1 language specification.

### Language

- Structs, enums, tuples, generics with bounds, traits with default methods, associated types and supertraits, `dyn Trait`, operator traits and closures
- Pattern matching with exhaustiveness checking, `if let`, `while let` and `let ... else`
- `?` with `From` conversion, the `Error` trait and `AnyErr`
- `@derive(Eq, Ord, Hash, Show, Transfer)`, constants, type aliases, modules and imports
- `async fn` and `.await`, `task.scope` with structured cancellation, and workers
- WIT imports, `export fn`, `@extern` and `@export`, `@target`, `@deprecated` and `test` blocks

### Toolchain

- `pud new`, `build`, `run`, `test`, `check`, `fmt`, `doc` and `add`
- `browser`, `wasi` (WASI 0.3) and `plugin` targets, all emitted as WebAssembly components on WasmGC
- An embedded Wasmtime runtime for `pud run`
- Git dependencies with minimal version selection and `pud.lock`, plus local path dependencies

### Testing and distribution

- A conformance suite in `conformance/` with cases for every normative section of SPEC.md
- CI on Linux, macOS and Windows
- Prebuilt binaries for Linux (x86_64, arm64), macOS (x86_64, arm64) and Windows (x86_64), with install scripts for each

### Known gaps

The conformance suite marks these differences from the spec as expected failures:

- no warnings for naming-convention violations, and struct literals need an uppercase type name (2.4)
- a float literal next to an unsigned integer does not default to `Float` (3.7)
- `Self.Item` does not resolve inside an impl block, and a duplicate impl is accepted (3.12)
- unannotated closure parameters are not inferred from the body or later calls (4.6)
- plugin exports that use WIT records, variants, enums or flags fail to compile (8.3)

[0.1.1]: https://github.com/puddi-lang/puddi/releases/tag/v0.1.1
[0.1.0]: https://github.com/puddi-lang/puddi/releases/tag/v0.1.0
