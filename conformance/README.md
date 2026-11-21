# Puddi conformance suite

Executable checks of [SPEC.md](../SPEC.md). Every case names the spec sections it verifies, and the runner reports which normative sections (chapters 2 to 10) have passing cases. The suite tests a `pud` binary from the outside, so it can check any build of the toolchain, including release downloads.

```sh
node conformance/run.mjs                        # uses target/release/pud, then target/debug/pud, then pud on PATH
node conformance/run.mjs --pud ~/.pud/bin/pud   # check another binary (or set PUD)
node conformance/run.mjs --filter 3.7           # cases for one section, or whose path contains the text
node conformance/run.mjs --strict-coverage      # also fail when a normative section has no passing case
node conformance/run.mjs --list                 # list cases without running them
```

Other options: `--jobs <n>` (default: CPU count, at most 8), `--timeout <seconds>` per case (default 120) and `--json <file>` for a machine-readable report. `cargo test` runs the suite with `--strict-coverage` against the binary it just built. Node.js 22 or newer is required, as for `pud test`.

## Writing a case

A case is a `.pud` file under `cases/<chapter>/`, or a package directory (with `pud.toml`) whose header is in `src/main.pud` or `src/lib.pud`. Directories whose name starts with `_` are fixtures used by other cases and are not run.

The header is the leading block of `//` comments:

| Header | Meaning |
|---|---|
| `// spec: 3.7 6.2` | sections of SPEC.md the case verifies (required) |
| `// mode: run` | `run` (default) runs the program; `test` runs `pud test`; `reject` expects `pud check` to fail; `check` expects it to pass; `build`, `fmt` and `doc` run those commands |
| `// exit: 101` | expected exit code (default 0) |
| `// args: --target browser` | extra arguments after the path |
| `// prog-args: greet puddi` | arguments passed to the program after `--` |
| `// host: node` | sets `PUD_HOST`; `// env: KEY=value` sets any variable |
| `// match: contains` | how `//>` lines are compared: `exact` (default for `run`) or `contains` |
| `// xfail: reason` | known non-conformance: reported but not counted as a failure |

Anywhere in the file:

- `//> text` is a line of expected output (stdout followed by stderr). With `exact` matching, the whole output must equal these lines.
- `//~ text` must appear in stderr. A `reject` case needs at least one; pick a fragment that shows the program was rejected for the right reason.
- `//!~ text` must not appear in the output.

An `xfail` case that starts passing makes the run fail, so the marker is removed when the compiler catches up. Uncovered sections and `xfail` cases are listed in the coverage report (`--coverage`).

## Known non-conformance

The `xfail` cases document where the current compiler differs from the draft 0.1 spec:

| Case | Section | Gap |
|---|---|---|
| `02-lexical/naming_warnings.pud` | 2.4 | no warnings for naming-convention violations |
| `02-lexical/naming_lowercase_type.pud` | 2.4 | struct literals need an uppercase type name |
| `03-types/trait_duplicate_impl.pud` | 3.12 | a duplicate impl is accepted |
| `04-expressions/closure_param_inference.pud` | 4.6 | `let inc = \|x\| x + 1` needs an annotation |
| `08-interop/wit_record_exports` | 8.3 | exports that use WIT records, variants, enums or flags fail to compile |
