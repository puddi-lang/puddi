# Runnable examples

Run these commands from the repository root with `pud` on your path.

| Example | Command | Result |
|---|---|---|
| [todo](todo) reads the bundled JSON file and counts incomplete tasks | `cd examples/todo && pud run` | Prints `2 of 4 left` |
| [wordfreq](wordfreq) counts words from standard input | `cd examples/wordfreq && printf 'a b a\n' \| pud run` | Prints the counts in descending order, with `2` next to `a` and `1` next to `b` |
| [plugin](plugin) uses a custom WIT logging interface | `cd examples/plugin && pud build --target plugin` | Writes `target/plugin/plug.wasm`. To invoke its `greet` export, the host supplies the logging interface declared in [host.wit](plugin/wit/host.wit) |
| [plugin-host](plugin-host) uses the bundled host capabilities and workers | `cd examples/plugin-host && pud run --target plugin -- run-jobs 3` | Prints the three completed jobs, `concurrent true`, and `worker Some(49)` |
