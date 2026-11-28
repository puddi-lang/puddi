# Tape-based liveness in Puddi IR

Joshua Tenner's Tape design stores computations in an indexed arena of 16-byte records with side storage for larger payloads. The scheduler carries IDs. A computation can lose its place in the schedule while its ID stays valid. Separate nodes for values, effects and guards let a pass keep an observable trap even if the value that originally produced it is dead. His design also gives facts a validity region in the control-flow graph and uses a sparse B-tree for facts that need ordered lookup. [The Tape](https://jtenner.github.io/posts/2026-11-21-thetape/) · [Puddi discussion](https://github.com/puddi-lang/puddi/discussions/5#discussioncomment-19814867)

## How Puddi applies the design

Puddi's elaborated IR is a typed, structured tree with explicit local IDs, assignments, captures, branches and loops. Inlining and code generation use this structure directly. The optimizer builds a per-function liveness tape over that tree. During each cleanup, removable bindings have stable indices, a flat table stores their local dependencies, and a separate schedule records statement positions. The tree supplies the executable payloads and their order within each region. [Implementation](../src/opt/tape.rs)

Demands start at retained expressions and include local reads, assignment targets and closure captures. An assignment can require the binding to initialize the captured local's box. The worklist follows each demanded local to its candidate definitions, including multiple bindings of a shared local ID, and visits each definition's operands once. Pattern destructuring and computations with unknown effects stay scheduled. The final walk removes dead statements and keeps the original order within each region. This is a mark-and-sweep formulation of the value liveness described in the proposal. LLVM's ADCE also propagates liveness from roots and additionally analyzes control dependence through its CFG. [LLVM ADCE](https://llvm.org/doxygen/ADCE_8cpp_source.html)

A chain such as `let a = 42; let b = a; let c = b` used to require a full use-count and removal pass for each dead link. A chain of length `n` could therefore take quadratic work in that phase. The tape costs linear work per cleanup in IR nodes, local slots and recorded uses. The arena, operand table and schedule use temporary linear space. The cleanup runs after inlining rewrites and also runs when the first rewrite round leaves a function unchanged. These are algorithmic bounds. Actual compiler cost includes building the tape, walking the tree to apply it and running later optimization rounds.

## Separating a read from its guard

For an unused `let item = xs[i]` on a scalar list, Puddi keeps evaluation of the list and index, the source-level list check, and the backing array's Wasm check. The element fetch disappears from the successful path. The tape treats the operands as required by the guard and tracks demand for `item` independently. A live `item` still lowers to the regular `array.get`. An unused one lowers to the new `ArrayGuard` IR node.

```text
Original                            After liveness
evaluate xs and i                   evaluate xs and i
check the list's logical length    check the list's logical length
item = array_get(xs.data, i)        ArrayGuard(xs.data, i)
```

The lowering evaluates the array and index once, in left-to-right order. It compares the index as unsigned against `array.len`, which also traps for a null array reference. This catches negative indices. The out-of-bounds branch executes the original typed Wasm get, so the engine reports the same bounds trap. Wasm traps before fetching an element on that branch. Reference-valued reads retain the ordinary get because Puddi also checks the loaded reference for null. [WebAssembly array instructions](https://webassembly.github.io/gc/core/exec/instructions.html) · [Lowering](../src/codegen.rs)

In-bounds reads now access the length without loading the element. The guard introduces a branch and may use two scratch locals. A Wasm engine can already optimize some `array.get; drop` sequences, so the runtime and code-size tradeoffs depend on the engine and workload. The regression checks the emitted guard and execution behavior. It supplies no performance measurements.

## Requirements for further Tape passes

**Guard elimination.** Puddi's existing range analysis follows integer locals through structured branches to prove arithmetic checks safe. Removing a bounds guard requires a proof about the same index and the same backing array on every path reaching it. A comparison with a list's mutable logical length and a comparison with the backing array's length establish different facts. Assignments, aliasing and loop backedges determine where those facts remain valid. WebAssembly GC array length is fixed for an array instance, and a live `array.get` retains its engine-level check. A fact store becomes useful when several independent passes need to share proofs. [Integer range analysis](../src/ranges.rs)

**Dead arguments.** Tenner's private parameter mask relies on demand propagation through direct calls and forwarding cycles. For Puddi, entry points, WIT exports, imports, function references, closure calls and trait shims constrain call signatures. A private direct-call implementation needs to prove eligibility for both caller and callee and keep the effects of argument evaluation in order. The current tape marks intraprocedural local demand and preserves the existing call ABI.
