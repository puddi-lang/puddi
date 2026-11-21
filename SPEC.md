# Puddi Language Specification

Version: draft 0.1
Status: complete draft. Section 14 lists what is deferred past v1.

## 1. Overview

Puddi is a statically typed, expression-oriented language that compiles to WebAssembly. It targets the browser, WASI runtimes (server, edge, CLI) and plugin hosts from a single source language, uses the WASM engine's garbage collector (WasmGC), and talks to hosts through the Component Model.

| Topic | Decision |
|---|---|
| Compile target | WASM only; any JS is loader glue only |
| Host environments | `browser`, `wasi` (server / edge / CLI, WASI 0.3), `plugin` |
| Memory management | WasmGC |
| Type system | Static, local type inference |
| Polymorphism | Generics + nominal traits, `dyn Trait` for dynamic dispatch |
| Null / errors | No null; `Option<T>`, `Result<T, E>`, `?` with `From` conversion; std `Error` trait and `AnyErr`; `panic` traps |
| Mutability | `let` / `var` bindings; field mutability declared per field; values are shared references |
| Numbers | `Int` = 32-bit signed, overflow traps; lossless widening is implicit |
| Strings | Opaque `Str`, no integer indexing |
| Async | `async fn` + postfix `.await`, structured concurrency |
| Parallelism | No shared-memory threads; isolated workers with message passing |
| Host interop | Component Model (WIT) as the main path, raw `@extern` / `@export` as the escape hatch |
| Metaprogramming | None in v1, except the compiler's built-in `@derive` |
| Syntax | Braces, optional semicolons, expression-oriented semantics |
| Toolchain | `pud` command, `pud.toml` manifest, git-based packages |
| Source files | UTF-8, extension `.pud` |

## 2. Lexical Structure

### 2.1 Source text

Source files are UTF-8 with the extension `.pud`. Identifiers follow Unicode UAX #31 (XID_Start followed by XID_Continue); `_` alone is the wildcard and is not an identifier.

### 2.2 Comments

```puddi
// line comment
/* block comment, may nest */
/// doc comment, attached to the next declaration
```

### 2.3 Keywords

```
as      async   await   break   const   continue  dyn     else
enum    export  false   fn      for     if        impl    import
in      let     loop    match   pub     return    self    Self
struct  test    trait   true    type    var       while
```

### 2.4 Naming conventions

Types, traits and enum variants use `UpperCamelCase`. Functions, variables, fields and modules use `snake_case`. Constants use `SCREAMING_SNAKE_CASE`. `pud fmt` does not rename, but the compiler warns on violations.

### 2.5 Statement termination

A newline ends a statement. A semicolon is optional and can separate several statements on one line. A semicolon is only a separator: it never changes the meaning of an expression.

A newline does not end a statement when:

1. it is inside an unclosed `(` or `[`;
2. the line ends with a binary operator or a comma;
3. the next line starts with `.`.

```puddi
let total = price * count +
    shipping                    // continues: line ends with +

let names = users
    .filter(|u| u.active)       // continues: next line starts with .
    .map(|u| u.name)
```

Inside struct, enum, trait and `match` bodies, members are separated by newlines or commas.

### 2.6 Numeric literals

```puddi
42    1_000    0xFF    0b1010    0o17
3.14  1e9      2.5e-3
```

An integer literal takes its type from context and defaults to `Int`. A float literal takes its type from context and defaults to `Float`. A literal that does not fit its type is a compile error.

### 2.7 Character literals

`Char` is a Unicode scalar value, written with single quotes: `'a'`, `'\n'`, `'\u{1F600}'`.

### 2.8 String literals

String literals use double quotes and support interpolation with `{expr}`. The interpolated expression must implement `Show`. A literal brace is written `\{` or `\}`.

```puddi
let s = "hi {name}, you have {count + 1} messages"
let t = "a literal \{brace\}"
```

Escapes: `\n` `\r` `\t` `\0` `\\` `\"` `\'` `\{` `\}` `\u{...}`.

## 3. Types

### 3.1 Type inference

Inference is local. Top-level function signatures (parameter types and return type) must be written out; a missing return type means `()`. Types of local bindings, closures and expressions inside function bodies are inferred.

```puddi
fn area(w: Int, h: Int) -> Int {
    let s = w * h      // inferred Int
    s
}
```

### 3.2 Built-in types

| Category | Types |
|---|---|
| Boolean | `Bool` |
| Integers | `Int` (= `I32`), `I8` `I16` `I32` `I64` `U8` `U16` `U32` `U64` |
| Floats | `Float` (= `F64`), `F32` `F64` |
| Text | `Char`, `Str` |
| Unit | `()` |
| Tuples | `(A, B, ...)` |
| Functions | `fn(A, B) -> R` |
| Collections | `List<T>`, `Map<K, V>`, `Set<T>` |
| Core enums | `Option<T>`, `Result<T, E>` |

### 3.3 Structs

```puddi
struct Point {
    x: Int
    var y: Int
}

struct Pair<A, B> { a: A, b: B }
```

Fields are private to the module unless marked `pub`. A field marked `var` can be assigned after construction; other fields cannot (see 4.1).

Construction uses field names, with shorthand and update syntax:

```puddi
let p = Point { x: 1, y: 2 }
let q = Point { x, y }          // shorthand for x: x, y: y
let r = Point { x: 5, ..p }     // copy remaining fields from p
```

### 3.4 Enums

Enums are algebraic data types. Variants can be bare, tuple-like or record-like.

```puddi
enum Shape {
    Circle(Float)
    Rect { w: Float, h: Float }
    Empty
}

let s = Shape.Circle(2.0)
```

`match` on an enum must be exhaustive.

### 3.5 Tuples and unit

Tuples are written `(Int, Str)` and constructed with `(1, "a")`. Fields are accessed as `t.0`, `t.1`. The unit type and its only value are both written `()`.

### 3.6 Function types and closures

Function values have types written `fn(Int, Int) -> Int`. Named functions and closures both convert to function types. Async functions have types written `async fn(Int) -> Str`.

### 3.7 Numeric types

`Int` maps to WASM `i32`, `I64` / `U64` to `i64`, `Float` to `f64`, `F32` to `f32`. `I8` `I16` `U8` `U16` `U32` are stored as `i32` and kept in range by the compiler.

Integer overflow traps. Integer division or remainder by zero traps. `/` on integers truncates toward zero, and `%` takes the sign of the dividend. Wrapping, saturating and checked arithmetic are available as explicit methods (`wrapping_add`, `saturating_add`, `checked_add`, and so on).

**Widening.** A conversion that can never lose information happens implicitly:

| From | Implicitly widens to |
|---|---|
| `I8` | `I16` `I32` `I64` `F32` `F64` |
| `I16` | `I32` `I64` `F32` `F64` |
| `I32` | `I64` `F64` |
| `U8` | `U16` `U32` `U64` `I16` `I32` `I64` `F32` `F64` |
| `U16` | `U32` `U64` `I32` `I64` `F32` `F64` |
| `U32` | `U64` `I64` `F64` |
| `F32` | `F64` |

`I64` and `U64` never widen to a float type, since `F64` cannot represent every 64-bit integer.

Widening applies wherever an expected type is known (annotated bindings, function arguments, return values, field initializers, collection elements). For a binary operator with operands of two different numeric types, both operands widen to the narrowest type that can hold both losslessly; if none exists (for example `I64` and `U64`, or `I64` and `Float`) it is a compile error.

**Narrowing.** Lossy conversions are always explicit. `to_<type>()` returns `Option` and yields `None` when the value does not fit. Explicit lossy methods such as `truncate_to_int()`, `round_to_int()` and `wrap_to_u8()` are also available.

```puddi
let a: Int = 5
let b: I64 = a              // ok, widening
let c: Int = b.to_int()?    // narrowing, returns Option<Int>
```

### 3.8 Strings and characters

`Str` is an immutable, opaque Unicode string. It has no integer indexing. Text is accessed by:

- iterating code points: `s.chars()` yields `Char`;
- iterating grapheme clusters: `s.graphemes()` yields `Str`;
- search and slicing: `s.find("x")` returns `Option<StrIndex>`, and `s.slice(start, end)` takes `StrIndex` values. `StrIndex` is opaque and only valid for the string that produced it.

`s.len()` is not provided, since its meaning would depend on the representation. Use `s.chars().count()`, `s.graphemes().count()` or `s.utf8_len()` explicitly.

The implementation may choose any internal representation, including the host's native strings.

### 3.9 Collections

| Type | Literal | Notes |
|---|---|---|
| `List<T>` | `[1, 2, 3]` | growable array |
| `Map<K, V>` | `["a": 1, "b": 2]`, empty `[:]` | `K: Eq + Hash`, insertion order preserved |
| `Set<T>` | `Set.from([1, 2, 3])` | `T: Eq + Hash`, insertion order preserved |

`xs[i]` on a `List` takes an `Int` and traps when out of bounds; `xs.get(i)` returns `Option<T>`. `m[k]` on a `Map` traps when the key is missing; `m.get(k)` returns `Option<V>`.

Collections are references like any other object. Whether a collection can be modified is decided by its type: `List`, `Map` and `Set` are mutable (`push`, `insert`, `remove`); their read-only views `ListView`, `MapView` and `SetView` expose only reading methods, and a mutable collection converts to its view implicitly.

### 3.10 Option and Result

Puddi has no null. A missing value is `Option<T>` (`Some(v)` / `None`) and a fallible result is `Result<T, E>` (`Ok(v)` / `Err(e)`). Both are ordinary enums. Their variants are in the prelude and can be written without a path. See 6 for `?`.

### 3.11 Generics

Type parameters use angle brackets. Bounds use `:` and are combined with `+`.

```puddi
fn largest<T: Ord>(xs: List<T>) -> Option<T> { ... }
fn dump<T: Show + Hash>(x: T) { ... }

struct Stack<T> { var items: List<T> }
```

Type arguments are inferred at call sites and can be written explicitly as `parse<Int>(s)`.

### 3.12 Traits

Traits are nominal. A type implements a trait only through an explicit `impl` block. Traits can have default methods, associated types and supertraits. `Self` refers to the implementing type.

```puddi
trait Show {
    fn show(self) -> Str
}

trait Iterator {
    type Item
    fn next(self) -> Option<Self.Item>
}

trait Shape: Show {
    fn area(self) -> Float
    fn describe(self) -> Str { "{self.show()} with area {self.area()}" }
}

impl Show for Point {
    fn show(self) -> Str { "({self.x}, {self.y})" }
}

impl<T: Show> Show for List<T> {
    fn show(self) -> Str { ... }
}
```

**Coherence.** An `impl Trait for Type` is allowed only in the package that defines `Trait` or the package that defines `Type`. At most one impl may apply to a given type.

**Async methods.** Trait methods can be `async fn`.

**Operator traits.** Operators are overloaded by implementing standard traits:

| Operator | Trait |
|---|---|
| `+` `-` `*` `/` `%` | `Add` `Sub` `Mul` `Div` `Rem` |
| unary `-` `!` | `Neg` `Not` |
| `==` `!=` | `Eq` |
| `<` `<=` `>` `>=` | `Ord` |
| `a[i]` | `Index` |
| `for x in a` | `Iterable` |
| `"{a}"` | `Show` |

### 3.13 Derive

`@derive` asks the compiler to generate standard trait impls. Only built-in traits can be derived; there are no user-defined derives in v1.

```puddi
@derive(Eq, Ord, Hash, Show)
struct Point { x: Int, y: Int }
```

Derivable traits: `Eq`, `Ord`, `Hash`, `Show`, `Transfer` (see 9.4).

### 3.14 Trait objects

`dyn Trait` is a type for any value whose type implements `Trait`. Calls on it are dispatched at runtime through a vtable. A value converts to `dyn Trait` implicitly wherever the expected type is `dyn Trait`.

```puddi
let items: List<dyn Show> = [Point.new(1, 2), "hi", 42]
for it in items { print(it.show()) }
```

A trait can be used as `dyn Trait` only if none of its methods has its own type parameters or mentions `Self` outside the receiver. Associated types must be fixed: `dyn Iterator<Item = Int>`.

Async methods are allowed on `dyn Trait`. Calling one through a trait object returns a heap-allocated future; since WasmGC objects already live on the heap, this adds little cost beyond the dynamic dispatch itself.

### 3.15 Type aliases

```puddi
type UserId = Int
type Callback<T> = fn(T) -> ()
```

An alias is the same type as its target, not a new type.

## 4. Expressions and Statements

Puddi is expression-oriented. Blocks, `if`, `match` and `loop` produce values. The last expression in a block is the block's value. When a block's expected type is `()`, the value of its last expression is discarded.

Assignment (`=`, `+=`, ...) is an expression of type `()`.

### 4.1 Bindings and mutability

`let` declares a binding that cannot be reassigned and `var` declares one that can. Both take a pattern. Binding mutability only controls reassignment.

Field mutability is declared on the type: only fields marked `var` can be assigned after construction. This maps directly onto WasmGC mutable and immutable struct fields.

Struct, enum and collection values are references: assignment and argument passing share the same object rather than copying it.

```puddi
struct Point {
    x: Int        // immutable
    var y: Int    // mutable
}

let p = Point { x: 1, y: 2 }
p.y = 5        // ok, y is var
p.x = 5        // error: x is immutable
p = Point { x: 0, y: 0 }   // error: p is let

let q = p      // q and p refer to the same object
```

`==` compares through `Eq`. Reference identity is checked with `same(a, b)` from the prelude.

### 4.2 Operators and precedence

From highest to lowest:

| Level | Operators | Associativity |
|---|---|---|
| 1 | `.field` `.method()` `f()` `a[i]` `?` `.await` | left |
| 2 | unary `-` `!` | prefix |
| 3 | `*` `/` `%` | left |
| 4 | `+` `-` | left |
| 5 | `<<` `>>` | left |
| 6 | `&` | left |
| 7 | `^` | left |
| 8 | `\|` | left |
| 9 | `==` `!=` `<` `<=` `>` `>=` | none |
| 10 | `&&` | left |
| 11 | `\|\|` | left |
| 12 | `..` `..=` | none |
| 13 | `=` `+=` `-=` `*=` `/=` `%=` `&=` `\|=` `^=` `<<=` `>>=` | right |

`&&` and `||` short-circuit. `a..b` is a half-open range and `a..=b` is inclusive.

### 4.3 Blocks and control flow

```puddi
let sign = if x > 0 { 1 } else if x < 0 { -1 } else { 0 }

let label = match code {
    200 -> "ok"
    404 -> "not found"
    500..=599 -> "server error"
    _ -> "other"
}
```

An `if` without `else` has type `()`. In the condition of `if`, `while` and `match`, a struct literal must be wrapped in parentheses.

### 4.4 Patterns

Patterns can destructure tuples, structs and enum variants, and can appear in `let`, `var`, `match`, `for`, `if let`, `while let` and `let ... else`.

| Pattern | Example |
|---|---|
| Wildcard | `_` |
| Binding | `x` |
| Literal | `42`, `"hi"`, `'a'`, `true` |
| Range | `1..=9`, `'a'..='z'` |
| Tuple | `(a, _, c)` |
| Struct | `Point { x, y: 0 }`, `Point { x, .. }` |
| Enum variant | `Some(v)`, `Shape.Rect { w, h }` |
| Or | `A \| B` |
| List | `[first, ..rest]`, `[]` |

`match` arms can have `if` guards.

```puddi
let (a, b) = pair

match shape {
    Shape.Circle(r) if r > 10.0 -> "big circle"
    Shape.Circle(_) -> "circle"
    Shape.Rect { w, h } -> "rect {w}x{h}"
    Shape.Empty -> "nothing"
}

if let Some(user) = find(id) { greet(user) }

let Some(cfg) = load() else { return }
```

The `else` block of `let ... else` must diverge (`return`, `break`, `continue` or `panic`).

### 4.5 Loops

```puddi
for x in xs { ... }
for (i, x) in xs.enumerate() { ... }
for i in 0..10 { ... }
while cond { ... }
while let Some(job) = queue.pop() { ... }

let found = loop {
    if done() { break value }
}
```

`break` can carry a value out of `loop`, which becomes the value of the `loop` expression. `for` and `while` have type `()`. `for x in e` works for any `e` whose type implements `Iterable`.

### 4.6 Closures

```puddi
let inc = |x| x + 1
let add = |a: Int, b: Int| -> Int { a + b }
let fetch = async |url| { http.get(url).await }
```

Closures capture variables by reference: a closure that captures a `var` binding sees and can make later assignments to it.

### 4.7 Paths

`.` is the only path separator, for module members, enum variants and associated functions alike: `io.read`, `Shape.Circle`, `Point.new(1, 2)`. There is no `::`.

## 5. Declarations

### 5.1 Functions

```puddi
fn add(a: Int, b: Int) -> Int { a + b }
async fn load(url: Str) -> Result<Str, HttpErr> { ... }
```

`return` exits early with a value. A function's body block provides its value otherwise.

### 5.2 Methods

Inherent methods are declared in an `impl` block. Methods take `self` as the first parameter; functions without `self` are associated functions. Since values are references and field mutability is declared per field, there is no separate mutable receiver.

```puddi
impl Point {
    fn new(x: Int, y: Int) -> Point { Point { x, y } }
    fn len(self) -> Float { ... }
    fn move_down(self, dy: Int) { self.y += dy }
}

let p = Point.new(1, 2)
p.len()
```

### 5.3 Constants

```puddi
const MAX_USERS: Int = 1_000
const GREETING: Str = "hi"
```

A constant's initializer must be a constant expression: literals, other constants, arithmetic and comparison on them, and struct, tuple and enum construction from constant expressions.

### 5.4 Visibility

Declarations and struct fields are private to their module by default. `pub` makes them visible to other modules and packages. `export` (see 8) is separate and marks component exports.

### 5.5 Attributes

Attributes start with `@` and apply to the next declaration.

| Attribute | Meaning |
|---|---|
| `@derive(...)` | generate standard trait impls (3.13) |
| `@target(t)` | include the declaration only when building for target `t`; `t` is `browser`, `wasi` or `plugin`, combinable as `@target(wasi, plugin)` |
| `@extern(module, name)` | raw core-wasm import (8.4) |
| `@export(name)` | raw core-wasm export (8.4) |
| `@deprecated(msg)` | warn on use |

### 5.6 Tests

`test` blocks can appear in any file. They are compiled only by `pud test`, which runs each test in a fresh instance. A test fails if it panics or a failed assertion traps. Test bodies may use `.await`.

```puddi
test "addition works" {
    assert_eq(add(2, 2), 4)
}
```

## 6. Error Handling

### 6.1 The `?` operator

Postfix `?` unwraps `Ok` / `Some`, or returns early from the enclosing function with the `Err` / `None`. On `Result`, when the error type differs from the function's error type, `?` converts it through `From`.

```puddi
enum AppErr {
    Io(IoErr)
    Bad
}

impl From<IoErr> for AppErr {
    fn from(e: IoErr) -> AppErr { AppErr.Io(e) }
}

fn load(path: Str) -> Result<Config, AppErr> {
    let text = fs.read(path)?         // IoErr converted to AppErr
    parse(text).ok_or(AppErr.Bad)
}
```

`?` on `Option` is allowed only in functions returning `Option`.

### 6.2 Panics

`panic(msg)` signals an unrecoverable error. So do failed `assert`, integer overflow, division by zero, and out-of-bounds indexing. A panic traps the WASM instance and cannot be caught inside Puddi. In a plugin, the host sees the trap and the host process keeps running.

### 6.3 The `Error` trait and `AnyErr`

Error types should implement `Error`:

```puddi
trait Error: Show {
    fn source(self) -> Option<dyn Error> { None }
}
```

`source` returns the underlying error, if any, so error chains can be walked and printed.

`AnyErr` wraps any value that implements `Error`. Since std provides `impl<E: Error> From<E> for AnyErr`, `?` converts any error into `AnyErr` automatically. Libraries should return their own error types; applications can use `AnyErr` and skip writing `From` impls.

```puddi
fn main() -> Result<(), AnyErr> {
    let s = fs.read(path)?        // IoErr -> AnyErr
    let v = json.decode(s)?       // ParseErr -> AnyErr
    ...
}
```

`e.downcast<E>()` returns `Option<E>` to recover the original error type. `AnyErr` implements `Error` by delegating to the wrapped value.

### 6.4 Errors from `main`

`main` may return `Result<(), E>` where `E: Show`. If it returns `Err`, the error is printed; on `wasi` the program then exits with a failure status, and on `browser` it is reported to the console.

## 7. Modules and Packages

### 7.1 Modules

One file is one module. Module paths follow the file layout under `src/`: `src/net/http.pud` is the module `net.http`. `src/main.pud` (or `src/lib.pud` for libraries) is the root.

```puddi
import net.http                   // use as http.get(...)
import net.http.{get, Request}    // import specific names
import net.http as h              // alias
import json                       // dependency named in pud.toml
import std.fs                     // standard library
```

Imports between modules of one package may form cycles. Dependencies between packages must be acyclic.

### 7.2 Manifest

```toml
[package]
name = "hello"
version = "0.1.0"
puddi = "0.1"

[deps]
json = "github.com/someone/puddi-json@1.2"

[target.wasi]
world = "wasi:cli/command"

[target.plugin]
world = "wit/host.wit#plugin"
```

`pud.lock` records the exact commit of every dependency and is committed to version control.

### 7.3 Dependencies

A dependency is a git repository plus a semver tag (`v1.2.0`). The version in `pud.toml` is a minimum. Versions are resolved with minimal version selection: each dependency gets the lowest version that meets every requirement, so builds stay the same without a lock file. Different major versions of one package are distinct packages and can coexist.

### 7.4 Toolchain

All tooling goes through the `pud` command.

| Command | Purpose |
|---|---|
| `pud new <name>` | create a package |
| `pud build [--target t]` | build for `browser`, `wasi` or `plugin` |
| `pud run` | build and run (wasi: in a WASI runtime; browser: dev server) |
| `pud test` | run `test` blocks |
| `pud fmt` | format with the single official style, no configuration |
| `pud doc` | generate documentation from `///` comments |
| `pud add <dep>` | add a dependency |

## 8. Host Interop

### 8.1 Targets

| Target | Output | Entry |
|---|---|---|
| `browser` | component plus generated JS loader glue | `fn main()` / `async fn main()` and/or `export fn` |
| `wasi` | WASI 0.3 component for the world in `[target.wasi]`, default `wasi:cli/command` | `fn main()` / `async fn main()` for commands, `export fn` for other worlds |
| `plugin` | component for the host world in `[target.plugin]` | the exports that the host world requires |

The compiler checks that every export required by the target world is provided with a matching signature.

The `wasi` target requires WASI 0.3 and uses its native async. There is no WASI 0.2 output.

### 8.2 Component Model

The Component Model is the main interop path. Importing a WIT interface generates typed bindings, and `export fn` makes a component export.

```puddi
import wasi:cli/stdout
import wasi:http/outgoing-handler

export fn run() -> Result<(), AppErr> { ... }
```

### 8.3 WIT type mapping

| WIT | Puddi |
|---|---|
| `bool` | `Bool` |
| `s8` `s16` `s32` `s64` | `I8` `I16` `I32` `I64` |
| `u8` `u16` `u32` `u64` | `U8` `U16` `U32` `U64` |
| `f32` `f64` | `F32` `F64` |
| `char` | `Char` |
| `string` | `Str` |
| `list<T>` | `List<T>` |
| `option<T>` | `Option<T>` |
| `result<T, E>` | `Result<T, E>` |
| `tuple<...>` | tuple |
| `record` | `struct` |
| `variant` / `enum` | `enum` |
| `flags` | generated struct of `Bool` fields |
| `resource` | opaque handle type with methods |

### 8.4 Raw core-wasm interop

Raw imports and exports are the low-level escape hatch. Only numeric types and `Str` may cross; marshaling beyond that is manual.

```puddi
@extern("env", "log")
fn log(msg: Str)

@export("run")
fn run() { log("hi") }
```

## 9. Concurrency

### 9.1 Async functions

Async uses explicit `async fn` and postfix `.await`. Async functions are colored: only async functions, async closures and test bodies can await.

```puddi
async fn fetch_user(id: Int) -> Result<User, HttpErr> {
    let res = http.get("/u/{id}").await?
    res.json().await
}
```

### 9.2 Structured concurrency

Concurrent child tasks are started inside a scope and cannot outlive it. The scope completes only when all its children have completed. If a child fails or the scope exits early, the remaining children are cancelled.

```puddi
async fn load_all() -> Result<(A, B), AppErr> {
    task.scope(async |s| {
        let a = s.spawn(load_a())
        let b = s.spawn(load_b())
        (a.await?, b.await?)
    }).await
}
```

There is no free-standing `spawn`.

### 9.3 Cancellation

Cancellation is cooperative. A cancelled task stops at its next `.await`, which returns early without resuming the task's code after that point. `task.is_cancelled()` lets long synchronous loops check for cancellation themselves.

### 9.4 Workers

Puddi has no shared-memory threads, since WasmGC objects cannot yet be shared across threads. Parallelism uses workers: each worker runs in its own WASM instance with its own heap and communicates only by message passing.

A worker is started from a task scope and runs a top-level async function (not a closure, since closures cannot leave their instance). The worker is terminated when the scope ends. Inside the worker, a `worker.Port<In, Out>` receives `In` and sends `Out`; outside, the handle returned by `s.worker(f)` sends `In` and receives `Out`.

```puddi
import std.worker

@derive(Transfer)
struct Job { id: Int, data: List<Int> }

async fn summer(port: worker.Port<Job, Int>) {
    while let Some(job) = port.recv().await {
        port.send(job.data.sum())
    }
}

async fn main() {
    task.scope(async |s| {
        let w = s.worker(summer)
        w.send(Job { id: 1, data: [1, 2, 3] })
        let total = w.recv().await     // Option<Int>
        print("{total}")
    }).await
}
```

Messages are deep-copied between instances. A message type must implement `Transfer`. It is implemented for numbers, `Bool`, `Char`, `Str`, tuples, `Option`, `Result` and collections of `Transfer` types, and can be derived for structs and enums whose fields are all `Transfer`. Function values, closures and `dyn` values are never `Transfer`.

`std.worker` is available on `browser` (Web Workers), and on other targets only when the target world provides a worker interface.

## 10. Standard Library

### 10.1 Prelude

Available in every module without import:

- types: `Bool` `Int` `Float` sized numeric types, `Char` `Str` `List` `Map` `Set` `Option` `Result` `AnyErr`
- variants: `Some` `None` `Ok` `Err`
- traits: `Eq` `Ord` `Hash` `Show` `From` `Error` `Transfer` `Add` `Sub` `Mul` `Div` `Rem` `Neg` `Not` `Index` `Iterable` `Iterator`
- functions: `print` `panic` `assert` `assert_eq` `same`

`print` writes a line to stdout on `wasi`, to the console on `browser`, and to `std.log` on `plugin`.

### 10.2 Modules by target

A module that the build target does not provide is a compile error to import.

| Module | browser | wasi | plugin |
|---|---|---|---|
| core (prelude and built-in collections) | yes | yes | yes |
| `std.bytes`, `std.collections`, `std.csv`, `std.encoding`, `std.fmt`, `std.iter`, `std.math`, `std.path`, `std.stats`, `std.text` | yes | yes | yes |
| `std.json` | yes | yes | yes |
| `std.log` | yes | yes | yes |
| `std.time` | yes | yes | host |
| `std.random` | yes | yes | host |
| `std.http` | yes | yes | host |
| `std.worker` | yes | host | host |
| `std.io` | - | yes | - |
| `std.fs` | - | yes | - |
| `std.env` | - | yes | - |
| `std.dom` | yes | - | - |

"host" means available only if the target world includes the corresponding interface. On `plugin`, `std.log` uses the host's logging interface if the world has one and does nothing otherwise.

### 10.3 Portable modules

Import portable modules by name, for example `import std.csv` to use `csv.parse`.

| Module | API | Behavior |
|---|---|---|
| `std.bytes` | `Endian.Big`, `Endian.Little`, `pack_u16`, `pack_u32`, `pack_u64`, `Reader` | The reader snapshots the bytes at construction. It supports `read`, `read_u8`, typed reads with explicit byte order, `skip`, `position`, and `remaining`. Failed reads and skips preserve the position. |
| `std.collections` | `Deque<T>`, `PriorityQueue<T>`, `count_by`, `group_by` | The deque supports amortized constant-time insertion and removal at either end. The priority queue pops the smallest value in logarithmic time. Grouping preserves input order within each group. |
| `std.csv` | `parse`, `stringify` | Parses comma-separated rows with quoted fields, doubled quotes, and LF, CRLF, or CR endings. It accepts rows of varying lengths. Serialization uses CRLF and writes a zero-field row as one empty field. Parse errors carry a zero-based byte offset. |
| `std.encoding` | `hex_encode`, `hex_decode`, `base64_encode`, `base64_decode`, `base64url_encode`, `base64url_decode`, `percent_encode`, `percent_decode` | Hex accepts either case and writes lowercase. Base64 uses canonical padding, and Base64url uses the URL-safe alphabet without padding. Percent encoding preserves ASCII letters, digits, `-`, `.`, `_`, and `~`. Percent decoding preserves literal plus signs. Decoders return bytes or an error with a zero-based byte offset. |
| `std.fmt` | `join`, `int_radix`, `uint_radix` | Joins values using `Show`. Radix formatting supports bases 2 through 36, uses lowercase digits, and returns `None` for other bases. |
| `std.iter` | `once`, `repeat`, `from_fn`, `unfold` | Creates lazy iterators from values, callbacks, or state transitions. `repeat` is infinite. Callback-based sources end at their first `None`. |
| `std.path` | `is_absolute`, `normalize`, `join`, `parent`, `file_name`, `stem`, `extension` | Handles slash-separated paths lexically. A leading slash denotes the root, and an absolute right operand replaces the left operand in `join`. Normalizing an empty relative path gives `.`. |
| `std.stats` | `summarize`, `median` | Summaries include count, mean, extrema, and population and sample variance and standard deviation. Empty samples and non-finite values return `None`. Summary overflow and sample variance with fewer than two observations also return `None`. |
| `std.text` | `strip_prefix`, `strip_suffix`, `truncate`, `pad_start`, `pad_end` | Truncation lengths and padding widths count Unicode scalars. Prefix and suffix matching is exact. |

```puddi
import std.collections
import std.csv

fn main() {
    let rows = csv.parse("fruit,red\nfruit,green\nvegetable,green").unwrap()
    let colors = collections.count_by(rows, |row| row[1])
    print(colors["green"])
}
```

## 11. Grammar Summary

Informal EBNF. `sep` is a newline, `;` or `,` as allowed by 2.5.

```ebnf
file          = { import } { item } ;
import        = "import" mod_path [ "." "{" ident { "," ident } "}" ] [ "as" ident ]
              | "import" wit_name ;

item          = { attribute } [ "pub" | "export" ]
                ( fn_decl | struct_decl | enum_decl | trait_decl | impl_decl
                | type_alias | const_decl | test_decl ) ;
attribute     = "@" ident [ "(" [ attr_arg { "," attr_arg } ] ")" ] ;

fn_decl       = fn_sig [ block ] ;                       (* no block only with @extern *)
fn_sig        = [ "async" ] "fn" ident [ generics ] "(" [ params ] ")" [ "->" type ] ;
params        = param { "," param } [ "," ] ;
param         = "self" | ident ":" type ;
generics      = "<" gparam { "," gparam } ">" ;
gparam        = ident [ ":" bound { "+" bound } ] ;

struct_decl   = "struct" ident [ generics ] "{" { field sep } "}" ;
field         = [ "pub" ] [ "var" ] ident ":" type ;
enum_decl     = "enum" ident [ generics ] "{" { variant sep } "}" ;
variant       = ident [ "(" type { "," type } ")" | "{" { field sep } "}" ] ;
trait_decl    = "trait" ident [ generics ] [ ":" bound { "+" bound } ]
                "{" { ( "type" ident | fn_decl ) sep } "}" ;
impl_decl     = "impl" [ generics ] [ type_path "for" ] type
                "{" { ( fn_decl | "type" ident "=" type ) sep } "}" ;
type_alias    = "type" ident [ generics ] "=" type ;
const_decl    = "const" ident ":" type "=" expr ;
test_decl     = "test" string_lit block ;

type          = type_path | "dyn" type_path | "Self"
              | "(" [ type { "," type } ] ")"
              | [ "async" ] "fn" "(" [ type { "," type } ] ")" [ "->" type ] ;
type_path     = path [ "<" type_arg { "," type_arg } ">" ] ;
type_arg      = type | ident "=" type ;

block         = "{" { stmt sep } [ expr ] "}" ;
stmt          = ( "let" | "var" ) pattern [ ":" type ] "=" expr [ "else" block ]
              | expr ;

expr          = (* operators per 4.2 *) unary { binop unary } ;
unary         = { "-" | "!" } postfix ;
postfix       = primary { "." ident [ call_args ] | "." int_lit | call_args
                        | "[" expr "]" | "?" | ".await" } ;
call_args     = [ "<" type { "," type } ">" ] "(" [ expr { "," expr } [ "," ] ] ")" ;
primary       = literal | path | block | "(" expr ")" | tuple
              | list_lit | map_lit | struct_lit
              | if_expr | match_expr | loop_expr | while_expr | for_expr | closure
              | "return" [ expr ] | "break" [ expr ] | "continue" ;

if_expr       = "if" cond block [ "else" ( if_expr | block ) ] ;
cond          = expr | "let" pattern "=" expr ;
match_expr    = "match" expr "{" { pattern [ "if" expr ] "->" expr sep } "}" ;
loop_expr     = "loop" block ;
while_expr    = "while" cond block ;
for_expr      = "for" pattern "in" expr block ;
closure       = [ "async" ] "|" [ cparam { "," cparam } ] "|" [ "->" type ] expr ;
cparam        = pattern [ ":" type ] ;

list_lit      = "[" [ expr { "," expr } [ "," ] ] "]" ;
map_lit       = "[" ":" "]" | "[" expr ":" expr { "," expr ":" expr } [ "," ] "]" ;
struct_lit    = path "{" [ field_init { "," field_init } ] [ "," ".." expr ] "}" ;
field_init    = ident [ ":" expr ] ;

pattern       = pat_atom { "|" pat_atom } ;
pat_atom      = "_" | literal | literal ( ".." | "..=" ) literal | ident
              | path [ "(" [ pattern { "," pattern } ] ")"
                     | "{" [ fpat { "," fpat } ] [ "," ".." ] "}" ]
              | "(" [ pattern { "," pattern } ] ")"
              | "[" [ pattern { "," pattern } ] [ "," ".." ident ] "]" ;
fpat          = ident [ ":" pattern ] ;
```

## 12. Implementation Notes (non-normative)

- **Generics** are monomorphized.
- **Structs** map to WasmGC structs; `var` fields are mutable, all others immutable.
- **Enums** map to a WasmGC base struct with one subtype per variant; `match` compiles to `br_on_cast` chains or a tag switch.
- **Trait objects** are a pair of a vtable reference and a data reference.
- **Closures** are structs holding a function reference and the captured environment; a captured `var` is boxed.
- **Strings** may use JS String Builtins in the browser and UTF-8 GC arrays elsewhere.
- **Async** builds on JSPI in the browser and native async in WASI 0.3.
- **Workers** map to Web Workers in the browser, each running its own instance of the module.
- **Overflow checks** compile to the native op plus an overflow test and a trap.

## 13. Example

```puddi
// src/main.pud, built with: pud build --target wasi
import std.fs
import json

@derive(Eq, Show)
struct Todo {
    title: Str
    var done: Bool
}

enum AppErr {
    Io(fs.IoErr)
    Parse(json.ParseErr)
}

impl From<fs.IoErr> for AppErr {
    fn from(e: fs.IoErr) -> AppErr { AppErr.Io(e) }
}

impl From<json.ParseErr> for AppErr {
    fn from(e: json.ParseErr) -> AppErr { AppErr.Parse(e) }
}

fn load(path: Str) -> Result<List<Todo>, AppErr> {
    let text = fs.read(path)?
    let todos: List<Todo> = json.decode(text)?
    Ok(todos)
}

fn main() {
    let todos = match load("todos.json") {
        Ok(t) -> t
        Err(e) -> {
            print("could not load: {e}")
            return
        }
    }

    let pending = todos.filter(|t| !t.done)
    print("{pending.len()} of {todos.len()} left")

    for t in pending {
        print(" - {t.title}")
    }
}

test "empty list has nothing pending" {
    let todos: List<Todo> = []
    assert_eq(todos.filter(|t| !t.done).len(), 0)
}
```

## 14. Deferred Past v1

- Shared-memory threads, once WasmGC can share objects across threads
- `where` clauses
- Const generics
- User-defined derives and compile-time execution
