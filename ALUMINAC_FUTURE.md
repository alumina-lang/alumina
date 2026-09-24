# aluminac — findings & opportunities

Status snapshot and forward-looking backlog for the self-hosted Alumina
compiler (`src/aluminac/`, Alumina → LLVM IR). Written 2026-05-16 at the
close of the alumina-boot → aluminac parity effort. This file replaces
the now-removed `PORTING.md` / `PORTING_STATUS.md` / `CLAUDE.md` parity
scaffolding; it is intentionally self-contained.

## Where the project stands

**The parity headline is DONE.** There is a single unified `sysroot/`;
`sysroot-aluminac/` has been deleted. The aluminac self-bootstrap
converges: alumina-boot compiles aluminac stage 1 (via C), stage 1
compiles stage 2 (= `build/<profile>/aluminac`), and stage 3 (built by
stage 2) emits **the same IR as stage 2**, all against `sysroot/`. The
full test runner (`sysroot/test.alu`, reflective
`attributed::<()>("test")` discovery) runs under aluminac.

The Makefile is aluminac-first (reworked 2026-09-24): everything but
alumina-boot itself is compiled with aluminac (tests, examples, docs,
doc tests, tools). Targets: `make` (aluminac, `./aluminac`), `make test`
(unit, feature, std, lang, libraries, diag, debug info, doc tests), `make bootstrap`
(the fixpoint), `make check` (all CI checks, incl. `lint-boot`,
`test-boot`, `check-node-kinds`, examples), `make boot` / `lint-boot` /
`test-boot` / `cross-check` (alumina-boot). `make build/debug/aluminac-stage1`
builds just stage 1; standalone repros: `build/debug/aluminac --sysroot
sysroot <file>.alu -o out`. alumina-boot is the language spec — when in
doubt, read `src/alumina-boot/src/` and compare; do not infer semantics
from aluminac (it is buggy by definition until proven otherwise).
alumina-boot emits C (not LLVM IR), so an "IR-level diff between the
two compilers" is not a valid debugging strategy.

Hosts: bootstrap works on x86_64 and aarch64 Linux and on arm64 macOS
(the supported platforms for now; not Intel macOS, riscv64 or Windows). The C
calling convention (how aggregates are passed) is `codegen/abi.alu`, per
target arch (AAPCS64, x86_64 SysV); check both when touching it.
`tests/aluminac/c_abi.alu` (with its C side, `tests/aluminac/c/c_abi.c`)
covers the shapes, both ways.

Coroutines / minicoro / `codegen_func` / `codegen_const` are
deliberately out of scope for aluminac (alumina-boot emits C and
dispatches through them; aluminac uses LLVM intrinsics). LLVM stackless
coroutines is a separate future project, not tracked here.

## Beyond parity (effort started 2026-09-23)

Goal: make aluminac meaningfully better than alumina-boot (diagnostics,
robust mono without "unpopulated symbol"-style failures, cross-compilation,
idiomatic Alumina code), while it stays compilable by alumina-boot and the
sysroot needs few `#[cfg(boot)]`s. alumina-boot remains the default
reference; aluminac rejects what boot accepts only for boot bugs or where
boot misreads the language (record such cases here).

### Done

- **Mono-context isolation (the former headline, `test_dyn`).** Root causes:
  `mono_function` lowered every body against the caller's shared
  `type_map` (new bindings leaked out, unrelated ones leaked in) and kept
  the caller's `expected_type` hint / loop stack; `mono_struct` and type
  aliases bound params into the shared map and never removed them; struct
  type args were never completed with defaults, so `HashMap<K, V>` and
  `HashMap<K, V, DefaultHash>` were distinct types (receiver unification
  then failed and inference fell back to unhinted arguments). Now each
  instantiation gets its own context (own generic params, protocol
  Self/generics the caller binds, and the enclosing context for local
  fns/closures only), and type args are canonicalized. `test_dyn`
  ungated. Regression: `tests/aluminac/mono_context_isolation.alu`.
- Code that relied on the leaks now infers properly: operator-overload
  method generics are unified from the operands (`infer_type_args_from_ir`);
  bare generic struct literals are inferred without first monomorphizing
  the struct with unbound params.
- **if/else branch types** are unified like alumina-boot (a diverging arm
  takes the other's type, otherwise one arm is coerced to the other's
  type, else "mismatched types"). Previously the arm with "more struct
  fields" won and the other arm was *reinterpreted* (an `&[]` arm read a
  garbage slice length).
- **Slice indexing goes through `#[lang(slice_index)]` /
  `#[lang(slice_range_index)]`** like alumina-boot, so `--debug` builds
  are bounds-checked (they never were). Slice range bounds are lowered as
  usize (explicit `range_bound_hint`, not the leaky `expected_type`).
- **Generic statics/consts** are one global per instantiation
  (`lower_static_ref` / `emit_static`, `static_cache`). They used to be
  inlined values: a generic static lost writes, and slicing a generic
  const array (`Type::variants()`) returned a dangling pointer.
- **Consts that cannot be evaluated are an error** that points at the
  sub-expression the evaluator gave up on (`ConstEvalFailure`), instead of
  a silently zero-initialized global. The const evaluator now handles
  slice fields on string constants reached through variables.
- **Macro resolution matches alumina-boot**: unresolved macros are an
  error (they used to be silently dropped — several tests "passed"
  vacuously that way); there is no global by-name fallback (unqualified
  `cfg!` etc. resolved from anywhere); macro invocations/references in a
  macro body resolve at the definition site (hygiene), by stored id.
- **Targets / cfg**: `aluminac::target::Target` (parsed once from the
  triple; `arm64-apple-*` is AArch64) drives cfg keys, LLVM backend init
  and ABI decisions; `aluminac::cfg::CfgSet` has alumina-boot's key/value
  semantics (bare `key` predicates, `target_family`, `output_type`);
  `#[cfg_attr]` and file-level `#![cfg]` work; malformed cfg predicates are
  errors. New CLI: `--target <triple>`, `-d/--debug` (cfg `debug`, as in
  alumina-boot; the Makefile passes it with `-g`), real errors for unknown
  options / missing values.
- The `ir_functions` use-after-free (element pointer held across pushes).
- macOS (arm64, Homebrew LLVM 21) bootstraps; `make bootstrap` compares
  the IR emitted by stage 2 and 3 (linked binaries are not reproducible on
  macOS).
- Stdlib: `HashMap::contains`, `Command::status`, `Type::variant_name`.
- Test runner: compile-fail tests can require `// EXPECTED_ERROR: text`.

- Codegen and mono caches are keyed by value, not by weak hashes: the
  djb2 `name_hash` collided (`"gz"` and `"i8"` shared a string constant;
  the same hash keyed function/global declarations), lang items were
  looked up by djb2 hash, and the mono caches by an FNV hash of pointers
  (`MonoKey` now compares id, type args and enclosing instantiation).
- Module paths match alumina-boot: a file given without `module=` is a
  module named after its stem, and `module_path` is absolute (`::a::b`).
  Test names print correctly. Stdlib: `Path::{file_name, file_stem,
  extension}`, `string::rfind_char`.
- `tests/aluminac/cross_check.sh` runs every aluminac test through
  alumina-boot. `// BOOT_DIVERGES: reason` marks justified divergences.

- **Threading works under aluminac** (`--cfg threading`; the Makefile now
  passes it, like for alumina-boot). Fixes: the entry point is the
  sysroot's `#[lang(entrypoint_glue)]` instantiated for `main` (it runs
  `threading_init`; codegen's hand-built C `main` is only a fallback for
  freestanding programs); `#[link_name]` symbols are emitted raw (`\x01`),
  like alumina-boot's C asm labels; method receivers auto-deref through
  any number of pointers; `for x in e` iterates `e` in place rather than a
  copy (a channel's copied mutex deadlocked the thread pool).
- `for const` loops: each step builds a fresh const evaluator (the old one
  held slices of `ir_functions` across lowering — use-after-free that cut
  loops short), and `const_replacements` are per instantiation (a
  recursive instantiation clobbered the caller's loop variable). With
  closure captures in `fields<T>`, `test_debug_formatter` is ungated.
- Unresolved identifiers/paths are errors ("could not resolve the path"),
  as are paths to non-values; they used to become a silent bogus local
  (`let b = undefined_thing;` compiled; `libc::libc::X` in the sysroot
  became `undef` and broke `RwLock` on macOS).

- **Layout agrees with alumina-boot** (`layout.alu` rewritten around
  `Layout`/`AggregateLayout`): enums take their underlying type's layout
  (the underlying type is the first variant value's type, not always
  i32), `#[align(N)]` and `#[packed(N)]` are honoured, unions are their
  largest field rounded to their alignment. Codegen's LLVM types are built
  from it (unions as bytes + a zero-length aligned member; `#[align]`
  structs get a trailing one). A union typed `[N x i64]` had alignment 8
  instead of 4, which shifted `SocketAddr` and corrupted
  `Result<SocketAddr>` — the macOS `std::net` failures.
- Per-function lowering state is one `FnState`, swapped by
  `enter_fn`/`leave_fn` for instantiations, lambdas and static
  initializers (lambdas used to see the caller's hints, loops and `for
  const` bindings).
- Inference skips an argument whose own generic arguments could not be
  inferred (`inference_incomplete`, cf. alumina-boot's "type hint
  required" skip), so `Option::some(Result::err(e))` takes `T` from the
  expected type instead of `Result<void, E>`; a lambda without a return
  type returns `()`.
- Codegen inconsistencies (missing function/global/local, field index out
  of range, unhandled node) are internal compiler errors, not warnings
  with an `undef` value.
- All 557 stdlib tests pass under aluminac on macOS (with threading).

- **Type checking is as strict as alumina-boot's.** Before, `try_coerce`
  accepted any two types with the same tag (`Option<i32>` for
  `Option<u8>`, `&i32` for `&u8`), `()` for anything, and inserted casts
  between any builtin types, so wrong instantiations were silently
  punned. Now:
  - types are compared structurally (`IrTy::same_as`; not all IR types
    are interned) and only alumina-boot's coercions remain (`&mut T` to
    `&T`, `&mut [T]` to `&[T]`, `&[T; N]` to `&[T]`, fn item to fn
    pointer, `&T` / `&mut dyn P` to `&dyn P`; no implicit `&` of a value);
  - binary and unary operands are typechecked (`typecheck_binary`); shift
    amounts may differ, pointers offset by `isize`/`usize` only;
  - `if`/`switch` branches are unified by `unify_branches`, where a
    missing `else`/default arm is `()` (with a note saying so); a `loop`
    without `break` is `!`; `break` with a value only in `loop`;
  - `&place` is `&T` only for immutable places (`is_const_place`, as
    alumina-boot's `is_const`), and collections are indexed through
    `#[lang(slice_slicify)]` (a mutable `Vector` gives `&mut [T]`).
  This exposed (and the fixes cover) many latent inference bugs:
  - **Type hints** are explicit (`lower_expr_hinted`) and flow as in
    alumina-boot: block value, both branches, `when`, `switch` arms and
    patterns, `loop` breaks, lambda bodies (return type), `&x`, operands,
    empty array literals, the arguments of every kind of call (the
    `slice_new` lang path lowered its length unhinted, so the entrypoint
    glue built `argv` slices with `cast<usize, ()>`), and alumina-boot's
    `local_type_hints` rule (`{ let x = ...; x }`). The enclosing
    function's return type is no longer a fallback hint.
  - Diagnostics from tentative lowering (for inference) are dropped
    (`tentative`, per function), and a lambda is lowered once per function
    instance (`lambda_cache`) — lowering it twice gave two closure types.
  - Protocol generics bound for a method call no longer leak into the
    caller's type map (an argument's `.map(...)` set the outer
    `.chain(...)`'s `T`); dyn calls bind the protocol's parameters to the
    `dyn` type's arguments; struct literal and `F: Fn(A...) -> R`
    inference use full unification; `MonoKey` compares types
    structurally (enum types were not interned, so `unwrap<u32, Error>`
    was instantiated twice).
  - `use a::{b as c}` resolved `b` in the importing scope, not in `a`.
- A generic parameter that cannot be inferred is "type hint required"
  (it silently became `()`; e.g. `cast<i32, ()>` got instantiated while
  lowering an argument tentatively). A `()` hint is told apart from no
  hint (`MonoCtx::no_hint`), and whether a tentatively lowered argument's
  type is unknown is scoped to that argument (`tentative_incomplete`).
  Array literal elements after the first get its type as hint.
- Casts follow alumina-boot's rules (`lower_cast`: e.g. no `value as &T`).
- `pointer_with_mut_of<T, Ptr>` is `&T` with `Ptr`'s mutability (aluminac
  expected a pointer `T`, so `std::typing`'s pointer checks were wrong).
- **Spread types** `(A, T...)` and `fn(T...)`, and spreads in tuple
  literals (`(x, t...)`), are supported; they used to parse as
  unresolved types.
- Type names in diagnostics and `type_name` match alumina-boot
  (`(Option<i32>, &mut [u8])`, `fn(i32) -> u8`, `&dyn P<..>`).
- Sysroot: `Deque::from_slice` passed `T` where `&mut T` was expected
  (alumina-boot rejected it too, when instantiated).
- **The C calling convention for aggregates** (`codegen/abi.alu`): LLVM
  passes a first-class aggregate member by member, which C does only for
  some, so structs crossing into C (or callbacks C calls, e.g.
  tree-sitter's read callback taking `TSPoint`) were garbled. Aggregates
  are now classified as clang does (AArch64: HFAs as they are, up to 16
  bytes as i64s, larger through memory/sret; x86_64: eightbytes, byval)
  for extern "C", exported and address-taken functions and every call
  through a pointer; other functions keep LLVM's passing. Found with it:
  `llvm_type` built pointee types, which could query a struct's layout
  while it was opaque and poison LLVM's layout cache (sizes of 0).
- **alumina-doc is built by aluminac** (`make docs`; no minicoro). Its
  output is byte-identical to the alumina-boot build's (all 1095 files,
  debug and -O3). Getting there fixed root paths (`use ::x`), universal
  macro calls in macro bodies and a `defer` that returns.

### alumina-boot bugs found (aluminac deliberately differs)

- `Ty::gcd` joins `&mut T` and `&T` to `&mut T` (its own `assignable_from`
  treats `&T` as the supertype), so `if c { &x } else { &y as &T }` is
  rejected. aluminac joins to `&T` (`if_branch_mut_const_pointer.alu`).
- Later path segments resolve lexically in the module found so far, so
  `std::std::mem::size_of` and `libc::libc::X` compile (the latter was a
  typo in `std::sync`, now fixed). aluminac resolves each later segment in
  the module named so far only, and reports the path.

- `intrinsics::fields` lays out union fields like struct fields (offsets
  0, 4, 12 for `union U { a: i32, b: f64, c: u8 }`); aluminac gives 0.
- Compound assignment `*f() += g()` is emitted as C `+=`, whose operand
  evaluation order is unspecified (clang calls `g()` first), although its
  lang tests expect left to right (special-cased only for zero-sized
  pointers); aluminac evaluates the place first
  (`compound_assign_once.alu`).
- Duplicate `#[lang]` items are accepted (one silently wins); aluminac
  reports them (`duplicate_lang_item_compile_fail.alu`).
- Crashes ("type ... was not registered") on a float cast to `i128`/`u128`
  at run time and on a function of a zero-sized return type taken as a
  `fn` pointer (`let f: fn(u8) -> Z = z;`); cannot IR-inline slice indexing
  of zero-sized elements (so `Vector<Z>` fails).
- Evaluates zero-sized struct/tuple elements before the others, and drops
  the receiver's effects in `f().len()` on arrays
  (`side_effects_evaluated_once.alu`).

### alumina-boot quirks aluminac follows (for now)

- `Alias::f` is the alias target's `f` with fresh generic parameters: the
  alias's own arguments are ignored (`type R = Result<i32, u8>;
  R::err(1)` in a function returning `Result<i32, u16>` is a
  `Result<i32, u16>`; `let x = R::ok(1)` needs a type hint). The sysroot
  relies on it (`Result::ok(())` in `std::io::unix` means
  `std::result::Result` under the `io::Result<T>` alias). Arguably a bug.
- Names resolve through enclosing modules lexically (a child module sees
  its parent's items).
- A path's first segment is also looked up in the *enclosing scopes of a
  star-imported scope*: through the root's `use std::prelude::*`, all of
  `std`'s modules (`mem::size_of`, `typing::is_same`) work anywhere without
  a `use`. Looks accidental, but the lang tests rely on it. (aluminac used
  to approximate it with the modules named by `use`s in scope.)

### Examples under aluminac

All of `examples/` except `coroutines` (no coroutines in aluminac) and the
network one compile with aluminac and print what alumina-boot's builds
print (modulo randomness and thread interleaving). Fixed for them:
- **Statics with non-constant initializers were silently zero** (e.g.
  `static X: i32 = f();`). Now, as in alumina-boot, such initializers run
  at startup in dependency order (a synthesized `#[static_ctor]`, before
  other constructors); only plain constants initialize the global directly
  (folding e.g. a loop that also updates another static would lose that).
- The const evaluator: a pointer to an array cast to a pointer to its
  elements (array-to-slice coercion) points to the first element; pointer
  differences; slice fields; ptr-to-ptr casts were misread as ptr-to-int.
  (`examples/constants.alu` fills an array through an iterator at compile
  time.)
- A generic function used as a value is instantiated from its expected
  function pointer type, or (beyond alumina-boot, whose example asks for a
  type hint here) from a generic parameter's `Fn(...)` bound.
- `&&[T]` was collapsed to `&[T]`; range literals take `T` from a
  `Range<T>` hint; type-level `T.(expr)` / `T.(a..b)`.

### alumina-boot's library tests under aluminac

`make test-libraries` builds `libraries/` (json, the
tree-sitter bindings, aluminac-common) with aluminac: all 22 tests pass.
Fixed for it: `?` inside macro bodies (it was expanded while pre-parsing,
before `try!` was available), `let (a, b): T;` / typed tuple patterns,
method generics inferred from the expected return type, `Type::is_slice`
(`SameBaseAs` through a generic parameter, and for slices), protocol
conformance decided by a method's bounds (e.g. `&[i32]` is not
`Formattable`; lang-protocol bounds such as `PointerOf<u8>` were taken as
always satisfied). A json bug that alumina-boot never instantiated
(`Error::NumberNotRepresentableExactly` is an `ErrorKind`) is fixed.

### alumina-boot's lang tests under aluminac

`tests/lang/lang.alu` (alumina-boot's language test suite) compiles and
runs with aluminac (`--cfg coroutines`, linking `minicoro.o`); see below
for the remaining failures. **Coroutines** are implemented as in
alumina-boot: a `fn*` instance's body becomes a function of its own that
returns `()`, and the instance calls `#[lang(coroutine_new)]` with it and
its arguments; `yield v` is `#[lang(coroutine_yield)]` (returning when the
coroutine is cancelled).
Found through it: compound assignment evaluated a place with side effects
twice (`*f() += 1`); nested aggregates (arrays of arrays) compared with a
bad `icmp`; offsets of pointers to zero-sized types were GEPs into `void`;
zero-length arrays and aligned zero-sized structs were given no alignment,
and **LLVM struct types now follow layout.alu exactly** (explicit padding
where LLVM would place a member elsewhere, e.g. after an aligned
zero-sized field or in `#[packed(N)]`; the struct type cache was keyed by
a weak hash); constants with `()` fields/elements were malformed;
constant slices of strings lost their offset; `transmute` in constants now
goes through the value's bytes (e.g. `[u8; 4]` to `u32`).
Also: `#[location("file", line)]`; **constants holding pointers into
other constants were null** (`const B: &i32 = &A[2];`; codegen now folds
them as addresses of the globals); references to zero-sized values are
dangling pointers (the alignment as address), as in alumina-boot.
`#[packed(N)]` (N > 1): a packed LLVM struct has alignment 1, so, as
clang, aluminac gives variables of such types (locals, parameters,
temporaries, globals) the layout's alignment explicitly
(`CodegenCtx::alignment_of`), which `_Alignof` also reports; tuples place
their elements as structs do (`place_members`: `(u8, S)` had `S` at
offset 1 and 7 bytes where size_of said 8), and constant tuples and
element-wise `==` go through the member index map.
All 33 pass. `stringify!` prints the expression as alumina-boot prints
its AST (`parser/pretty.alu`, a port of `ast/pretty.rs`): after macro
expansion and name resolution, with nested operators parenthesized and
`while` desugared; it used to give the source text. `T::name` in a type
(`TyTag::Defered`) is the type of `T`'s associated function, as in
alumina-boot, and `T::name` as a value is a path to it (both were errors).
Done for
it: **linear block scopes** (each item declared in a block starts a new
scope for the rest of the block, so a later `const A` / `fn foo` /
`struct foo` shadows an earlier one from its declaration on; aluminac
registered all of a block's items up front and the last one won), tuple slicing
`t.(a..b)`, `#[tuple_args]` (aluminac had a `tuple_call` of its own),
`codegen_type_func` `sizeof`/`_Alignof` (from
LLVM's data layout, so it checks aluminac's layout), prelude module paths,
and a crash (`transmute` lowered without its target type, which the const
evaluator dereferenced).

### Diagnostics parity (tests/diag)

`tests/aluminac/diag_check.py` runs alumina-boot's diagnostics tests
(`tests/diag/*.alu`) under aluminac and compares where errors and
warnings are reported (the first line in the test file of each
diagnostic's location, expansion or instantiation chain). Done so far:

- **Macro expansion backtraces**: spans carry the macro expansion they come
  from (`Span::expansion`, into `DiagnosticContext::expansions`), and a
  diagnostic in expanded code ends with "in this expansion of `m!`" notes
  up to the call as written, which alumina-boot also reports (as backtrace
  frames).
- **Constant evaluation** (all 16 `const*` tests match): failures use
  alumina-boot's reasons, located at the expression that failed, with "in
  this call to `f`, evaluated at compile time" notes for the calls it
  happened in. `const_eval!` must be evaluable (it used to fall back to
  run time silently, so the stdlib's `const_eval!` tests passed without
  evaluating anything); `const_panic`/`const_warning`/`const_note` take
  computed messages (the stdlib's `assert_eq!` builds one in a buffer);
  reading an uninitialized local is an error; **the evaluator has a heap**
  (`const_alloc`/`const_free`, with use-after-free and invalid-free errors,
  and `const_bake`: baked allocations become constant globals, so
  `const H: HashMap<..> = { ...; m.const_bake!() }` works). Also:
  indexing through pointers (dyn calls through vtables, sub-slices of
  arrays), assigning a slice's fields, slice casts; "constant string
  expected" for `concat!`/`format_args!`/`include_bytes!`, and
  `include_bytes!` of an unreadable file is an error (it gave `""`).

- **Declarations** (as in alumina-boot): duplicate names in a scope
  (functions of different `impl` blocks shadow with a warning), duplicate
  and invalid attributes, `#[align]` with `#[packed]` (and `#[align(1)]`
  warns), unknown lang items and builtin macros, `#[transparent]` with
  other than one field, `extern`/protocol/coroutine/varargs function
  combinations, functions without bodies, extern statics, aliases without
  targets and misapplied type operators (which resolved to `()`), too many
  enum variants, `std::builtins::array`/`tuple` as types, struct literals
  of non-struct types, duplicate field initializers, a default `switch`
  arm that is not last.
- **Macros**: argument counts, `$...` outside macros / without `...`
  parameters / nested, `...` outside tuples, items and lambdas in macro
  bodies, recursive macros (also indirect ones, which overflowed the
  stack), invalid escapes (and `\u` escapes, which aluminac kept
  verbatim), format strings (aluminac ignored errors, e.g. dropping
  arguments).
- Found along the way: **an `impl` before its type lost its methods**
  (pass 1 now visits `impl` blocks last); a tuple spread `t...` in a macro
  body was taken for the macro's `$...` (now `ExprTag::MacroEtCetera`);
  branches that disagree coerce to the expected type when they all can
  (`let s: &[T] = if c { &[a] } else { &[a, b] }`); `#[lang("x")]` was
  silently ignored; erroneous expressions lower to `!` (`mk_error`) so the
  error does not cascade; types have no spans, so errors in them point at
  the enclosing expression (`Mono::type_span`).

- **`#[inline(ir)]` is implemented** (`mono/inliner.alu`): calls are
  replaced by the callee's body during mono, as in alumina-boot, with its
  restrictions reported (variables, flow control, early returns). This is
  about meaning, not speed: **`stack_alloc` allocated in its own frame**,
  freed on return (two `stack_alloc`s in a function overlapped at -O0);
  `test_const_stack_alloc` runs again.
- Mono checks: `break`/`continue` outside loops, `return`/`defer` outside
  function bodies, `defer`/`yield` in `defer`, argument counts (none were
  checked; the LLVM IR was invalid), methods without parameters, closures
  binding non-locals, addresses of intrinsics, `dyn` of non-protocols /
  builtin protocols / non-dispatchable functions / another `dyn` (a `dyn`
  now conforms to its protocols), protocols with generic functions used
  other than as mixins, recursive protocol bounds; compilation stops after
  syntax errors. Constant evaluation of pointer comparisons and
  differences (same place, string bytes by value), `&*p`, function pointer
  equality.
- Cycles: module-level `use`s are resolved eagerly, so unresolvable ones
  are errors (aluminac ignored them unless used) and alias cycles are
  reported (following one recursed forever); static initializers that
  depend on each other; a function signature that depends on itself
  through `typeof` (aluminac instantiated the function twice). Mixins of
  non-protocols.
- **Lints** (111 of 112 tests match): warnings carry a lint name, and
  `#[allow(lint)]`/`#[deny(lint)]`/`#[warn(lint)]` (or `warnings`) on
  items and statements apply as in alumina-boot (the innermost around the
  warning decides; denied ones are errors; unknown lint names are
  reported). Unused variables, parameters, closure bindings and imports
  in functions (tracked per declaration: alumina-boot marks names, so
  e.g. a method call `x.args()` counts as a use of a variable `args`;
  two dead declarations in the stdlib were found this way), dead code,
  pure statements, `#[diag::must_use]` types, constant conditions (not
  those depending on calls or `in_const_context()`), `while true`,
  unnecessary casts (outside generic code), `defer` in loops,
  uninitialized fields, union initializer overrides (the last now wins,
  as in alumina-boot; aluminac rejected them), `std::typing::Self` in
  signatures, protocols/consts/statics as value types, unknown attributes,
  redundant top-level blocks. Lint warnings in macro-produced statements
  point at the invocation; each place warns once (not per instance).
  Found along the way: a struct literal missing a field crashed the
  compiler; the constant evaluator took a static's initial value for its
  value.
- **All 112 diagnostics tests match.** For `const_only`, as in
  alumina-boot: an `if` whose condition is known at run time when
  compiling (evaluated with `in_const_context()` false) compiles only the
  branch taken, and codegen compiles only the functions reachable from
  the program's roots (`codegen/reach.alu`), reporting const-only code
  among them. aluminac compiling itself now emits 4252 functions instead
  of 6603. Found along the way: the type caches (tuples, function
  pointers, slices, arrays) were keyed by hashes of pointers and ids and
  returned whatever type had the same hash; the constant evaluator
  compared integers by their 64-bit storage (a negative `i32` stored
  sign-extended or not), computed 128-bit values in 64 bits, and
  transmuted variables it had no value for into zeros; a call to a
  function codegen had not declared silently became `undef`.
- Remaining: unused macro parameters (alumina-boot warns).

### Cross-check status

`tests/aluminac/cross_check.sh`: every aluminac test behaves the same
under alumina-boot, except those marked `// BOOT_DIVERGES: reason`
(aluminac-only intrinsics, freestanding tests with their own lang items,
and the alumina-boot bugs above). Invalid tests found along the way were
fixed (partial turbofish, `value as &T`, shadowed generics, duplicate
lang items, a `max` field shadowing `IteratorExt::max`, ...).

Also matched to alumina-boot in this pass: a field takes precedence over
a method of the same name; `Type::<T>::method()` is rejected (generic
arguments go on the function); protocol types check their parameters'
bounds (`Formattable<T, F>` needs `F: Formatter<F>`), as do struct
instances.

### Backlog (found along the way)

- **Strictness gaps vs alumina-boot** (aluminac accepted invalid code):
  protocol conformance compared method names only; it now compares
  signatures as alumina-boot (`has_protocol_signature`: the candidate's and
  a mixin protocol's generics inferred from the protocol's signature,
  cached per type/protocol; `protocol_signatures.alu`), and a `&mut self`
  method called through `&` is an error. (Missing `not_equals` and
  `use std::io::ErrorKind` were already fixed.) Also now errors (probing
  every alumina-boot error kind): unknown struct literal fields, non-`bool`
  `if`/`while` conditions, duplicate enum values (alumina-boot: internal
  error), generic argument counts of types, too many `for` variables,
  structs containing themselves (not through a pointer), `*T`/`T.N` of a
  non-pointer/non-tuple, capturing closures as `fn` pointers
  (`invalid_code_compile_fail.alu`); closures are `{{anonymous}}` in type
  names, as in alumina-boot.
- ~~Ad-hoc inference paths~~: done. `mono/infer.alu` is the one engine
  (`Inference`, `infer_call`, `infer_from_types`) every call path feeds:
  functions, methods, deferred `T::f` calls, protocol generics of mixed-in
  methods, operators, `for` loops and generic functions taken as values.
  Evidence in order (first binding wins): explicit type arguments and the
  receiver, arguments typed on their own, the expected type (unified with
  the result type), what the receiver's type implies, untyped literals,
  then protocol bounds to a fixpoint. It replaced ~900 lines (two copies
  of an `Fn`-bound scan, four shape-specific uses of the hint, three
  positional guesses of slice methods' type arguments) and fixed the
  method path's bugs (inferences it never recorded, arguments whose own
  inference had failed). Beyond alumina-boot (the user allows inferring
  more where unambiguous): untyped literals are the weakest evidence
  (`let x: u8 = id(5)`, `same(1, 2u8)`; `inference_literals.alu`), and a
  generic function passed where an `Fn` bound is known (`call(id)`).
  Arguments are still lowered twice (tentatively, then with their
  parameter types), as in alumina-boot.
  Candidate next step: a local's type from later statements
  (`let v = Vector::new(); v.push(1u8);`), which neither compiler infers.
- The std tests under aluminac lack `--cfg libbacktrace` (backtraces use
  libc's `backtrace`); coroutines link minicoro until LLVM coroutines.
- ~~Cascading errors~~: done. What fails to lower is an error value of
  type `!` (`mk_error`) that uses do not report again: unresolved methods
  and fields, invalid operators, dereferences and indexing, incompatible
  branches (75 errors for the 10 mistakes of
  `errors_do_not_cascade_compile_fail.alu`, which checks the count with
  `// EXPECTED_ERROR_COUNT`). A protocol instance's bounds are checked
  once, and bound errors of struct and protocol instances are located
  where the type is used (`type_span`).
- Protocol conformance of a method with a generic parameter that its
  signature does not determine (e.g. a method `<T>` shadowing the impl's
  `T`): alumina-boot says "does not match" (type hint would be needed),
  aluminac lets it match.
- Cross-compilation: `--target` exists, but ABI lowering only knows
  x86_64 SysV / AAPCS64 (Apple arm64 variadics differ), there is no
  per-target sysroot/linker story, and only x86_64/aarch64 parse. The
  x86_64 aggregate classification has not been run on an x86_64 host
  yet (the c_abi test will, on Linux CI).

## Remaining `#[cfg(boot)]` gated tests (the cleanup queue)

Goal: `#[cfg(boot)]` should be a small, justified allowlist. All 54
`cfg(boot)`/`cfg(not(boot))` sites were reviewed and this
classification confirmed by the maintainer. Items 1, 2, 5 are DONE
this effort (13+ gates removed); the rest is backlog.

### APPROPRIATE — keep (genuine boot-only-by-design; both sides real)

The legitimate, permanent allowlist — aluminac fundamentally uses a
different mechanism and both paths are fully implemented:

- `std/intrinsics.alu` `#[cfg(boot)]`/`#[cfg(not(boot))]` blocks:
  `codegen_func`/`codegen_const`/`codegen_type_func` (boot, C
  emission) vs aluminac LLVM intrinsics (`llvm`, `stack_alloc`,
  `atomic_*`). The core divergence model.
- `std/builtins.alu` `count_ones`/`ctlz`/`cttz` (C/libc vs
  `intrinsics::llvm`), `checked_add/sub/mul` vs `__builtin_*_overflow`,
  `wrapping_add/sub/mul` (C vs LLVM wrap). Real C-vs-LLVM semantics.
  *Style nit only:* could be inline `if in_const_context() … else
  when cfg!("boot") … else …` — but see the `when cfg!`
  name-resolution constraint under item 6.
- `std/mem.alu` `stack_alloc` fn pair (boot-only codegen_func; aluminac
  has its own `intrinsics::stack_alloc`); both compilers run
  `test_stack_alloc` and `test_const_stack_alloc` now that aluminac
  inlines `#[inline(ir)]`.
- `std/sync/mod.alu` `test_ordering_values_match` (boot-only
  `codegen_const` C-constant check; aluminac coverage is
  `tests/aluminac/atomic_intrinsics.alu`).

### DONE this effort

1. **i128/u128 literal gap — fixed, 10 gates removed.** Root: integer
   literals stored as `u64` across parser/AST/IR, truncating 128-bit
   literals (`i128::max_value()` = `0x7fff…ffffu128 as i128` collapsed
   to all-ones). Threaded the full value: `parser/mod.alu`
   `parse_int_with_suffix` → `u128`; `ast.alu`
   `_ExprLitData`/`_IrLitData` gained `int_val_hi` (+`int_val_u128()`);
   `mono/lower.alu` `mk_int_lit_u128`; `llvm.alu` binds
   `LLVMConstIntOfArbitraryPrecision`; both IntLit codegen paths emit
   `[lo,hi]` words for >64-bit int types. Regression
   `tests/aluminac/i128_u128_literals.alu`. **Deferred sub-item
   (non-blocking):** const-eval of 128-bit values
   (`_CVIntData`/`const_eval.alu` int arithmetic still `u64`) — only
   matters for a 128-bit literal in a `const`/static initializer
   (none of the removed gates needed it). If needed: add `int_val_hi`
   to `_CVIntData`, `ConstValue::make_int_u128`, and 128-bit paths in
   `const_eval.alu` int arithmetic/compare/cast.
2. **per-call mono-context (test_fuse/test_flatten_2) — ungated.**
   Eliminated by this effort's union/`mk_if`/empty-StructLit fixes.
   The deeper variant survives as `test_dyn` (headline section).
5. **vestigial `test_cases!()` deleted** end-to-end (dead since
   `test.alu` uses `attributed::<()>("test")`): the macro decl
   (`std/macros.alu` now cfg-clean), `expand_test_cases` + builtin
   dispatch (`parser/expr.alu`), `all_test_functions` /
   `share_test_functions` (`parser/mod.alu`), call site (`main.alu`).

### TODO — backlog

3. ~~`test_dyn` (typing.alu)~~ — fixed by mono-context isolation, ungated.
4. ~~Deeper feature gaps~~: `std/typing.alu` `element_types` (type-level
   `Tup.(1..)` and splats) and `std/fmt` `test_const_println` both work
   (their `#[cfg(boot)]` gates were stale and are removed; a constant's
   notes were hidden, see below); so does `test_debug_formatter`.
   Standalone notes (a constant's `println!`) were dropped after an allowed
   lint: notes on a diagnostic are now marked `attached` and only those go
   with it.
6. **atomics inline-dispatch refactor** — *gated on item 3*. Desired
   shape: statement-level `#[cfg(boot)] return …; #[cfg(not(boot))
   return …; intrinsics::unreachable()` inlined into each `Atomic<T>`
   method, deleting `std/sync/mod.alu`'s `atomic_internal` `#[cfg]`
   twin. Compiles cleanly under both compilers (verified) but
   re-triggers the item-3 mono-context pollution
   (`test_flatten_2` SIGSEGV). Land after the mono-context root is
   fixed. `atomic_internal` stays meanwhile (correct, just not the
   desired shape).

   **Name-resolution constraint (important, was stale in prior
   comments):** aluminac **elides** the non-selected branch of a
   statement-level `when cfg!(...)` from name resolution;
   **alumina-boot does NOT**. A statement-level `#[cfg(...)]`
   attribute **does** elide in *both*. So inline boot/aluminac
   dispatch must use `#[cfg]`-attributed statements, not `when cfg!`
   (the aluminac `intrinsics::atomic_*` are `#[cfg(not(boot))]`-
   declared and would fail to name-resolve under alumina-boot in a
   non-selected `when cfg!` arm).

## Codegen / mono audit class: operands evaluated once, in order

Done (2026-09-23). Found with probes that log every operand's evaluation
(compared with alumina-boot) and fixed:
- `f()[i]` on an array evaluated `f()` twice (codegen evaluated the base
  as a value and again as a place), for every array type;
- `arr[a..b]` evaluated the range once per bound (aluminac sliced arrays
  by hand; they now go through `slice_slicify` and `slice_range_index` as
  in alumina-boot, which also bounds-checks them in debug mode);
- `() == ()` was folded without evaluating either side;
- assigning to a zero-sized place, and field places whose container has
  no LLVM fields, skipped evaluating the place;
- struct literals were evaluated in declaration order, not as written;
- struct/array literals of LLVM-void type skipped their elements, and an
  indirect call through a value-less callee dropped the call (now an
  internal error).

**Guard:** `CompilationUnit::check_evaluated_once` (on unless
`--no-verify`) reports any expression with effects that appears twice in
a function's IR, i.e. would be evaluated twice. It is clean over aluminac,
the std/lang/library tests and the feature suite.

Deliberate differences from alumina-boot (whose order comes from C and is
partly unspecified): alumina-boot evaluates zero-sized struct/tuple
elements before the others and drops the receiver's effects in
`f().len()` on arrays; aluminac evaluates as written. Compound assignment
evaluates the place first (alumina-boot's lang tests expect it; its
`=` evaluates the value first, as aluminac's).

## Other architectural opportunities (non-blocking)

- **Const-eval completeness.** Doesn't fold calls through
  `format!`/`_finish_format`. (128-bit integers: done, the evaluator is
  128 bits wide; `const_eval_integers.alu`.)
  Structured comparison vs `src/alumina-boot/src/ir/` const-eval if
  this becomes a priority (alumina-boot's interpreter is ~2000 LoC;
  aluminac's gaps: pointer-arena chasing, dyn dispatch, heap-bake).
- **Fully-qualified macro paths.** `std::println!` is now an error
  ("could not resolve the path"), as in alumina-boot (the macro lives in
  `std::io`); no longer a silent no-op.
- **`when cfg!` name-resolution asymmetry.** (See item 6.) Making
  aluminac and alumina-boot agree (ideally both elide non-selected
  `when cfg!` arms from name resolution) would unblock the cleaner
  inline-dispatch style across `builtins.alu` and `sync/mod.alu`.

- Aggregates are LLVM first-class values everywhere (loads, stores,
  arguments), where clang uses memcpy/memset and pointers. For large ones
  that is slow to compile and can break LLVM: a `store [65536 x i8]`
  overflows x86_64 instruction selection (found through locals, which
  were all zeroed; copying such an array by value is still one
  load/store).
- ~~Every local was zero-initialized~~ (to hide defers of untaken
  branches running on uninitialized locals): defers now have flags and
  run only if reached, from one cleanup block, as in alumina-boot; locals
  are uninitialized, as `let x: T;` is. That exposed `for i in 0usize..8`
  storing the `8` as an i32 into the usize bound.
- A `const`/`static` in a generic function's body may use the function's
  generic parameters (`const SIZE: usize = size_of::<T>();`) but is one
  item for all instances, so every instance sees the first one's value (as
  in alumina-boot). Should be an error (Rust: "can't use generic parameters
  from outer item") or per instance.
- Codegen does not convert values to the LLVM types expected of them
  (arguments, results, fields, `&`, branches of an `if`): mono gives them
  those types, and a value of another type is an internal compiler error
  (it was converted, e.g. an `i32` argument to a pointer, which hid a type
  check missing in mono). Casts and intrinsics' results are converted.
- ~~On macOS, `-g` output has no usable debug info~~: aluminac runs
  `dsymutil` after linking.
- Debug information (2026-09-24; alumina-boot had `#line` only): DWARF as
  C++ (the language debuggers know with namespaces). Modules are
  namespaces; types are named as written (`&[u8]`, tuples, `fn(i32) ->
  i32`, pointers as typedefs `&T`, builtins as typedefs so `i32` is not
  `int`); structs, unions and enums in their modules, methods in their
  type's namespace; locals in lexical blocks from their `let` (macro
  expansions' and `_`-prefixed ones hidden); macro code at the call site.
  Symbols of functions, closures and statics are Itanium-style paths
  (`_ZN4main11report<i32>E`), so lldb, gdb, perf and `nm -C` show
  `main::report<i32>`; items in a function body are in the function
  (`main::g<u8>::h`, `main::main::{closure#0}`; a static there, one for
  all instances, `main::g::X`). Programs are compiled whole, so names need
  only be unique, not canonical (no hashes; a `.N` suffix on a clash).
  `#[export]`, `#[no_mangle]`, `#[link_name]` and extern items keep their
  names. lldb formatters for the standard library's types
  and `alumina-lldb`: `tools/lldb`. Tests: `tests/debuginfo` (lldb
  commands and expected output, `make test-debuginfo`).
  Open: type arguments as Itanium template arguments (`_ZN4main1gIu2u8EE`;
  demanglers read `g<u8>` in a name, but `c++filt` as a text filter
  splits the symbol at the `<`); gdb pretty printers; enums as `enum class` (gdb shows
  `main::shapes::Green`; the C API has no flag for it); `lldb-server` 22 from
  apt.llvm.org crashes on OrbStack's kernel, so the lldb tests do not run
  in the local Linux containers (gdb works there).

## Test infrastructure backlog

- **Unit tests** of the compiler itself: `#[cfg(test)] mod tests` beside
  the code (const_eval's integer arithmetic, layout, literal parsing and
  unescaping, cfg specs, lint levels and notes, AST helpers, targets),
  built with aluminac by `make test-unit`; `make test` runs them with the
  rest of the suites.

- ~~`make test-docs` under aluminac~~: done (the doc tests are compiled
  with aluminac; it found `format_args!(concat, ...)` crashing, `Fn(..)`
  types being function pointers, `Type<X>` of same-named items, and
  mixin `self: Self` methods through pointers).
- `make test-diag` checks aluminac's diagnostics against the annotations
  in tests/diag (alumina-boot's `tools/diag.py` wrote them).

`tests/aluminac/*.alu` is the aluminac feature suite (run by
`tests/aluminac/run_tests.sh`); add a regression per concrete fix.
Regressions added this effort: `i128_u128_literals`,
`typeop_tuple_index_of`, `reflect_fn_type_name`,
`use_exposes_top_module`, `const_zst_struct_descriptor`,
`union_switch_arm_value`.

## Operating notes (carried over from the retired scaffolding)

- alumina-boot's behavior is the spec; verify framings against
  `src/alumina-boot/src/`, not against prose — status narratives went
  stale repeatedly over this project.
- When patching the same dispatch site twice (a second special-case
  branch), stop: the model is likely wrong-shaped and the fix is
  upstream (the dyn-vtable 4-branch site at `mono/lower.alu` ~3821 is
  the canonical example).
- Alumina `switch` is sugar for if-else; when fixing switch-pattern
  bugs, check whether an integer fast-path is even needed.
- Add a `tests/aluminac/` regression for every concrete bug fixed.
