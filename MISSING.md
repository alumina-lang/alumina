# List of known bugs and missing features

## General

- Make IR inlining better
  - Better error messages for why recursive functions can't be inlined (rather than just "Unpopulated symbol")
- stack overflow in codegen stage because infinite size recursive structs are not rejected during monomorphization
    - could be a similar issue with protocols, though these are more coservative vis-a-vis recursion
- if tentative monomorphization fails (e.g. error), but type inference still succeeds, we are left with unpopulated symbols
    - this is now especially an issue with `when` expressions which do tentative mono during proto bound checking
    - This is a big problem, unfortunately there is no easy solution with the current `mono` architecture.
- "any/don't care" in protocol bounds. Especially for things like `Hashable` and `Formattable`, it would be great if users didn't need to introduce a new generic parameter for the hasher and formatter (since that complicates type inference).
  - Alternatively, allow pre-monomorphized types to be used as protocol bounds
  - This could be solved by `infer`. It needs to do the same thing as `check_protocol_bounds` - go through all the AST methods of the protocol in the bound and IR method of the type in the slot and
  match the slots on all of them. It's quite a lot of work and also `infer` will probably need to start looping until no more changes are made (e.g. in nested protocol bounds), but it would be quite awesome. By doing that, protocols would actually start *helping* type inference instead of making it harder.
- Some limited pattern matching in macros (optional arguments)
- Local items (functions, structs defined in linear scopes) that bind ambient generic parameters
  - Right now there is not even a good error message to say that this is not supported, just a cryptic "unbound placeholder" during mono
- Recursive local functions lead to stack overflow as mono monomorphizes them over and over again. The local item handling for functions was designed for lambdas that cannot be recursive (without indirection)
- Macros cannot define local items or use anonymous function. This is quite bad and should be fixed.
- `if opt.is_some { opt.inner }` and  `if res.is_ok() { res.unwrap() }` do not spark joy. Full pattern matching is overkill, but this is very common and
  deserves a better idiom.
- a coherent story for operator overloading
- `dyn` pointers for certain builtin protocols. Specifically `dyn Callable<...>` would be very useful for being type-erased closures.
- Fix that damn "local with unknown type" issue. It can happen that compilation will fail with 0 errors and 0 warnings now.
- get rid of println! and eprintln! in const-eval, give them separate names

## Grammar, parsing, AST

- Switch is a bit cumbersome at the moment / improve?
- macros could be more expressive (esp. accept type parameters) - but this needs a nice-looking syntax.

## Std library


- proper float parsing that can handle all the edge cases (curront one will reject numbers with a lot of digits)
- extras, nice to have:
  - date/time???? this is a big can of worms
    - durations/monotonic timer are implemented
  - regexes? probably not, maybe a PCRE wrapper outside stdlib
  - JSON? Some sort of Serde-like generic serialization/deserialization would be nice to have built-in
  - vectored I/O?

## Optimizations

- Get rid of all the redundant variable assignments and copying. I assume C compiler can optimize those well, but the
  generated code looks very bloated.
    - IR inlining and struct expressions made this much better
- Maybe run `elide_zst` on everything, not just when ZSTs are present
  - It works, but simple programs start being like 100,000 lines of generated C code. Not feasible until redundant variables are assigned

## Diagnostics

- More warnings and notes
  - Allocating collections and not freeing them - this would be pretty great to have if I can figure out a way to do it without false positives and in a generic enough fashion
    - OTOH, this is a bit of a slippery slope. Do I need to invent whole ownership system for this? If so, it's not happening, Alumina is not C++ or Rust even though it doesn't try very hard to not look like them.
- Add more specific spans to compile errors. It's pretty good right now, but could be better.
- do not panic on cyclic/recursive protocol bounds (figure out which ones are appropriate), but rather give a meaningful error message

## Compiler architecture

- Is IR low-level enough to eventually use LLVM as backend?
  - IMO it should be mostly OK, modulo a few gaps:
    - ABI awareness. Not sure how much of this LLVM gives you
    - Copying and passing structs by value needs to be explicit
    - Expressions need to be flattened into SSA form
      - This should be easy enough, with two caveats which C handles for us today:
          - order of evaluation needs to be exactly preserved.
          - || and && need to short circuit
    - Type casts need to be explicit
    - Spaghetti gotos need to be converted to LLVM basic blocks
- Clean up `mono`. It's a mess.
  -  It's been slightly cleaned up, and a major rewrite will probably never happen. I'd like to start focusing on the self-hosting compiler instead.
- Should monomorphization and type checking be separate stages? Can this even be done with the loose duck-typed language?
- Will the compiler architecture scale to large programs?
    - So far it's looking good. Stdlib is ~70k lines of code and it compiles with tests in half a second. With serialized AST it's even faster and the bottleneck is mono, which means that even as stlib grows, small programs will still be fast to compile.
- AST expression should have a convenience builder, like the one for IR expressions. `expressions.rs` is overly verbose right now, especially with all the span tagging.
- Most panics should probably use `ice!` macro to report the source span where the compiler panicked
- Cross-compilation
  - Should be easy enough, as generated C code has almost no platform dependencies. This is more of a concern for the standard library to ensure `cfg` attributes are sprinkled around appropriately.
    - const eval needs to adjust usizes etc. to the target platform

## Exploratory

- tagged unions
  - I miss them quite a lot from Rust. They are not hard, but need a good syntax for `match`
- ability to monkey-patch in a nice way without linker tricks
- full Hindley-Milner type inference. Global type inference will pretty much require a full rewrite of `mono`, so whis would be a massive project, but it would also be super awesome to have
  - Type inference gaps are a big pain point right now, especially since there are so many places where adding a type hint is not even possible (e.g. when chaining methods).
- some sort of type-checking of pre-monomorphized functions might be useful. they can have pretty blatant errors inside that would fail to compile no matter what the type parameters are, but you don't know until you actually try to use it.
- attributes in reflection

## Tooling

- a compiler driver (i.e. Cargo)
- integrated codegen (a la `go generate` or procedural macros)
- a REPL. Totally doable with const-eval.

## Bikeshedding

- Name conventions (PascalCase, snake_case, ...)
  - This is settled now. See: Rust.
- Why "Alumina"?
  - Rust begets more Rust until everything is oxidized. Aluminium forms just a thin passivation layer leaving "bare metal" just under the surface (I am really stretching the metaphor here, the real reason is just that it is another metal oxide)
