# List of known bugs and missing features

## General

- Function inlining in Alumina compiler proper (rather than relying on C compiler)
    - It's not a priority, since C compiler can inline perfectly fine, except in special cases like `alloca` where the allocated buffer cannot leave the stack frame. To have a good wrapper around `alloca`, it needs to be force-inlined except if done in a macro (but macros don't really have a good type parameter system, params can only be expressions).
- stack overflow in codegen stage because infinite size recursive structs are not rejected during monomorphization
    - could be a similar issue with protocols, though these are more coservative vis-a-vis recursion
- Whole ZST and divergence handling might still be buggy, in particular, uninitialized variables of `!` type might be problematic since lowering is quite liberal with making temporary name bindings for various stuff.
    - It might be fine now, it's been a while since I last ran into a ZST bug
- if tentative monomorphization fails (e.g. error), but type inference still succeeds, we are left with unpopulated symbols
    - this is now especially an issue with `when` expressions which do tentative mono during proto bound checking
    - This is a big problem, unfortunately there is no easy solution with the current `mono` architecture
- statics in function scope
- "any/don't care" in protocol bounds. Especially for things like `Hashable` and `Formattable`, it would be great if users didn't need to introduce a new generic parameter for the hasher and formatter (since that complicates type inference).
  - Alternatively, allow pre-monomorphized types to be used as protocol bounds
  - This could be solved by `infer`. It needs to do the same thing as `check_protocol_bounds` - go through all the AST methods of the protocol in the bound and IR method of the type in the slot and
  match the slots on all of them. It's quite a lot of work and also `infer` will probably need to start looping until no more changes are made (e.g. in nested protocol bounds), but it would be quite awesome. By doing that, protocols would actually start *helping* type inference instead of making it harder.
- Some limited pattern matching in macros (optional arguments)
- Local items (functions, structs defined in linear scopes) that bind ambient generic parameters
  - Right now there is not even a good error message to say that this is not supported, just a cryptic "unbound placeholder" during mono
- Lambdas in macros are broken.
- Promoting all variables to function scope is a bit of a unique feature of Alumina and I like it (comes in quite handy for autoref - can take an address of any rvalue and defer), but it may inhibit some optimizations downstream.
- `if opt.is_some { opt.inner }` and  `if res.is_ok() { res.unwrap() }` do not spark joy. Full pattern matching is overkill, but this is very common and
  deserves a better idiom.
- vtables are stored in mutable static variables and initialized in the static constructor like all other statics. clang can optimize this to statis storage and even de-virtualize automatically (which is quite amazing really), but gcc seems to not do this. Maybe extend codegen so that they can be properly const-initialized. Might be useful for other things as well (constant arrays, ...)
- a coherent story for operator overloading
- `dyn` pointers for certain builtin protocols. Specifically `dyn Callable<...>` would be very useful for being type-erased closures.
- `format_args` macro is not bad right now, but the generated code is huge. It would be cool to have something like this so the result on `format_args` can still be collected into an array, but can also be unpacked into a sequence of statements directly writing into the formatter
- unify `void` type and empty tuple in `mono`. They are the same thing. Maybe just hack it in `intern_type`?
- docstrings for fields and enum variants

```
macro write!($fmt, $s, $args...) {
    { format_arg!($s, $args).fmt($fmt); }...
}
```

## Grammar, parsing, AST

- Switch is a bit cumbersome at the moment / improve?
- macros could be more expressive (esp. accept type parameters) - but this needs a nice-looking syntax.

## Std library

- basic structure and philosophy. how big should it be?
  - Philosophy is settled: see Rust standard library.
  - Rely on libc as little as possible. I'd like to use Alumina on bare-metal.
  - Ignore ^ for now. libc is fine. Rust relies heavily on libc. That said, no libc in following areas:
    - no string formatting, anything locale dependent really
    - no buffered I/O (fwrite/...). Native Alumina IO primitives should be much more ergonomic.
    - no random small functions where it can be done efficiently in Alumina (memfrob, htonl, ...)
      - memcpy/memove/strlen are an exception. these are heavily optimized an may actually be compiler builtins
    - I really wanted to say *absolutely nothing with varargs*, but unfortunately `ioctl` and `fcntl` are varargs :(
- Windows and non-glibc support on Linux (specifically musl)
- these are definitely needed:
  - file IO and streams
    - done
  - process/exec
    - done
  - string formatting
    - The pattern is well-established (Formattable protocol) and I'm very happy with it,
      but it's very very basic right now
      - update: it's not so basic anymore, it's actually quite fine
    - more control for float formatting (fixed precision)
  - heap-allocating collections
    - Vector, HashMap, HashSet are implemented (very basic, probably do not perform very well)
    - Vector might actually be pretty ok. Hashed collections are probably bad.

- extras, nice to have:
  - date/time???? this is a big can of worms
    - durations/monotonic timer are implemented
  - regexes? probably not, maybe a PCRE wrapper outside stdlib

## Optimizations

- Get rid of all the redundant variable assignments and copying. I assume C compiler can optimize those well, but the
  generated code looks very bloated.
- Maybe run `elide_zst` on everything, not just when ZSTs are present
  - It works, but simple programs start being like 100,000 lines of generated C code. Not feasible until redundant variables are assigned

## Diagnostics

- More warnings and notes
  - Unused variables
  - Unused imports
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
- Should monomorphization and type checking be separate stages? Can this even be done with the loose duck-typed language?
- Will the compiler architecture scale to large programs? Is it possible to pre-compile the libraries at least to AST?
- AST expression should have a convenience builder, like the one for IR expressions. `expressions.rs` is overly verbose right now, especially with all the span tagging.
- Most panics should probably use `ice!` macro to report the source span where the compiler panicked
- Cross-compilation
  - Should be easy enough, as generated C code has almost no platform dependencies. This is more of a concern for the standard library to ensure `cfg` attributes are sprinkled around appropriately.
- Logging, timings

## Exploratory

- specialization/SFINAE/function overloading?
  - I am leaning pretty strongly towards not having either of these. With protocols the language
    is expressive enough to do string formatting, iterators and collections, which are a good litmus test if generics are any good.
- tagged unions
  - I miss them quite a lot from Rust. They are not hard, but need a good syntax for `match`
- full Hindley-Milner type inference. Global type inference will pretty much require a full rewrite of `mono`, so whis would be a massive project, but it would also be super awesome to have
  - Type inference gaps are a big pain point right now, especially since there are so many places where adding a type hint is not even possible (e.g. when chaining methods).
- true variadic functions (certainly they'd be generic and variadic only pre-monomorphization, varargs is an abomination). This is hard to do, both from the syntax and `mono` perspective but the payoff is that tuples can have nice protocol implementations.
  - something like `extern "rust-call"` could come to the rescue here. It is already kinda possible to have recursive varargs by `tuple_head_of` and `tuple_tail_of`.
  - Probably not needed.
- some sort of type-checking of pre-monomorphized functions might be useful. they can have pretty blatant errors inside that would fail to compile no matter what the type parameters are, but you don't know until you actually try to use it.
- generators? coroutines? lmao, not gonna happen

## Tooling

- a compiler driver (i.e. Cargo)

## Bikeshedding

- Name conventions (PascalCase, snake_case, ...)
  - This is settled now. See: Rust.
- Why "Alumina"?
  - Because it's another metal oxide, like Rust
    - Rust begets more Rust until everything is oxidized. Aluminium forms just a thin passivation layer leaving "bare metal" just under the surface.
