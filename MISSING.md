# List of known bugs and missing features

## General

- Whole const_eval thing. It's very ad-hoc and messy. Full const-eval is not a priority, but it needs to be good enough
  so `consts` and enum members can have values that people usually put there + in as much as compiler intrinsics need them.
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - It's not a priority, since C compiler can inline perfectly fine, except in special cases like `alloca` where the allocated buffer cannot leave the stack frame. To have a good wrapper around `alloca`, it needs to be force-inlined except if done in a macro (but macros don't really have a good type parameter system, params can only be expressions).
- stack overflow in codegen stage because infinite size recursive structs are not rejected during monomorphization
    - could be a similar issue with protocols, though these are more coservative vis-a-vis recursion
- Whole ZST and divergence handling might still be buggy, in particular, uninitialized variables of `!` type might be problematic since lowering is quite liberal with making temporary name bindings for various stuff.
    - It might be fine now, it's been a while since I last ran into a ZST bug
- if tentative monomorphization fails (e.g. error), but type inference still succeeds, we are left with unpopulated symbols
    - this is now especially an issue with `when` expressions which do tentative mono during proto bound checking
- statics in function scope
- unqualified types gaps:
  - unqualified string in if/else does not coerce to a slice
  - probably other places too, since it's very ad-hoc
- "any/don't care" in protocol bounds. Especially for things like `Hashable` and `Formattable`, it would be great if users didn't need to introduce a new generic parameter for the hasher and formatter (since that complicates type inference).
  - Alternatively, allow pre-monomorphized types to be used as protocol bounds
  - This could be solved by `infer`. It needs to do the same thing as `check_protocol_bounds` - go through all the AST methods of the protocol in the bound and IR method of the type in the slot and
  match the slots on all of them. It's quite a lot of work and also `infer` will probably need to start looping until no more changes are made (e.g. in nested protocol bounds), but it would be quite awesome. By doing that, protocols would actually start *helping* type inference instead of making it harder.
- How does Equatable and Comparable work for pointers? Autoref makes this quite complicated... Maybe it's better to simply not have that.
- Some limited pattern matching in macros (optional arguments)
- Ability to define types in function scope (especially for ENums, very useful for state machines). Simple in theory, but the same caveats apply as with lambdas: these can bind generic placeholders, so they need to be monomorphized carefully.
- Lambdas in macros are broken.

## Grammar, parsing, AST

- Switch is a bit cumbersome at the moment / improve?
- hex integer literals
- macros could be more expressive (esp. accept type parameters) - but this needs a nice-looking syntax.


## Std library

- basic structure and philosophy. how big should it be?
  - Rely on libc as little as possible. I'd like to use Alumina on bare-metal.
  - Ignore ^ for now. libc is fine. Rust relies heavily on libc. That said, no libc in following areas:
    - no string formatting, anything locale dependent really
    - no buffered I/O (fwrite/...). Native Alumina IO primitives should be much more ergonomic.
    - no random small functions where it can be done efficiently in Alumina (memfrob, htonl, ...)
      - memcpy/memove/strlen are an exception. these are heavily optimized an may actually be compiler builtins
    - I really wanted to say *absolutely nothing with varargs*, but unfortunately `ioctl` and `fcntl` are varargs :(
- tests
- how portable should it be? currently it seems to be working quite well on ARM and x86_64 on Linux, Android and Mac. Windows is not supported yet.
- these are definitely needed:
  - file IO and streams
    - done
  - process/exec
    - done
  - string formatting
    - The pattern is well-established (Formattable protocol) and I'm very happy with it,
      but it's very very basic right now
      - update: it's not so basic anymore, it's actually quite fine
    - formatting for floats is especially terrible, needs to be much better
  - heap-allocating collections
    - Vector, HashMap, HashSet are implemented (very basic, probably do not perform very well)
    - Vector might actually be pretty ok. Hashed collections are probably bad.

- extras, nice to have:
  - network/sockets
    - done
  - date/time???? this is a big can of worms
    - durations/monotonic timer are implemented
  - regexes? probably not, maybe a PCRE wrapper outside stdlib

## Optimizations

- Get rid of all the redundant variable assignments and copying. I assume C compiler can optimize those well, but the
  generated code looks very bloated.
- Maybe run `elide_zst` on everything, not just when ZSTs are present

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
    - Expressions need to be flattened into SSA form (should be easy enough)
    - Type casts need to be explicit
    - Spaghetti gotos need to be converted to LLVM basic blocks
- Clean up `mono`. It's a mess.
- Should monomorphization and type checking be separate stages? Can this even be done with the loose duck-typed language?
- Will the compiler architecture scale to large programs? Is it possible to pre-compile the libraries at least to AST?
- AST expression should have a convenience builder, like the one for IR expressions. `expressions.rs` is overly verbose right now, especially with all the span tagging.
- Most panics should probably use `ice!` macro to report the source span where the compiler panicked
- Refactor/consolidate the contexts that are passed around
- Cross-compilation
  - Should be easy enough, as generated C code has almost no platform dependencies. This is more of a concern for the standard library to ensure `cfg` attributes are sprinkled around appropriately.
- Logging, timings

## Exploratory

- specialization/SFINAE/overloading?
  - I am leaning pretty strongly towards not having either of these. With protocols the language
    is expressive enough to do string formatting, iterators and collections, which are a good litmus test if generics are any good.
- tagged unions
  - I miss them quite a lot from Rust. They are not hard, but need a good syntax for `match`
- full Hindley-Milner type inference. Global type inference will pretty much require a full rewrite of `mono`, so whis would be a massive project, but it would also be super awesome to have
- true variadic functions (certainly they'd be generic and variadic only pre-monomorphization, varargs is an abomination). This is hard to do, both from the syntax and `mono` perspective but the payoff is that tuples can have nice protocol implementations.
  - something like `extern "rust-call"` could come to the rescue here. It is already kinda possible to have recursive varargs by `tuple_head_of` and `tuple_tail_of`.
- generators? coroutines? lmao, not gonna happen

## Tooling

- a compiler driver (i.e. Cargo)

## Bikeshedding

- Name conventions (PascalCase, snake_case, ...)
  - This is settled now. See: Rust.
