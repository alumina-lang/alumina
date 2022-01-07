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
- if tentative monomorphization fails (e.g. error), but type inference still succeeds, we are left with unpopulated symbols (maybe fixed, not sure)
- generic-binding typedefs (e.g. `type HashSet<T> = HashMap<T, ()>`). 
  - This has been attempted and reverted because it was a big mess.
  - It sounds really simple to implement, but the naive approach leads to a bunch of issues (dependencies during AST construction, `impl` forwarding, whether IR should even be aware of them and if not, should they be handled in `mono`, name resolution needs another 'defered' type, ...). That's because they are in a way partial specializations of generic types.
  - typedefs that don't bind generic parameters are already possible with `use X as Y`.
  - It could be easier now with `rebind` in AST 
  - Attempt #2 revealed a more fundamental issue - since `impl` blocks are only loosely bound to their types, typedefs cannot effectively bind generic parameters for methods. E.g. `type HashMap<K, V> = HashMapImpl<K, V, SpecificHasher>` will still require `HashMap::new::<i32, i32, SpecificHasher>`. Not sure how to make this work, but here are a few ideas:
    - get rid of impl-forwarding typedefs and only allow newtypes. Mixins could be extended to allow copying impls from general types (and not just protocols)
    - forward impls, but allow typedefs to have their own impl blocks, which would shadow the ones from the underlyhing types (for the hashmap example, only constructors would need to be overriden, since the hasher can be inferred from the self parameter)
    - leave things as-is and introduce additional constructors that allow overriding the "optional" generic parameters.
    - do not have typedefs, use default generic parameters
- statics in function scope
- unqualified types gaps:
  - unqualified string in if/else does not coerce to a slice
  - probably other places too, since it's very ad-hoc
- lambdas need to be better
  - type inference does not cross the lambda boundary, requiring a lot of type annotations, which 
    kind of defeats the purpose of lambdas.
- "any/don't care" in protocol bounds. Especially for things like `Hashable` and `Formattable`, it would be great if users didn't need to introduce a new generic parameter for the hasher and formatter (since that complicates type inference). 
  - Alternatively, allow pre-monomorphized types to be used as protocol bounds
  - This could be solved by `infer`. It needs to do the same thing as `check_protocol_bounds` - go through all the AST methods of the protocol in the bound and IR method of the type in the slot and
  match the slots on all of them. It's quite a lot of work and also `infer` will probably need to start looping until no more changes are made (e.g. in nested protocol bounds), but it would be quite awesome. By doing that, protocols would actually start *helping* type inference instead of making it harder.
- How does Equatable and Comparable work for pointers? Autoref makes this quite complicated... Maybe it's better to simply not have that.
- Some limited pattern matching in macros (optional arguments)
- Tuple unpacking in for expressions
- Ability to define types in function scope (especially for ENums, very useful for state machines). Simple in theory, but the same caveats apply as with lambdas: these can bind generic placeholders, so they need to be monomorphized carefully.

## Grammar, parsing, AST

- Switch is a bit cumbersome at the moment / improve?
- hex integer literals
- macros could be more expressive (esp. accept type parameters) - but this needs a nice-looking syntax.


## Std library

- basic structure and philosophy. how big should it be?
  - Rely on libc as little as possible. I'd like to use Alumina on bare-metal.
- tests
- how portable should it be? I'm not sure if I'll have the grit to support anything other than `x86_64-unknown-linux-gnu` and maybe `aarch64`.
- these are definitely needed:
  - file IO and streams
    - done
  - string formatting
    - The pattern is well-established (Formattable protocol) and I'm very happy with it,
      but it's very very basic right now
  - heap-allocating collections
    - Vector, HashMap, HashSet are implemented (very basic, probably do not perform very well)
    - Maybe a heap? A VecDeque/ring buffer
    - No linked lists.
  - math
- extras, nice to have:
  - threading, atomics, ...
    - This will definitely defer to pthread (what about Windows?)
    - Need a good story for thread-local storage
  - network and unix sockets
  - random number generation
    - basic RNG is implemented, need a good way to make it generic over various integer lengths
  - date/time???? this is a big can of worms

## Optimizations

- Get rid of all the redundant variable assignments and copying. I assume C compiler can optimize those well, but the
  generated code looks very bloated.

## Diagnostics

- More warnings and notes
  - Unused variables
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
    is expressive enough to do string formatting and collections, which are a good litmus test if generics are any good.
- full Hindley-Milner type inference. Global type inference will pretty much require a full rewrite of `mono`, so whis would be a massive project, but it would also be super awesome to have
- true variadic functions (certainly they'd be generic and variadic only pre-monomorphization, varargs is an abomination). This is hard to do, both from the syntax and `mono` perspective but the payoff is that tuples can have nice protocol implementations.
- generators? coroutines? lmao, not gonna happen

## Tooling

- rustdoc-like thing. This will have to wait until a self-hosted compiler
- test framework

## Bikeshedding

- Name conventions (PascalCase, snake_case, ...)
