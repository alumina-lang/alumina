# Aluminac Future Work

## Compiler Bugs

### Protocol method resolution fails in non-generic impl blocks during bootstrap
Methods in `impl Option { ... }` (non-generic impl) that call protocol methods on
constrained generic parameters fail during bootstrap compilation. For example:
```
impl Option {
    fn equals<T: Equatable<T>>(lhs: &Option<T>, rhs: &Option<T>) -> bool {
        lhs._inner.equals(&rhs._inner)  // fails: "could not resolve method 'equals'"
    }
}
```
The error occurs at stage 2 compilation. The `.equals()` call on `T: Equatable<T>` works
in user code tests but fails when compiling the compiler itself via `make bootstrap`.
Root cause: protocol constraints on method-level generics in non-generic impl blocks
don't provide method resolution context during monomorphization for all instantiation
sites.

**Workaround**: Don't add protocol-constrained methods (equals, compare, hash, fmt with
inner formatting) to `impl Option {}` or `impl Result {}` until this is fixed.

### Type alias static method calls fail for non-generic aliases
Calling static methods through non-generic type aliases fails:
`std::fmt::Result::ok(())` where `type Result = std::result::Result<(), Error>`.
**Workaround**: Use `let r: std::fmt::Result = std::result::Result::ok(()); r`

### Nested generic type inference in non-generic impl blocks
`Option::transpose()` with signature `fn transpose<T, E>(self: Option<Result<T, E>>)`
incorrectly binds T to `Result<i32, i32>` instead of `i32` when called on
`Option<Result<i32, i32>>`. The type inference doesn't decompose nested generic types.
**Workaround**: Avoid methods that pattern-match nested generic types in self position.

### Nested `Option<Option<T>>` causes LLVM IR verification failure
`Option::some(Option::some(42i32))` generates invalid IR where an `i32` is stored into
an `Option<Option<i32>>*`. Type inference for `Option::some()` incorrectly infers `T=i32`
instead of `T=Option<i32>` when the argument is itself an `Option<i32>`.

### UFCS doesn't work for free functions on built-in/slice types
Free functions defined with `self: &[u8]` as the first parameter cannot be called using
UFCS (universal function call syntax) as methods on `&[u8]` slices. E.g. defining
`fn starts_with(self: &[u8], prefix: &[u8]) -> bool` and calling `"hello".starts_with("hel")`
fails with "could not resolve method 'starts_with'". This also affects calls within the
same module (e.g. `trim_prefix` calling `self.starts_with(prefix)`).

**Workaround**: Use regular parameter names and call as `std::string::starts_with(s, prefix)`.

## Features to Port

### Method calls on bounded generic types
`lhs._inner.equals(&rhs._inner)` where `T: Equatable<T>` — the compiler can't resolve
methods through protocol bounds on generic type parameters. Need to implement protocol
constraint satisfaction during method resolution.

### Protocol mixin annotations
The `/// @ cmp::Equatable::equals` doc comment annotation for registering protocol
implementations needs proper support.
