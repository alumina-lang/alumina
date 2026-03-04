# Aluminac Future Work

## Compiler Bugs

### `equals` method on `impl Option {}` causes miscompilation
When an `equals` function is added to `impl Option {}` (non-generic impl), the compiler's
operator overloading (`try_operator_overload`) picks it up for `==` comparisons on all
Option types. This causes S2 to crash with infinite recursion in the parser. The issue is
that the generic `<T>` on the method doesn't match how the compiler resolves type args
for operator overloading on non-generic impl blocks.

**Workaround**: Don't add `equals`/`not_equals`/`compare` to `impl Option {}` or
`impl Result {}` until this is fixed.

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

### Static method calls on generic type parameters
`H::new()` where `H: Hasher<H>` fails with "expression is not callable". Calling static
methods (associated functions) through generic type parameters is not supported. Instance
method calls on generic types (`h.write(...)`) work fine.

**Workaround**: Use concrete types directly instead of going through generics for static calls.

### Protocol mixin annotations
The `/// @ cmp::Equatable::equals` doc comment annotation for registering protocol
implementations needs proper support.
