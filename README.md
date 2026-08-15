# luffs

`luffs` is an early experiment in a proof-carrying Rust subset for untrusted
binary parsers. Programs look like Rust, but every array access names an inline
Lean proof. The checker emits Lean and asks Lean's kernel to verify it; the
compiler emits optimized Rust whose proven accesses use `get_unchecked`.

This repository is an initial vertical slice, not yet a replacement for
[Wuffs](https://github.com/google/wuffs). It currently supports integer and
array/slice code that is otherwise valid Rust, `Option<T>` returns, guards,
inline Lean proofs, shared/mutable slices, fixed arrays, and two slice forms:

- `a[begin..+len] by p` — conventional `(begin, length)`
- `a[begin..<end] by p` — parser-friendly `(begin, end)`
- `a![begin..<end] by p` — the mutable form (`!` marks mutable access)

General structs/enums and general return types are intentionally rejected.
SIMD operations will be admitted individually, each with a Lean model, as the
zch decoder needs them.

## A complete small program

```rust
fn first(input: &[u8]) -> Option<u8> {
    guard input_len > 0 else None;
    proof first_in_bounds (input_len : Nat) : 0 < input_len := by omega;
    Some(input[0] by first_in_bounds)
}
```

The guard compiles to a runtime early return and becomes a hypothesis in Lean.
The generated theorem is essentially:

```lean
theorem first_in_bounds (input_len : Nat)
    (h_guard_0 : input_len > 0) : 0 < input_len := by omega
```

The compiler checks that the theorem's conclusion exactly matches the access
obligation `0 < input_len`. Only then does it emit:

```rust
Some(unsafe { *input.get_unchecked(0) })
```

Thus there is one check at the parser boundary and no redundant bounds check at
the access. Proof declarations cannot introduce arbitrary hypotheses: their
hypotheses come from preceding `guard` statements, which compile to actual
runtime checks.

## Use

```sh
cargo run -- emit examples/minimal.luffs
cargo run -- check examples/minimal.luffs
cargo run -- build examples/minimal.luffs -o build/minimal
```

`check` and `build` require Lean 4 through `elan`; `lean-toolchain` pins the
version. `emit` only needs Rust.

## zch reference

[`examples/zch_stored.luffs`](examples/zch_stored.luffs) follows the current
zch framing: an eight-byte little-endian plaintext length, a two-byte block
prefix, and prefix zero for a stored block. The example proves every header and
payload access, uses both slice conventions, and emits unchecked accesses after
the two aggregate length guards.

It currently decodes one stored 128-byte-multiple block. Full zch compatibility
still requires raw tails, multiple blocks, canonical Huffman table validation,
four-way bitstream decoding, zero expansion, and architecture-specific SIMD.
Those pieces should be added only alongside their Lean models and safety proofs.

## Safety boundary and current limitations

The prototype validates proof names and exact access obligations, and Lean
checks the proof terms. Its parser is intentionally line-oriented and not yet a
complete Rust-subset parser. Before running generated code on hostile data, the
language needs a typed AST, lexical scopes/path-sensitive guards, integer
overflow semantics in the Lean model, and end-to-end soundness tests. The
checked-in example demonstrates the intended design, not a claim that this
prototype compiler is already a production-grade safety verifier.

