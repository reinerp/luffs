# luffs

`luffs` is an early experiment in a proof-carrying Rust subset for untrusted
binary parsers. Programs look like Rust, but every array access names an inline
Lean proof. The checker emits Lean and asks Lean's kernel to verify it; the
compiler emits optimized Rust whose proven accesses use `get_unchecked`.

This repository is an initial vertical slice, not yet a replacement for
[Wuffs](https://github.com/google/wuffs). It currently supports integer and
array/slice code that is otherwise valid Rust, `Option<T>` returns, CFG-derived
facts, inline Lean proofs, shared/mutable slices, fixed arrays, and two slice forms:

- `a[begin..+len]` — conventional `(begin, length)`
- `a[begin..<end]` — parser-friendly `(begin, end)`

Mutability is inferred from `&mut [T]`, as in Rust. Ordinary accesses use
`omega` automatically; `by name` selects an explicitly declared proof.

General structs/enums and general return types are intentionally rejected.
SIMD operations will be admitted individually, each with a Lean model, as the
zch decoder needs them.

## Memory verification

The memory-safety layer is being built on
[Iris-Lean](https://github.com/leanprover-community/iris-lean), pinned to the
release matching this repository's Lean toolchain. Luffs does not define a
second separation logic. Its memory propositions are Iris propositions, and
exclusive byte ownership is the resource from which unique mutable references
will be derived.

The intended trust boundary is deliberately narrow: successful `mmap` calls
produce exclusive ownership of a fresh, page-aligned byte region, and `munmap`
consumes that ownership. TLSF is above this boundary. Its free lists, bitmaps,
block splitting, coalescing, allocation, and deallocation must preserve a
machine-checked Iris heap invariant. `Box<T>` and `Vec<T>` will then be proved as
clients of TLSF rather than of an assumed `malloc` specification.

The checked-in foundation currently contains:

- half-open byte regions and proved containment/disjointness lemmas;
- an Iris `OwnsBytes` interface backed by authoritative ghost-map fragments,
  with checked splitting, recombination, heap agreement, and overlap
  exclusivity laws;
- small-step semantics for checked pointer offsets, loads, stores, `mmap`, and
  `munmap`, with proved stuckness criteria for offsets and memory accesses;
- the trusted `mmap`/`munmap` contract, kept separate from TLSF;
- the initial pure TLSF block invariant and checked split/coalesce byte-count
  lemmas, plus an intrinsically bounded two-level size-class reference mapping
  with checked linear/high-bin coverage, and a bitmap reference search with
  checked bounds, set-bit soundness, and minimality.
- a gap-free contiguous pool-partition invariant and a proved TLSF block split
  at arbitrary list positions that preserves the physical partition,
  alignment, nonemptiness, and Iris byte ownership; the first executable
  allocation transition is proved to return an exact-size allocated block.
- executable deallocation checks that reject wrong regions and double frees,
  plus arbitrary-position coalescing proofs preserving the pool partition,
  alignment, and exact Iris ownership.
- predecessor-free boundary tags with checked consistency across allocation,
  deallocation, and coalescing, providing the basis for O(1) backward merging.
- intrusive free-list links with verified front insertion/removal, link
  consistency, unique offsets, and detached removal results.
- a two-level bin invariant tying cached bitmap bits to nonempty intrusive
  chains and proving every selected chain head is free and correctly classified.

It does **not** yet constitute a fully verified generic TLSF-backed `Box` or
`Vec`. The current Lean development instantiates `OwnsBytes` with Iris
authoritative ghost-map resources and proves the allocator's main allocation/
deallocation ownership paths plus allocator-backed byte Box and Vec clients.
The Luffs Vec growth loop has checked addresses and an exact generated
allocation/copy/deallocation model, now composed with abstract `Vec.grow`, its
Iris ownership update, and an operational byte-copy trace. Remaining work
includes generic lowering, weakest-precondition integration, borrowing syntax,
and the allocator's O(1) link-update refinement. See
[`VERIFICATION.md`](VERIFICATION.md) for the precise proof boundary and
completion criteria.

## A complete small program

```rust
fn first(input: &[u8]) -> Option<u8> {
    if input.len() == 0 { return None; }
    Some(input[0])
}
```

The compiler sees that the `if` branch unconditionally returns, so its negated
condition is a fact on the continuation edge. The generated theorem is:

```lean
theorem __auto_0 (input_len : Nat)
    (h_fact_0 : ¬ (input_len = 0)) : 0 < input_len := by omega
```

`.len()` remains ordinary Rust syntax in Luffs and becomes a natural-number
length only in the generated Lean model. Once Lean proves the exact access
obligation, the compiler emits:

```rust
Some(unsafe { *input.get_unchecked(0) })
```

Thus there is one check at the parser boundary and no redundant bounds check at
the access. Proof declarations cannot introduce arbitrary hypotheses: their
hypotheses come from facts on the function's control-flow graph. A longer proof
can be declared as `proof name: proposition by ...;` and attached with `by name`.

## Checked arithmetic and explicit proofs

Typed integer arithmetic creates a separate representability obligation. For
example, after `if len > usize::MAX - begin { return None; }`, the binding
`let end: usize = begin + len;` generates a Lean theorem proving
`begin + len ≤ usize::MAX`. See
[`examples/overflow.luffs`](examples/overflow.luffs).

Named proofs can use multiline Lean tactic code while receiving integer range
facts, bindings, and CFG facts automatically:

```rust
proof lane_bounds: begin <= end && end <= input.len() by {
    omega
}

Some(input[begin..<end] by lane_bounds)
```

See [`examples/explicit_proof.luffs`](examples/explicit_proof.luffs).

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
zch framing: an eight-byte little-endian plaintext length, 32 KiB stored blocks
with two-byte zero prefixes, and a final sub-128-byte raw tail. The example
handles any number of stored blocks, proves every header and payload access,
uses parser-friendly begin/end slices, and emits unchecked accesses only after
the corresponding ordinary Rust early-return checks.

Full zch compatibility still requires coded-block dispatch, canonical Huffman
table validation, four-way bitstream decoding, zero expansion, rANS blocks,
and architecture-specific SIMD.
Those pieces should be added only alongside their Lean models and safety proofs.

## Safety boundary and current limitations

The prototype validates proof names and exact access obligations, and Lean
checks the proof terms. Checked arithmetic currently covers typed `usize`
bindings with one top-level `+`, `-`, or `*`; extending the same model to every
integer type and nested expression is still required. Its parser is
intentionally line-oriented and not yet a complete Rust-subset parser. Before
running generated code on hostile data, the language needs a typed AST, fully
lexical/path-sensitive CFG facts, and end-to-end soundness tests. The checked-in
examples demonstrate the intended design, not a claim that this prototype
compiler is already a production-grade safety verifier.
