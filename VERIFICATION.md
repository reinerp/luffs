# Memory verification plan

This file is a checklist of claims, not a list of trusted intentions. A box is
checked only when Lean checks the implementation theorem and the corresponding
Luffs source compiles to Rust.

## Trusted base

The final trusted computing base is intended to contain only:

1. Lean's kernel and the Iris-Lean model;
2. Luffs-to-Lean and Luffs-to-Rust translation correctness (initially tested,
   ultimately proved);
3. the platform refinement of the `mmap`/`munmap` specification;
4. Rust/LLVM and the operating system at execution time.

In particular, TLSF is not an axiom and `malloc` is not a primitive.

## Semantic layers

- [x] Pin and compile Iris-Lean.
- [x] Define pure half-open memory regions.
- [x] State exclusive byte ownership and the `mmap` boundary as Iris
  propositions.
- [x] Instantiate byte ownership with an Iris authoritative finite-map
  resource; prove splitting, recombination, agreement, and exclusivity.
- [x] Define Luffs small-step semantics for raw loads/stores, pointer
  arithmetic, `mmap`, and `munmap`.
- [ ] Prove weakest-precondition rules and adequacy: a closed proved Luffs
  program cannot get stuck on memory access.
- [ ] Derive shared borrows from fractional ownership and mutable borrows from
  exclusive ownership, including reborrowing and lifetime restoration.

## TLSF

- [x] Define the first pure block layout predicates and prove that splitting
  and coalescing preserve byte counts.
- [ ] Implement size-class mapping and prove every `(fl, sl)` index in range.
  The Lean reference mapping returns `Fin 64 × Fin 32`; its high-range quotient
  is proved not to wrap and its selected interval is proved to contain the
  request. The corrected 32-bin linear branch is also proved to contain every
  request through 256 bytes. The Luffs implementation remains.
- [ ] Implement bitmap search and prove it returns a nonempty suitable bin.
  The reference search is proved in-bounds, set-bit sound, and minimal from its
  starting index. Cached first/second-level bits are now proved equivalent to
  nonempty intrusive chains, and a successful second-level search is proved to
  return a free head classified into that bin. The cross-bin size-suitability
  inequality remains.
- [ ] Implement intrusive free-list insertion/removal and prove link
  consistency and ownership preservation.
  Blocks now carry intrusive previous/next offsets. Front insertion and removal
  are executable and proved to preserve bidirectional link consistency and
  offset uniqueness; removed blocks are proved detached. A joint bin invariant
  now requires every member to be free and classified into its containing bin.
  Connecting bin-chain block copies to the authoritative physical-block table
  remains.
- [ ] Prove physical blocks form a disjoint partition of every mapped pool.
  `partitions` now requires adjacency from offset zero plus exact byte coverage,
  closing the gap permitted by the earlier ordered/sum-only invariant.
- [ ] Prove split and coalesce preserve alignment, boundary tags, bin
  membership, and the pool partition.
  Head-block splitting now preserves the contiguous pool partition and
  transfers the original Iris byte ownership exactly to the two output blocks.
  Arbitrary-position splitting now preserves the partition; aligned requests
  produce two aligned, nonempty blocks. The executable block model now carries
  a predecessor-free boundary tag, and allocation, deallocation, and
  coalescing are proved to preserve tag consistency. Bin membership remains.
- [ ] Prove `alloc`: failure preserves the heap; success returns a fresh,
  aligned owned region of at least the requested size.
  The executable split-success transition now rejects non-free, undersized, or
  unaligned requests and is proved to return an exact-size aligned allocated
  block while preserving the physical pool partition. Bin/free-list selection
  and the whole-pool Iris invariant remain.
- [ ] Prove `dealloc`: consuming exactly a live allocation restores it to the
  allocator without leaks, overlap, or double-free.
  The executable deallocation transition now requires the exact returned
  region, rejects already-free blocks, preserves the physical partition, and
  has proved arbitrary-position coalescing with exact Iris ownership
  recombination. Neighbor selection and bin reinsertion remain.
- [ ] Prove the bounded-step property of bin lookup and local list updates.

The first target is sequential TLSF with fixed-size pools obtained from `mmap`.
Growing pools, `realloc`, aligned allocation beyond the base alignment, and
concurrency are later extensions and are not prerequisites for `Box` and
`Vec`.

## Containers

- [ ] `Box<T>`: allocation/layout, initialization before exposure, unique
  ownership, dereference rules, and exactly-once drop/deallocation.
- [ ] `Vec<T>`: invariant `len <= capacity`, initialized prefix ownership,
  spare-capacity ownership, checked layout arithmetic, growth without loss or
  double-drop, `push`, `pop`, indexing, shared/mutable slices, and drop.
- [ ] End-to-end examples compile to Rust with no redundant bounds checks and
  are accepted by Lean from a clean checkout.
