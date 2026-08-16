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
  inequality is now proved for logarithmic bins, including second-level skips,
  first-level skips, and the `sl = 31` carry. The mapping-up request key is
  distinct from mapping-down block classification and is proved no smaller
  than the request. For both the linear and logarithmic ranges, successful
  bitmap search is proved end-to-end to identify an authoritative physical,
  aligned, free block whose size is at least the request. The executable lookup
  wrapper now combines same-level and later-first-level branches, bounds-checks
  raw bitmap indices before converting them to `Fin`, and has one unified
  success-suitability theorem. Bitmap search is also proved complete: it
  succeeds whenever an eligible bit exists, and returns `none` exactly when no
  eligible same-level or later-first-level bin exists. A checked class-valued
  facade now converts successful raw indices to `Fin` fields; success proves
  that exact class has a nonempty chain and inherits the unified physical-block
  suitability result.
- [ ] Implement intrusive free-list insertion/removal and prove link
  consistency and ownership preservation.
  Blocks now carry intrusive previous/next offsets. Front insertion and removal
  are executable and proved to preserve bidirectional link consistency and
  offset uniqueness; removed blocks are proved detached. A joint bin invariant
  now requires every member to be free and classified into its containing bin.
  A whole-pool agreement invariant now additionally relates every bin-chain
  entry to a header in the authoritative physical-block sequence and gives
  every free physical header a bin representative. The relation deliberately
  equates offset, size, and allocation state while the physical sequence owns
  boundary tags and the chain projection owns intrusive links. Bitmap-selected heads are proved to represent
  physical blocks, with free state, size classification, alignment, and region
  transferred across that relation; classification functionality rules out
  two distinct classes. State-changing bin operations must still be proved to
  preserve this agreement. Bitmap caches can now be rebuilt from
  chains with a proof that both levels exactly reflect chain nonemptiness;
  front insertion of a fresh, correctly classified block preserves intrusive
  links, classification, and both rebuilt bitmap invariants. Front removal is
  likewise proved to preserve those invariants, returns a detached block, and
  rebuilds both bitmap levels (including empty-bin clearing). The simultaneous
  physical-metadata update remains. Lookup and removal are now composed as an
  executable `takeCandidate` transition: success preserves bin validity and
  returns a detached head, while failure occurs exactly when no eligible bin
  exists. Suitability is proved class-wide, so the exact detached head is now
  proved aligned and large enough, and remains related to an authoritative
  physical header. Executable physical-header lookup by shared metadata is
  proved sound and complete. Applying the exact-fit/split mutation and
  reinserting a remainder remain.
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
  is now composed with checked physical-header lookup, exact/near-fit whole
  allocation, and split allocation. Both branches preserve full physical
  well-formedness (ordering, exact coverage, boundary tags, positivity,
  alignment, and bounds). Split remainders are proved fresh, positive, aligned,
  addressable, classifiable, and reinserted; the executable public allocation
  path is proved complete once an eligible bin exists and safe through bin
  validity. Both directions of the physical/bin representation relation are
  now restored after whole-block allocation and splitting, yielding the main
  theorem that successful aligned allocation preserves the complete pure
  allocator invariant. The allocator's Iris assertion owns exactly its free
  physical regions. Successful allocation is now proved to split or transfer
  exactly the selected region to the client while retaining all other free
  capabilities; this ownership law is composed through bin removal, physical
  mutation, remainder reinsertion, and the public allocation operation.
- [ ] Prove `dealloc`: consuming exactly a live allocation restores it to the
  allocator without leaks, overlap, or double-free.
  The executable deallocation transition now requires the exact returned
  region, rejects already-free blocks, preserves the physical partition, and
  has proved arbitrary-position coalescing with exact Iris ownership
  recombination. The Iris return law now proves that marking the exact live
  block free consumes the client's region capability and restores it to the
  allocator assertion, including arbitrary physical-list positions. An
  executable uncoalesced stage now validates the return, marks the physical
  header, classifies and inserts it, preserves physical well-formedness, and
  is composed with that ownership law. Both directions of physical/bin
  agreement, size-class membership, bitmap consistency, and intrusive-link
  consistency are now proved for that stage, yielding preservation of the
  complete allocator invariant. Neighbor removal/reinsertion around
  coalescing remains. A checked arbitrary-offset free-list removal primitive
  now exists: it detaches the selected header, rebuilds canonical intrusive
  links and bitmap caches, and is proved to preserve chain validity and
  size-class membership. Removal is also proved to preserve forward physical
  representation and every non-removed block's backward representation. An
  executable adjacent-pair coalescer now removes both bin entries, merges and
  reclassifies the physical header, and reinserts it; its Iris ownership and
  physical well-formedness laws are checked. Its complete physical/bin
  invariant preservation is now proved in both directions. The public
  deallocation path restores the returned block, conditionally merges right
  and then left, preserves the full allocator invariant, and has an end-to-end
  Iris law consuming exactly the returned capability. The public path is now
  also proved complete: for a valid pool smaller than the supported TLSF size
  range, returning the exact live region cannot fail at classification,
  arbitrary unlink, or either conditional coalescing step. The O(1)
  predecessor/successor link-update refinement and Luffs lowering remain.
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
