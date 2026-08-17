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

The first concrete `stdlib/tlsf.luffs` runtime layer now implements bounded
bitmap search plus intrusive insert/remove over fixed parallel metadata arrays,
without expanding the initial language with aggregate types. Every metadata
index is lowered to an unchecked Rust access only after a generated Lean
obligation succeeds, and potentially overflowing bitmap-index arithmetic uses
Rust `checked_mul`/`checked_add`. This is not yet claimed to refine the abstract
TLSF transition: the compiler still needs a function-semantics translation and
a refinement hook connecting these emitted operations to the existing Lean
allocator proofs.

`Luffs.Runtime.TLSF` now defines the first exact parallel-array metadata state
and the pure effect of Luffs front insertion. Successful insertion is proved to
preserve all three array lengths and to establish the new bin head, forward
link, detached-sentinel predecessor, and (when present) old-head back-link.
`RepresentsBin` states the abstraction relation from these arrays to a logical
intrusive chain. A generic linked-chain frame lemma proves that equal lengths
and pointwise-equal metadata on a chain preserve its representation. Combined
with freshness and `Nodup`, this yields the full insertion theorem:
`RepresentsBin state bin chain` becomes
`RepresentsBin nextState bin (block :: chain)`. Compiler-generated multi-array
semantics now translate the three mutable arrays and ordered writes in
`tlsf_insert` into an executable Lean state transformer. Its `refines`
declaration is checked extensionally against `insertArrays`, connecting the
Luffs body directly to the represented-chain insertion theorem; source drift
fails `luffs check`.
The exact parallel-array removal transition is now defined in the same layer,
including head replacement, predecessor/successor bypass writes, and final
detachment. Successful removal proves all input indices were valid, preserves
all metadata-array lengths, and leaves the removed node's links at the two
array-length sentinels. Head removal is now proved complete under
`RepresentsBin`: every represented `block :: rest` produces a next state that
represents exactly `rest`, preserves its entire linked tail, and detaches
`block`. Removal of the node immediately after the head is also proved
complete: the head table is unchanged, the head bypasses the removed node, the
successor's back-link is repaired when present, and the removed node is
detached. The exact post-state equations are now framed through the entire
tail, proving `RepresentsBin nextState bin (head :: rest)` including link
consistency and `Nodup`. Generalizing the same local frame under an arbitrary
prefix remains.
Compiler-generated multi-array semantics now cover `tlsf_remove` as well. Lean
checks its ordered conditional bypass and detachment writes extensionally
against `removeArrays`; this preserves sequential alias behavior even for
malformed metadata, while the `RepresentsBin` theorems supply well-formedness
for allocator calls.
The current linear size/free-array fallback also has executable list semantics.
Success is proved to return an in-bounds entry whose flag is nonzero and whose
size satisfies the request; conversely, any such entry proves lookup cannot
fail. The compiler now recognizes the corresponding Luffs loop, generates its
typed recursive Lean semantics, and checks equality to `findFit`; changes to
the loop's guards, access order, suitability test, or increment invalidate this
refinement. Eventual replacement by the two-level O(1) bitmap path remains.
The four-word bitmap path now has a flat little-endian bit semantics as well.
Its reference search is proved sound, complete, and minimal from `start_bin`;
for at most four words every success is below 256. Refinement of the Luffs
masked-first-word/`trailing_zeros` loop to this definition is the next step.

The first target is sequential TLSF with fixed-size pools obtained from `mmap`.
Growing pools, `realloc`, aligned allocation beyond the base alignment, and
concurrency are later extensions and are not prerequisites for `Box` and
`Vec`.

## Containers

- [ ] `Box<T>`: allocation/layout, initialization before exposure, unique
  ownership, dereference rules, and exactly-once drop/deallocation.
  A verified generic codec interface now fixes size, alignment, encoding,
  decoding, encoded length, and decode/encode round trips. Iris-Lean has a
  separate authoritative byte-content map with exact initialized-byte
  fragments, append and lookup laws, and frame-preserving initialization and
  deinitialization updates. The first Box core rounds payload sizes to TLSF
  alignment, proves allocation safety/completeness and payload fit, finds its
  live block for drop, and proves drop completeness. `Box::Owns` combines the
  exclusive allocation with exact encoded contents; duplicate ownership is
  impossible, initialization creates it, and drop consumes both initialized
  contents and the allocation while restoring TLSF ownership. Concrete integer
  codecs now cover 8/16/32/64/128-bit unsigned and two's-complement signed
  values plus 64-bit `usize`/`isize`, with bit-blasted round-trip proofs.
  Box byte dereference produces exact operational load steps. Whole-value Box
  reads now retain the Iris ownership resources, execute a load step for every
  encoded byte, and return the codec's proved decoded value. Whole-value stores
  now prove every destination is mapped from the old encoded ownership,
  execute an explicit store step for every new byte, update the authoritative
  content map and all fragments, and preserve exclusive Box ownership of the
  new logical value. Target-width parameterization and Luffs lowering remain
  before this item is complete.
- [ ] `Vec<T>`: invariant `len <= capacity`, initialized prefix ownership,
  spare-capacity ownership, checked layout arithmetic, growth without loss or
  double-drop, `push`, `pop`, indexing, shared/mutable slices, and drop.
  A first generic Vec core proves `len <= capacity` and
  `capacity * size <= allocation bytes`, plus preservation by in-capacity push
  and pop. Its Iris assertion exclusively owns the full allocation and exact
  initialized prefix. Element/byte offsets are proved within the encoded
  prefix and allocation, and indexing produces exact operational load steps.
  Push appends initialized fragments through a frame-preserving content update;
  pop deletes exactly the last encoding, retains the prefix, and proves the
  new logical length. Capacity allocation now checks the complete
  `capacity * size` request path, transfers the exact TLSF region into an empty
  Vec assertion, and preserves the allocator invariant. Final drop deletes the
  complete initialized prefix, returns that exact region to TLSF, and restores
  allocator ownership; its pure transition is proved safe and complete. A
  replacement-buffer growth transition now allocates before freeing, preserves
  the complete allocator invariant, proves the larger layout fits, and has an
  Iris ownership law that initializes exactly one copy of the logical prefix,
  deletes the old copy, and returns the old region without loss or
  double-ownership. Growth is also proved complete when TLSF reports an
  eligible replacement bin: allocation preserves the old live block, so its
  subsequent deallocation cannot fail. The memory semantics now represents a
  copy as an explicit load/store trace for every byte, proves such a trace
  exists from exact source bytes, mapped destination bytes, and non-overlap,
  and derives the old/new non-overlap from the allocator partition invariant.
  Connecting the entire trace to the Iris authoritative maps in one framed
  weakest-precondition rule remains for growth. Reading a Vec's initialized
  prefix is now a framed Iris rule producing the complete operational load
  trace and the codec round-trip for every logical element. Element-focused
  reads now split out exactly one encoding, execute its load trace, decode it,
  and reassemble the unchanged owner. Begin/end slice handles have checked
  element and byte ranges; shared slice reads similarly isolate the selected
  initialized sublist, produce its exact operational trace, and reassemble all
  prefix/suffix ownership. Mutable begin/end slicing now transfers the exact
  middle allocation and initialized fragments away from the parent, retains
  opaque prefix/tail resources, and proves duplicate nonempty mutable-slice
  ownership contradictory. An equal-length replacement executes an explicit
  store trace and updates the Iris content map; recombination reconstructs the
  Vec with the new logical middle and unchanged prefix/suffix. Scoped lifetime
  notation in Luffs and lowering remain.

`stdlib/containers.luffs` now contains the first byte-monomorphized Box and Vec
lowering: initialization/load/store, push/pop length transitions, indexed get,
shared/mutable begin/end slices, and growth copying. Generated Rust uses only
proof-gated unchecked accesses and checked scalar arithmetic. The corresponding
Lean reference semantics proves successful runtime operations' bounds, storage
updates, length preservation, and refinement to the abstract Vec push/pop
handle transitions. Compiler-generated function semantics still need to
replace the remaining hand-associated reference functions before the
end-to-end refinement claim is complete. The compiler now generates executable
Lean semantics for its straight-line scalar `Option<usize>` subset directly
from the function body. `vec_len_after_pop` carries a `refines` declaration,
and Lean checks extensional equality between that generated definition and the
verified runtime model; source/model drift therefore fails `luffs check`.
The same translation now covers one mutable byte slice, scalar parameters, one
proved array update, and `Option<usize>` or `Option<()>` results. Both Box byte
initialization and replacement are checked against `boxStoreU8`, so their
updated storage semantics now come from the Luffs bodies. Immutable byte-slice
translation also derives Box load and Vec last/get semantics from their Luffs
bodies; successful Vec reads are proved inside the logical length and backing
storage. Shared and mutable begin/end slice functions now also generate their
exact logical sublist semantics and refine `vecSliceU8`; the generic Iris Vec
theorems separately transfer shared or exclusive ownership for that range.
Growth copying now has source-derived two-buffer semantics as well: the first
`len` destination bytes become the source prefix while the destination suffix
is unchanged. Lean checks this generated transition against `vecCopyGrowU8`,
whose result theorem proves both bounds and destination-length preservation.
`vec_push_u8` is translated
from its two early-return guards and mutation into executable Lean semantics,
then checked extensionally against `vecPushU8`; its result theorem connects that
model to the abstract verified Vec handle transition. Multiple mutations,
loops, and general checked-arithmetic semantics are the next translation cases.
- [ ] End-to-end examples compile to Rust with no redundant bounds checks and
  are accepted by Lean from a clean checkout.
