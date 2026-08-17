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
  request through 256 bytes. Luffs now implements the 64-bit mapping-down path
  used for free-block insertion: a source-shape checked refinement maps every
  accepted positive size to the encoded Lean `sizeClass`, whose result is
  proved below 2048. The mapping-up request path and a word-level theorem for
  the `leading_zeros` lowering remain.
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
  reinserting a remainder remain. The concrete Luffs insertion wrapper now
  performs all bounds checks before mutation, inserts the block through the
  intrusive primitive, and sets both packed bitmap-cache levels. Its exact
  generated state model proves metadata-length preservation, representation
  of the new selected chain under freshness, and that both selected cache bits
  are true. Setting a class bit is now proved to preserve every other packed
  class bit. Consequently, under abstract bin validity, the entire concrete
  second-level bitmap refines `Bins.State.insert`; setting the corresponding
  first-level bit is also proved to preserve `FirstBitmapRep`. Every
  non-selected intrusive chain is now framed across the concrete writes using
  cross-bin offset disjointness, including the selected old head's back-link.
  The final insertion theorem therefore refines exactly `Bins.State.insert`,
  preserves abstract bin validity, represents every successor chain, and
  preserves both bitmap abstractions. The concrete uncoalesced-deallocation
  wrapper now composes exact-region validation, the physical free-bit and
  successor-boundary-tag writes, mapping-down classification, offset-keyed
  intrusive insertion, and both bitmap updates. All fallible checks precede
  its first write. Lean proves the combined array result refines `markFreeAt`
  and `Bins.State.insert` simultaneously, preserving abstract bin validity and
  the representations of every chain and both bitmap levels. Successful
  concrete execution now additionally witnesses the existing abstract
  `deallocateUncoalesced` transition, so its Iris-Lean ownership theorem applies
  directly: the client's exact returned `OwnsBytes` capability is consumed and
  becomes part of the allocator's `OwnsFree` assertion.
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
  predecessor/successor link-update refinement and the rest of the Luffs
  lowering remain. The first concrete deallocation stage is now lowered from
  Luffs: before mutation it rejects out-of-range headers, double-free, and any
  returned `(offset, bytes)` pair that differs from the authoritative physical
  header. It then marks the selected allocation free and updates the
  successor's `prev_free` boundary tag. Its generated Lean semantics is
  source-shape checked against the exact parallel-array model. That model is
  proved to be precisely the free-bit and boundary-tag projection of the
  abstract `markFreeAt` transition, framing every other physical header.
  The concrete Luffs uncoalesced transaction now composes that marking with
  classification and full bin insertion. Its successful generated semantics
  is proved to refine the corresponding abstract physical and bin transitions
  without conflating a physical-array index with the block's byte offset.
  Concrete arbitrary-node class removal is now lowered from Luffs. It updates
  intrusive links and clears the selected second-level bit, plus its
  first-level bit exactly when that word becomes empty. The empty-class test is
  proved to require both a sentinel predecessor and successor: a proof-driven
  audit caught and fixed the incorrect tail-only test, which would have hidden
  a still-live prefix from bitmap search. Its compiler-generated
  model is definitionally tied to the checked Lean transformer. Lean now also
  connects arbitrary abstract `removeOffset` to this exact singleton test:
  the rebuilt abstract chain has precisely the old offsets with the selected
  offset erased, and the concrete transition preserves both bitmap levels for
  the resulting abstract bin state. The arbitrary intrusive splice is now
  proved as well: the predecessor and successor are relinked, the selected
  node is detached, the prefix and suffix remain in order, every other bin is
  framed, cross-bin offset disjointness is preserved, and the complete
  concrete metadata plus both bitmap levels refine abstract `removeOffset`.
  The fixed
  physical-header arrays now have an explicit active-prefix
  representation and the concrete free entry point rejects selectors outside
  `block_count`; inactive capacity can no longer masquerade as a live header.
  This count is also the basis for the compaction required when coalescing
  deletes a neighbor. Luffs now has that checked physical compaction primitive:
  it validates active adjacent free headers, uses checked arithmetic for both
  adjacency and merged size, shifts all four physical metadata arrays, and
  decrements the active count. The compiler source-shape gate connects it to
  an exact Lean array transformer; success proves the removed neighbor was
  active, both free flags were set, adjacency was exact, and the count drops by
  one. The exact active-prefix compaction is now proved to represent abstract
  `coalesceAt` at every physical-list position, not merely at the head: the
  untouched prefix is framed, the adjacent pair becomes its merged header,
  the suffix shifts left, and the old final active slot becomes spare capacity.
  Luffs now also lowers the complete adjacent-pair metadata transaction: it
  preflights both old and merged classes, removes both old nodes, compacts the
  physical arrays, and reinserts the merged node. The generated transaction is
  tied to its exact Lean composition, and its physical projection is proved to
  refine arbitrary-position `coalesceAt`; the same theorem carries the
  Iris-Lean `OwnsFree` equivalence showing that adjacent byte capabilities are
  recombined without loss or duplication. Proving that the composed concrete
  bin arrays can therefore be composed with the abstract removals; the
  two removals and merged-node insertion are now composed as a single bin
  refinement theorem. It carries validity, both bitmap levels, every intrusive
  chain, and cross-bin offset disjointness through all three operations;
  insertion itself now has a separate proof that fresh offsets preserve that
  disjointness invariant. The complete coalescing theorem now identifies the
  runtime-classified blocks with the abstract adjacent pair, derives global
  freshness of the merged offset from the two removals, and combines the bin
  theorem with physical compaction. Given allocator validity, the pool size
  bound, and `canCoalesce`, successful Luffs execution constructs and refines
  the abstract `coalescePair` successor. Together with the Iris-Lean
  `OwnsFree` equivalence, the same transition preserves metadata invariants
  and recombines the adjacent byte capabilities without loss or duplication.
  Pointer-to-offset validation belongs at the mmap-backed pool boundary.
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
The concrete Luffs runtime now composes bounded bitmap lookup with head loading,
intrusive removal, and exhausted-bin bitmap clearing in
`tlsf_take_candidate`. All potentially failing bounds checks precede the first
write. Its exact array/bitmap transition has a Lean model; success proves the
returned bin was a set bit at or above the requested start, all selected
indices were valid, the modeled removal occurred, and the bitmap changes only
through the exhausted-chain clear operation. The compiler's specialized
source-shape gate emits the corresponding refinement declaration. Relating
this fixed-array state to `Bins.State.takeCandidate` is still required before
the abstract allocator proof can consume it.
The clear operation is no longer opaque: Lean proves array length preservation,
preservation of every other bitmap word, preservation of every other bit in
the selected word, and that the selected bit becomes false.
The earlier flat 256-bin path was found insufficient for the abstract
allocator's `64 × 32` class space. The concrete metadata has therefore been
aligned to true two-level TLSF: 2048 heads, 64 packed `u32` second-level
bitmaps, and one `u64` first-level bitmap. Luffs now implements same-level
masked search, constant-time first-level jumping, second-level `ctz`, candidate
removal, and both cache updates for this layout. Lean defines the matching
flattened 2048-bit semantics, proves successful lowered lookup is in range and
points to a set class bit, proves every result decodes to an in-range
`SizeClass`, and relates the packed bitmap to `Bins.State.slSet`. Under
`Bins.Valid`, every successful concrete lookup therefore selects an abstract
class whose intrusive chain is nonempty. The candidate-removal body now also
has a compiler-recognized exact semantic model covering intrusive removal and
both conditional bitmap clears. Lean proves its result equation and that
clearing a selected class bit preserves every other class bit. It also proves
the second-level abstraction step in both cases: clearing the bit represents
replacing the selected abstract chain by the empty list, while an unchanged
bitmap represents replacement by any nonempty remainder. Connecting the
intrusive successor sentinel to those two cases and preserving the first-level
cache relation are now proved as well. The composed candidate theorem starts
from valid abstract bins plus concrete bitmap/list representations and proves
that a successful Luffs transition returns the abstract head offset and
preserves both bitmap levels for the abstract `removeFront` successor state.
With the proved cross-bin offset-disjointness premise, the composed theorem
also preserves the intrusive metadata representation for every chain in the
successor state: the selected head is detached, its remainder is represented,
and all other bins are framed unchanged. This closes the modeled candidate
transition from concrete Luffs metadata to the abstract bin operation.
The abstract two-level lookup is now separately proved minimal in encoded
class order. Combining abstract and concrete minimality proves that the Luffs
lookup selects exactly `Bins.findCandidate`; the final composed theorem proves
the concrete candidate transition refines `Bins.State.takeCandidate`, including
the returned block offset and all successor representations.
The logical 2048-bit search is also proved equal to a chunked search that
examines only the suffix of the starting `u32` and then the remaining complete
second-level words. For each `u32`, masked `ctz` is proved exactly equal to its
logical suffix search, including the zero-mask failure case. The first-level
cache relation is stated extensionally as equality between its 64 bits and the
64-element map of second-level-word nonemptiness; proving that cached jump
equal to the remaining complete-word search is now complete. Under that cache
relation and `start_sl < 32`, the exact lowered Luffs lookup equals logical
first-set search over all 2048 classes. Consequently it is sound, complete,
and minimal. The compiler emits this lowered model and checks the refinement
theorem with the cache relation as an explicit premise.
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
masked-first-word loop to this definition is underway. Bitmap words use
`BitVec 64`, and `BitVec.ctz.toNat` is proved equal to the list-level first true
index for every nonzero word. The exact Rust first-word operation—AND with
`u64::MAX << start_bit`, followed by `trailing_zeros()`—is now proved equal to
the logical suffix search. These proofs use checked selected-bit, lower-bit,
shift, and bitwise-AND lemmas rather than trusting a trailing-zero or mask
axiom.
The compiler recognizes the checked source shape of `tlsf_find_nonempty_bin`
and emits executable lowered Lean semantics plus a refinement theorem; a
changed mask direction is rejected. The lowered model performs the same word
division and remainder, first-word mask, zero-word skipping, and per-word
`ctz` operations as the Rust. It is proved equal to flat first-set search via
word-drop, append-search, and offset-shifting lemmas. The recognizer itself is
still specialized rather than a compositional translation of arbitrary loops.

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
