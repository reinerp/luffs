import Luffs.Containers.Vec
import Luffs.Memory.Scalar
import Luffs.Runtime.TLSF

set_option autoImplicit false

namespace Luffs.Runtime.Containers

open Luffs.Memory
open Luffs.Allocator.TLSF

structure BoxNewU8ArraysResult extends
    Luffs.Runtime.TLSF.AllocateArraysResult where
  storage : List Byte
deriving DecidableEq, Repr

/-- Exact state transformer for allocator-backed `tlsf_box_new_u8`. The
allocator transition precedes initialization of the returned pool byte. -/
def boxNewU8Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : Byte) :
    Option BoxNewU8ArraysResult := do
  let allocated ← Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
    prevFree count second first heads next previous 8
  if allocated.allocatedOffset ≥ storage.length then none
  pure {
    offsets := allocated.offsets
    sizes := allocated.sizes
    isFree := allocated.isFree
    prevFree := allocated.prevFree
    count := allocated.count
    second := allocated.second
    first := allocated.first
    heads := allocated.heads
    next := allocated.next
    previous := allocated.previous
    allocatedOffset := allocated.allocatedOffset
    allocatedBytes := allocated.allocatedBytes
    storage := storage.set allocated.allocatedOffset value }

theorem boxNewU8Arrays_result
    {storage : List Byte} {offsets sizes : List Nat}
    {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {value : Byte}
    {result : BoxNewU8ArraysResult}
    (hsuccess : boxNewU8Arrays storage offsets sizes isFree prevFree count
      second first heads next previous value = some result) :
    ∃ allocated,
      Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
          second first heads next previous 8 = some allocated ∧
      allocated.allocatedOffset < storage.length ∧
      result.toAllocateArraysResult = allocated ∧
      result.storage = storage.set allocated.allocatedOffset value := by
  unfold boxNewU8Arrays at hsuccess
  cases halloc : Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
      prevFree count second first heads next previous 8 with
  | none => simp [boxNewU8Arrays, halloc] at hsuccess
  | some allocated =>
      by_cases hbound : allocated.allocatedOffset ≥ storage.length
      · simp [boxNewU8Arrays, halloc, hbound] at hsuccess
      · simp [boxNewU8Arrays, halloc, hbound] at hsuccess
        subst result
        exact ⟨allocated, rfl, Nat.lt_of_not_ge hbound, rfl, rfl⟩

@[simp] theorem boxU8_requestBytes :
    Luffs.Containers.Box.requestBytes Scalar.u8.size = 8 := by
  decide

set_option maxHeartbeats 1200000 in
/-- The allocator-backed Luffs byte Box constructor is the abstract verified
Box allocation, followed by initialization of exactly its first payload byte.
The returned scalar handle is the abstract block's pool offset. -/
theorem boxNewU8Arrays_refines_box
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {value : Byte}
    {result : BoxNewU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hsuccess : boxNewU8Arrays storage
      (Luffs.Runtime.TLSF.blockOffsets blocks)
      (Luffs.Runtime.TLSF.blockSizes blocks)
      (Luffs.Runtime.TLSF.freeFlags blocks)
      (Luffs.Runtime.TLSF.prevFreeFlags blocks) blocks.length second first
      heads next previous value = some result) :
    ∃ (hkeyMax : requestKey
          (Luffs.Containers.Box.requestBytes Scalar.u8.size) <
            2 ^ firstLevelCount)
        (boxResult : Luffs.Containers.Box.Result),
      Luffs.Containers.Box.allocate Scalar.u8
          { physical := blocks, bins := state } hkeyMax = some boxResult ∧
      result.allocatedOffset = boxResult.block.offset ∧
      result.allocatedBytes = boxResult.block.bytes ∧
      result.storage = storage.set boxResult.block.offset value ∧
      (Ownership.OwnsFree (PROP := Iris.IProp GF) pool blocks ⊣⊢
        OwnsBytes (boxResult.block.region pool) ∗
          Ownership.OwnsFree pool boxResult.state.physical) := by
  obtain ⟨allocated, halloc, _, hresult, hstorage⟩ :=
    boxNewU8Arrays_result hsuccess
  obtain ⟨hrequest, hkey, abstractResult, habstract, hoffset, hbytes,
      _, _, _, _, _, _, howns⟩ :=
    Luffs.Runtime.TLSF.allocateArrays_ownsFree
      (PROP := Iris.IProp GF) hvalid hsecond hfirst hbins hdisjoint halloc
  have hkeyBox : requestKey
      (Luffs.Containers.Box.requestBytes Scalar.u8.size) <
        2 ^ firstLevelCount := by
    simpa using hkey
  let boxResult : Luffs.Containers.Box.Result := {
    block := abstractResult.allocated
    state := abstractResult.state }
  have hbox : Luffs.Containers.Box.allocate Scalar.u8
      { physical := blocks, bins := state } hkeyBox = some boxResult := by
    simp [Luffs.Containers.Box.allocate, boxResult, habstract]
  have hresultOffset : result.allocatedOffset = allocated.allocatedOffset := by
    exact congrArg Luffs.Runtime.TLSF.AllocateArraysResult.allocatedOffset hresult
  have hresultBytes : result.allocatedBytes = allocated.allocatedBytes := by
    exact congrArg Luffs.Runtime.TLSF.AllocateArraysResult.allocatedBytes hresult
  refine ⟨hkeyBox, boxResult, hbox, ?_, ?_, ?_, ?_⟩
  · simpa [boxResult, hresultOffset] using hoffset
  · simpa [boxResult, hresultBytes] using hbytes
  · simpa [boxResult, hoffset] using hstorage
  · simpa [boxResult] using howns

/-- End-to-end Iris ownership law for successful allocator-backed byte Box
construction. The raw allocation capability is initialized and becomes a
typed Box capability while the allocator retains exactly the remaining free
pool. -/
theorem boxNewU8Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {value : Byte}
    {result : BoxNewU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hsuccess : boxNewU8Arrays storage
      (Luffs.Runtime.TLSF.blockOffsets blocks)
      (Luffs.Runtime.TLSF.blockSizes blocks)
      (Luffs.Runtime.TLSF.freeFlags blocks)
      (Luffs.Runtime.TLSF.prevFreeFlags blocks) blocks.length second first
      heads next previous value = some result) :
    ∃ (hkeyMax : requestKey
          (Luffs.Containers.Box.requestBytes Scalar.u8.size) <
            2 ^ firstLevelCount)
        (boxResult : Luffs.Containers.Box.Result),
      Luffs.Containers.Box.allocate Scalar.u8
          { physical := blocks, bins := state } hkeyMax = some boxResult ∧
      result.allocatedOffset = boxResult.block.offset ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents (boxResult.block.region pool).base
          (Scalar.u8.encode (Scalar.bv8OfByte value)) →
        contentsInterp (G := G) contents ∗
            Ownership.OwnsFree pool blocks ==∗
          contentsInterp
              (insertBytes contents (boxResult.block.region pool).base
                (Scalar.u8.encode (Scalar.bv8OfByte value))) ∗
            (Luffs.Containers.Box.Owns Scalar.u8 pool boxResult.block
                (Scalar.bv8OfByte value) ∗
              Ownership.OwnsFree pool boxResult.state.physical) := by
  obtain ⟨hkeyMax, boxResult, hbox, hoffset, _, _, howns⟩ :=
    boxNewU8Arrays_refines_box (GF := GF) hvalid hsecond hfirst hbins
      hdisjoint hsuccess
  refine ⟨hkeyMax, boxResult, hbox, hoffset, ?_⟩
  intro contents hfresh
  iintro ⟨Hcontents, Hallocator⟩
  ihave ⟨Hregion, Hallocator⟩ := howns.mp $$ Hallocator
  icombine Hcontents Hregion as Hinit
  imod Luffs.Containers.Box.initialize_owns Scalar.u8 pool boxResult.block
    (Scalar.bv8OfByte value) contents hfresh $$ Hinit with
      ⟨Hcontents, Hbox⟩
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplitl [Hbox]
    · iassumption
    · iassumption

def boxDropU8Arrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (returnedOffset : Nat) :
    Option Luffs.Runtime.TLSF.CoalesceClassResult := do
  if count = 0 ∨ count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length then none
  let block ← Luffs.Runtime.TLSF.findOffsetIndex offsets count returnedOffset
  if isFree[block]? ≠ some 0 then none
  let returnedBytes ← sizes[block]?
  Luffs.Runtime.TLSF.deallocateArrays offsets sizes isFree prevFree second
    first heads next previous count block returnedOffset returnedBytes

theorem boxDropU8Arrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {returnedOffset : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hsuccess : boxDropU8Arrays offsets sizes isFree prevFree count second
      first heads next previous returnedOffset = some result) :
    ∃ block returnedBytes,
      Luffs.Runtime.TLSF.findOffsetIndex offsets count returnedOffset =
          some block ∧
      isFree[block]? = some 0 ∧ sizes[block]? = some returnedBytes ∧
      Luffs.Runtime.TLSF.deallocateArrays offsets sizes isFree prevFree second
        first heads next previous count block returnedOffset returnedBytes =
          some result := by
  let bad := count = 0 ∨ count > offsets.length ∨ count > sizes.length ∨
    count > isFree.length
  by_cases hbad : bad
  · simp [boxDropU8Arrays, bad, hbad] at hsuccess
  · cases hblock : Luffs.Runtime.TLSF.findOffsetIndex offsets count
        returnedOffset with
    | none => simp [boxDropU8Arrays, bad, hbad, hblock] at hsuccess
    | some block =>
      by_cases hfree : isFree[block]? ≠ some 0
      · simp [boxDropU8Arrays, bad, hbad, hblock, hfree] at hsuccess
      · cases hbytes : sizes[block]? with
        | none =>
          simp [boxDropU8Arrays, bad, hbad, hblock, hfree, hbytes] at hsuccess
        | some returnedBytes =>
          have hdealloc : Luffs.Runtime.TLSF.deallocateArrays offsets sizes
              isFree prevFree second first heads next previous count block
              returnedOffset returnedBytes = some result := by
            have hparts := hsuccess
            simp [boxDropU8Arrays, bad, hbad, hblock, hfree, hbytes] at hparts
            exact hparts.2
          exact ⟨block, returnedBytes, rfl, Decidable.not_not.mp hfree,
            hbytes, hdealloc⟩

set_option maxHeartbeats 1200000 in
theorem boxDropU8Arrays_refines_box
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {returnedOffset : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : blocks.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hsuccess : boxDropU8Arrays
      (Luffs.Runtime.TLSF.blockOffsets blocks)
      (Luffs.Runtime.TLSF.blockSizes blocks)
      (Luffs.Runtime.TLSF.freeFlags blocks)
      (Luffs.Runtime.TLSF.prevFreeFlags blocks) blocks.length second first
      heads next previous returnedOffset = some result) :
    ∃ (selected : Block) (abstractNext : Alloc.State),
      selected.offset = returnedOffset ∧
      Luffs.Containers.Box.drop pool
          { physical := blocks, bins := state } selected = some abstractNext ∧
      (OwnsBytes (PROP := Iris.IProp GF) (selected.region pool) ∗
          Ownership.OwnsFree pool blocks ⊣⊢
        Ownership.OwnsFree pool abstractNext.physical) := by
  obtain ⟨i, returnedBytes, hfind, hfree, hbytes, hdealloc⟩ :=
    boxDropU8Arrays_result hsuccess
  have hscan := Luffs.Runtime.TLSF.findOffsetIndex_sound hfind
  have hi : i < blocks.length := by simpa using hscan.1
  let selected := blocks.get ⟨i, hi⟩
  have hget : blocks[i]? = some selected := by
    exact List.getElem?_eq_getElem hi
  have hcanonical := Luffs.Runtime.TLSF.canonical_representsPhysicalArrays blocks
  have hoffsetArray :=
    Luffs.Runtime.TLSF.representsPhysicalArrays_get_offset hcanonical hget
  have hselectedOffset : selected.offset = returnedOffset := by
    rw [hoffsetArray] at hscan
    exact Option.some.inj hscan.2
  have hsizeArray :=
    Luffs.Runtime.TLSF.representsPhysicalArrays_get_size hcanonical hget
  have hselectedBytes : selected.bytes = returnedBytes := by
    rw [hsizeArray] at hbytes
    exact Option.some.inj hbytes
  have hfreeArray :=
    Luffs.Runtime.TLSF.representsPhysicalArrays_get_free hcanonical hget
  have hallocated : selected.free = false := by
    rw [hfreeArray] at hfree
    cases hselectedFree : selected.free <;> simp [hselectedFree] at hfree ⊢
  have hdealloc' : Luffs.Runtime.TLSF.deallocateArrays
      (Luffs.Runtime.TLSF.blockOffsets blocks)
      (Luffs.Runtime.TLSF.blockSizes blocks)
      (Luffs.Runtime.TLSF.freeFlags blocks)
      (Luffs.Runtime.TLSF.prevFreeFlags blocks) second first heads next previous
      blocks.length i selected.offset selected.bytes = some result := by
    simpa [hselectedOffset, hselectedBytes] using hdealloc
  have hfresh := Luffs.Runtime.TLSF.allocatedBlock_offset_fresh hvalid hget
    hallocated
  obtain ⟨abstractNext, habstract, howns⟩ :=
    Luffs.Runtime.TLSF.deallocateArrays_ownsFree
      (PROP := Iris.IProp GF) hget hallocated hvalid hpoolMax hcountMax
      hsecond hfirst hbins hdisjoint hfresh hdealloc'
  have hfindPhysical : Bins.findPhysicalIndex blocks selected = some i := by
    rw [← Luffs.Runtime.TLSF.findOffsetIndex_refines_findPhysicalIndex
      (target := selected) (actual := selected) hvalid.1
      (List.mem_iff_getElem?.2 ⟨i, hget⟩) (Bins.samePhysical_refl selected)]
    simpa [hselectedOffset] using hfind
  have hboxDrop : Luffs.Containers.Box.drop pool
      { physical := blocks, bins := state } selected = some abstractNext := by
    simp [Luffs.Containers.Box.drop, hfindPhysical, habstract]
  exact ⟨selected, abstractNext, hselectedOffset, hboxDrop, howns⟩

theorem boxDropU8Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {returnedOffset : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : blocks.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hsuccess : boxDropU8Arrays
      (Luffs.Runtime.TLSF.blockOffsets blocks)
      (Luffs.Runtime.TLSF.blockSizes blocks)
      (Luffs.Runtime.TLSF.freeFlags blocks)
      (Luffs.Runtime.TLSF.prevFreeFlags blocks) blocks.length second first
      heads next previous returnedOffset = some result) :
    ∃ (selected : Block) (abstractNext : Alloc.State),
      selected.offset = returnedOffset ∧
      ∀ (value : BitVec 8) (contents : ContentsMap),
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Box.Owns Scalar.u8 pool selected value ∗
              Ownership.OwnsFree pool blocks) ==∗
          contentsInterp
              (deleteBytes contents (selected.region pool).base
                (Scalar.u8.encode value)) ∗
            Ownership.OwnsFree pool abstractNext.physical := by
  obtain ⟨selected, abstractNext, hoffset, hdrop, _⟩ :=
    boxDropU8Arrays_refines_box (GF := GF) hvalid hpoolMax hcountMax hsecond
      hfirst hbins hdisjoint hsuccess
  refine ⟨selected, abstractNext, hoffset, ?_⟩
  intro value contents
  exact Luffs.Containers.Box.drop_owns Scalar.u8 value contents hdrop

/-- Pure reference semantics for the first byte-monomorphized Luffs lowering.
These definitions deliberately expose both the mutated storage and scalar
return value; the Rust functions mutate the first component in place. -/
def boxLoadU8 (storage : List Byte) (begin : Nat) : Option Byte :=
  storage[begin]?

def boxStoreU8 (storage : List Byte) (begin : Nat) (value : Byte) :
    Option (List Byte) :=
  if begin ≥ storage.length then none else some (storage.set begin value)

def vecPushU8 (storage : List Byte) (len capacity : Nat) (value : Byte) :
    Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if capacity > storage.length then none
  else some (storage.set len value, len + 1)

def vecLastU8 (storage : List Byte) (len : Nat) : Option Byte :=
  if len = 0 then none
  else if len > storage.length then none
  else storage[len - 1]?

def vecLenAfterPop (len : Nat) : Option Nat :=
  if 0 < len then some (len - 1) else none

def vecGetU8 (storage : List Byte) (len index : Nat) : Option Byte :=
  if index ≥ len then none
  else if len > storage.length then none
  else storage[index]?

def vecSliceU8 (storage : List Byte) (len begin end_ : Nat) :
    Option (List Byte) :=
  if begin > end_ then none
  else if end_ > len then none
  else if len > storage.length then none
  else some ((storage.drop begin).take (end_ - begin))

def vecCopyGrowU8 (source destination : List Byte) (len : Nat) :
    Option (List Byte) :=
  if len > source.length then none
  else if len > destination.length then none
  else some (source.take len ++ destination.drop len)

theorem boxLoadU8_result {storage : List Byte} {begin : Nat} {value : Byte}
    (hload : boxLoadU8 storage begin = some value) :
    begin < storage.length ∧ storage[begin]? = some value := by
  unfold boxLoadU8 at hload
  exact ⟨(getElem?_eq_some_iff.mp hload).1, hload⟩

theorem boxStoreU8_result {storage next : List Byte} {begin : Nat}
    {value : Byte} (hstore : boxStoreU8 storage begin value = some next) :
    begin < storage.length ∧ next = storage.set begin value ∧
      next.length = storage.length := by
  unfold boxStoreU8 at hstore
  split at hstore
  next => contradiction
  next hbound =>
    simp only [Option.some.injEq] at hstore
    subst next
    exact ⟨Nat.lt_of_not_ge hbound, rfl, List.length_set⟩

theorem vecPushU8_result {storage next : List Byte} {len capacity nextLen : Nat}
    {value : Byte}
    (hpush : vecPushU8 storage len capacity value = some (next, nextLen)) :
    len < capacity ∧ capacity ≤ storage.length ∧
      next = storage.set len value ∧ nextLen = len + 1 ∧
      next.length = storage.length := by
  unfold vecPushU8 at hpush
  split at hpush
  next => contradiction
  next hlen =>
    split at hpush
    next => contradiction
    next hcapacity =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hpush
      rcases hpush with ⟨hnext, hnextLen⟩
      subst next
      subst nextLen
      exact ⟨Nat.lt_of_not_ge hlen, Nat.le_of_not_gt hcapacity,
        rfl, rfl, List.length_set⟩

theorem vecPushU8_refines_handle {storage next : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {nextLen : Nat} {value : Byte}
    (hpush : vecPushU8 storage handle.len handle.capacity value =
      some (next, nextLen)) :
    Luffs.Containers.Vec.push handle =
      some { handle with len := nextLen } := by
  have hresult := vecPushU8_result hpush
  simp [Luffs.Containers.Vec.push, hresult.1, hresult.2.2.2.1]

theorem vecLastU8_result {storage : List Byte} {len : Nat} {value : Byte}
    (hlast : vecLastU8 storage len = some value) :
    0 < len ∧ len ≤ storage.length ∧ storage[len - 1]? = some value := by
  unfold vecLastU8 at hlast
  split at hlast
  next => contradiction
  next hpositive =>
    split at hlast
    next => contradiction
    next hbound =>
      exact ⟨Nat.pos_of_ne_zero hpositive, Nat.le_of_not_gt hbound, hlast⟩

theorem vecLenAfterPop_refines_handle {handle : Luffs.Containers.Vec.Handle}
    {nextLen : Nat} (hpop : vecLenAfterPop handle.len = some nextLen) :
    Luffs.Containers.Vec.pop handle = some { handle with len := nextLen } := by
  unfold vecLenAfterPop at hpop
  split at hpop
  next hpositive =>
    simp only [Option.some.injEq] at hpop
    subst nextLen
    simp [Luffs.Containers.Vec.pop, hpositive]
  next => contradiction

theorem vecGetU8_result {storage : List Byte} {len index : Nat} {value : Byte}
    (hget : vecGetU8 storage len index = some value) :
    index < len ∧ len ≤ storage.length ∧ storage[index]? = some value := by
  unfold vecGetU8 at hget
  split at hget
  next => contradiction
  next hindex =>
    split at hget
    next => contradiction
    next hlen =>
      exact ⟨Nat.lt_of_not_ge hindex, Nat.le_of_not_gt hlen, hget⟩

theorem vecSliceU8_result {storage slice : List Byte} {len begin end_ : Nat}
    (hslice : vecSliceU8 storage len begin end_ = some slice) :
    begin ≤ end_ ∧ end_ ≤ len ∧ len ≤ storage.length ∧
      slice = (storage.drop begin).take (end_ - begin) := by
  unfold vecSliceU8 at hslice
  split at hslice
  next => contradiction
  next hbegin =>
    split at hslice
    next => contradiction
    next hend =>
      split at hslice
      next => contradiction
      next hlen =>
        simp only [Option.some.injEq] at hslice
        exact ⟨Nat.le_of_not_gt hbegin, Nat.le_of_not_gt hend,
          Nat.le_of_not_gt hlen, hslice.symm⟩

theorem vecCopyGrowU8_result {source destination next : List Byte} {len : Nat}
    (hcopy : vecCopyGrowU8 source destination len = some next) :
    len ≤ source.length ∧ len ≤ destination.length ∧
      next = source.take len ++ destination.drop len ∧
      next.length = destination.length := by
  unfold vecCopyGrowU8 at hcopy
  split at hcopy
  next => contradiction
  next hsource =>
    split at hcopy
    next => contradiction
    next hdestination =>
      simp only [Option.some.injEq] at hcopy
      subst next
      have hsource' := Nat.le_of_not_gt hsource
      have hdestination' := Nat.le_of_not_gt hdestination
      refine ⟨hsource', hdestination', rfl, ?_⟩
      rw [List.length_append, List.length_take, List.length_drop,
        Nat.min_eq_left hsource']
      omega

end Luffs.Runtime.Containers
