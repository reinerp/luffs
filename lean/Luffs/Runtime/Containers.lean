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

/-- Replace a byte range while retaining the prefix and suffix outside it. -/
def writeBytes (storage : List Byte) (offset : Nat) (bytes : List Byte) : List Byte :=
  storage.take offset ++ bytes ++ storage.drop (offset + bytes.length)

theorem writeBytes_singleton_eq_set {α : Type} (values : List α)
    (offset : Nat) (value : α) (hbound : offset < values.length) :
    values.take offset ++ [value] ++ values.drop (offset + 1) =
      values.set offset value := by
  induction values generalizing offset with
  | nil => simp at hbound
  | cons head tail ih =>
      cases offset with
      | zero => simp
      | succ offset =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hbound
          simp only [List.take_succ_cons, List.drop_succ_cons, List.set,
            List.cons_append, List.cons.injEq, true_and]
          simpa [Nat.succ_eq_add_one] using ih offset hbound

/-- Codec-generic executable state transformer for allocator-backed Box
construction. A Luffs monomorphization supplies one of the verified scalar
codecs and lowers the finite encoding to byte stores. -/
def boxNewArrays {α : Type} (codec : Codec α) (storage : List Byte)
    (offsets sizes : List Nat) (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : α) :
    Option BoxNewU8ArraysResult := do
  let allocated ← Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
    prevFree count second first heads next previous
      (Luffs.Containers.Box.requestBytes codec.size)
  if allocated.allocatedOffset + codec.size > storage.length then none
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
    storage := writeBytes storage allocated.allocatedOffset (codec.encode value) }

theorem boxNewArrays_result {α : Type} {codec : Codec α}
    {storage : List Byte} {offsets sizes : List Nat}
    {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {value : α}
    {result : BoxNewU8ArraysResult}
    (hsuccess : boxNewArrays codec storage offsets sizes isFree prevFree count
      second first heads next previous value = some result) :
    ∃ allocated,
      Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
          second first heads next previous
            (Luffs.Containers.Box.requestBytes codec.size) = some allocated ∧
      allocated.allocatedOffset + codec.size ≤ storage.length ∧
      result.toAllocateArraysResult = allocated ∧
      result.storage = writeBytes storage allocated.allocatedOffset
        (codec.encode value) := by
  unfold boxNewArrays at hsuccess
  cases halloc : Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
      prevFree count second first heads next previous
        (Luffs.Containers.Box.requestBytes codec.size) with
  | none => simp [halloc] at hsuccess
  | some allocated =>
      by_cases hbound : allocated.allocatedOffset + codec.size > storage.length
      · simp [halloc, hbound] at hsuccess
      · simp [halloc, hbound] at hsuccess
        subst result
        exact ⟨allocated, rfl, Nat.le_of_not_gt hbound, rfl, rfl⟩

set_option maxHeartbeats 1200000 in
theorem boxNewArrays_refines_box {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] {α : Type} {codec : Codec α}
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {value : α}
    {result : BoxNewU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxNewArrays codec storage offsets sizes isFree prevFree count
      second first heads next previous value = some result) :
    ∃ (hkeyMax : requestKey (Luffs.Containers.Box.requestBytes codec.size) <
          2 ^ firstLevelCount)
        (boxResult : Luffs.Containers.Box.Result),
      Luffs.Containers.Box.allocate codec
          { physical := blocks, bins := state } hkeyMax = some boxResult ∧
      result.allocatedOffset = boxResult.block.offset ∧
      result.allocatedBytes = boxResult.block.bytes ∧
      result.storage = writeBytes storage boxResult.block.offset
        (codec.encode value) ∧
      (Ownership.OwnsFree (PROP := Iris.IProp GF) pool blocks ⊣⊢
        OwnsBytes (boxResult.block.region pool) ∗
          Ownership.OwnsFree pool boxResult.state.physical) := by
  obtain ⟨allocated, halloc, _, hresult, hstorage⟩ :=
    boxNewArrays_result hsuccess
  obtain ⟨hrequest, hkey, abstractResult, habstract, hoffset, hbytes,
      _, _, _, _, _, _, howns⟩ :=
    Luffs.Runtime.TLSF.allocateArrays_ownsFree
      (PROP := Iris.IProp GF) hvalid hsecond hfirst hbins hdisjoint hphysical
      halloc
  let boxResult : Luffs.Containers.Box.Result := {
    block := abstractResult.allocated
    state := abstractResult.state }
  have hbox : Luffs.Containers.Box.allocate codec
      { physical := blocks, bins := state } hkey = some boxResult := by
    simp [Luffs.Containers.Box.allocate, boxResult, habstract]
  have hresultOffset : result.allocatedOffset = allocated.allocatedOffset :=
    congrArg Luffs.Runtime.TLSF.AllocateArraysResult.allocatedOffset hresult
  have hresultBytes : result.allocatedBytes = allocated.allocatedBytes :=
    congrArg Luffs.Runtime.TLSF.AllocateArraysResult.allocatedBytes hresult
  refine ⟨hkey, boxResult, hbox, ?_, ?_, ?_, ?_⟩
  · simpa [boxResult, hresultOffset] using hoffset
  · simpa [boxResult, hresultBytes] using hbytes
  · simpa [boxResult, hoffset] using hstorage
  · simpa [boxResult] using howns

/-- Successful generic construction turns the allocator's raw byte capability
into the codec-indexed exclusive Box capability. -/
theorem boxNewArrays_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {α : Type} {codec : Codec α}
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {value : α}
    {result : BoxNewU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxNewArrays codec storage offsets sizes isFree prevFree count
      second first heads next previous value = some result) :
    ∃ (hkeyMax : requestKey (Luffs.Containers.Box.requestBytes codec.size) <
          2 ^ firstLevelCount)
        (boxResult : Luffs.Containers.Box.Result),
      Luffs.Containers.Box.allocate codec
          { physical := blocks, bins := state } hkeyMax = some boxResult ∧
      result.allocatedOffset = boxResult.block.offset ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents (boxResult.block.region pool).base
          (codec.encode value) →
        contentsInterp (G := G) contents ∗ Ownership.OwnsFree pool blocks ==∗
          contentsInterp
              (insertBytes contents (boxResult.block.region pool).base
                (codec.encode value)) ∗
            (Luffs.Containers.Box.Owns codec pool boxResult.block value ∗
              Ownership.OwnsFree pool boxResult.state.physical) := by
  obtain ⟨hkeyMax, boxResult, hbox, hoffset, _, _, howns⟩ :=
    boxNewArrays_refines_box (GF := GF) hvalid hsecond hfirst hbins hdisjoint
      hphysical hsuccess
  refine ⟨hkeyMax, boxResult, hbox, hoffset, ?_⟩
  intro contents hfresh
  iintro ⟨Hcontents, Hallocator⟩
  ihave ⟨Hregion, Hallocator⟩ := howns.mp $$ Hallocator
  icombine Hcontents Hregion as Hinit
  imod Luffs.Containers.Box.initialize_owns codec pool boxResult.block value
    contents hfresh $$ Hinit with ⟨Hcontents, Hbox⟩
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplitl [Hbox]
    · iassumption
    · iassumption

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

theorem boxNewU8Arrays_eq_generic
    (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : Byte) :
    boxNewU8Arrays storage offsets sizes isFree prevFree count second first
        heads next previous value =
      boxNewArrays Scalar.u8 storage offsets sizes isFree prevFree count second
        first heads next previous (Scalar.bv8OfByte value) := by
  unfold boxNewU8Arrays boxNewArrays
  rw [boxU8_requestBytes]
  cases halloc : Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree
      count second first heads next previous 8 with
  | none => simp [halloc]
  | some allocated =>
      by_cases hbound : allocated.allocatedOffset ≥ storage.length
      · have hgeneric : allocated.allocatedOffset + Scalar.u8.size >
            storage.length := by
          simp only [Scalar.u8]
          omega
        simp [halloc, hbound, hgeneric]
      · have hlt : allocated.allocatedOffset < storage.length :=
          Nat.lt_of_not_ge hbound
        have hgeneric : ¬allocated.allocatedOffset + Scalar.u8.size >
            storage.length := by
          simp only [Scalar.u8]
          omega
        have hwrite := writeBytes_singleton_eq_set storage
          allocated.allocatedOffset value hlt
        simp [halloc, hbound, hgeneric, writeBytes, Scalar.u8, Scalar.encode8,
          Scalar.bv8OfByte, Scalar.byteOfBV8, hwrite]
        exact ⟨by omega, by
          simpa only [List.cons_append, List.nil_append, List.append_assoc] using
            hwrite.symm⟩

set_option maxHeartbeats 1200000 in
/-- The allocator-backed Luffs byte Box constructor is the abstract verified
Box allocation, followed by initialization of exactly its first payload byte.
The returned scalar handle is the abstract block's pool offset. -/
theorem boxNewU8Arrays_refines_box
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {value : Byte}
    {result : BoxNewU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxNewU8Arrays storage
      offsets sizes isFree prevFree count second first
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
      (PROP := Iris.IProp GF) hvalid hsecond hfirst hbins hdisjoint hphysical
      halloc
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
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {value : Byte}
    {result : BoxNewU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxNewU8Arrays storage
      offsets sizes isFree prevFree count second first
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
      hdisjoint hphysical hsuccess
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

def boxDropPointerU8Arrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (poolBase poolBytes pointer : Nat) :
    Option Luffs.Runtime.TLSF.CoalesceClassResult := do
  let offset ← Luffs.Runtime.TLSF.pointerToOffset poolBase poolBytes pointer
  boxDropU8Arrays offsets sizes isFree prevFree count second first heads next
    previous offset

theorem boxDropPointerU8Arrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {poolBase poolBytes pointer : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hsuccess : boxDropPointerU8Arrays offsets sizes isFree prevFree count
      second first heads next previous poolBase poolBytes pointer = some result) :
    ∃ offset,
      pointer = poolBase + offset ∧ offset < poolBytes ∧
      boxDropU8Arrays offsets sizes isFree prevFree count second first heads
        next previous offset = some result := by
  unfold boxDropPointerU8Arrays at hsuccess
  cases hoffset : Luffs.Runtime.TLSF.pointerToOffset poolBase poolBytes pointer with
  | none => simp [hoffset] at hsuccess
  | some offset =>
      have hpointer := Luffs.Runtime.TLSF.pointerToOffset_result hoffset
      simp only [hoffset, Option.bind_some] at hsuccess
      exact ⟨offset, hpointer.1, hpointer.2, hsuccess⟩

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
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {returnedOffset : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxDropU8Arrays
      offsets sizes isFree prevFree count second first
      heads next previous returnedOffset = some result) :
    ∃ (selected : Block) (abstractNext : Alloc.State),
      selected.offset = returnedOffset ∧
      selected ∈ blocks ∧
      Luffs.Containers.Box.drop pool
          { physical := blocks, bins := state } selected = some abstractNext ∧
      (OwnsBytes (PROP := PROP) (selected.region pool) ∗
          Ownership.OwnsFree (PROP := PROP) pool blocks ⊣⊢
        Ownership.OwnsFree (PROP := PROP) pool abstractNext.physical) := by
  obtain ⟨i, returnedBytes, hfind, hfree, hbytes, hdealloc⟩ :=
    boxDropU8Arrays_result hsuccess
  have hscan := Luffs.Runtime.TLSF.findOffsetIndex_sound hfind
  have hi : i < blocks.length := by simpa [← hphysical.1] using hscan.1
  let selected := blocks.get ⟨i, hi⟩
  have hget : blocks[i]? = some selected := by
    exact List.getElem?_eq_getElem hi
  have hoffsetArray :=
    Luffs.Runtime.TLSF.representsPhysicalArrays_get_offset hphysical hget
  have hselectedOffset : selected.offset = returnedOffset := by
    rw [hoffsetArray] at hscan
    exact Option.some.inj hscan.2
  have hsizeArray :=
    Luffs.Runtime.TLSF.representsPhysicalArrays_get_size hphysical hget
  have hselectedBytes : selected.bytes = returnedBytes := by
    rw [hsizeArray] at hbytes
    exact Option.some.inj hbytes
  have hfreeArray :=
    Luffs.Runtime.TLSF.representsPhysicalArrays_get_free hphysical hget
  have hallocated : selected.free = false := by
    rw [hfreeArray] at hfree
    cases hselectedFree : selected.free <;> simp [hselectedFree] at hfree ⊢
  have hdealloc' : Luffs.Runtime.TLSF.deallocateArrays
      offsets sizes isFree prevFree second first heads next previous
      count i selected.offset selected.bytes = some result := by
    simpa [hselectedOffset, hselectedBytes] using hdealloc
  have hfresh := Luffs.Runtime.TLSF.allocatedBlock_offset_fresh hvalid hget
    hallocated
  obtain ⟨abstractNext, habstract, howns⟩ :=
    Luffs.Runtime.TLSF.deallocateArrays_ownsFree
      (PROP := PROP) hget hallocated hphysical hvalid hpoolMax
      hcountMax hsecond hfirst hbins hdisjoint hfresh hdealloc'
  have hfindPhysical : Bins.findPhysicalIndex blocks selected = some i := by
    rw [← Luffs.Runtime.TLSF.findOffsetIndex_refines_findPhysicalIndex_represented
      (target := selected) (actual := selected) hphysical hvalid.1
      (List.mem_iff_getElem?.2 ⟨i, hget⟩) (Bins.samePhysical_refl selected)]
    simpa [hselectedOffset] using hfind
  have hboxDrop : Luffs.Containers.Box.drop pool
      { physical := blocks, bins := state } selected = some abstractNext := by
    simp [Luffs.Containers.Box.drop, hfindPhysical, habstract]
  exact ⟨selected, abstractNext, hselectedOffset,
    List.mem_iff_getElem?.2 ⟨i, hget⟩, hboxDrop, howns⟩

set_option maxHeartbeats 1200000 in
theorem boxDropPointerU8Arrays_refines_box
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {pointer : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxDropPointerU8Arrays offsets sizes isFree prevFree count
      second first heads next previous pool.base pool.bytes pointer = some result) :
    ∃ (selected : Block) (abstractNext : Alloc.State),
      pointer = pool.base + selected.offset ∧ selected ∈ blocks ∧
      Luffs.Containers.Box.drop pool
          { physical := blocks, bins := state } selected = some abstractNext ∧
      (OwnsBytes (PROP := Iris.IProp GF) (selected.region pool) ∗
          Ownership.OwnsFree pool blocks ⊣⊢
        Ownership.OwnsFree pool abstractNext.physical) := by
  obtain ⟨offset, hpointer, _, hdrop⟩ :=
    boxDropPointerU8Arrays_result hsuccess
  obtain ⟨selected, abstractNext, hselectedOffset, hmember, habstract, howns⟩ :=
    boxDropU8Arrays_refines_box (PROP := Iris.IProp GF) hvalid hpoolMax hcountMax hsecond
      hfirst hbins hdisjoint hphysical hdrop
  exact ⟨selected, abstractNext, by rw [hpointer, ← hselectedOffset], hmember,
    habstract, howns⟩

theorem boxDropU8Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {returnedOffset : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxDropU8Arrays
      offsets sizes isFree prevFree count second first
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
  obtain ⟨selected, abstractNext, hoffset, _, hdrop, _⟩ :=
    boxDropU8Arrays_refines_box (PROP := Iris.IProp GF) hvalid hpoolMax hcountMax hsecond
      hfirst hbins hdisjoint hphysical hsuccess
  refine ⟨selected, abstractNext, hoffset, ?_⟩
  intro value contents
  exact Luffs.Containers.Box.drop_owns Scalar.u8 value contents hdrop

/-- Codec-generic executable allocation boundary for Vec. The two guards are
the source-level `checked_mul` and rounding-addition checks needed before the
TLSF request is formed on a 64-bit target. -/
def vecNewArrays {α : Type} (codec : Codec α) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (capacity : Nat) :
    Option Luffs.Runtime.TLSF.AllocateArraysResult :=
  if capacity = 0 ∨ capacity > Luffs.Runtime.TLSF.usizeMax / codec.size then none
  else if capacity * codec.size > Luffs.Runtime.TLSF.usizeMax - 7 then none
  else Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
    second first heads next previous
      (Luffs.Containers.Vec.allocationBytes codec capacity)

theorem vecNewArrays_result {α : Type} {codec : Codec α}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {capacity : Nat}
    {result : Luffs.Runtime.TLSF.AllocateArraysResult}
    (hsuccess : vecNewArrays codec offsets sizes isFree prevFree count second
      first heads next previous capacity = some result) :
    0 < capacity ∧
      capacity ≤ Luffs.Runtime.TLSF.usizeMax / codec.size ∧
      capacity * codec.size ≤ Luffs.Runtime.TLSF.usizeMax - 7 ∧
      Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
        second first heads next previous
          (Luffs.Containers.Vec.allocationBytes codec capacity) = some result := by
  unfold vecNewArrays at hsuccess
  split at hsuccess
  next hbad => contradiction
  next hmul =>
    split at hsuccess
    next hround => contradiction
    next hround =>
      exact ⟨Nat.pos_of_ne_zero (fun hzero => hmul (Or.inl hzero)),
        Nat.le_of_not_gt (fun hlarge => hmul (Or.inr hlarge)),
        Nat.le_of_not_gt hround, hsuccess⟩

set_option maxHeartbeats 1200000 in
theorem vecNewArrays_refines_vec
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [Luffs.Memory.ByteContentsGS GF] {α : Type} {codec : Codec α}
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {capacity : Nat}
    {result : Luffs.Runtime.TLSF.AllocateArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : vecNewArrays codec offsets sizes isFree prevFree count second
      first heads next previous capacity = some result) :
    ∃ (hcapacity : 0 < capacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes codec capacity) <
            2 ^ firstLevelCount)
        (vecResult : Luffs.Containers.Vec.AllocResult),
      Luffs.Containers.Vec.allocate codec capacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some vecResult ∧
      result.allocatedOffset = vecResult.handle.block.offset ∧
      result.allocatedBytes = vecResult.handle.block.bytes ∧
      vecResult.handle.len = 0 ∧ vecResult.handle.capacity = capacity ∧
      (Ownership.OwnsFree (PROP := Iris.IProp GF) pool blocks ⊣⊢
        Luffs.Containers.Vec.Owns codec pool vecResult.handle [] ∗
          Ownership.OwnsFree pool vecResult.state.physical) := by
  obtain ⟨hcapacity, _, _, halloc⟩ := vecNewArrays_result hsuccess
  obtain ⟨_, hkeyMax, abstractResult, habstract, hoffset, hbytes,
      _, _, _, _, _, _, howns⟩ :=
    Luffs.Runtime.TLSF.allocateArrays_ownsFree
      (PROP := Iris.IProp GF) hvalid hsecond hfirst hbins hdisjoint hphysical
      halloc
  let vecResult : Luffs.Containers.Vec.AllocResult := {
    handle := ⟨abstractResult.allocated, 0, capacity⟩
    state := abstractResult.state }
  have hvec : Luffs.Containers.Vec.allocate codec capacity hcapacity
      { physical := blocks, bins := state } hkeyMax = some vecResult := by
    simp [Luffs.Containers.Vec.allocate, vecResult, habstract]
  refine ⟨hcapacity, hkeyMax, vecResult, hvec, ?_, ?_, rfl, rfl, ?_⟩
  · simpa [vecResult] using hoffset
  · simpa [vecResult] using hbytes
  · simpa [vecResult, Luffs.Containers.Vec.Owns,
      Luffs.Containers.Vec.encodeValues, PointsToBytes] using
        howns.trans (Iris.BI.sep_congr_left Iris.BI.sep_emp.symm)

def vecNewU8Arrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (capacity : Nat) :
    Option Luffs.Runtime.TLSF.AllocateArraysResult :=
  if capacity = 0 ∨ capacity > Luffs.Runtime.TLSF.usizeMax - 7 then none
  else Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
    second first heads next previous
      (Luffs.Containers.Vec.allocationBytes Scalar.u8 capacity)

theorem vecNewU8Arrays_eq_generic :
    vecNewU8Arrays = vecNewArrays Scalar.u8 := by
  funext offsets sizes isFree prevFree count second first heads next previous capacity
  simp only [vecNewU8Arrays, vecNewArrays, Scalar.u8, Scalar.encode8]
  by_cases hzero : capacity = 0
  · simp [hzero]
  · by_cases hlarge : capacity > Luffs.Runtime.TLSF.usizeMax - 7
    · have hover : capacity * 1 > Luffs.Runtime.TLSF.usizeMax - 7 := by omega
      simp [hzero, hlarge, hover]
    · have hmax : capacity ≤ Luffs.Runtime.TLSF.usizeMax := by
        unfold Luffs.Runtime.TLSF.usizeMax at hlarge ⊢
        omega
      have hmul : ¬capacity * 1 > Luffs.Runtime.TLSF.usizeMax - 7 := by omega
      have hnmax : ¬Luffs.Runtime.TLSF.usizeMax < capacity :=
        Nat.not_lt_of_ge hmax
      simp [hzero, hlarge, hnmax, hmul]

theorem vecNewU8Arrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {capacity : Nat}
    {result : Luffs.Runtime.TLSF.AllocateArraysResult}
    (hsuccess : vecNewU8Arrays offsets sizes isFree prevFree count second first
      heads next previous capacity = some result) :
    0 < capacity ∧ capacity ≤ Luffs.Runtime.TLSF.usizeMax - 7 ∧
      Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
        second first heads next previous
          (Luffs.Containers.Vec.allocationBytes Scalar.u8 capacity) =
            some result := by
  unfold vecNewU8Arrays at hsuccess
  split at hsuccess
  next hbad => contradiction
  next hgood =>
    exact ⟨Nat.pos_of_ne_zero (fun hzero => hgood (Or.inl hzero)),
      Nat.le_of_not_gt (fun hlarge => hgood (Or.inr hlarge)), hsuccess⟩

set_option maxHeartbeats 1200000 in
theorem vecNewU8Arrays_refines_vec
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {capacity : Nat}
    {result : Luffs.Runtime.TLSF.AllocateArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : vecNewU8Arrays
      offsets sizes isFree prevFree count second first
      heads next previous capacity = some result) :
    ∃ (hcapacity : 0 < capacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes Scalar.u8 capacity) <
            2 ^ firstLevelCount)
        (vecResult : Luffs.Containers.Vec.AllocResult),
      Luffs.Containers.Vec.allocate Scalar.u8 capacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some vecResult ∧
      result.allocatedOffset = vecResult.handle.block.offset ∧
      result.allocatedBytes = vecResult.handle.block.bytes ∧
      vecResult.handle.len = 0 ∧ vecResult.handle.capacity = capacity ∧
      (Ownership.OwnsFree (PROP := Iris.IProp GF) pool blocks ⊣⊢
        Luffs.Containers.Vec.Owns Scalar.u8 pool vecResult.handle [] ∗
          Ownership.OwnsFree pool vecResult.state.physical) := by
  have hgeneric : vecNewArrays Scalar.u8 offsets sizes isFree prevFree count
      second first heads next previous capacity = some result := by
    simpa only [← vecNewU8Arrays_eq_generic] using hsuccess
  exact vecNewArrays_refines_vec hvalid hsecond hfirst hbins hdisjoint
    hphysical hgeneric

structure VecPushU8OffsetResult where
  storage : List Byte
  nextLen : Nat
deriving DecidableEq, Repr

def vecPushU8Offset (storage : List Byte) (offset len capacity : Nat)
    (value : Byte) : Option VecPushU8OffsetResult :=
  if len ≥ capacity then none
  else if offset + len ≥ 2 ^ 64 then none
  else
    let index := offset + len
    if index ≥ storage.length then none
    else some ⟨storage.set index value, len + 1⟩

theorem vecPushU8Offset_result
    {storage : List Byte} {offset len capacity : Nat} {value : Byte}
    {result : VecPushU8OffsetResult}
    (hsuccess : vecPushU8Offset storage offset len capacity value =
      some result) :
    len < capacity ∧ offset + len < 2 ^ 64 ∧
      offset + len < storage.length ∧
      result.storage = storage.set (offset + len) value ∧
      result.nextLen = len + 1 := by
  by_cases hlen : len ≥ capacity
  · simp [vecPushU8Offset, hlen] at hsuccess
  · by_cases hoverflow : offset + len ≥ 2 ^ 64
    · simp [vecPushU8Offset, hlen, hoverflow] at hsuccess
    · by_cases hbound : offset + len ≥ storage.length
      · simp [vecPushU8Offset, hlen, hoverflow, hbound] at hsuccess
      · simp [vecPushU8Offset, hlen, hoverflow, hbound] at hsuccess
        subst result
        exact ⟨Nat.lt_of_not_ge hlen, Nat.lt_of_not_ge hoverflow,
          Nat.lt_of_not_ge hbound, rfl, rfl⟩

theorem vecPushU8Offset_refines_handle
    {storage : List Byte} {handle : Luffs.Containers.Vec.Handle}
    {value : Byte} {result : VecPushU8OffsetResult}
    (hsuccess : vecPushU8Offset storage handle.block.offset handle.len
      handle.capacity value = some result) :
    Luffs.Containers.Vec.push handle =
      some { handle with len := result.nextLen } := by
  have hresult := vecPushU8Offset_result hsuccess
  simp [Luffs.Containers.Vec.push, hresult.1, hresult.2.2.2.2]

theorem vecPushU8Offset_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {handle : Luffs.Containers.Vec.Handle}
    {storage : List Byte} {values : List (BitVec 8)} {value : Byte}
    {result : VecPushU8OffsetResult}
    (hlen : values.length = handle.len)
    (hsuccess : vecPushU8Offset storage handle.block.offset handle.len
      handle.capacity value = some result) :
    ∃ next,
      Luffs.Containers.Vec.push handle = some next ∧
      (handle.block.region pool).base +
          (Luffs.Containers.Vec.encodeValues Scalar.u8 values).length =
        pool.base + (handle.block.offset + handle.len) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues Scalar.u8 values).length)
          (Scalar.u8.encode (Scalar.bv8OfByte value)) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns Scalar.u8 pool handle values ==∗
          contentsInterp (insertBytes contents
              ((handle.block.region pool).base +
                (Luffs.Containers.Vec.encodeValues Scalar.u8 values).length)
              (Scalar.u8.encode (Scalar.bv8OfByte value))) ∗
            Luffs.Containers.Vec.Owns Scalar.u8 pool next
              (values ++ [Scalar.bv8OfByte value]) := by
  let next := { handle with len := result.nextLen }
  have hpush : Luffs.Containers.Vec.push handle = some next := by
    exact vecPushU8Offset_refines_handle hsuccess
  have haddress : (handle.block.region pool).base +
      (Luffs.Containers.Vec.encodeValues Scalar.u8 values).length =
      pool.base + (handle.block.offset + handle.len) := by
    rw [Luffs.Containers.Vec.encodeValues_length, hlen]
    simp [Block.region, Scalar.u8, Nat.add_assoc]
  refine ⟨next, hpush, haddress, ?_⟩
  intro contents hfresh
  exact Luffs.Containers.Vec.push_owns Scalar.u8
    (Scalar.bv8OfByte value) contents hpush hfresh

def vecGetU8Offset (storage : List Byte) (offset len index : Nat) :
    Option Byte :=
  if index ≥ len then none
  else if offset + index ≥ 2 ^ 64 then none
  else
    let address := offset + index
    if address ≥ storage.length then none else storage[address]?

theorem vecGetU8Offset_result
    {storage : List Byte} {offset len index : Nat} {value : Byte}
    (hget : vecGetU8Offset storage offset len index = some value) :
    index < len ∧ offset + index < 2 ^ 64 ∧
      offset + index < storage.length ∧
      storage[offset + index]? = some value := by
  by_cases hindex : index ≥ len
  · simp [vecGetU8Offset, hindex] at hget
  · by_cases hoverflow : offset + index ≥ 2 ^ 64
    · simp [vecGetU8Offset, hindex, hoverflow] at hget
    · by_cases hbound : offset + index ≥ storage.length
      · simp [vecGetU8Offset, hindex, hoverflow, hbound] at hget
      · exact ⟨Nat.lt_of_not_ge hindex, Nat.lt_of_not_ge hoverflow,
          Nat.lt_of_not_ge hbound, by
            simpa [vecGetU8Offset, hindex, hoverflow, hbound] using hget⟩

theorem vecDropU8Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {offset len capacity : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxDropU8Arrays
      offsets sizes isFree prevFree count second first
      heads next previous offset = some result) :
    ∃ (handle : Luffs.Containers.Vec.Handle) (abstractNext : Alloc.State),
      handle.block.offset = offset ∧ handle.len = len ∧
      handle.capacity = capacity ∧
      Luffs.Containers.Vec.drop pool
          { physical := blocks, bins := state } handle = some abstractNext ∧
      ∀ (values : List (BitVec 8)) (contents : ContentsMap),
        values.length = len →
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Vec.Owns Scalar.u8 pool handle values ∗
              Ownership.OwnsFree pool blocks) ==∗
          contentsInterp
              (deleteBytes contents (handle.block.region pool).base
                (Luffs.Containers.Vec.encodeValues Scalar.u8 values)) ∗
            Ownership.OwnsFree pool abstractNext.physical := by
  obtain ⟨selected, abstractNext, hoffset, _, hdrop, _⟩ :=
    boxDropU8Arrays_refines_box (PROP := Iris.IProp GF) hvalid hpoolMax hcountMax hsecond
      hfirst hbins hdisjoint hphysical hsuccess
  let handle : Luffs.Containers.Vec.Handle := ⟨selected, len, capacity⟩
  have hvecDrop : Luffs.Containers.Vec.drop pool
      { physical := blocks, bins := state } handle = some abstractNext := by
    simpa [Luffs.Containers.Vec.drop, handle] using hdrop
  refine ⟨handle, abstractNext, by simpa [handle] using hoffset,
    rfl, rfl, hvecDrop, ?_⟩
  intro values contents _
  exact Luffs.Containers.Vec.drop_owns Scalar.u8 values contents hvecDrop

theorem vecDropPointerU8Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {pointer len capacity : Nat}
    {result : Luffs.Runtime.TLSF.CoalesceClassResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxDropPointerU8Arrays offsets sizes isFree prevFree count
      second first heads next previous pool.base pool.bytes pointer = some result) :
    ∃ (handle : Luffs.Containers.Vec.Handle) (abstractNext : Alloc.State),
      pointer = pool.base + handle.block.offset ∧ handle.len = len ∧
      handle.capacity = capacity ∧
      Luffs.Containers.Vec.drop pool
          { physical := blocks, bins := state } handle = some abstractNext ∧
      ∀ (values : List (BitVec 8)) (contents : ContentsMap),
        values.length = len →
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Vec.Owns Scalar.u8 pool handle values ∗
              Ownership.OwnsFree pool blocks) ==∗
          contentsInterp
              (deleteBytes contents (handle.block.region pool).base
                (Luffs.Containers.Vec.encodeValues Scalar.u8 values)) ∗
            Ownership.OwnsFree pool abstractNext.physical := by
  obtain ⟨offset, hpointer, _, hdrop⟩ :=
    boxDropPointerU8Arrays_result hsuccess
  obtain ⟨handle, abstractNext, hoffset, hlen, hcapacity, hdropAbstract,
      howns⟩ := vecDropU8Arrays_owns (GF := GF) hvalid hpoolMax hcountMax
        hsecond hfirst hbins hdisjoint hphysical hdrop
  exact ⟨handle, abstractNext, hpointer.trans (congrArg (pool.base + ·)
    hoffset.symm), hlen, hcapacity, hdropAbstract, howns⟩

def copyByteRange (storage : List Byte) (source destination : Nat) :
    Nat → Option (List Byte)
  | 0 => some storage
  | n + 1 => do
      let copied ← copyByteRange storage source destination n
      let byte ← storage[source + n]?
      if destination + n ≥ storage.length then none
      pure (copied.set (destination + n) byte)

theorem copyByteRange_result
    {storage copied : List Byte} {source destination len : Nat}
    (hcopy : copyByteRange storage source destination len = some copied) :
    copied.length = storage.length ∧
      (∀ i, i < len →
        copied[destination + i]? = storage[source + i]?) ∧
      (∀ j, (j < destination ∨ destination + len ≤ j) →
        copied[j]? = storage[j]?) := by
  induction len generalizing copied with
  | zero =>
      simp [copyByteRange] at hcopy
      subst copied
      simp
  | succ n ih =>
      simp only [copyByteRange] at hcopy
      cases hprefix : copyByteRange storage source destination n with
      | none => simp [hprefix] at hcopy
      | some copiedPrefix =>
        cases hbyte : storage[source + n]? with
        | none => simp [hprefix, hbyte] at hcopy
        | some byte =>
          by_cases hbound : destination + n ≥ storage.length
          · simp [hprefix, hbyte, hbound] at hcopy
          · simp [hprefix, hbyte, hbound] at hcopy
            subst copied
            obtain ⟨hlength, hpref, houtside⟩ := ih hprefix
            have hdest : destination + n < copiedPrefix.length := by
              rw [hlength]
              exact Nat.lt_of_not_ge hbound
            refine ⟨by simp [hlength], ?_, ?_⟩
            · intro i hi
              by_cases heq : i = n
              · subst i
                simp [List.getElem?_set_self hdest, hbyte]
              · have hin : i < n := by omega
                have hne : destination + i ≠ destination + n := by omega
                rw [List.getElem?_set_ne (Ne.symm hne)]
                exact hpref i hin
            · intro j hj
              have hne : j ≠ destination + n := by
                rcases hj with hleft | hright <;> omega
              rw [List.getElem?_set_ne (Ne.symm hne)]
              apply houtside j
              rcases hj with hleft | hright
              · exact Or.inl hleft
              · exact Or.inr (by omega)

structure VecGrowU8ArraysResult where
  allocator : Luffs.Runtime.TLSF.CoalesceClassResult
  storage : List Byte
  newOffset : Nat
  allocatedBytes : Nat
deriving DecidableEq, Repr

/-- Exact state transformer for `tlsf_vec_grow_u8`: validate the old live
prefix, allocate a replacement, copy from the old prefix snapshot, and only
then return the old block to TLSF. -/
def vecGrowU8Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (oldOffset len oldCapacity newCapacity : Nat) :
    Option VecGrowU8ArraysResult := do
  if len > oldCapacity ∨ newCapacity ≤ oldCapacity ∨
      newCapacity > Luffs.Runtime.TLSF.usizeMax - 7 then none
  if oldOffset + len ≥ 2 ^ 64 ∨ oldOffset + len > storage.length then none
  let allocated ← Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
    prevFree count second first heads next previous
      (Luffs.Containers.Vec.allocationBytes Scalar.u8 newCapacity)
  if allocated.allocatedOffset + len ≥ 2 ^ 64 ∨
      allocated.allocatedOffset + len > storage.length then none
  let copied ← copyByteRange storage oldOffset allocated.allocatedOffset len
  let released ← boxDropU8Arrays allocated.offsets allocated.sizes
    allocated.isFree allocated.prevFree allocated.count allocated.second
    allocated.first allocated.heads allocated.next allocated.previous oldOffset
  pure ⟨released, copied, allocated.allocatedOffset, allocated.allocatedBytes⟩

theorem vecGrowU8Arrays_result
    {storage : List Byte} {offsets sizes : List Nat}
    {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {oldOffset len oldCapacity newCapacity : Nat}
    {result : VecGrowU8ArraysResult}
    (hsuccess : vecGrowU8Arrays storage offsets sizes isFree prevFree count
      second first heads next previous oldOffset len oldCapacity newCapacity =
        some result) :
    ∃ allocated copied released,
      len ≤ oldCapacity ∧ oldCapacity < newCapacity ∧
      newCapacity ≤ Luffs.Runtime.TLSF.usizeMax - 7 ∧
      oldOffset + len < 2 ^ 64 ∧ oldOffset + len ≤ storage.length ∧
      Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
        second first heads next previous
          (Luffs.Containers.Vec.allocationBytes Scalar.u8 newCapacity) =
            some allocated ∧
      allocated.allocatedOffset + len < 2 ^ 64 ∧
      allocated.allocatedOffset + len ≤ storage.length ∧
      copyByteRange storage oldOffset allocated.allocatedOffset len = some copied ∧
      boxDropU8Arrays allocated.offsets allocated.sizes allocated.isFree
        allocated.prevFree allocated.count allocated.second allocated.first
        allocated.heads allocated.next allocated.previous oldOffset =
          some released ∧
      result = ⟨released, copied, allocated.allocatedOffset,
        allocated.allocatedBytes⟩ := by
  let badPre := len > oldCapacity ∨ newCapacity ≤ oldCapacity ∨
    newCapacity > Luffs.Runtime.TLSF.usizeMax - 7
  let badOld := oldOffset + len ≥ 2 ^ 64 ∨
    oldOffset + len > storage.length
  by_cases hpre : badPre
  · simp [vecGrowU8Arrays, badPre, hpre] at hsuccess
  · by_cases hold : badOld
    · simp [vecGrowU8Arrays, badPre, badOld, hpre, hold] at hsuccess
    · cases halloc : Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
          prevFree count second first heads next previous
            (Luffs.Containers.Vec.allocationBytes Scalar.u8 newCapacity) with
      | none =>
          simp [vecGrowU8Arrays, badPre, badOld, hpre, hold, halloc] at hsuccess
      | some allocated =>
        let badNew := allocated.allocatedOffset + len ≥ 2 ^ 64 ∨
          allocated.allocatedOffset + len > storage.length
        by_cases hnew : badNew
        · simp [vecGrowU8Arrays, badPre, badOld, badNew, hpre, hold,
            halloc, hnew] at hsuccess
        · cases hcopy : copyByteRange storage oldOffset
              allocated.allocatedOffset len with
          | none =>
            simp [vecGrowU8Arrays, badPre, badOld, badNew, hpre, hold,
              halloc, hnew, hcopy] at hsuccess
          | some copied =>
            cases hdrop : boxDropU8Arrays allocated.offsets allocated.sizes
                allocated.isFree allocated.prevFree allocated.count
                allocated.second allocated.first allocated.heads allocated.next
                allocated.previous oldOffset with
            | none =>
              simp [vecGrowU8Arrays, badPre, badOld, badNew, hpre, hold,
                halloc, hnew, hcopy, hdrop] at hsuccess
            | some released =>
              simp [vecGrowU8Arrays, badPre, badOld, badNew, hpre, hold,
                halloc, hnew, hcopy, hdrop] at hsuccess
              subst result
              have hlen : len ≤ oldCapacity :=
                Nat.le_of_not_gt (fun h => hpre (Or.inl h))
              have hcapacity : oldCapacity < newCapacity :=
                Nat.lt_of_not_ge (fun h => hpre (Or.inr (Or.inl h)))
              have hmax : newCapacity ≤ Luffs.Runtime.TLSF.usizeMax - 7 :=
                Nat.le_of_not_gt (fun h => hpre (Or.inr (Or.inr h)))
              have hold64 : oldOffset + len < 2 ^ 64 :=
                Nat.lt_of_not_ge (fun h => hold (Or.inl h))
              have holdBound : oldOffset + len ≤ storage.length :=
                Nat.le_of_not_gt (fun h => hold (Or.inr h))
              have hnew64 : allocated.allocatedOffset + len < 2 ^ 64 :=
                Nat.lt_of_not_ge (fun h => hnew (Or.inl h))
              have hnewBound : allocated.allocatedOffset + len ≤ storage.length :=
                Nat.le_of_not_gt (fun h => hnew (Or.inr h))
              exact ⟨allocated, copied, released, hlen, hcapacity, hmax,
                hold64, holdBound, rfl, hnew64, hnewBound, hcopy, hdrop, rfl⟩

theorem vecGrowU8Arrays_copies_prefix
    {storage : List Byte} {offsets sizes : List Nat}
    {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {oldOffset len oldCapacity newCapacity : Nat}
    {result : VecGrowU8ArraysResult}
    (hsuccess : vecGrowU8Arrays storage offsets sizes isFree prevFree count
      second first heads next previous oldOffset len oldCapacity newCapacity =
        some result) :
    result.storage.length = storage.length ∧
      (∀ i, i < len →
        result.storage[result.newOffset + i]? = storage[oldOffset + i]?) ∧
      (∀ j, (j < result.newOffset ∨ result.newOffset + len ≤ j) →
        result.storage[j]? = storage[j]?) := by
  obtain ⟨allocated, copied, released, _, _, _, _, _, _, _, _, hcopy, _,
      hresult⟩ := vecGrowU8Arrays_result hsuccess
  subst result
  simpa using copyByteRange_result hcopy

set_option maxHeartbeats 1600000 in
/-- Successful concrete allocator-backed byte growth is the abstract verified
Vec growth transition. In particular, allocation preserves the old live
block, the copied destination is the newly allocated block, and the final
deallocation targets the preserved old block even if its intrusive links were
updated by allocation. -/
theorem vecGrowU8Arrays_refines_vec
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat}
    {handle : Luffs.Containers.Vec.Handle} {newCapacity : Nat}
    {result : VecGrowU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysicalInput : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hmember : handle.block ∈ blocks)
    (hallocated : handle.block.free = false)
    (harrayMax : offsets.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsuccess : vecGrowU8Arrays storage
      offsets sizes isFree prevFree count second first
      heads next previous handle.block.offset handle.len handle.capacity
      newCapacity = some result) :
    ∃ (hcapacity : 0 < newCapacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes Scalar.u8 newCapacity) <
            2 ^ firstLevelCount)
        (growResult : Luffs.Containers.Vec.GrowResult),
      Luffs.Containers.Vec.grow Scalar.u8 pool handle newCapacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some growResult ∧
      result.newOffset = growResult.handle.block.offset ∧
      growResult.handle.len = handle.len ∧
      growResult.handle.capacity = newCapacity := by
  obtain ⟨concreteAllocated, copied, released, _, hcapacityLt, _, _, _,
      hconcreteAlloc, _, _, _, hconcreteDrop, rfl⟩ :=
    vecGrowU8Arrays_result hsuccess
  obtain ⟨_, hkeyMax, abstractAllocated, habstractAlloc, hoffset, _,
      hphysical, hbinsValid, hpostBins, hpostDisjoint, hpostSecond,
      hpostFirst, _⟩ :=
    Luffs.Runtime.TLSF.allocateArrays_ownsFree
      (PROP := PROP) hvalid hsecond hfirst hbins hdisjoint
      hphysicalInput
      hconcreteAlloc
  have hcapacity : 0 < newCapacity := by omega
  have hpostValid : Alloc.Valid pool abstractAllocated.state :=
    Alloc.allocate_preserves_valid hvalid
      (Luffs.Containers.Box.requestBytes_aligned (newCapacity * Scalar.u8.size))
      habstractAlloc
  have hpostCountMax : concreteAllocated.count ≤
      Luffs.Runtime.TLSF.usizeMax := by
    have hcount := Luffs.Runtime.TLSF.allocateArrays_count_le_offsets
      hconcreteAlloc
    exact Nat.le_trans hcount harrayMax
  obtain ⟨updated, hupdated, hsame, _⟩ :=
    Alloc.allocate_preserves_allocated hvalid habstractAlloc hmember hallocated
  have hupdatedAllocated : updated.free = false :=
    (Bins.samePhysical_free hsame).trans hallocated
  obtain ⟨selected, abstractNext, hselectedOffset, hselectedMember,
      hdropSelected, _⟩ :=
    boxDropU8Arrays_refines_box (PROP := PROP) hpostValid hpoolMax
      hpostCountMax hpostSecond hpostFirst
      hpostBins hpostDisjoint hphysical hconcreteDrop
  have hupdatedOffset : updated.offset = handle.block.offset := hsame.1
  have hselectedEq : selected = updated := by
    apply wellFormed_same_offset hpostValid.1 hselectedMember hupdated
    rw [hselectedOffset, hupdatedOffset]
  subst selected
  have hdropOld : Luffs.Containers.Vec.drop pool abstractAllocated.state
      handle = some abstractNext := by
    unfold Luffs.Containers.Vec.drop
    unfold Luffs.Containers.Box.drop at hdropSelected ⊢
    have hfind := Bins.findPhysicalIndex_congr_target
      (physical := abstractAllocated.state.physical) hsame
    have hregion := Bins.samePhysical_region hsame pool
    rw [← hfind, ← hregion]
    exact hdropSelected
  let vecAllocated : Luffs.Containers.Vec.AllocResult := {
    handle := ⟨abstractAllocated.allocated, 0, newCapacity⟩
    state := abstractAllocated.state }
  have hvecAllocate : Luffs.Containers.Vec.allocate Scalar.u8 newCapacity
      hcapacity { physical := blocks, bins := state } hkeyMax =
        some vecAllocated := by
    simp [Luffs.Containers.Vec.allocate, vecAllocated, habstractAlloc]
  let growResult : Luffs.Containers.Vec.GrowResult := {
    handle := ⟨abstractAllocated.allocated, handle.len, newCapacity⟩
    state := abstractNext }
  have hgrow : Luffs.Containers.Vec.grow Scalar.u8 pool handle newCapacity
      hcapacity { physical := blocks, bins := state } hkeyMax =
        some growResult := by
    simp [Luffs.Containers.Vec.grow, hvecAllocate, vecAllocated, hdropOld,
      growResult]
  exact ⟨hcapacity, hkeyMax, growResult, hgrow, by
    simpa [growResult] using hoffset, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- Iris ownership law inherited by the concrete allocator-backed byte growth
transaction: one old Vec capability and allocator capability become exactly
one replacement Vec capability and the post-coalescing allocator capability. -/
theorem vecGrowU8Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat}
    {handle : Luffs.Containers.Vec.Handle} {newCapacity : Nat}
    {result : VecGrowU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysicalInput : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hmember : handle.block ∈ blocks)
    (hallocated : handle.block.free = false)
    (harrayMax : offsets.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsuccess : vecGrowU8Arrays storage
      offsets sizes isFree prevFree count second first
      heads next previous handle.block.offset handle.len handle.capacity
      newCapacity = some result) :
    ∃ (hcapacity : 0 < newCapacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes Scalar.u8 newCapacity) <
            2 ^ firstLevelCount)
        (growResult : Luffs.Containers.Vec.GrowResult),
      Luffs.Containers.Vec.grow Scalar.u8 pool handle newCapacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some growResult ∧
      result.newOffset = growResult.handle.block.offset ∧
      ∀ (values : List (BitVec 8)) (contents : ContentsMap),
        CanInsertBytes contents (growResult.handle.block.region pool).base
          (Luffs.Containers.Vec.encodeValues Scalar.u8 values) →
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Vec.Owns Scalar.u8 pool handle values ∗
              Ownership.OwnsFree pool blocks) ==∗
          contentsInterp
              (deleteBytes
                (insertBytes contents
                  (growResult.handle.block.region pool).base
                  (Luffs.Containers.Vec.encodeValues Scalar.u8 values))
                (handle.block.region pool).base
                (Luffs.Containers.Vec.encodeValues Scalar.u8 values)) ∗
            (Luffs.Containers.Vec.Owns Scalar.u8 pool growResult.handle values ∗
              Ownership.OwnsFree pool growResult.state.physical) := by
  obtain ⟨hcapacity, hkeyMax, growResult, hgrow, hoffset, _, _⟩ :=
    vecGrowU8Arrays_refines_vec (PROP := Iris.IProp GF) hvalid hpoolMax hsecond hfirst
      hbins hdisjoint hphysicalInput hmember hallocated harrayMax hsuccess
  refine ⟨hcapacity, hkeyMax, growResult, hgrow, hoffset, ?_⟩
  intro values contents hfresh
  obtain ⟨allocated, next, halloc, hdrop, hresult⟩ :=
    Luffs.Containers.Vec.grow_result hgrow
  subst growResult
  exact Luffs.Containers.Vec.grow_owns_step Scalar.u8 hvalid halloc hdrop
    values contents hfresh

set_option maxHeartbeats 1800000 in
/-- End-to-end growth theorem for the concrete Luffs byte Vec. It combines the
source-derived pool-array copy/frame law, abstract allocator/Vec refinement,
Iris ownership transfer, and the operational load/store trace for the same
initialized byte prefix. -/
theorem vecGrowU8Arrays_owns_with_copy
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat}
    {handle : Luffs.Containers.Vec.Handle} {newCapacity : Nat}
    {result : VecGrowU8ArraysResult}
    (hhandle : Luffs.Containers.Vec.Valid Scalar.u8 handle)
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins
      { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysicalInput : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hmember : handle.block ∈ blocks)
    (hallocated : handle.block.free = false)
    (harrayMax : offsets.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsuccess : vecGrowU8Arrays storage
      offsets sizes isFree prevFree count second first
      heads next previous handle.block.offset handle.len handle.capacity
      newCapacity = some result) :
    ∃ (hcapacity : 0 < newCapacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes Scalar.u8 newCapacity) <
            2 ^ firstLevelCount)
        (growResult : Luffs.Containers.Vec.GrowResult),
      Luffs.Containers.Vec.grow Scalar.u8 pool handle newCapacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some growResult ∧
      result.newOffset = growResult.handle.block.offset ∧
      result.storage.length = storage.length ∧
      (∀ i, i < handle.len →
        result.storage[result.newOffset + i]? =
          storage[handle.block.offset + i]?) ∧
      (∀ j, (j < result.newOffset ∨ result.newOffset + handle.len ≤ j) →
        result.storage[j]? = storage[j]?) ∧
      ∀ (values : List (BitVec 8)) (contents : ContentsMap) (mem : Memory),
        values.length = handle.len → ContentsRep contents mem →
        (∀ i, i < (Luffs.Containers.Vec.encodeValues Scalar.u8 values).length →
          mem.mapped ((growResult.handle.block.region pool).base + i)) →
        CanInsertBytes contents (growResult.handle.block.region pool).base
          (Luffs.Containers.Vec.encodeValues Scalar.u8 values) →
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Vec.Owns Scalar.u8 pool handle values ∗
              Ownership.OwnsFree pool blocks) ==∗
          (contentsInterp
              (deleteBytes
                (insertBytes contents
                  (growResult.handle.block.region pool).base
                  (Luffs.Containers.Vec.encodeValues Scalar.u8 values))
                (handle.block.region pool).base
                (Luffs.Containers.Vec.encodeValues Scalar.u8 values)) ∗
            (Luffs.Containers.Vec.Owns Scalar.u8 pool growResult.handle values ∗
              Ownership.OwnsFree pool growResult.state.physical)) ∗
            ⌜∃ memNext, CopySteps (handle.block.region pool).base
              (growResult.handle.block.region pool).base
              (Luffs.Containers.Vec.encodeValues Scalar.u8 values) mem memNext⌝ := by
  have hcopy := vecGrowU8Arrays_copies_prefix hsuccess
  obtain ⟨_, _, _, hlenOld, hcapacityLt, _, _, _, _, _, _, _, _, _⟩ :=
    vecGrowU8Arrays_result hsuccess
  have hlenCapacity : handle.len ≤ newCapacity := by omega
  obtain ⟨hcapacity, hkeyMax, growResult, hgrow, hoffset, _, _⟩ :=
    vecGrowU8Arrays_refines_vec (PROP := Iris.IProp GF) hvalid hpoolMax hsecond hfirst
      hbins hdisjoint hphysicalInput hmember hallocated harrayMax hsuccess
  obtain ⟨vecAllocated, abstractNext, hvecAlloc, hdrop, hresult⟩ :=
    Luffs.Containers.Vec.grow_result hgrow
  subst growResult
  refine ⟨hcapacity, hkeyMax,
    { handle := ⟨vecAllocated.handle.block, handle.len, newCapacity⟩,
      state := abstractNext }, hgrow, hoffset, hcopy.1, hcopy.2.1,
    hcopy.2.2, ?_⟩
  intro values contents mem hlen hrep hdst hfresh
  exact Luffs.Containers.Vec.grow_owns_step_with_copy Scalar.u8 hhandle
    hlenCapacity hvalid hmember hallocated hvecAlloc hdrop values hlen
    contents mem hrep hdst hfresh

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
