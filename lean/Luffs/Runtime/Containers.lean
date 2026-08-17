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

theorem writeBytes_pair_eq_set {α : Type} (values : List α)
    (offset : Nat) (first second : α)
    (hbound : offset + 2 ≤ values.length) :
    values.take offset ++ [first, second] ++ values.drop (offset + 2) =
      (values.set offset first).set (offset + 1) second := by
  induction values generalizing offset with
  | nil => simp at hbound
  | cons head tail ih =>
      cases offset with
      | zero =>
          cases tail with
          | nil => simp at hbound
          | cons oldSecond rest => simp
      | succ offset =>
          have htail : offset + 2 ≤ tail.length := by
            simp only [List.length_cons] at hbound
            omega
          simp only [List.take_succ_cons, List.drop_succ_cons, List.set,
            List.cons_append, List.cons.injEq, true_and]
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            ih offset htail

theorem writeBytes_four_eq_set {α : Type} (values : List α)
    (offset : Nat) (b0 b1 b2 b3 : α)
    (hbound : offset + 4 ≤ values.length) :
    values.take offset ++ [b0, b1, b2, b3] ++ values.drop (offset + 4) =
      (((values.set offset b0).set (offset + 1) b1).set
        (offset + 2) b2).set (offset + 3) b3 := by
  induction values generalizing offset with
  | nil => simp at hbound
  | cons head tail ih =>
      cases offset with
      | zero =>
          cases tail with
          | nil => simp at hbound
          | cons t1 tail =>
              cases tail with
              | nil => simp at hbound
              | cons t2 tail =>
                  cases tail with
                  | nil => simp at hbound
                  | cons t3 rest => simp
      | succ offset =>
          have htail : offset + 4 ≤ tail.length := by
            simp only [List.length_cons] at hbound
            omega
          simp only [List.take_succ_cons, List.drop_succ_cons, List.set,
            List.cons_append, List.cons.injEq, true_and]
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih offset htail

theorem writeBytes_eight_eq_set {α : Type} (values : List α)
    (offset : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : α)
    (hbound : offset + 8 ≤ values.length) :
    values.take offset ++ [b0, b1, b2, b3, b4, b5, b6, b7] ++
        values.drop (offset + 8) =
      (((((((values.set offset b0).set (offset + 1) b1).set
        (offset + 2) b2).set (offset + 3) b3).set
        (offset + 4) b4).set (offset + 5) b5).set
        (offset + 6) b6).set (offset + 7) b7 := by
  induction values generalizing offset with
  | nil => simp at hbound
  | cons head tail ih =>
      cases offset with
      | zero =>
          cases tail with
          | nil => simp at hbound
          | cons t1 tail =>
              cases tail with
              | nil => simp at hbound
              | cons t2 tail =>
                  cases tail with
                  | nil => simp at hbound
                  | cons t3 tail =>
                      cases tail with
                      | nil => simp at hbound
                      | cons t4 tail =>
                          cases tail with
                          | nil => simp at hbound
                          | cons t5 tail =>
                              cases tail with
                              | nil => simp at hbound
                              | cons t6 tail =>
                                  cases tail with
                                  | nil => simp at hbound
                                  | cons t7 rest => simp
      | succ offset =>
          have htail : offset + 8 ≤ tail.length := by
            simp only [List.length_cons] at hbound
            omega
          simp only [List.take_succ_cons, List.drop_succ_cons, List.set,
            List.cons_append, List.cons.injEq, true_and]
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih offset htail

theorem writeBytes_sixteen_eq_set {α : Type} (values : List α)
    (offset : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : α)
    (hbound : offset + 16 ≤ values.length) :
    values.take offset ++
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
          b15] ++ values.drop (offset + 16) =
      ((((((((((((((((values.set offset b0).set (offset + 1) b1).set
        (offset + 2) b2).set (offset + 3) b3).set (offset + 4) b4).set
        (offset + 5) b5).set (offset + 6) b6).set (offset + 7) b7).set
        (offset + 8) b8).set (offset + 9) b9).set (offset + 10) b10).set
        (offset + 11) b11).set (offset + 12) b12).set (offset + 13) b13).set
        (offset + 14) b14).set (offset + 15) b15) := by
  induction values generalizing offset with
  | nil => simp at hbound
  | cons head tail ih =>
      cases offset with
      | zero =>
          cases tail with
          | nil => simp at hbound
          | cons t1 tail =>
              cases tail with
              | nil => simp at hbound
              | cons t2 tail =>
                  cases tail with
                  | nil => simp at hbound
                  | cons t3 tail =>
                      cases tail with
                      | nil => simp at hbound
                      | cons t4 tail =>
                          cases tail with
                          | nil => simp at hbound
                          | cons t5 tail =>
                              cases tail with
                              | nil => simp at hbound
                              | cons t6 tail =>
                                  cases tail with
                                  | nil => simp at hbound
                                  | cons t7 tail =>
                                      cases tail with
                                      | nil => simp at hbound
                                      | cons t8 tail =>
                                          cases tail with
                                          | nil => simp at hbound
                                          | cons t9 tail =>
                                              cases tail with
                                              | nil => simp at hbound
                                              | cons t10 tail =>
                                                  cases tail with
                                                  | nil => simp at hbound
                                                  | cons t11 tail =>
                                                      cases tail with
                                                      | nil => simp at hbound
                                                      | cons t12 tail =>
                                                          cases tail with
                                                          | nil => simp at hbound
                                                          | cons t13 tail =>
                                                              cases tail with
                                                              | nil => simp at hbound
                                                              | cons t14 tail =>
                                                                  cases tail with
                                                                  | nil => simp at hbound
                                                                  | cons t15 rest => simp
      | succ offset =>
          have htail : offset + 16 ≤ tail.length := by
            simp only [List.length_cons] at hbound
            omega
          simp only [List.take_succ_cons, List.drop_succ_cons, List.set,
            List.cons_append, List.cons.injEq, true_and]
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih offset htail

theorem writeBytes_length (values : List Byte) (offset : Nat)
    (replacement : List Byte) (hbound : offset + replacement.length ≤ values.length) :
    (writeBytes values offset replacement).length = values.length := by
  simp [writeBytes, List.length_take, List.length_drop]
  omega

theorem writeBytes_read_back (values : List Byte) (offset : Nat)
    (replacement : List Byte) (hbound : offset + replacement.length ≤ values.length) :
    ((writeBytes values offset replacement).drop offset).take replacement.length =
      replacement := by
  induction values generalizing offset with
  | nil =>
      simp only [List.length_nil, Nat.le_zero] at hbound
      have hoffset : offset = 0 := by omega
      have hlength : replacement.length = 0 := by omega
      have hempty := List.eq_nil_of_length_eq_zero hlength
      subst offset
      subst replacement
      rfl
  | cons head tail ih =>
      cases offset with
      | zero => simp [writeBytes]
      | succ offset =>
          have htail : offset + replacement.length ≤ tail.length := by
            simp only [List.length_cons] at hbound
            omega
          simpa [writeBytes, Nat.succ_add] using ih offset htail

theorem drop_take_pair_of_getElem? {α : Type} (values : List α) (offset : Nat)
    (first second : α) (hfirst : values[offset]? = some first)
    (hsecond : values[offset + 1]? = some second) :
    (values.drop offset).take 2 = [first, second] := by
  induction values generalizing offset with
  | nil => simp at hfirst
  | cons head tail ih =>
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hfirst
          subst first
          cases tail with
          | nil => simp at hsecond
          | cons next rest =>
              simp only [Nat.zero_add, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at hsecond
              subst second
              simp
      | succ offset =>
          simp only [List.getElem?_cons_succ] at hfirst
          have hsecond' : tail[offset + 1]? = some second := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hsecond
          simp only [List.drop_succ_cons]
          exact ih offset hfirst hsecond'

theorem drop_take_four_of_getElem? {α : Type} (values : List α) (offset : Nat)
    (b0 b1 b2 b3 : α) (h0 : values[offset]? = some b0)
    (h1 : values[offset + 1]? = some b1)
    (h2 : values[offset + 2]? = some b2)
    (h3 : values[offset + 3]? = some b3) :
    (values.drop offset).take 4 = [b0, b1, b2, b3] := by
  induction values generalizing offset with
  | nil => simp at h0
  | cons head tail ih =>
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
          subst b0
          cases tail with
          | nil => simp at h1
          | cons next1 tail =>
              simp only [Nat.zero_add, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at h1
              subst b1
              cases tail with
              | nil => simp at h2
              | cons next2 tail =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                    Option.some.injEq] at h2
                  subst b2
                  cases tail with
                  | nil => simp at h3
                  | cons next3 rest =>
                      simp only [List.getElem?_cons_succ,
                        List.getElem?_cons_zero, Option.some.injEq] at h3
                      subst b3
                      simp
      | succ offset =>
          simp only [List.getElem?_cons_succ] at h0
          have h1' : tail[offset + 1]? = some b1 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h1
          have h2' : tail[offset + 2]? = some b2 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h2
          have h3' : tail[offset + 3]? = some b3 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h3
          simp only [List.drop_succ_cons]
          exact ih offset h0 h1' h2' h3'

theorem drop_take_eight_of_getElem? {α : Type} (values : List α) (offset : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : α)
    (h0 : values[offset]? = some b0) (h1 : values[offset + 1]? = some b1)
    (h2 : values[offset + 2]? = some b2) (h3 : values[offset + 3]? = some b3)
    (h4 : values[offset + 4]? = some b4) (h5 : values[offset + 5]? = some b5)
    (h6 : values[offset + 6]? = some b6) (h7 : values[offset + 7]? = some b7) :
    (values.drop offset).take 8 = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  induction values generalizing offset with
  | nil => simp at h0
  | cons head tail ih =>
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
          subst b0
          cases tail with
          | nil => simp at h1
          | cons t1 tail =>
              simp only [Nat.zero_add, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at h1
              subst b1
              cases tail with
              | nil => simp at h2
              | cons t2 tail =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                    Option.some.injEq] at h2
                  subst b2
                  cases tail with
                  | nil => simp at h3
                  | cons t3 tail =>
                      simp only [List.getElem?_cons_succ,
                        List.getElem?_cons_zero, Option.some.injEq] at h3
                      subst b3
                      cases tail with
                      | nil => simp at h4
                      | cons t4 tail =>
                          simp only [List.getElem?_cons_succ,
                            List.getElem?_cons_zero, Option.some.injEq] at h4
                          subst b4
                          cases tail with
                          | nil => simp at h5
                          | cons t5 tail =>
                              simp only [List.getElem?_cons_succ,
                                List.getElem?_cons_zero,
                                Option.some.injEq] at h5
                              subst b5
                              cases tail with
                              | nil => simp at h6
                              | cons t6 tail =>
                                  simp only [List.getElem?_cons_succ,
                                    List.getElem?_cons_zero,
                                    Option.some.injEq] at h6
                                  subst b6
                                  cases tail with
                                  | nil => simp at h7
                                  | cons t7 rest =>
                                      simp only [List.getElem?_cons_succ,
                                        List.getElem?_cons_zero,
                                        Option.some.injEq] at h7
                                      subst b7
                                      simp
      | succ offset =>
          simp only [List.getElem?_cons_succ] at h0
          have h1' : tail[offset + 1]? = some b1 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h1
          have h2' : tail[offset + 2]? = some b2 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h2
          have h3' : tail[offset + 3]? = some b3 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h3
          have h4' : tail[offset + 4]? = some b4 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h4
          have h5' : tail[offset + 5]? = some b5 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h5
          have h6' : tail[offset + 6]? = some b6 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h6
          have h7' : tail[offset + 7]? = some b7 := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h7
          simp only [List.drop_succ_cons]
          exact ih offset h0 h1' h2' h3' h4' h5' h6' h7'

theorem drop_take_sixteen_of_getElem? {α : Type} (values : List α) (offset : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : α)
    (h0 : values[offset]? = some b0) (h1 : values[offset + 1]? = some b1)
    (h2 : values[offset + 2]? = some b2) (h3 : values[offset + 3]? = some b3)
    (h4 : values[offset + 4]? = some b4) (h5 : values[offset + 5]? = some b5)
    (h6 : values[offset + 6]? = some b6) (h7 : values[offset + 7]? = some b7)
    (h8 : values[offset + 8]? = some b8) (h9 : values[offset + 9]? = some b9)
    (h10 : values[offset + 10]? = some b10)
    (h11 : values[offset + 11]? = some b11)
    (h12 : values[offset + 12]? = some b12)
    (h13 : values[offset + 13]? = some b13)
    (h14 : values[offset + 14]? = some b14)
    (h15 : values[offset + 15]? = some b15) :
    (values.drop offset).take 16 =
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
        b15] := by
  rw [show 16 = 8 + 8 by omega, List.take_add]
  rw [drop_take_eight_of_getElem? values offset b0 b1 b2 b3 b4 b5 b6 b7
    h0 h1 h2 h3 h4 h5 h6 h7]
  have hsecond := drop_take_eight_of_getElem? values (offset + 8)
    b8 b9 b10 b11 b12 b13 b14 b15 h8 (by simpa [Nat.add_assoc] using h9)
    (by simpa [Nat.add_assoc] using h10) (by simpa [Nat.add_assoc] using h11)
    (by simpa [Nat.add_assoc] using h12) (by simpa [Nat.add_assoc] using h13)
    (by simpa [Nat.add_assoc] using h14) (by simpa [Nat.add_assoc] using h15)
  rw [List.drop_drop]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsecond

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

def boxStore {α : Type} (codec : Codec α) (storage : List Byte)
    (offset : Nat) (value : α) : Option (List Byte) :=
  if offset + codec.size > storage.length then none
  else some (writeBytes storage offset (codec.encode value))

theorem boxStore_result {α : Type} {codec : Codec α} {storage : List Byte}
    {offset : Nat} {value : α} {result : List Byte}
    (hsuccess : boxStore codec storage offset value = some result) :
    offset + codec.size ≤ storage.length ∧
      result = writeBytes storage offset (codec.encode value) := by
  unfold boxStore at hsuccess
  split at hsuccess
  next => contradiction
  next hbound =>
    exact ⟨Nat.le_of_not_gt hbound, Option.some.inj hsuccess |>.symm⟩

def boxLoad {α : Type} (codec : Codec α) (storage : List Byte)
    (offset : Nat) : Option α :=
  if offset + codec.size > storage.length then none
  else codec.decode ((storage.drop offset).take codec.size)

theorem boxLoad_result {α : Type} {codec : Codec α} {storage : List Byte}
    {offset : Nat} {value : α}
    (hsuccess : boxLoad codec storage offset = some value) :
    offset + codec.size ≤ storage.length ∧
      codec.decode ((storage.drop offset).take codec.size) = some value := by
  unfold boxLoad at hsuccess
  split at hsuccess
  next => contradiction
  next hbound => exact ⟨Nat.le_of_not_gt hbound, hsuccess⟩

theorem boxLoad_of_encoded {α : Type} (codec : Codec α)
    (storage : List Byte) (offset : Nat) (value : α)
    (hbound : offset + codec.size ≤ storage.length)
    (hencoded : (storage.drop offset).take codec.size = codec.encode value) :
    boxLoad codec storage offset = some value := by
  simp [boxLoad, Nat.not_lt_of_ge hbound, hencoded, codec.decode_encode]

theorem boxLoad_after_boxStore {α : Type} (codec : Codec α)
    (storage : List Byte) (offset : Nat) (value : α) (result : List Byte)
    (hsuccess : boxStore codec storage offset value = some result) :
    boxLoad codec result offset = some value := by
  obtain ⟨hbound, rfl⟩ := boxStore_result hsuccess
  apply boxLoad_of_encoded codec _ offset value
  · rw [writeBytes_length storage offset (codec.encode value)]
    · simpa [codec.encode_length] using hbound
    · simpa [codec.encode_length] using hbound
  · have hread := writeBytes_read_back storage offset (codec.encode value)
      (by simpa [codec.encode_length] using hbound)
    simpa only [codec.encode_length] using hread

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

/-- Exact allocator-backed `Box<u16>` semantics. Unlike the historical byte
specialization, this is just the generic verified constructor instantiated
with the little-endian `u16` codec. -/
def boxNewU16Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 16) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.u16 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewU32Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 32) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.u32 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewU64Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 64) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.u64 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewU128Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 128) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.u128 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewI8Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 8) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.i8 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewI16Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 16) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.i16 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewI32Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 32) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.i32 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewI64Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 64) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.i64 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewI128Arrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 128) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.i128 storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewUsizeArrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 64) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.usize storage offsets sizes isFree prevFree count second
    first heads next previous value

def boxNewIsizeArrays (storage : List Byte) (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (value : BitVec 64) :
    Option BoxNewU8ArraysResult :=
  boxNewArrays Scalar.isize storage offsets sizes isFree prevFree count second
    first heads next previous value

set_option maxHeartbeats 1200000 in
theorem boxNewU16Arrays_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage : List Byte} {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {value : BitVec 16}
    {result : BoxNewU8ArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxNewU16Arrays storage offsets sizes isFree prevFree count
      second first heads next previous value = some result) :
    ∃ (hkeyMax : requestKey (Luffs.Containers.Box.requestBytes Scalar.u16.size) <
          2 ^ firstLevelCount)
        (boxResult : Luffs.Containers.Box.Result),
      Luffs.Containers.Box.allocate Scalar.u16
          { physical := blocks, bins := state } hkeyMax = some boxResult ∧
      result.allocatedOffset = boxResult.block.offset ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents (boxResult.block.region pool).base
          (Scalar.u16.encode value) →
        contentsInterp (G := G) contents ∗ Ownership.OwnsFree pool blocks ==∗
          contentsInterp
              (insertBytes contents (boxResult.block.region pool).base
                (Scalar.u16.encode value)) ∗
            (Luffs.Containers.Box.Owns Scalar.u16 pool boxResult.block value ∗
              Ownership.OwnsFree pool boxResult.state.physical) := by
  exact boxNewArrays_owns hvalid hsecond hfirst hbins hdisjoint hphysical hsuccess

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

/-- Allocator-backed `Vec<u16>` construction is the codec-generic verified
allocation boundary specialized to two-byte little-endian elements. -/
def vecNewU16Arrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (capacity : Nat) :
    Option Luffs.Runtime.TLSF.AllocateArraysResult :=
  vecNewArrays Scalar.u16 offsets sizes isFree prevFree count second first
    heads next previous capacity

def vecNewU32Arrays := vecNewArrays Scalar.u32
def vecNewU64Arrays := vecNewArrays Scalar.u64
def vecNewU128Arrays := vecNewArrays Scalar.u128
def vecNewI8Arrays := vecNewArrays Scalar.i8
def vecNewI16Arrays := vecNewArrays Scalar.i16
def vecNewI32Arrays := vecNewArrays Scalar.i32
def vecNewI64Arrays := vecNewArrays Scalar.i64
def vecNewI128Arrays := vecNewArrays Scalar.i128
def vecNewUsizeArrays := vecNewArrays Scalar.usize
def vecNewIsizeArrays := vecNewArrays Scalar.isize

set_option maxHeartbeats 1200000 in
theorem vecNewU16Arrays_refines_vec
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
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : vecNewU16Arrays offsets sizes isFree prevFree count second
      first heads next previous capacity = some result) :
    ∃ (hcapacity : 0 < capacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes Scalar.u16 capacity) <
            2 ^ firstLevelCount)
        (vecResult : Luffs.Containers.Vec.AllocResult),
      Luffs.Containers.Vec.allocate Scalar.u16 capacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some vecResult ∧
      result.allocatedOffset = vecResult.handle.block.offset ∧
      result.allocatedBytes = vecResult.handle.block.bytes ∧
      vecResult.handle.len = 0 ∧ vecResult.handle.capacity = capacity ∧
      (Ownership.OwnsFree (PROP := Iris.IProp GF) pool blocks ⊣⊢
        Luffs.Containers.Vec.Owns Scalar.u16 pool vecResult.handle [] ∗
          Ownership.OwnsFree pool vecResult.state.physical) := by
  exact vecNewArrays_refines_vec hvalid hsecond hfirst hbins hdisjoint
    hphysical hsuccess

structure VecPushResult where
  storage : List Byte
  nextLen : Nat
deriving DecidableEq, Repr

/-- Codec-generic Vec push boundary, including every 64-bit arithmetic check
needed to form the element's byte address. -/
def vecPush {α : Type} (codec : Codec α) (storage : List Byte)
    (offset len capacity : Nat) (value : α) : Option VecPushResult :=
  if capacity > Luffs.Runtime.TLSF.usizeMax ∨ len ≥ capacity then none
  else if len > Luffs.Runtime.TLSF.usizeMax / codec.size then none
  else
    let byteOffset := len * codec.size
    if offset > Luffs.Runtime.TLSF.usizeMax - byteOffset then none
    else
      let address := offset + byteOffset
      if address > Luffs.Runtime.TLSF.usizeMax - codec.size then none
      else match boxStore codec storage address value with
        | none => none
        | some nextStorage => some ⟨nextStorage, len + 1⟩

theorem vecPush_result {α : Type} {codec : Codec α} {storage : List Byte}
    {offset len capacity : Nat} {value : α} {result : VecPushResult}
    (hsuccess : vecPush codec storage offset len capacity value = some result) :
    capacity ≤ Luffs.Runtime.TLSF.usizeMax ∧ len < capacity ∧
      len ≤ Luffs.Runtime.TLSF.usizeMax / codec.size ∧
      offset ≤ Luffs.Runtime.TLSF.usizeMax - len * codec.size ∧
      offset + len * codec.size ≤
        Luffs.Runtime.TLSF.usizeMax - codec.size ∧
      offset + len * codec.size + codec.size ≤ storage.length ∧
      result.storage = writeBytes storage (offset + len * codec.size)
        (codec.encode value) ∧ result.nextLen = len + 1 := by
  unfold vecPush at hsuccess
  split at hsuccess
  next => contradiction
  next hcapacity =>
    split at hsuccess
    next => contradiction
    next hmul =>
      dsimp only at hsuccess
      split at hsuccess
      next => contradiction
      next hoffset =>
        split at hsuccess
        next => contradiction
        next haddress =>
          cases hstore : boxStore codec storage (offset + len * codec.size) value with
          | none => simp [hstore] at hsuccess
          | some nextStorage =>
              simp [hstore] at hsuccess
              subst result
              obtain ⟨hstorageBound, hstorage⟩ := boxStore_result hstore
              exact ⟨Nat.le_of_not_gt (fun h => hcapacity (Or.inl h)),
                Nat.lt_of_not_ge (fun h => hcapacity (Or.inr h)),
                Nat.le_of_not_gt hmul, Nat.le_of_not_gt hoffset,
                Nat.le_of_not_gt haddress, hstorageBound, hstorage, rfl⟩

theorem vecPush_refines_handle {α : Type} {codec : Codec α}
    {storage : List Byte} {handle : Luffs.Containers.Vec.Handle} {value : α}
    {result : VecPushResult}
    (hsuccess : vecPush codec storage handle.block.offset handle.len
      handle.capacity value = some result) :
    Luffs.Containers.Vec.push handle =
      some { handle with len := result.nextLen } := by
  have hresult := vecPush_result hsuccess
  simp [Luffs.Containers.Vec.push, hresult.2.1, hresult.2.2.2.2.2.2.2]

theorem vecPush_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {α : Type} (codec : Codec α) {pool : Region}
    {storage : List Byte} {handle : Luffs.Containers.Vec.Handle}
    {values : List α} {value : α} {result : VecPushResult}
    (hlen : values.length = handle.len)
    (hsuccess : vecPush codec storage handle.block.offset handle.len
      handle.capacity value = some result) :
    ∃ next,
      Luffs.Containers.Vec.push handle = some next ∧
      result.nextLen = next.len ∧
      result.storage = writeBytes storage
        (handle.block.offset +
          (Luffs.Containers.Vec.encodeValues codec values).length)
        (codec.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues codec values).length)
          (codec.encode value) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns codec pool handle values ==∗
          contentsInterp
              (insertBytes contents
                ((handle.block.region pool).base +
                  (Luffs.Containers.Vec.encodeValues codec values).length)
                (codec.encode value)) ∗
            Luffs.Containers.Vec.Owns codec pool next (values ++ [value]) := by
  let next := { handle with len := result.nextLen }
  have hpush : Luffs.Containers.Vec.push handle = some next :=
    vecPush_refines_handle hsuccess
  have hresult := vecPush_result hsuccess
  have hstorage : result.storage = writeBytes storage
      (handle.block.offset +
        (Luffs.Containers.Vec.encodeValues codec values).length)
      (codec.encode value) := by
    rw [Luffs.Containers.Vec.encodeValues_length, hlen]
    exact hresult.2.2.2.2.2.2.1
  refine ⟨next, hpush, rfl, hstorage, ?_⟩
  intro contents hfresh
  exact Luffs.Containers.Vec.push_owns codec value contents hpush hfresh

def vecGet {α : Type} (codec : Codec α) (storage : List Byte)
    (offset len index : Nat) : Option α :=
  if index ≥ len then none
  else if index > Luffs.Runtime.TLSF.usizeMax / codec.size then none
  else
    let byteOffset := index * codec.size
    if offset > Luffs.Runtime.TLSF.usizeMax - byteOffset then none
    else
      let address := offset + byteOffset
      if address > Luffs.Runtime.TLSF.usizeMax - codec.size then none
      else boxLoad codec storage address

theorem vecGet_result {α : Type} {codec : Codec α} {storage : List Byte}
    {offset len index : Nat} {value : α}
    (hsuccess : vecGet codec storage offset len index = some value) :
    index < len ∧ index ≤ Luffs.Runtime.TLSF.usizeMax / codec.size ∧
      offset ≤ Luffs.Runtime.TLSF.usizeMax - index * codec.size ∧
      offset + index * codec.size ≤
        Luffs.Runtime.TLSF.usizeMax - codec.size ∧
      offset + index * codec.size + codec.size ≤ storage.length ∧
      codec.decode
        ((storage.drop (offset + index * codec.size)).take codec.size) =
          some value := by
  unfold vecGet at hsuccess
  split at hsuccess
  next => contradiction
  next hindex =>
    split at hsuccess
    next => contradiction
    next hmul =>
      dsimp only at hsuccess
      split at hsuccess
      next => contradiction
      next hoffset =>
        split at hsuccess
        next => contradiction
        next haddress =>
          obtain ⟨hstorage, hdecode⟩ := boxLoad_result hsuccess
          exact ⟨Nat.lt_of_not_ge hindex, Nat.le_of_not_gt hmul,
            Nat.le_of_not_gt hoffset, Nat.le_of_not_gt haddress,
            hstorage, hdecode⟩

theorem vecGet_value {α : Type} {codec : Codec α} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {index : Nat}
    {value expected : α}
    (hsuccess : vecGet codec storage handle.block.offset handle.len index =
      some value)
    (hencoded :
      (storage.drop (handle.block.offset + index * codec.size)).take codec.size =
        codec.encode expected) :
    value = expected := by
  have hresult := vecGet_result hsuccess
  have hdecode := hresult.2.2.2.2.2
  rw [hencoded, codec.decode_encode] at hdecode
  exact Option.some.inj hdecode |>.symm

theorem vecGet_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {α : Type} (codec : Codec α) {pool : Region}
    {storage : List Byte} {handle : Luffs.Containers.Vec.Handle}
    {values : List α} {index : Nat} {value expected : α}
    (hlen : values.length = handle.len)
    (hsuccess : vecGet codec storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some expected)
    (hencoded :
      (storage.drop (handle.block.offset + index * codec.size)).take codec.size =
        codec.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns codec pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns codec pool handle values) ∗
          ⌜ReadSteps ((handle.block.region pool).base + index * codec.size)
              (codec.encode expected) mem ∧
            codec.decode (codec.encode expected) = some expected⌝) := by
  have hresult := vecGet_result hsuccess
  have hiValues : index < values.length := (getElem?_eq_some_iff.mp hvalues).1
  have hvalueAt : values[index] = expected :=
    (getElem?_eq_some_iff.mp hvalues).2
  refine ⟨vecGet_value hsuccess hencoded, ?_⟩
  simpa [hvalueAt] using
    (Luffs.Containers.Vec.read_element codec hlen hrep hresult.1)

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

/-- The concrete allocator-offset `Vec<u8>` get recognized from Luffs source
returns only the owned logical element, preserves exclusive Vec ownership, and
exposes the exact one-byte operational read. -/
theorem vecGetU8Offset_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {values : List (BitVec 8)}
    {index : Nat} {value expected : Byte}
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hget : vecGetU8Offset storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some (Scalar.bv8OfByte expected))
    (hencoded :
      (storage.drop (handle.block.offset + index)).take Scalar.u8.size =
        Scalar.u8.encode (Scalar.bv8OfByte expected))
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns Scalar.u8 pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns Scalar.u8 pool handle values) ∗
          ⌜ReadSteps ((handle.block.region pool).base + index)
              (Scalar.u8.encode (Scalar.bv8OfByte expected)) mem ∧
            Scalar.u8.decode (Scalar.u8.encode (Scalar.bv8OfByte expected)) =
              some (Scalar.bv8OfByte expected)⌝) := by
  have hresult := vecGetU8Offset_result hget
  have haddress : handle.block.offset + index + Scalar.u8.size ≤
      storage.length := by
    simp only [Scalar.u8]
    omega
  have hboxExpected : boxLoad Scalar.u8 storage
      (handle.block.offset + index) = some (Scalar.bv8OfByte expected) :=
    boxLoad_of_encoded Scalar.u8 storage (handle.block.offset + index)
      (Scalar.bv8OfByte expected) haddress hencoded
  have haddressLtMax : handle.block.offset + index <
      Luffs.Runtime.TLSF.usizeMax := by omega
  have hindexMax : ¬index > Luffs.Runtime.TLSF.usizeMax / Scalar.u8.size := by
    simp only [Scalar.u8]
    omega
  have hoffsetMax : ¬handle.block.offset >
      Luffs.Runtime.TLSF.usizeMax - index * Scalar.u8.size := by
    simp only [Scalar.u8]
    omega
  have haddressMax : ¬handle.block.offset + index * Scalar.u8.size >
      Luffs.Runtime.TLSF.usizeMax - Scalar.u8.size := by
    simp only [Scalar.u8]
    omega
  have hgeneric : vecGet Scalar.u8 storage handle.block.offset handle.len index =
      some (Scalar.bv8OfByte expected) := by
    unfold vecGet
    rw [if_neg (Nat.not_le.mpr hresult.1), if_neg hindexMax]
    dsimp only
    rw [if_neg hoffsetMax]
    rw [if_neg haddressMax]
    simpa only [Scalar.u8, Nat.mul_one] using hboxExpected
  have hsliceValue :
      (storage.drop (handle.block.offset + index)).take Scalar.u8.size =
        Scalar.u8.encode (Scalar.bv8OfByte value) := by
    have hbound : handle.block.offset + index < storage.length := hresult.2.2.1
    have hvalueAt : storage[handle.block.offset + index] = value := by
      have hread := hresult.2.2.2
      rw [List.getElem?_eq_getElem hbound] at hread
      exact Option.some.inj hread
    have hdrop : storage.drop (handle.block.offset + index) =
        value :: storage.drop (handle.block.offset + index + 1) := by
      rw [List.drop_eq_getElem_cons hbound]
      rw [hvalueAt]
    rw [hdrop]
    simp [Scalar.u8, Scalar.encode8, Scalar.bv8OfByte, Scalar.byteOfBV8]
  have hbv : Scalar.bv8OfByte value = Scalar.bv8OfByte expected := by
    have hboxValue : boxLoad Scalar.u8 storage
        (handle.block.offset + index) = some (Scalar.bv8OfByte value) :=
      boxLoad_of_encoded Scalar.u8 storage (handle.block.offset + index)
        (Scalar.bv8OfByte value) haddress hsliceValue
    rw [hboxExpected] at hboxValue
    exact Option.some.inj hboxValue.symm
  have hvalue : value = expected :=
    Fin.ext (congrArg BitVec.toNat hbv)
  have hencodedGeneric :
      (storage.drop (handle.block.offset + index * Scalar.u8.size)).take
          Scalar.u8.size = Scalar.u8.encode (Scalar.bv8OfByte expected) := by
    simpa only [Scalar.u8, Nat.mul_one] using hencoded
  refine ⟨hvalue, ?_⟩
  simpa [Scalar.u8, Nat.add_assoc] using
    (vecGet_owns Scalar.u8 hlen hgeneric hvalues hencodedGeneric hrep)

theorem vecDropArrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF] {α : Type} (codec : Codec α)
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
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hsuccess : boxDropU8Arrays offsets sizes isFree prevFree count second first
      heads next previous offset = some result) :
    ∃ (handle : Luffs.Containers.Vec.Handle) (abstractNext : Alloc.State),
      handle.block.offset = offset ∧ handle.len = len ∧
      handle.capacity = capacity ∧
      Luffs.Containers.Vec.drop pool
          { physical := blocks, bins := state } handle = some abstractNext ∧
      ∀ (values : List α) (contents : ContentsMap),
        values.length = len →
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Vec.Owns codec pool handle values ∗
              Ownership.OwnsFree pool blocks) ==∗
          contentsInterp
              (deleteBytes contents (handle.block.region pool).base
                (Luffs.Containers.Vec.encodeValues codec values)) ∗
            Ownership.OwnsFree pool abstractNext.physical := by
  obtain ⟨selected, abstractNext, hoffset, _, hdrop, _⟩ :=
    boxDropU8Arrays_refines_box (PROP := Iris.IProp GF) hvalid hpoolMax hcountMax
      hsecond hfirst hbins hdisjoint hphysical hsuccess
  let handle : Luffs.Containers.Vec.Handle := ⟨selected, len, capacity⟩
  have hvecDrop : Luffs.Containers.Vec.drop pool
      { physical := blocks, bins := state } handle = some abstractNext := by
    simpa [Luffs.Containers.Vec.drop, handle] using hdrop
  refine ⟨handle, abstractNext, by simpa [handle] using hoffset,
    rfl, rfl, hvecDrop, ?_⟩
  intro values contents _
  exact Luffs.Containers.Vec.drop_owns codec values contents hvecDrop

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
  exact vecDropArrays_owns Scalar.u8 hvalid hpoolMax hcountMax hsecond hfirst
    hbins hdisjoint hphysical hsuccess

theorem vecDropU16Arrays_owns
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
      ∀ (values : List (BitVec 16)) (contents : ContentsMap),
        values.length = len →
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Vec.Owns Scalar.u16 pool handle values ∗
              Ownership.OwnsFree pool blocks) ==∗
          contentsInterp
              (deleteBytes contents (handle.block.region pool).base
                (Luffs.Containers.Vec.encodeValues Scalar.u16 values)) ∗
            Ownership.OwnsFree pool abstractNext.physical := by
  exact vecDropArrays_owns Scalar.u16 hvalid hpoolMax hcountMax hsecond hfirst
    hbins hdisjoint hphysical hsuccess

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

/-- Codec-generic concrete growth transaction. `len` remains an element count;
all pool ranges and the copied prefix use the checked encoded byte count. -/
def vecGrowArrays {α : Type} (codec : Codec α) (storage : List Byte)
    (offsets sizes : List Nat) (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat)
    (oldOffset len oldCapacity newCapacity : Nat) :
    Option VecGrowU8ArraysResult := do
  if len > oldCapacity ∨ newCapacity ≤ oldCapacity ∨
      len > Luffs.Runtime.TLSF.usizeMax / codec.size ∨
      newCapacity > Luffs.Runtime.TLSF.usizeMax / codec.size ∨
      newCapacity * codec.size > Luffs.Runtime.TLSF.usizeMax - 7 then none
  let initializedBytes := len * codec.size
  if oldOffset + initializedBytes ≥ 2 ^ 64 ∨
      oldOffset + initializedBytes > storage.length then none
  let allocated ← Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
    prevFree count second first heads next previous
      (Luffs.Containers.Vec.allocationBytes codec newCapacity)
  if allocated.allocatedOffset + initializedBytes ≥ 2 ^ 64 ∨
      allocated.allocatedOffset + initializedBytes > storage.length then none
  let copied ← copyByteRange storage oldOffset allocated.allocatedOffset
    initializedBytes
  let released ← boxDropU8Arrays allocated.offsets allocated.sizes
    allocated.isFree allocated.prevFree allocated.count allocated.second
    allocated.first allocated.heads allocated.next allocated.previous oldOffset
  pure ⟨released, copied, allocated.allocatedOffset, allocated.allocatedBytes⟩

theorem vecGrowArrays_result {α : Type} {codec : Codec α}
    {storage : List Byte} {offsets sizes : List Nat}
    {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {oldOffset len oldCapacity newCapacity : Nat}
    {result : VecGrowU8ArraysResult}
    (hsuccess : vecGrowArrays codec storage offsets sizes isFree prevFree count
      second first heads next previous oldOffset len oldCapacity newCapacity =
        some result) :
    ∃ allocated copied released,
      len ≤ oldCapacity ∧ oldCapacity < newCapacity ∧
      len ≤ Luffs.Runtime.TLSF.usizeMax / codec.size ∧
      newCapacity ≤ Luffs.Runtime.TLSF.usizeMax / codec.size ∧
      newCapacity * codec.size ≤ Luffs.Runtime.TLSF.usizeMax - 7 ∧
      oldOffset + len * codec.size < 2 ^ 64 ∧
      oldOffset + len * codec.size ≤ storage.length ∧
      Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree prevFree count
        second first heads next previous
          (Luffs.Containers.Vec.allocationBytes codec newCapacity) =
            some allocated ∧
      allocated.allocatedOffset + len * codec.size < 2 ^ 64 ∧
      allocated.allocatedOffset + len * codec.size ≤ storage.length ∧
      copyByteRange storage oldOffset allocated.allocatedOffset
        (len * codec.size) = some copied ∧
      boxDropU8Arrays allocated.offsets allocated.sizes allocated.isFree
        allocated.prevFree allocated.count allocated.second allocated.first
        allocated.heads allocated.next allocated.previous oldOffset =
          some released ∧
      result = ⟨released, copied, allocated.allocatedOffset,
        allocated.allocatedBytes⟩ := by
  let badPre := len > oldCapacity ∨ newCapacity ≤ oldCapacity ∨
    len > Luffs.Runtime.TLSF.usizeMax / codec.size ∨
    newCapacity > Luffs.Runtime.TLSF.usizeMax / codec.size ∨
    newCapacity * codec.size > Luffs.Runtime.TLSF.usizeMax - 7
  let initializedBytes := len * codec.size
  let badOld := oldOffset + initializedBytes ≥ 2 ^ 64 ∨
    oldOffset + initializedBytes > storage.length
  by_cases hpre : badPre
  · simp [vecGrowArrays, badPre, hpre] at hsuccess
  · by_cases hold : badOld
    · simp [vecGrowArrays, badPre, initializedBytes, badOld, hpre, hold]
        at hsuccess
    · cases halloc : Luffs.Runtime.TLSF.allocateArrays offsets sizes isFree
          prevFree count second first heads next previous
            (Luffs.Containers.Vec.allocationBytes codec newCapacity) with
      | none =>
          simp [vecGrowArrays, badPre, initializedBytes, badOld, hpre, hold,
            halloc] at hsuccess
      | some allocated =>
        let badNew := allocated.allocatedOffset + initializedBytes ≥ 2 ^ 64 ∨
          allocated.allocatedOffset + initializedBytes > storage.length
        by_cases hnew : badNew
        · simp [vecGrowArrays, badPre, initializedBytes, badOld, badNew,
            hpre, hold, halloc, hnew] at hsuccess
        · cases hcopy : copyByteRange storage oldOffset
              allocated.allocatedOffset initializedBytes with
          | none =>
            simp [vecGrowArrays, badPre, initializedBytes, badOld, badNew,
              hpre, hold, halloc, hnew, hcopy] at hsuccess
          | some copied =>
            cases hdrop : boxDropU8Arrays allocated.offsets allocated.sizes
                allocated.isFree allocated.prevFree allocated.count
                allocated.second allocated.first allocated.heads allocated.next
                allocated.previous oldOffset with
            | none =>
              simp [vecGrowArrays, badPre, initializedBytes, badOld, badNew,
                hpre, hold, halloc, hnew, hcopy, hdrop] at hsuccess
            | some released =>
              simp [vecGrowArrays, badPre, initializedBytes, badOld, badNew,
                hpre, hold, halloc, hnew, hcopy, hdrop] at hsuccess
              subst result
              refine ⟨allocated, copied, released, ?_, ?_, ?_, ?_, ?_, ?_,
                ?_, rfl, ?_, ?_, hcopy, hdrop, rfl⟩
              · exact Nat.le_of_not_gt (fun h => hpre (Or.inl h))
              · exact Nat.lt_of_not_ge (fun h => hpre (Or.inr (Or.inl h)))
              · exact Nat.le_of_not_gt
                  (fun h => hpre (Or.inr (Or.inr (Or.inl h))))
              · exact Nat.le_of_not_gt
                  (fun h => hpre (Or.inr (Or.inr (Or.inr (Or.inl h)))))
              · exact Nat.le_of_not_gt
                  (fun h => hpre (Or.inr (Or.inr (Or.inr (Or.inr h)))))
              · exact Nat.lt_of_not_ge (fun h => hold (Or.inl h))
              · exact Nat.le_of_not_gt (fun h => hold (Or.inr h))
              · exact Nat.lt_of_not_ge (fun h => hnew (Or.inl h))
              · exact Nat.le_of_not_gt (fun h => hnew (Or.inr h))

theorem vecGrowArrays_copies_prefix {α : Type} {codec : Codec α}
    {storage : List Byte} {offsets sizes : List Nat}
    {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {oldOffset len oldCapacity newCapacity : Nat}
    {result : VecGrowU8ArraysResult}
    (hsuccess : vecGrowArrays codec storage offsets sizes isFree prevFree count
      second first heads next previous oldOffset len oldCapacity newCapacity =
        some result) :
    result.storage.length = storage.length ∧
      (∀ i, i < len * codec.size →
        result.storage[result.newOffset + i]? = storage[oldOffset + i]?) ∧
      (∀ j, (j < result.newOffset ∨ result.newOffset + len * codec.size ≤ j) →
        result.storage[j]? = storage[j]?) := by
  obtain ⟨allocated, copied, released, _, _, _, _, _, _, _, _, _, _, hcopy, _,
      hresult⟩ := vecGrowArrays_result hsuccess
  subst result
  simpa using copyByteRange_result hcopy

set_option maxHeartbeats 1600000 in
theorem vecGrowArrays_refines_vec {α : Type} {codec : Codec α}
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
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysicalInput : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hmember : handle.block ∈ blocks)
    (hallocated : handle.block.free = false)
    (harrayMax : offsets.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsuccess : vecGrowArrays codec storage offsets sizes isFree prevFree count
      second first heads next previous handle.block.offset handle.len
      handle.capacity newCapacity = some result) :
    ∃ (hcapacity : 0 < newCapacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes codec newCapacity) <
            2 ^ firstLevelCount)
        (growResult : Luffs.Containers.Vec.GrowResult),
      Luffs.Containers.Vec.grow codec pool handle newCapacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some growResult ∧
      result.newOffset = growResult.handle.block.offset ∧
      growResult.handle.len = handle.len ∧
      growResult.handle.capacity = newCapacity := by
  obtain ⟨concreteAllocated, copied, released, _, hcapacityLt, _, _, _, _, _,
      hconcreteAlloc, _, _, _, hconcreteDrop, rfl⟩ :=
    vecGrowArrays_result hsuccess
  obtain ⟨_, hkeyMax, abstractAllocated, habstractAlloc, hoffset, _,
      hphysical, hbinsValid, hpostBins, hpostDisjoint, hpostSecond,
      hpostFirst, _⟩ :=
    Luffs.Runtime.TLSF.allocateArrays_ownsFree
      (PROP := PROP) hvalid hsecond hfirst hbins hdisjoint hphysicalInput
      hconcreteAlloc
  have hcapacity : 0 < newCapacity := by omega
  have hpostValid : Alloc.Valid pool abstractAllocated.state :=
    Alloc.allocate_preserves_valid hvalid
      (Luffs.Containers.Box.requestBytes_aligned (newCapacity * codec.size))
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
      hpostCountMax hpostSecond hpostFirst hpostBins hpostDisjoint hphysical
      hconcreteDrop
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
  have hvecAllocate : Luffs.Containers.Vec.allocate codec newCapacity
      hcapacity { physical := blocks, bins := state } hkeyMax =
        some vecAllocated := by
    simp [Luffs.Containers.Vec.allocate, vecAllocated, habstractAlloc]
  let growResult : Luffs.Containers.Vec.GrowResult := {
    handle := ⟨abstractAllocated.allocated, handle.len, newCapacity⟩
    state := abstractNext }
  have hgrow : Luffs.Containers.Vec.grow codec pool handle newCapacity
      hcapacity { physical := blocks, bins := state } hkeyMax =
        some growResult := by
    simp [Luffs.Containers.Vec.grow, hvecAllocate, vecAllocated, hdropOld,
      growResult]
  exact ⟨hcapacity, hkeyMax, growResult, hgrow, by
    simpa [growResult] using hoffset, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
theorem vecGrowArrays_owns {α : Type} {codec : Codec α}
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
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysicalInput : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hmember : handle.block ∈ blocks)
    (hallocated : handle.block.free = false)
    (harrayMax : offsets.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsuccess : vecGrowArrays codec storage offsets sizes isFree prevFree count
      second first heads next previous handle.block.offset handle.len
      handle.capacity newCapacity = some result) :
    ∃ (hcapacity : 0 < newCapacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes codec newCapacity) <
            2 ^ firstLevelCount)
        (growResult : Luffs.Containers.Vec.GrowResult),
      Luffs.Containers.Vec.grow codec pool handle newCapacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some growResult ∧
      result.newOffset = growResult.handle.block.offset ∧
      ∀ (values : List α) (contents : ContentsMap),
        CanInsertBytes contents (growResult.handle.block.region pool).base
          (Luffs.Containers.Vec.encodeValues codec values) →
        contentsInterp (G := G) contents ∗
            (Luffs.Containers.Vec.Owns codec pool handle values ∗
              Ownership.OwnsFree pool blocks) ==∗
          contentsInterp
              (deleteBytes
                (insertBytes contents
                  (growResult.handle.block.region pool).base
                  (Luffs.Containers.Vec.encodeValues codec values))
                (handle.block.region pool).base
                (Luffs.Containers.Vec.encodeValues codec values)) ∗
            (Luffs.Containers.Vec.Owns codec pool growResult.handle values ∗
              Ownership.OwnsFree pool growResult.state.physical) := by
  obtain ⟨hcapacity, hkeyMax, growResult, hgrow, hoffset, _, _⟩ :=
    vecGrowArrays_refines_vec (PROP := Iris.IProp GF) hvalid hpoolMax hsecond
      hfirst hbins hdisjoint hphysicalInput hmember hallocated harrayMax hsuccess
  refine ⟨hcapacity, hkeyMax, growResult, hgrow, hoffset, ?_⟩
  intro values contents hfresh
  obtain ⟨allocated, next, halloc, hdrop, hresult⟩ :=
    Luffs.Containers.Vec.grow_result hgrow
  subst growResult
  exact Luffs.Containers.Vec.grow_owns_step codec hvalid halloc hdrop
    values contents hfresh

/-- The first non-byte source specialization of codec-generic Vec growth. -/
def vecGrowU16Arrays := vecGrowArrays Scalar.u16

/-- Four-byte source specialization of codec-generic Vec growth. -/
def vecGrowU32Arrays := vecGrowArrays Scalar.u32

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

def boxLoadU16 (storage : List Byte) (begin : Nat) : Option (BitVec 16) := do
  if begin = Luffs.Runtime.TLSF.usizeMax then none
  let second := begin + 1
  if second ≥ storage.length then none
  let low ← storage[begin]?
  let high ← storage[second]?
  Scalar.decode16 [low, high]

def boxStoreU8 (storage : List Byte) (begin : Nat) (value : Byte) :
    Option (List Byte) :=
  if begin ≥ storage.length then none else some (storage.set begin value)

def boxLoadI8 (storage : List Byte) (begin : Nat) : Option (BitVec 8) := do
  if begin ≥ storage.length then none
  let byte ← storage[begin]?
  Scalar.decode8 [byte]

def boxStoreI8 (storage : List Byte) (begin : Nat) (value : BitVec 8) :
    Option (List Byte) :=
  if begin ≥ storage.length then none
  else some (storage.set begin (Scalar.byteAt value 0))

def boxStoreU16 (storage : List Byte) (begin : Nat) (value : BitVec 16) :
    Option (List Byte) :=
  if begin = Luffs.Runtime.TLSF.usizeMax then none
  else
    let second := begin + 1
    if second ≥ storage.length then none
    else some ((storage.set begin (Scalar.byteAt value 0)).set second
      (Scalar.byteAt value 8))

def boxLoadU32 (storage : List Byte) (begin : Nat) : Option (BitVec 32) := do
  if begin > Luffs.Runtime.TLSF.usizeMax - 3 then none
  let fourth := begin + 3
  if fourth ≥ storage.length then none
  let byte0 ← storage[begin]?
  let byte1 ← storage[begin + 1]?
  let byte2 ← storage[begin + 2]?
  let byte3 ← storage[fourth]?
  Scalar.decode32 [byte0, byte1, byte2, byte3]

def boxStoreU32 (storage : List Byte) (begin : Nat) (value : BitVec 32) :
    Option (List Byte) :=
  if begin > Luffs.Runtime.TLSF.usizeMax - 3 then none
  else
    let fourth := begin + 3
    if fourth ≥ storage.length then none
    else some ((((storage.set begin (Scalar.byteAt value 0)).set (begin + 1)
      (Scalar.byteAt value 8)).set (begin + 2) (Scalar.byteAt value 16)).set
      fourth (Scalar.byteAt value 24))

theorem boxLoadU32_after_boxStoreU32 (storage result : List Byte) (begin : Nat)
    (value : BitVec 32)
    (hsuccess : boxStoreU32 storage begin value = some result) :
    boxLoadU32 result begin = some value := by
  unfold boxStoreU32 at hsuccess
  split at hsuccess <;> try contradiction
  next hword =>
    dsimp only at hsuccess
    split at hsuccess <;> try contradiction
    next hbound =>
      simp only [Option.some.injEq] at hsuccess
      subst result
      have h0 : begin < storage.length := by omega
      have h1 : begin + 1 < storage.length := by omega
      have h2 : begin + 2 < storage.length := by omega
      have h3 : begin + 3 < storage.length := by omega
      simpa [boxLoadU32, hword, hbound, h0, h1, h2, h3,
        Scalar.encode32] using Scalar.decode32_encode32 value

def boxLoadU64 (storage : List Byte) (begin : Nat) : Option (BitVec 64) := do
  if begin > Luffs.Runtime.TLSF.usizeMax - 7 then none
  let eighth := begin + 7
  if eighth ≥ storage.length then none
  let byte0 ← storage[begin]?
  let byte1 ← storage[begin + 1]?
  let byte2 ← storage[begin + 2]?
  let byte3 ← storage[begin + 3]?
  let byte4 ← storage[begin + 4]?
  let byte5 ← storage[begin + 5]?
  let byte6 ← storage[begin + 6]?
  let byte7 ← storage[eighth]?
  Scalar.decode64 [byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7]

def boxStoreU64 (storage : List Byte) (begin : Nat) (value : BitVec 64) :
    Option (List Byte) :=
  if begin > Luffs.Runtime.TLSF.usizeMax - 7 then none
  else
    let eighth := begin + 7
    if eighth ≥ storage.length then none
    else some ((((((((storage.set begin (Scalar.byteAt value 0)).set (begin + 1)
      (Scalar.byteAt value 8)).set (begin + 2) (Scalar.byteAt value 16)).set
      (begin + 3) (Scalar.byteAt value 24)).set (begin + 4)
      (Scalar.byteAt value 32)).set (begin + 5) (Scalar.byteAt value 40)).set
      (begin + 6) (Scalar.byteAt value 48)).set eighth (Scalar.byteAt value 56))

def boxLoadU128 (storage : List Byte) (begin : Nat) : Option (BitVec 128) := do
  if begin > Luffs.Runtime.TLSF.usizeMax - 15 then none
  if begin + 15 ≥ storage.length then none
  let byte0 ← storage[begin]?
  let byte1 ← storage[begin + 1]?
  let byte2 ← storage[begin + 2]?
  let byte3 ← storage[begin + 3]?
  let byte4 ← storage[begin + 4]?
  let byte5 ← storage[begin + 5]?
  let byte6 ← storage[begin + 6]?
  let byte7 ← storage[begin + 7]?
  let byte8 ← storage[begin + 8]?
  let byte9 ← storage[begin + 9]?
  let byte10 ← storage[begin + 10]?
  let byte11 ← storage[begin + 11]?
  let byte12 ← storage[begin + 12]?
  let byte13 ← storage[begin + 13]?
  let byte14 ← storage[begin + 14]?
  let byte15 ← storage[begin + 15]?
  Scalar.decode128 [byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
    byte8, byte9, byte10, byte11, byte12, byte13, byte14, byte15]

def boxStoreU128 (storage : List Byte) (begin : Nat) (value : BitVec 128) :
    Option (List Byte) :=
  if begin > Luffs.Runtime.TLSF.usizeMax - 15 then none
  else if begin + 15 ≥ storage.length then none
  else some ((((((((((((((((storage.set begin (Scalar.byteAt value 0)).set
    (begin + 1) (Scalar.byteAt value 8)).set (begin + 2)
    (Scalar.byteAt value 16)).set (begin + 3) (Scalar.byteAt value 24)).set
    (begin + 4) (Scalar.byteAt value 32)).set (begin + 5)
    (Scalar.byteAt value 40)).set (begin + 6) (Scalar.byteAt value 48)).set
    (begin + 7) (Scalar.byteAt value 56)).set (begin + 8)
    (Scalar.byteAt value 64)).set (begin + 9) (Scalar.byteAt value 72)).set
    (begin + 10) (Scalar.byteAt value 80)).set (begin + 11)
    (Scalar.byteAt value 88)).set (begin + 12) (Scalar.byteAt value 96)).set
    (begin + 13) (Scalar.byteAt value 104)).set (begin + 14)
    (Scalar.byteAt value 112)).set (begin + 15) (Scalar.byteAt value 120))

theorem boxLoadU64_after_boxStoreU64 (storage result : List Byte) (begin : Nat)
    (value : BitVec 64)
    (hsuccess : boxStoreU64 storage begin value = some result) :
    boxLoadU64 result begin = some value := by
  unfold boxStoreU64 at hsuccess
  split at hsuccess <;> try contradiction
  next hword =>
    dsimp only at hsuccess
    split at hsuccess <;> try contradiction
    next hbound =>
      simp only [Option.some.injEq] at hsuccess
      subst result
      have h0 : begin < storage.length := by omega
      have h1 : begin + 1 < storage.length := by omega
      have h2 : begin + 2 < storage.length := by omega
      have h3 : begin + 3 < storage.length := by omega
      have h4 : begin + 4 < storage.length := by omega
      have h5 : begin + 5 < storage.length := by omega
      have h6 : begin + 6 < storage.length := by omega
      have h7 : begin + 7 < storage.length := by omega
      simpa [boxLoadU64, hword, hbound, h0, h1, h2, h3, h4, h5, h6, h7,
        Scalar.encode64] using Scalar.decode64_encode64 value

/-- Pointer-sized scalar codecs for the current 64-bit Luffs target. Indices
remain natural numbers in the checker; stored values are truncated exactly as
Rust's `as u64` conversion. -/
def boxLoadUsize (storage : List Byte) (begin : Nat) : Option Nat :=
  (boxLoadU64 storage begin).map BitVec.toNat

def boxStoreUsize (storage : List Byte) (begin value : Nat) :
    Option (List Byte) :=
  boxStoreU64 storage begin (BitVec.ofNat 64 value)

theorem boxLoadU16_eq_generic (storage : List Byte) (begin : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxLoadU16 storage begin = boxLoad Scalar.u16 storage begin := by
  by_cases hmax : begin = Luffs.Runtime.TLSF.usizeMax
  · have hgeneric : begin + Scalar.u16.size > storage.length := by
      simp only [Scalar.u16]
      omega
    have hleft : boxLoadU16 storage begin = none := by
      simp [boxLoadU16, hmax]
    have hright : boxLoad Scalar.u16 storage begin = none := by
      simp [boxLoad, hgeneric]
    rw [hleft, hright]
  · by_cases hbound : begin + 1 ≥ storage.length
    · have hgeneric : begin + Scalar.u16.size > storage.length := by
        simp only [Scalar.u16]
        omega
      simp [boxLoadU16, boxLoad, hmax, hbound, hgeneric]
    · have hfit : begin + 2 ≤ storage.length := by omega
      have hgeneric : ¬begin + Scalar.u16.size > storage.length := by
        simp only [Scalar.u16]
        omega
      have hlowBound : begin < storage.length := by omega
      have hhighBound : begin + 1 < storage.length := by omega
      let low := storage[begin]'hlowBound
      let high := storage[begin + 1]'hhighBound
      have hlowValue : storage[begin]? = some low :=
        List.getElem?_eq_getElem hlowBound
      have hhighValue : storage[begin + 1]? = some high :=
        List.getElem?_eq_getElem hhighBound
      rw [boxLoadU16, if_neg hmax, if_neg hbound, boxLoad, if_neg hgeneric]
      rw [hlowValue, hhighValue]
      simp only [Option.bind_eq_bind, Option.bind_some, Scalar.u16]
      congr 1
      exact (drop_take_pair_of_getElem? storage begin low high hlowValue
        hhighValue).symm

theorem boxLoadU32_eq_generic (storage : List Byte) (begin : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxLoadU32 storage begin = boxLoad Scalar.u32 storage begin := by
  by_cases hword : begin > Luffs.Runtime.TLSF.usizeMax - 3
  · have hgeneric : begin + Scalar.u32.size > storage.length := by
      simp only [Scalar.u32]
      omega
    simp [boxLoadU32, boxLoad, hword, hgeneric]
  · by_cases hbound : begin + 3 ≥ storage.length
    · have hgeneric : begin + Scalar.u32.size > storage.length := by
        simp only [Scalar.u32]
        omega
      simp [boxLoadU32, boxLoad, hword, hbound, hgeneric]
    · have hgeneric : ¬begin + Scalar.u32.size > storage.length := by
        simp only [Scalar.u32]
        omega
      have h0 : begin < storage.length := by omega
      have h1 : begin + 1 < storage.length := by omega
      have h2 : begin + 2 < storage.length := by omega
      have h3 : begin + 3 < storage.length := by omega
      let b0 := storage[begin]'h0
      let b1 := storage[begin + 1]'h1
      let b2 := storage[begin + 2]'h2
      let b3 := storage[begin + 3]'h3
      have hb0 : storage[begin]? = some b0 := List.getElem?_eq_getElem h0
      have hb1 : storage[begin + 1]? = some b1 := List.getElem?_eq_getElem h1
      have hb2 : storage[begin + 2]? = some b2 := List.getElem?_eq_getElem h2
      have hb3 : storage[begin + 3]? = some b3 := List.getElem?_eq_getElem h3
      rw [boxLoadU32, if_neg hword, if_neg hbound, boxLoad, if_neg hgeneric]
      rw [hb0, hb1, hb2, hb3]
      simp only [Option.bind_eq_bind, Option.bind_some, Scalar.u32]
      congr 1
      exact (drop_take_four_of_getElem? storage begin b0 b1 b2 b3 hb0 hb1
        hb2 hb3).symm

theorem boxLoadU64_eq_generic (storage : List Byte) (begin : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxLoadU64 storage begin = boxLoad Scalar.u64 storage begin := by
  by_cases hword : begin > Luffs.Runtime.TLSF.usizeMax - 7
  · have hgeneric : begin + Scalar.u64.size > storage.length := by
      simp only [Scalar.u64]
      omega
    simp [boxLoadU64, boxLoad, hword, hgeneric]
  · by_cases hbound : begin + 7 ≥ storage.length
    · have hgeneric : begin + Scalar.u64.size > storage.length := by
        simp only [Scalar.u64]
        omega
      simp [boxLoadU64, boxLoad, hword, hbound, hgeneric]
    · have hgeneric : ¬begin + Scalar.u64.size > storage.length := by
        simp only [Scalar.u64]
        omega
      have h0 : begin < storage.length := by omega
      have h1 : begin + 1 < storage.length := by omega
      have h2 : begin + 2 < storage.length := by omega
      have h3 : begin + 3 < storage.length := by omega
      have h4 : begin + 4 < storage.length := by omega
      have h5 : begin + 5 < storage.length := by omega
      have h6 : begin + 6 < storage.length := by omega
      have h7 : begin + 7 < storage.length := by omega
      let b0 := storage[begin]'h0
      let b1 := storage[begin + 1]'h1
      let b2 := storage[begin + 2]'h2
      let b3 := storage[begin + 3]'h3
      let b4 := storage[begin + 4]'h4
      let b5 := storage[begin + 5]'h5
      let b6 := storage[begin + 6]'h6
      let b7 := storage[begin + 7]'h7
      have hb0 : storage[begin]? = some b0 := List.getElem?_eq_getElem h0
      have hb1 : storage[begin + 1]? = some b1 := List.getElem?_eq_getElem h1
      have hb2 : storage[begin + 2]? = some b2 := List.getElem?_eq_getElem h2
      have hb3 : storage[begin + 3]? = some b3 := List.getElem?_eq_getElem h3
      have hb4 : storage[begin + 4]? = some b4 := List.getElem?_eq_getElem h4
      have hb5 : storage[begin + 5]? = some b5 := List.getElem?_eq_getElem h5
      have hb6 : storage[begin + 6]? = some b6 := List.getElem?_eq_getElem h6
      have hb7 : storage[begin + 7]? = some b7 := List.getElem?_eq_getElem h7
      rw [boxLoadU64, if_neg hword, if_neg hbound, boxLoad, if_neg hgeneric]
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
      simp only [Option.bind_eq_bind, Option.bind_some, Scalar.u64]
      congr 1
      exact (drop_take_eight_of_getElem? storage begin b0 b1 b2 b3 b4 b5 b6 b7
        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7).symm

theorem boxStoreU64_eq_generic (storage : List Byte) (begin : Nat)
    (value : BitVec 64)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxStoreU64 storage begin value = boxStore Scalar.u64 storage begin value := by
  by_cases hword : begin > Luffs.Runtime.TLSF.usizeMax - 7
  · have hgeneric : begin + Scalar.u64.size > storage.length := by
      simp only [Scalar.u64]
      omega
    simp [boxStoreU64, boxStore, hword, hgeneric]
  · by_cases hbound : begin + 7 ≥ storage.length
    · have hgeneric : begin + Scalar.u64.size > storage.length := by
        simp only [Scalar.u64]
        omega
      simp [boxStoreU64, boxStore, hword, hbound, hgeneric]
    · have hfit : begin + 8 ≤ storage.length := by omega
      have hwrite := writeBytes_eight_eq_set storage begin
        (Scalar.byteAt value 0) (Scalar.byteAt value 8)
        (Scalar.byteAt value 16) (Scalar.byteAt value 24)
        (Scalar.byteAt value 32) (Scalar.byteAt value 40)
        (Scalar.byteAt value 48) (Scalar.byteAt value 56) hfit
      simp [boxStoreU64, boxStore, hword, hbound, writeBytes,
        Scalar.u64, Scalar.encode64]
      exact ⟨hfit, by
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using
          hwrite.symm⟩

theorem boxLoadU128_eq_generic (storage : List Byte) (begin : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxLoadU128 storage begin = boxLoad Scalar.u128 storage begin := by
  by_cases hword : begin > Luffs.Runtime.TLSF.usizeMax - 15
  · have hgeneric : begin + Scalar.u128.size > storage.length := by
      simp only [Scalar.u128]
      omega
    simp [boxLoadU128, boxLoad, hword, hgeneric]
  · by_cases hbound : begin + 15 ≥ storage.length
    · have hgeneric : begin + Scalar.u128.size > storage.length := by
        simp only [Scalar.u128]
        omega
      simp [boxLoadU128, boxLoad, hword, hbound, hgeneric]
    · have hgeneric : ¬begin + Scalar.u128.size > storage.length := by
        simp only [Scalar.u128]
        omega
      have h0 : begin < storage.length := by omega
      have h1 : begin + 1 < storage.length := by omega
      have h2 : begin + 2 < storage.length := by omega
      have h3 : begin + 3 < storage.length := by omega
      have h4 : begin + 4 < storage.length := by omega
      have h5 : begin + 5 < storage.length := by omega
      have h6 : begin + 6 < storage.length := by omega
      have h7 : begin + 7 < storage.length := by omega
      have h8 : begin + 8 < storage.length := by omega
      have h9 : begin + 9 < storage.length := by omega
      have h10 : begin + 10 < storage.length := by omega
      have h11 : begin + 11 < storage.length := by omega
      have h12 : begin + 12 < storage.length := by omega
      have h13 : begin + 13 < storage.length := by omega
      have h14 : begin + 14 < storage.length := by omega
      have h15 : begin + 15 < storage.length := by omega
      let b0 := storage[begin]'h0
      let b1 := storage[begin + 1]'h1
      let b2 := storage[begin + 2]'h2
      let b3 := storage[begin + 3]'h3
      let b4 := storage[begin + 4]'h4
      let b5 := storage[begin + 5]'h5
      let b6 := storage[begin + 6]'h6
      let b7 := storage[begin + 7]'h7
      let b8 := storage[begin + 8]'h8
      let b9 := storage[begin + 9]'h9
      let b10 := storage[begin + 10]'h10
      let b11 := storage[begin + 11]'h11
      let b12 := storage[begin + 12]'h12
      let b13 := storage[begin + 13]'h13
      let b14 := storage[begin + 14]'h14
      let b15 := storage[begin + 15]'h15
      have hb0 : storage[begin]? = some b0 := List.getElem?_eq_getElem h0
      have hb1 : storage[begin + 1]? = some b1 := List.getElem?_eq_getElem h1
      have hb2 : storage[begin + 2]? = some b2 := List.getElem?_eq_getElem h2
      have hb3 : storage[begin + 3]? = some b3 := List.getElem?_eq_getElem h3
      have hb4 : storage[begin + 4]? = some b4 := List.getElem?_eq_getElem h4
      have hb5 : storage[begin + 5]? = some b5 := List.getElem?_eq_getElem h5
      have hb6 : storage[begin + 6]? = some b6 := List.getElem?_eq_getElem h6
      have hb7 : storage[begin + 7]? = some b7 := List.getElem?_eq_getElem h7
      have hb8 : storage[begin + 8]? = some b8 := List.getElem?_eq_getElem h8
      have hb9 : storage[begin + 9]? = some b9 := List.getElem?_eq_getElem h9
      have hb10 : storage[begin + 10]? = some b10 := List.getElem?_eq_getElem h10
      have hb11 : storage[begin + 11]? = some b11 := List.getElem?_eq_getElem h11
      have hb12 : storage[begin + 12]? = some b12 := List.getElem?_eq_getElem h12
      have hb13 : storage[begin + 13]? = some b13 := List.getElem?_eq_getElem h13
      have hb14 : storage[begin + 14]? = some b14 := List.getElem?_eq_getElem h14
      have hb15 : storage[begin + 15]? = some b15 := List.getElem?_eq_getElem h15
      rw [boxLoadU128, if_neg hword, if_neg hbound, boxLoad, if_neg hgeneric]
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11,
        hb12, hb13, hb14, hb15]
      simp only [Option.bind_eq_bind, Option.bind_some, Scalar.u128]
      congr 1
      exact (drop_take_sixteen_of_getElem? storage begin b0 b1 b2 b3 b4 b5 b6
        b7 b8 b9 b10 b11 b12 b13 b14 b15 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
        hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15).symm

theorem boxStoreU128_eq_generic (storage : List Byte) (begin : Nat)
    (value : BitVec 128)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxStoreU128 storage begin value = boxStore Scalar.u128 storage begin value := by
  by_cases hword : begin > Luffs.Runtime.TLSF.usizeMax - 15
  · have hgeneric : begin + Scalar.u128.size > storage.length := by
      simp only [Scalar.u128]
      omega
    simp [boxStoreU128, boxStore, hword, hgeneric]
  · by_cases hbound : begin + 15 ≥ storage.length
    · have hgeneric : begin + Scalar.u128.size > storage.length := by
        simp only [Scalar.u128]
        omega
      simp [boxStoreU128, boxStore, hword, hbound, hgeneric]
    · have hfit : begin + 16 ≤ storage.length := by omega
      have hwrite := writeBytes_sixteen_eq_set storage begin
        (Scalar.byteAt value 0) (Scalar.byteAt value 8)
        (Scalar.byteAt value 16) (Scalar.byteAt value 24)
        (Scalar.byteAt value 32) (Scalar.byteAt value 40)
        (Scalar.byteAt value 48) (Scalar.byteAt value 56)
        (Scalar.byteAt value 64) (Scalar.byteAt value 72)
        (Scalar.byteAt value 80) (Scalar.byteAt value 88)
        (Scalar.byteAt value 96) (Scalar.byteAt value 104)
        (Scalar.byteAt value 112) (Scalar.byteAt value 120) hfit
      simp [boxStoreU128, boxStore, hword, hbound, writeBytes,
        Scalar.u128, Scalar.encode128]
      exact ⟨hfit, by
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using
          hwrite.symm⟩

/-- A successful source-shaped sixteen-byte Box load returns exactly the owned
logical value and preserves exclusive ownership while exposing its read trace. -/
theorem boxLoadU128_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage : List Byte}
    {value expected : BitVec 128} (hstorageMax : storage.length ≤
      Luffs.Runtime.TLSF.usizeMax)
    (hload : boxLoadU128 storage block.offset = some value)
    (hencoded : (storage.drop block.offset).take Scalar.u128.size =
      Scalar.u128.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u128 pool block expected ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Box.Owns Scalar.u128 pool block expected) ∗
          ⌜ReadSteps (block.region pool).base (Scalar.u128.encode expected) mem ∧
            Scalar.u128.decode (Scalar.u128.encode expected) = some expected⌝) := by
  have hgeneric : boxLoad Scalar.u128 storage block.offset = some value := by
    rw [← boxLoadU128_eq_generic storage block.offset hstorageMax]
    exact hload
  have hexpected : boxLoad Scalar.u128 storage block.offset = some expected :=
    boxLoad_of_encoded Scalar.u128 storage block.offset expected
      (boxLoad_result hgeneric).1 hencoded
  have hvalue : value = expected := by
    rw [hgeneric] at hexpected
    exact Option.some.inj hexpected
  refine ⟨hvalue, ?_⟩
  exact Luffs.Containers.Box.deref_read Scalar.u128 hrep

/-- A successful source-shaped sixteen-byte Box store inherits the generic
frame-preserving ownership update and exact closed write WP. -/
theorem boxStoreU128_owns_wp {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage nextStorage : List Byte}
    (oldValue newValue : BitVec 128)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hstore : boxStoreU128 storage block.offset newValue = some nextStorage)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    nextStorage = writeBytes storage block.offset (Scalar.u128.encode newValue) ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u128 pool block oldValue ==∗
        (contentsInterp
            (insertBytes contents (block.region pool).base
              (Scalar.u128.encode newValue)) ∗
          Luffs.Containers.Box.Owns Scalar.u128 pool block newValue) ∗
          ⌜∃ next,
            WriteSteps (block.region pool).base (Scalar.u128.encode newValue)
              mem next ∧
            (⊢@{Iris.IProp GF} Program.wp
              (Program.writeBytes (block.region pool).base
                (Scalar.u128.encode newValue))
              mem (fun final => final = next))⌝) := by
  have hgeneric : boxStore Scalar.u128 storage block.offset newValue =
      some nextStorage := by
    rw [← boxStoreU128_eq_generic storage block.offset newValue hstorageMax]
    exact hstore
  exact ⟨(boxStore_result hgeneric).2, Luffs.Containers.Box.store_wp Scalar.u128
    oldValue newValue contents mem hrep⟩

/-- A successful concrete eight-byte Box load returns the logical value encoded
in the owned allocation and preserves both authoritative contents and exclusive
Box ownership while exposing the exact read trace. -/
theorem boxLoadU64_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage : List Byte}
    {value expected : BitVec 64} (hstorageMax : storage.length ≤
      Luffs.Runtime.TLSF.usizeMax)
    (hload : boxLoadU64 storage block.offset = some value)
    (hencoded : (storage.drop block.offset).take Scalar.u64.size =
      Scalar.u64.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u64 pool block expected ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Box.Owns Scalar.u64 pool block expected) ∗
          ⌜ReadSteps (block.region pool).base (Scalar.u64.encode expected) mem ∧
            Scalar.u64.decode (Scalar.u64.encode expected) = some expected⌝) := by
  have hgeneric : boxLoad Scalar.u64 storage block.offset = some value := by
    rw [← boxLoadU64_eq_generic storage block.offset hstorageMax]
    exact hload
  have hexpected : boxLoad Scalar.u64 storage block.offset = some expected :=
    boxLoad_of_encoded Scalar.u64 storage block.offset expected
      (boxLoad_result hgeneric).1 hencoded
  have hvalue : value = expected := by
    rw [hgeneric] at hexpected
    exact Option.some.inj hexpected
  refine ⟨hvalue, ?_⟩
  exact Luffs.Containers.Box.deref_read Scalar.u64 hrep

/-- A successful concrete eight-byte Box store is exactly the generic codec
write and inherits its frame-preserving Iris ownership update and closed WP. -/
theorem boxStoreU64_owns_wp {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage nextStorage : List Byte}
    (oldValue newValue : BitVec 64)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hstore : boxStoreU64 storage block.offset newValue = some nextStorage)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    nextStorage = writeBytes storage block.offset (Scalar.u64.encode newValue) ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u64 pool block oldValue ==∗
        (contentsInterp
            (insertBytes contents (block.region pool).base
              (Scalar.u64.encode newValue)) ∗
          Luffs.Containers.Box.Owns Scalar.u64 pool block newValue) ∗
          ⌜∃ next,
            WriteSteps (block.region pool).base (Scalar.u64.encode newValue)
              mem next ∧
            (⊢@{Iris.IProp GF} Program.wp
              (Program.writeBytes (block.region pool).base
                (Scalar.u64.encode newValue))
              mem (fun final => final = next))⌝) := by
  have hgeneric : boxStore Scalar.u64 storage block.offset newValue =
      some nextStorage := by
    rw [← boxStoreU64_eq_generic storage block.offset newValue hstorageMax]
    exact hstore
  exact ⟨(boxStore_result hgeneric).2, Luffs.Containers.Box.store_wp Scalar.u64
    oldValue newValue contents mem hrep⟩

theorem boxStoreU32_eq_generic (storage : List Byte) (begin : Nat)
    (value : BitVec 32)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxStoreU32 storage begin value = boxStore Scalar.u32 storage begin value := by
  by_cases hword : begin > Luffs.Runtime.TLSF.usizeMax - 3
  · have hgeneric : begin + Scalar.u32.size > storage.length := by
      simp only [Scalar.u32]
      omega
    simp [boxStoreU32, boxStore, hword, hgeneric]
  · by_cases hbound : begin + 3 ≥ storage.length
    · have hgeneric : begin + Scalar.u32.size > storage.length := by
        simp only [Scalar.u32]
        omega
      simp [boxStoreU32, boxStore, hword, hbound, hgeneric]
    · have hfit : begin + 4 ≤ storage.length := by omega
      have hgeneric : ¬begin + Scalar.u32.size > storage.length := by
        simp only [Scalar.u32]
        omega
      have hwrite := writeBytes_four_eq_set storage begin
        (Scalar.byteAt value 0) (Scalar.byteAt value 8)
        (Scalar.byteAt value 16) (Scalar.byteAt value 24) hfit
      simp [boxStoreU32, boxStore, hword, hbound, writeBytes,
        Scalar.u32, Scalar.encode32]
      exact ⟨hfit, by
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using
          hwrite.symm⟩

/-- A successful concrete four-byte Box load returns the logical value encoded
in the owned allocation and preserves both authoritative contents and exclusive
Box ownership while exposing the exact read trace. -/
theorem boxLoadU32_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage : List Byte}
    {value expected : BitVec 32} (hstorageMax : storage.length ≤
      Luffs.Runtime.TLSF.usizeMax)
    (hload : boxLoadU32 storage block.offset = some value)
    (hencoded : (storage.drop block.offset).take Scalar.u32.size =
      Scalar.u32.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u32 pool block expected ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Box.Owns Scalar.u32 pool block expected) ∗
          ⌜ReadSteps (block.region pool).base (Scalar.u32.encode expected) mem ∧
            Scalar.u32.decode (Scalar.u32.encode expected) = some expected⌝) := by
  have hgeneric : boxLoad Scalar.u32 storage block.offset = some value := by
    rw [← boxLoadU32_eq_generic storage block.offset hstorageMax]
    exact hload
  have hexpected : boxLoad Scalar.u32 storage block.offset = some expected :=
    boxLoad_of_encoded Scalar.u32 storage block.offset expected
      (boxLoad_result hgeneric).1 hencoded
  have hvalue : value = expected := by
    rw [hgeneric] at hexpected
    exact Option.some.inj hexpected
  refine ⟨hvalue, ?_⟩
  exact Luffs.Containers.Box.deref_read Scalar.u32 hrep

/-- A successful concrete four-byte Box store is exactly the generic codec
write and inherits its frame-preserving Iris ownership update and closed WP. -/
theorem boxStoreU32_owns_wp {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage nextStorage : List Byte}
    (oldValue newValue : BitVec 32)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hstore : boxStoreU32 storage block.offset newValue = some nextStorage)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    nextStorage = writeBytes storage block.offset (Scalar.u32.encode newValue) ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u32 pool block oldValue ==∗
        (contentsInterp
            (insertBytes contents (block.region pool).base
              (Scalar.u32.encode newValue)) ∗
          Luffs.Containers.Box.Owns Scalar.u32 pool block newValue) ∗
          ⌜∃ next,
            WriteSteps (block.region pool).base (Scalar.u32.encode newValue)
              mem next ∧
            (⊢@{Iris.IProp GF} Program.wp
              (Program.writeBytes (block.region pool).base
                (Scalar.u32.encode newValue))
              mem (fun final => final = next))⌝) := by
  have hgeneric : boxStore Scalar.u32 storage block.offset newValue =
      some nextStorage := by
    rw [← boxStoreU32_eq_generic storage block.offset newValue hstorageMax]
    exact hstore
  exact ⟨(boxStore_result hgeneric).2, Luffs.Containers.Box.store_wp Scalar.u32
    oldValue newValue contents mem hrep⟩

theorem boxStoreU16_eq_generic (storage : List Byte) (begin : Nat)
    (value : BitVec 16)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    boxStoreU16 storage begin value = boxStore Scalar.u16 storage begin value := by
  by_cases hmax : begin = Luffs.Runtime.TLSF.usizeMax
  · have hgeneric : begin + Scalar.u16.size > storage.length := by
      simp only [Scalar.u16]
      omega
    simp [boxStoreU16, boxStore, hmax, hgeneric]
    omega
  · by_cases hbound : begin + 1 ≥ storage.length
    · have hgeneric : begin + Scalar.u16.size > storage.length := by
        simp only [Scalar.u16]
        omega
      simp [boxStoreU16, boxStore, hmax, hbound, hgeneric]
    · have hfit : begin + 2 ≤ storage.length := by omega
      have hgeneric : ¬begin + Scalar.u16.size > storage.length := by
        simp only [Scalar.u16]
        omega
      have hwrite := writeBytes_pair_eq_set storage begin
        (Scalar.byteAt value 0) (Scalar.byteAt value 8) hfit
      simp [boxStoreU16, boxStore, hmax, hbound, hgeneric, writeBytes,
        Scalar.u16, Scalar.encode16]
      exact ⟨hfit, by
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using
          hwrite.symm⟩

/-- A successful concrete two-byte Box load returns the logical value encoded
in the owned allocation and preserves both authoritative contents and exclusive
Box ownership while exposing the exact read trace. -/
theorem boxLoadU16_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage : List Byte}
    {value expected : BitVec 16} (hstorageMax : storage.length ≤
      Luffs.Runtime.TLSF.usizeMax)
    (hload : boxLoadU16 storage block.offset = some value)
    (hencoded : (storage.drop block.offset).take Scalar.u16.size =
      Scalar.u16.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u16 pool block expected ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Box.Owns Scalar.u16 pool block expected) ∗
          ⌜ReadSteps (block.region pool).base (Scalar.u16.encode expected) mem ∧
            Scalar.u16.decode (Scalar.u16.encode expected) = some expected⌝) := by
  have hgeneric : boxLoad Scalar.u16 storage block.offset = some value := by
    rw [← boxLoadU16_eq_generic storage block.offset hstorageMax]
    exact hload
  have hexpected : boxLoad Scalar.u16 storage block.offset = some expected :=
    boxLoad_of_encoded Scalar.u16 storage block.offset expected
      (boxLoad_result hgeneric).1 hencoded
  have hvalue : value = expected := by
    rw [hgeneric] at hexpected
    exact Option.some.inj hexpected
  refine ⟨hvalue, ?_⟩
  exact Luffs.Containers.Box.deref_read Scalar.u16 hrep

/-- A successful concrete two-byte Box store is exactly the generic codec
write and inherits its frame-preserving Iris ownership update and closed WP. -/
theorem boxStoreU16_owns_wp {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage nextStorage : List Byte}
    (oldValue newValue : BitVec 16)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hstore : boxStoreU16 storage block.offset newValue = some nextStorage)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    nextStorage = writeBytes storage block.offset (Scalar.u16.encode newValue) ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u16 pool block oldValue ==∗
        (contentsInterp
            (insertBytes contents (block.region pool).base
              (Scalar.u16.encode newValue)) ∗
          Luffs.Containers.Box.Owns Scalar.u16 pool block newValue) ∗
          ⌜∃ next,
            WriteSteps (block.region pool).base (Scalar.u16.encode newValue)
              mem next ∧
            (⊢@{Iris.IProp GF} Program.wp
              (Program.writeBytes (block.region pool).base
                (Scalar.u16.encode newValue))
              mem (fun final => final = next))⌝) := by
  have hgeneric : boxStore Scalar.u16 storage block.offset newValue =
      some nextStorage := by
    rw [← boxStoreU16_eq_generic storage block.offset newValue hstorageMax]
    exact hstore
  exact ⟨(boxStore_result hgeneric).2, Luffs.Containers.Box.store_wp Scalar.u16
    oldValue newValue contents mem hrep⟩

theorem boxLoadU16_after_boxStoreU16 (storage result : List Byte) (begin : Nat)
    (value : BitVec 16)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hsuccess : boxStoreU16 storage begin value = some result) :
    boxLoadU16 result begin = some value := by
  have hgenericStore : boxStore Scalar.u16 storage begin value = some result := by
    rw [← boxStoreU16_eq_generic storage begin value hstorageMax]
    exact hsuccess
  obtain ⟨hbound, hresult⟩ := boxStore_result hgenericStore
  have hresultLength : result.length = storage.length := by
    rw [hresult, writeBytes_length storage begin (Scalar.u16.encode value)]
    simpa [Scalar.u16, Scalar.encode16] using hbound
  rw [boxLoadU16_eq_generic result begin (by omega)]
  exact boxLoad_after_boxStore Scalar.u16 storage begin value result hgenericStore

theorem boxStoreU8_eq_generic (storage : List Byte) (begin : Nat)
    (value : Byte) :
    boxStoreU8 storage begin value =
      boxStore Scalar.u8 storage begin (Scalar.bv8OfByte value) := by
  by_cases hbound : begin ≥ storage.length
  · have hgeneric : begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    simp [boxStoreU8, boxStore, hbound, hgeneric]
  · have hlt : begin < storage.length := Nat.lt_of_not_ge hbound
    have hgeneric : ¬begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    have hwrite := writeBytes_singleton_eq_set storage begin value hlt
    simp [boxStoreU8, boxStore, hbound, hgeneric, writeBytes, Scalar.u8,
      Scalar.encode8, Scalar.bv8OfByte, Scalar.byteOfBV8]
    exact ⟨by omega, by
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        hwrite.symm⟩

theorem boxLoadU8_eq_generic (storage : List Byte) (begin : Nat) :
    (boxLoadU8 storage begin).map Scalar.bv8OfByte =
      boxLoad Scalar.u8 storage begin := by
  by_cases hbound : begin < storage.length
  · have hgeneric : ¬begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    have hget : storage[begin]? = some storage[begin] :=
      List.getElem?_eq_getElem hbound
    have hslice : (storage.drop begin).take 1 = [storage[begin]] := by
      rw [List.drop_eq_getElem_cons hbound]
      rfl
    rw [boxLoadU8, hget, boxLoad, if_neg hgeneric]
    change some (Scalar.bv8OfByte storage[begin]) =
      Scalar.decode8 ((storage.drop begin).take 1)
    rw [hslice]
    rfl
  · have hgeneric : begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    have hget : storage[begin]? = none :=
      List.getElem?_eq_none (Nat.le_of_not_gt hbound)
    simp [boxLoadU8, hget, boxLoad, hgeneric]

theorem boxLoadI8_eq_generic (storage : List Byte) (begin : Nat) :
    boxLoadI8 storage begin = boxLoad Scalar.u8 storage begin := by
  by_cases hbound : begin < storage.length
  · have hgeneric : ¬begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    have hget : storage[begin]? = some storage[begin] :=
      List.getElem?_eq_getElem hbound
    have hslice : (storage.drop begin).take 1 = [storage[begin]] := by
      rw [List.drop_eq_getElem_cons hbound]
      rfl
    rw [boxLoadI8, if_neg (Nat.not_le.mpr hbound), hget, boxLoad,
      if_neg hgeneric]
    change Scalar.decode8 [storage[begin]] =
      Scalar.decode8 ((storage.drop begin).take 1)
    rw [hslice]
  · have hgeneric : begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    have hget : storage[begin]? = none :=
      List.getElem?_eq_none (Nat.le_of_not_gt hbound)
    simp [boxLoadI8, hget, boxLoad, hgeneric]

theorem boxStoreI8_eq_generic (storage : List Byte) (begin : Nat)
    (value : BitVec 8) :
    boxStoreI8 storage begin value = boxStore Scalar.u8 storage begin value := by
  by_cases hbound : begin ≥ storage.length
  · have hgeneric : begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    simp [boxStoreI8, boxStore, hbound, hgeneric]
  · have hlt : begin < storage.length := Nat.lt_of_not_ge hbound
    have hgeneric : ¬begin + Scalar.u8.size > storage.length := by
      simp only [Scalar.u8]
      omega
    have hbyte : Scalar.byteAt value 0 = Scalar.byteOfBV8 value := by
      apply Fin.ext
      rfl
    have hwrite := writeBytes_singleton_eq_set storage begin
      (Scalar.byteAt value 0) hlt
    rw [hbyte] at hwrite
    simp [boxStoreI8, boxStore, hbound, hgeneric, writeBytes, Scalar.u8,
      Scalar.encode8, hbyte]
    exact ⟨by omega, by
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        hwrite.symm⟩

/-- Signed one-byte loads use the generic `Scalar.u8` representation, return
the exclusively owned bits, and expose exactly one operational read. -/
theorem boxLoadI8_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage : List Byte}
    {value expected : BitVec 8}
    (hload : boxLoadI8 storage block.offset = some value)
    (hencoded : (storage.drop block.offset).take Scalar.u8.size =
      Scalar.u8.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block expected ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block expected) ∗
          ⌜ReadSteps (block.region pool).base (Scalar.u8.encode expected) mem ∧
            Scalar.u8.decode (Scalar.u8.encode expected) = some expected⌝) := by
  have hgeneric : boxLoad Scalar.u8 storage block.offset = some value := by
    rw [← boxLoadI8_eq_generic storage block.offset]
    exact hload
  have hexpected : boxLoad Scalar.u8 storage block.offset = some expected :=
    boxLoad_of_encoded Scalar.u8 storage block.offset expected
      (boxLoad_result hgeneric).1 hencoded
  have hvalue : value = expected := by
    rw [hgeneric] at hexpected
    exact Option.some.inj hexpected
  refine ⟨hvalue, ?_⟩
  exact Luffs.Containers.Box.deref_read Scalar.u8 hrep

/-- Signed one-byte stores update the generic bit representation and inherit
the exact frame-preserving one-write WP. -/
theorem boxStoreI8_owns_wp {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage nextStorage : List Byte}
    (oldValue newValue : BitVec 8)
    (hstore : boxStoreI8 storage block.offset newValue = some nextStorage)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    nextStorage = writeBytes storage block.offset (Scalar.u8.encode newValue) ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block oldValue ==∗
        (contentsInterp
            (insertBytes contents (block.region pool).base
              (Scalar.u8.encode newValue)) ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block newValue) ∗
          ⌜∃ next,
            WriteSteps (block.region pool).base (Scalar.u8.encode newValue)
              mem next ∧
            (⊢@{Iris.IProp GF} Program.wp
              (Program.writeBytes (block.region pool).base
                (Scalar.u8.encode newValue))
              mem (fun final => final = next))⌝) := by
  have hgeneric : boxStore Scalar.u8 storage block.offset newValue =
      some nextStorage := by
    rw [← boxStoreI8_eq_generic storage block.offset newValue]
    exact hstore
  exact ⟨(boxStore_result hgeneric).2, Luffs.Containers.Box.store_wp Scalar.u8
    oldValue newValue contents mem hrep⟩

/-- A successful concrete byte Box load returns the logical byte encoded in the
owned allocation and preserves ownership while exposing its one-read trace. -/
theorem boxLoadU8_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage : List Byte}
    {value expected : Byte} (hload : boxLoadU8 storage block.offset = some value)
    (hencoded : (storage.drop block.offset).take Scalar.u8.size =
      Scalar.u8.encode (Scalar.bv8OfByte expected))
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block
            (Scalar.bv8OfByte expected) ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block
            (Scalar.bv8OfByte expected)) ∗
          ⌜ReadSteps (block.region pool).base
              (Scalar.u8.encode (Scalar.bv8OfByte expected)) mem ∧
            Scalar.u8.decode (Scalar.u8.encode (Scalar.bv8OfByte expected)) =
              some (Scalar.bv8OfByte expected)⌝) := by
  have hgeneric : boxLoad Scalar.u8 storage block.offset =
      some (Scalar.bv8OfByte value) := by
    rw [← boxLoadU8_eq_generic storage block.offset, hload]
    rfl
  have hexpected : boxLoad Scalar.u8 storage block.offset =
      some (Scalar.bv8OfByte expected) :=
    boxLoad_of_encoded Scalar.u8 storage block.offset
      (Scalar.bv8OfByte expected) (boxLoad_result hgeneric).1 hencoded
  have hbv : Scalar.bv8OfByte value = Scalar.bv8OfByte expected := by
    rw [hgeneric] at hexpected
    exact Option.some.inj hexpected
  have hvalue : value = expected := by
    exact Fin.ext (congrArg BitVec.toNat hbv)
  refine ⟨hvalue, ?_⟩
  exact Luffs.Containers.Box.deref_read Scalar.u8 hrep

/-- A successful concrete byte Box store inherits the generic codec's
frame-preserving ownership update and closed one-write WP. -/
theorem boxStoreU8_owns_wp {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {block : Block} {storage nextStorage : List Byte}
    (oldValue newValue : Byte)
    (hstore : boxStoreU8 storage block.offset newValue = some nextStorage)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    nextStorage = writeBytes storage block.offset
        (Scalar.u8.encode (Scalar.bv8OfByte newValue)) ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block
            (Scalar.bv8OfByte oldValue) ==∗
        (contentsInterp
            (insertBytes contents (block.region pool).base
              (Scalar.u8.encode (Scalar.bv8OfByte newValue))) ∗
          Luffs.Containers.Box.Owns Scalar.u8 pool block
            (Scalar.bv8OfByte newValue)) ∗
          ⌜∃ next,
            WriteSteps (block.region pool).base
              (Scalar.u8.encode (Scalar.bv8OfByte newValue)) mem next ∧
            (⊢@{Iris.IProp GF} Program.wp
              (Program.writeBytes (block.region pool).base
                (Scalar.u8.encode (Scalar.bv8OfByte newValue)))
              mem (fun final => final = next))⌝) := by
  have hgeneric : boxStore Scalar.u8 storage block.offset
      (Scalar.bv8OfByte newValue) = some nextStorage := by
    rw [← boxStoreU8_eq_generic storage block.offset newValue]
    exact hstore
  exact ⟨(boxStore_result hgeneric).2, Luffs.Containers.Box.store_wp Scalar.u8
    (Scalar.bv8OfByte oldValue) (Scalar.bv8OfByte newValue) contents mem hrep⟩

def vecPushU8 (storage : List Byte) (len capacity : Nat) (value : Byte) :
    Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if capacity > storage.length then none
  else some (storage.set len value, len + 1)

def vecPushU16 (storage : List Byte) (offset len capacity : Nat)
    (value : BitVec 16) : Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if len > Luffs.Runtime.TLSF.usizeMax / 2 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - len * 2 then none
  else if offset + len * 2 > Luffs.Runtime.TLSF.usizeMax - 2 then none
  else if offset + len * 2 + 1 ≥ storage.length then none
  else some ((storage.set (offset + len * 2) (Scalar.byteAt value 0)).set
    (offset + len * 2 + 1) (Scalar.byteAt value 8), len + 1)

theorem vecPushU16_result {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 16}
    (hpush : vecPushU16 storage offset len capacity value = some (next, nextLen)) :
    len < capacity ∧ len ≤ Luffs.Runtime.TLSF.usizeMax / 2 ∧
      offset ≤ Luffs.Runtime.TLSF.usizeMax - len * 2 ∧
      offset + len * 2 ≤ Luffs.Runtime.TLSF.usizeMax - 2 ∧
      offset + len * 2 + 2 ≤ storage.length ∧
      next = (storage.set (offset + len * 2) (Scalar.byteAt value 0)).set
        (offset + len * 2 + 1) (Scalar.byteAt value 8) ∧
      nextLen = len + 1 := by
  unfold vecPushU16 at hpush
  split at hpush
  next => contradiction
  next hlen =>
    split at hpush
    next => contradiction
    next hmul =>
      split at hpush
      next => contradiction
      next hoffset =>
        split at hpush
        next => contradiction
        next haddress =>
          split at hpush
          next => contradiction
          next hstorage =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hpush
            exact ⟨Nat.lt_of_not_ge hlen, Nat.le_of_not_gt hmul,
              Nat.le_of_not_gt hoffset, Nat.le_of_not_gt haddress,
              by omega, hpush.1.symm, hpush.2.symm⟩

theorem vecPushU16_refines_generic {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 16}
    (hcapacityMax : capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hpush : vecPushU16 storage offset len capacity value = some (next, nextLen)) :
    vecPush Scalar.u16 storage offset len capacity value =
      some ⟨next, nextLen⟩ := by
  obtain ⟨hlen, hmul, hoffset, haddress, hstorage, hnext, hnextLen⟩ :=
    vecPushU16_result hpush
  have hwrite := writeBytes_pair_eq_set storage (offset + len * 2)
    (Scalar.byteAt value 0) (Scalar.byteAt value 8) hstorage
  have hstoreBound : ¬storage.length < offset + len * 2 + 2 := by omega
  rw [hnext, hnextLen]
  simp [vecPush, Scalar.u16, hcapacityMax, hlen, hmul, hoffset, haddress,
    boxStore, hstoreBound, writeBytes, Scalar.encode16]
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using
    hwrite

/-- The concrete two-byte Luffs push inherits the generic Vec ownership law:
exactly one initialized `u16` encoding is appended and exclusive ownership of
the same allocation is retained. -/
theorem vecPushU16_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage nextStorage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {values : List (BitVec 16)}
    {value : BitVec 16} {nextLen : Nat}
    (hcapacityMax : handle.capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hpush : vecPushU16 storage handle.block.offset handle.len
      handle.capacity value = some (nextStorage, nextLen)) :
    ∃ nextHandle,
      Luffs.Containers.Vec.push handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage
        (handle.block.offset +
          (Luffs.Containers.Vec.encodeValues Scalar.u16 values).length)
        (Scalar.u16.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues Scalar.u16 values).length)
          (Scalar.u16.encode value) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns Scalar.u16 pool handle values ==∗
          contentsInterp
              (insertBytes contents
                ((handle.block.region pool).base +
                  (Luffs.Containers.Vec.encodeValues Scalar.u16 values).length)
                (Scalar.u16.encode value)) ∗
            Luffs.Containers.Vec.Owns Scalar.u16 pool nextHandle
              (values ++ [value]) := by
  have hgeneric : vecPush Scalar.u16 storage handle.block.offset handle.len
      handle.capacity value = some ⟨nextStorage, nextLen⟩ :=
    vecPushU16_refines_generic hcapacityMax hpush
  exact vecPush_owns Scalar.u16 hlen hgeneric

def vecPushU32 (storage : List Byte) (offset len capacity : Nat)
    (value : BitVec 32) : Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if len > Luffs.Runtime.TLSF.usizeMax / 4 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - len * 4 then none
  else if offset + len * 4 > Luffs.Runtime.TLSF.usizeMax - 4 then none
  else if offset + len * 4 + 3 ≥ storage.length then none
  else some (((((storage.set (offset + len * 4) (Scalar.byteAt value 0)).set
    (offset + len * 4 + 1) (Scalar.byteAt value 8)).set
    (offset + len * 4 + 2) (Scalar.byteAt value 16)).set
    (offset + len * 4 + 3) (Scalar.byteAt value 24)), len + 1)

theorem vecPushU32_result {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 32}
    (hpush : vecPushU32 storage offset len capacity value =
      some (next, nextLen)) :
    len < capacity ∧ len ≤ Luffs.Runtime.TLSF.usizeMax / 4 ∧
      offset ≤ Luffs.Runtime.TLSF.usizeMax - len * 4 ∧
      offset + len * 4 ≤ Luffs.Runtime.TLSF.usizeMax - 4 ∧
      offset + len * 4 + 4 ≤ storage.length ∧
      next = (((storage.set (offset + len * 4) (Scalar.byteAt value 0)).set
        (offset + len * 4 + 1) (Scalar.byteAt value 8)).set
        (offset + len * 4 + 2) (Scalar.byteAt value 16)).set
        (offset + len * 4 + 3) (Scalar.byteAt value 24) ∧
      nextLen = len + 1 := by
  unfold vecPushU32 at hpush
  split at hpush <;> try contradiction
  next hlen =>
    split at hpush <;> try contradiction
    next hmul =>
      split at hpush <;> try contradiction
      next hoffset =>
        split at hpush <;> try contradiction
        next haddress =>
          split at hpush <;> try contradiction
          next hstorage =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hpush
            exact ⟨Nat.lt_of_not_ge hlen, Nat.le_of_not_gt hmul,
              Nat.le_of_not_gt hoffset, Nat.le_of_not_gt haddress,
              by omega, hpush.1.symm, hpush.2.symm⟩

theorem vecPushU32_refines_generic {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 32}
    (hcapacityMax : capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hpush : vecPushU32 storage offset len capacity value =
      some (next, nextLen)) :
    vecPush Scalar.u32 storage offset len capacity value =
      some ⟨next, nextLen⟩ := by
  obtain ⟨hlen, hmul, hoffset, haddress, hstorage, hnext, hnextLen⟩ :=
    vecPushU32_result hpush
  have hwrite := writeBytes_four_eq_set storage (offset + len * 4)
    (Scalar.byteAt value 0) (Scalar.byteAt value 8)
    (Scalar.byteAt value 16) (Scalar.byteAt value 24) hstorage
  have hstoreBound : ¬storage.length < offset + len * 4 + 4 := by omega
  rw [hnext, hnextLen]
  simp [vecPush, Scalar.u32, hcapacityMax, hlen, hmul, hoffset, haddress,
    boxStore, hstoreBound, writeBytes, Scalar.encode32]
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using hwrite

theorem vecPushU32_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage nextStorage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {values : List (BitVec 32)}
    {value : BitVec 32} {nextLen : Nat}
    (hcapacityMax : handle.capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hpush : vecPushU32 storage handle.block.offset handle.len
      handle.capacity value = some (nextStorage, nextLen)) :
    ∃ nextHandle,
      Luffs.Containers.Vec.push handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage
        (handle.block.offset +
          (Luffs.Containers.Vec.encodeValues Scalar.u32 values).length)
        (Scalar.u32.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues Scalar.u32 values).length)
          (Scalar.u32.encode value) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns Scalar.u32 pool handle values ==∗
          contentsInterp
              (insertBytes contents
                ((handle.block.region pool).base +
                  (Luffs.Containers.Vec.encodeValues Scalar.u32 values).length)
                (Scalar.u32.encode value)) ∗
            Luffs.Containers.Vec.Owns Scalar.u32 pool nextHandle
              (values ++ [value]) := by
  have hgeneric : vecPush Scalar.u32 storage handle.block.offset handle.len
      handle.capacity value = some ⟨nextStorage, nextLen⟩ :=
    vecPushU32_refines_generic hcapacityMax hpush
  exact vecPush_owns Scalar.u32 hlen hgeneric

def vecPushU64 (storage : List Byte) (offset len capacity : Nat)
    (value : BitVec 64) : Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if len > Luffs.Runtime.TLSF.usizeMax / 8 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - len * 8 then none
  else if offset + len * 8 > Luffs.Runtime.TLSF.usizeMax - 8 then none
  else if offset + len * 8 + 7 ≥ storage.length then none
  else some (((((((((storage.set (offset + len * 8) (Scalar.byteAt value 0)).set
    (offset + len * 8 + 1) (Scalar.byteAt value 8)).set
    (offset + len * 8 + 2) (Scalar.byteAt value 16)).set
    (offset + len * 8 + 3) (Scalar.byteAt value 24)).set
    (offset + len * 8 + 4) (Scalar.byteAt value 32)).set
    (offset + len * 8 + 5) (Scalar.byteAt value 40)).set
    (offset + len * 8 + 6) (Scalar.byteAt value 48)).set
    (offset + len * 8 + 7) (Scalar.byteAt value 56)), len + 1)

def vecPushU128 (storage : List Byte) (offset len capacity : Nat)
    (value : BitVec 128) : Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if len > Luffs.Runtime.TLSF.usizeMax / 16 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - len * 16 then none
  else if offset + len * 16 > Luffs.Runtime.TLSF.usizeMax - 16 then none
  else if offset + len * 16 + 15 ≥ storage.length then none
  else some (((((((((((((((((storage.set (offset + len * 16)
    (Scalar.byteAt value 0)).set (offset + len * 16 + 1)
    (Scalar.byteAt value 8)).set (offset + len * 16 + 2)
    (Scalar.byteAt value 16)).set (offset + len * 16 + 3)
    (Scalar.byteAt value 24)).set (offset + len * 16 + 4)
    (Scalar.byteAt value 32)).set (offset + len * 16 + 5)
    (Scalar.byteAt value 40)).set (offset + len * 16 + 6)
    (Scalar.byteAt value 48)).set (offset + len * 16 + 7)
    (Scalar.byteAt value 56)).set (offset + len * 16 + 8)
    (Scalar.byteAt value 64)).set (offset + len * 16 + 9)
    (Scalar.byteAt value 72)).set (offset + len * 16 + 10)
    (Scalar.byteAt value 80)).set (offset + len * 16 + 11)
    (Scalar.byteAt value 88)).set (offset + len * 16 + 12)
    (Scalar.byteAt value 96)).set (offset + len * 16 + 13)
    (Scalar.byteAt value 104)).set (offset + len * 16 + 14)
    (Scalar.byteAt value 112)).set (offset + len * 16 + 15)
    (Scalar.byteAt value 120)), len + 1)

theorem vecPushU128_result {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 128}
    (hpush : vecPushU128 storage offset len capacity value =
      some (next, nextLen)) :
    len < capacity ∧ len ≤ Luffs.Runtime.TLSF.usizeMax / 16 ∧
      offset ≤ Luffs.Runtime.TLSF.usizeMax - len * 16 ∧
      offset + len * 16 ≤ Luffs.Runtime.TLSF.usizeMax - 16 ∧
      offset + len * 16 + 16 ≤ storage.length ∧
      next = writeBytes storage (offset + len * 16) (Scalar.u128.encode value) ∧
      nextLen = len + 1 := by
  unfold vecPushU128 at hpush
  split at hpush <;> try contradiction
  next hlen =>
    split at hpush <;> try contradiction
    next hmul =>
      split at hpush <;> try contradiction
      next hoffset =>
        split at hpush <;> try contradiction
        next haddress =>
          split at hpush <;> try contradiction
          next hstorage =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hpush
            have hfit : offset + len * 16 + 16 ≤ storage.length := by omega
            have hwrite := writeBytes_sixteen_eq_set storage
              (offset + len * 16) (Scalar.byteAt value 0)
              (Scalar.byteAt value 8) (Scalar.byteAt value 16)
              (Scalar.byteAt value 24) (Scalar.byteAt value 32)
              (Scalar.byteAt value 40) (Scalar.byteAt value 48)
              (Scalar.byteAt value 56) (Scalar.byteAt value 64)
              (Scalar.byteAt value 72) (Scalar.byteAt value 80)
              (Scalar.byteAt value 88) (Scalar.byteAt value 96)
              (Scalar.byteAt value 104) (Scalar.byteAt value 112)
              (Scalar.byteAt value 120) hfit
            have hnext : next = writeBytes storage (offset + len * 16)
                (Scalar.u128.encode value) := by
              rw [hpush.1.symm]
              simpa [writeBytes, Scalar.u128, Scalar.encode128,
                List.append_assoc] using hwrite.symm
            exact ⟨Nat.lt_of_not_ge hlen, Nat.le_of_not_gt hmul,
              Nat.le_of_not_gt hoffset, Nat.le_of_not_gt haddress, hfit,
              hnext, hpush.2.symm⟩

theorem vecPushU128_refines_generic {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 128}
    (hcapacityMax : capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hpush : vecPushU128 storage offset len capacity value =
      some (next, nextLen)) :
    vecPush Scalar.u128 storage offset len capacity value =
      some ⟨next, nextLen⟩ := by
  obtain ⟨hlen, hmul, hoffset, haddress, hstorage, hnext, hnextLen⟩ :=
    vecPushU128_result hpush
  have hstoreBound : ¬storage.length < offset + len * 16 + 16 := by omega
  rw [hnext, hnextLen]
  simp [vecPush, Scalar.u128, hcapacityMax, hlen, hmul, hoffset, haddress,
    boxStore, hstoreBound]

/-- The concrete sixteen-byte Luffs push appends exactly one initialized u128
encoding and transfers the same exclusive Vec capability to the next handle. -/
theorem vecPushU128_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage nextStorage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {values : List (BitVec 128)}
    {value : BitVec 128} {nextLen : Nat}
    (hcapacityMax : handle.capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hpush : vecPushU128 storage handle.block.offset handle.len
      handle.capacity value = some (nextStorage, nextLen)) :
    ∃ nextHandle,
      Luffs.Containers.Vec.push handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage
        (handle.block.offset +
          (Luffs.Containers.Vec.encodeValues Scalar.u128 values).length)
        (Scalar.u128.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues Scalar.u128 values).length)
          (Scalar.u128.encode value) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns Scalar.u128 pool handle values ==∗
          contentsInterp
              (insertBytes contents
                ((handle.block.region pool).base +
                  (Luffs.Containers.Vec.encodeValues Scalar.u128 values).length)
                (Scalar.u128.encode value)) ∗
            Luffs.Containers.Vec.Owns Scalar.u128 pool nextHandle
              (values ++ [value]) := by
  have hgeneric : vecPush Scalar.u128 storage handle.block.offset handle.len
      handle.capacity value = some ⟨nextStorage, nextLen⟩ :=
    vecPushU128_refines_generic hcapacityMax hpush
  exact vecPush_owns Scalar.u128 hlen hgeneric

/-- Signed 128-bit values use the same two's-complement byte representation as
`u128`; the source-level type remains distinct while the verified transition is
shared. -/
def vecPushI128 (storage : List Byte) (offset len capacity : Nat)
    (value : BitVec 128) : Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if len > Luffs.Runtime.TLSF.usizeMax / 16 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - len * 16 then none
  else if offset + len * 16 > Luffs.Runtime.TLSF.usizeMax - 16 then none
  else if offset + len * 16 + 15 ≥ storage.length then none
  else some (((((((((((((((((storage.set (offset + len * 16)
    (Scalar.byteAt value 0)).set (offset + len * 16 + 1)
    (Scalar.byteAt value 8)).set (offset + len * 16 + 2)
    (Scalar.byteAt value 16)).set (offset + len * 16 + 3)
    (Scalar.byteAt value 24)).set (offset + len * 16 + 4)
    (Scalar.byteAt value 32)).set (offset + len * 16 + 5)
    (Scalar.byteAt value 40)).set (offset + len * 16 + 6)
    (Scalar.byteAt value 48)).set (offset + len * 16 + 7)
    (Scalar.byteAt value 56)).set (offset + len * 16 + 8)
    (Scalar.byteAt value 64)).set (offset + len * 16 + 9)
    (Scalar.byteAt value 72)).set (offset + len * 16 + 10)
    (Scalar.byteAt value 80)).set (offset + len * 16 + 11)
    (Scalar.byteAt value 88)).set (offset + len * 16 + 12)
    (Scalar.byteAt value 96)).set (offset + len * 16 + 13)
    (Scalar.byteAt value 104)).set (offset + len * 16 + 14)
    (Scalar.byteAt value 112)).set (offset + len * 16 + 15)
      (Scalar.byteAt value 120)), len + 1)

/-- Exact one-byte signed Vec push used by the Luffs source lowering. -/
def vecPushI8 (storage : List Byte) (offset len capacity : Nat)
    (value : BitVec 8) : Option (List Byte × Nat) :=
  if capacity > Luffs.Runtime.TLSF.usizeMax then none
  else if len ≥ capacity then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - len then none
  else if offset + len > Luffs.Runtime.TLSF.usizeMax - 1 then none
  else if offset + len ≥ storage.length then none
  else some (storage.set (offset + len) (Scalar.byteAt value 0), len + 1)

theorem vecPushI8_refines_generic {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 8}
    (hpush : vecPushI8 storage offset len capacity value =
      some (next, nextLen)) :
    vecPush Scalar.i8 storage offset len capacity value =
      some ⟨next, nextLen⟩ := by
  unfold vecPushI8 at hpush
  split at hpush <;> try contradiction
  next hcapacity =>
    split at hpush <;> try contradiction
    next hlen =>
      split at hpush <;> try contradiction
      next hoffset =>
        split at hpush <;> try contradiction
        next haddress =>
          split at hpush <;> try contradiction
          next hstorage =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hpush
            rw [← hpush.1, ← hpush.2]
            have hfit : offset + len < storage.length :=
              Nat.lt_of_not_ge hstorage
            have hmul : ¬len > Luffs.Runtime.TLSF.usizeMax := by omega
            have hbound : ¬storage.length < offset + len + 1 := by omega
            have hbyte : Scalar.byteAt value 0 = Scalar.byteOfBV8 value := by
              apply Fin.ext
              rfl
            have hwrite := writeBytes_singleton_eq_set storage (offset + len)
              (Scalar.byteAt value 0) hfit
            rw [hbyte] at hwrite
            simp [vecPush, Scalar.i8, Scalar.u8, hcapacity, hlen, hmul,
              hoffset, haddress, boxStore, hbound, writeBytes, Scalar.encode8]
            rw [hbyte]
            simpa using hwrite

theorem vecPushI8_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage nextStorage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {values : List (BitVec 8)}
    {value : BitVec 8} {nextLen : Nat}
    (hlen : values.length = handle.len)
    (hpush : vecPushI8 storage handle.block.offset handle.len
      handle.capacity value = some (nextStorage, nextLen)) :
    ∃ nextHandle,
      Luffs.Containers.Vec.push handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage
        (handle.block.offset +
          (Luffs.Containers.Vec.encodeValues Scalar.i8 values).length)
        (Scalar.i8.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues Scalar.i8 values).length)
          (Scalar.i8.encode value) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns Scalar.i8 pool handle values ==∗
          contentsInterp
              (insertBytes contents
                ((handle.block.region pool).base +
                  (Luffs.Containers.Vec.encodeValues Scalar.i8 values).length)
                (Scalar.i8.encode value)) ∗
            Luffs.Containers.Vec.Owns Scalar.i8 pool nextHandle
              (values ++ [value]) := by
  exact vecPush_owns Scalar.i8 hlen (vecPushI8_refines_generic hpush)

theorem vecPushI128_eq_u128 (storage : List Byte) (offset len capacity : Nat)
    (value : BitVec 128) :
    vecPushI128 storage offset len capacity value =
      vecPushU128 storage offset len capacity value := by
  rfl

theorem vecPushI128_refines_generic {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 128}
    (hcapacityMax : capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hpush : vecPushI128 storage offset len capacity value =
      some (next, nextLen)) :
    vecPush Scalar.i128 storage offset len capacity value =
      some ⟨next, nextLen⟩ := by
  exact vecPushU128_refines_generic hcapacityMax hpush

/-- A successful concrete `Vec<i128>` push appends the signed logical bit
pattern and transfers, rather than duplicates, the exclusive Vec capability. -/
theorem vecPushI128_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage nextStorage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {values : List (BitVec 128)}
    {value : BitVec 128} {nextLen : Nat}
    (hcapacityMax : handle.capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hpush : vecPushI128 storage handle.block.offset handle.len
      handle.capacity value = some (nextStorage, nextLen)) :
    ∃ nextHandle,
      Luffs.Containers.Vec.push handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage
        (handle.block.offset +
          (Luffs.Containers.Vec.encodeValues Scalar.i128 values).length)
        (Scalar.i128.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues Scalar.i128 values).length)
          (Scalar.i128.encode value) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns Scalar.i128 pool handle values ==∗
          contentsInterp
              (insertBytes contents
                ((handle.block.region pool).base +
                  (Luffs.Containers.Vec.encodeValues Scalar.i128 values).length)
                (Scalar.i128.encode value)) ∗
            Luffs.Containers.Vec.Owns Scalar.i128 pool nextHandle
              (values ++ [value]) := by
  have hgeneric : vecPush Scalar.i128 storage handle.block.offset handle.len
      handle.capacity value = some ⟨nextStorage, nextLen⟩ :=
    vecPushI128_refines_generic hcapacityMax hpush
  exact vecPush_owns Scalar.i128 hlen hgeneric

theorem vecPushU64_result {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 64}
    (hpush : vecPushU64 storage offset len capacity value =
      some (next, nextLen)) :
    len < capacity ∧ len ≤ Luffs.Runtime.TLSF.usizeMax / 8 ∧
      offset ≤ Luffs.Runtime.TLSF.usizeMax - len * 8 ∧
      offset + len * 8 ≤ Luffs.Runtime.TLSF.usizeMax - 8 ∧
      offset + len * 8 + 8 ≤ storage.length ∧
      next = (((((((storage.set (offset + len * 8) (Scalar.byteAt value 0)).set
        (offset + len * 8 + 1) (Scalar.byteAt value 8)).set
        (offset + len * 8 + 2) (Scalar.byteAt value 16)).set
        (offset + len * 8 + 3) (Scalar.byteAt value 24)).set
        (offset + len * 8 + 4) (Scalar.byteAt value 32)).set
        (offset + len * 8 + 5) (Scalar.byteAt value 40)).set
        (offset + len * 8 + 6) (Scalar.byteAt value 48)).set
        (offset + len * 8 + 7) (Scalar.byteAt value 56) ∧
      nextLen = len + 1 := by
  unfold vecPushU64 at hpush
  split at hpush <;> try contradiction
  next hlen =>
    split at hpush <;> try contradiction
    next hmul =>
      split at hpush <;> try contradiction
      next hoffset =>
        split at hpush <;> try contradiction
        next haddress =>
          split at hpush <;> try contradiction
          next hstorage =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hpush
            exact ⟨Nat.lt_of_not_ge hlen, Nat.le_of_not_gt hmul,
              Nat.le_of_not_gt hoffset, Nat.le_of_not_gt haddress,
              by omega, hpush.1.symm, hpush.2.symm⟩

theorem vecPushU64_refines_generic {storage next : List Byte}
    {offset len capacity nextLen : Nat} {value : BitVec 64}
    (hcapacityMax : capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hpush : vecPushU64 storage offset len capacity value =
      some (next, nextLen)) :
    vecPush Scalar.u64 storage offset len capacity value =
      some ⟨next, nextLen⟩ := by
  obtain ⟨hlen, hmul, hoffset, haddress, hstorage, hnext, hnextLen⟩ :=
    vecPushU64_result hpush
  have hwrite := writeBytes_eight_eq_set storage (offset + len * 8)
    (Scalar.byteAt value 0) (Scalar.byteAt value 8)
    (Scalar.byteAt value 16) (Scalar.byteAt value 24)
    (Scalar.byteAt value 32) (Scalar.byteAt value 40)
    (Scalar.byteAt value 48) (Scalar.byteAt value 56) hstorage
  have hstoreBound : ¬storage.length < offset + len * 8 + 8 := by omega
  rw [hnext, hnextLen]
  simp [vecPush, Scalar.u64, hcapacityMax, hlen, hmul, hoffset, haddress,
    boxStore, hstoreBound, writeBytes, Scalar.encode64]
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using hwrite

theorem vecPushU64_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage nextStorage : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {values : List (BitVec 64)}
    {value : BitVec 64} {nextLen : Nat}
    (hcapacityMax : handle.capacity ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hpush : vecPushU64 storage handle.block.offset handle.len
      handle.capacity value = some (nextStorage, nextLen)) :
    ∃ nextHandle,
      Luffs.Containers.Vec.push handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage
        (handle.block.offset +
          (Luffs.Containers.Vec.encodeValues Scalar.u64 values).length)
        (Scalar.u64.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents
          ((handle.block.region pool).base +
            (Luffs.Containers.Vec.encodeValues Scalar.u64 values).length)
          (Scalar.u64.encode value) →
        contentsInterp (G := G) contents ∗
            Luffs.Containers.Vec.Owns Scalar.u64 pool handle values ==∗
          contentsInterp
              (insertBytes contents
                ((handle.block.region pool).base +
                  (Luffs.Containers.Vec.encodeValues Scalar.u64 values).length)
                (Scalar.u64.encode value)) ∗
            Luffs.Containers.Vec.Owns Scalar.u64 pool nextHandle
              (values ++ [value]) := by
  have hgeneric : vecPush Scalar.u64 storage handle.block.offset handle.len
      handle.capacity value = some ⟨nextStorage, nextLen⟩ :=
    vecPushU64_refines_generic hcapacityMax hpush
  exact vecPush_owns Scalar.u64 hlen hgeneric

/-- The signed two's-complement codecs are definitionally the corresponding
unsigned codecs, so these are direct Iris ownership corollaries with no cast or
trusted representation bridge. -/
def vecPushI16_owns := @vecPushU16_owns
def vecPushI32_owns := @vecPushU32_owns
def vecPushI64_owns := @vecPushU64_owns
def vecPushUsize_owns := @vecPushU64_owns
def vecPushIsize_owns := @vecPushU64_owns

set_option maxHeartbeats 1200000 in
/-- End-to-end first push for an allocator-backed `Vec<u16>`. This composes the
concrete TLSF allocation, the empty typed Vec capability, the concrete
little-endian push, and the generic Iris initialization update. -/
theorem vecNewPushU16Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage nextStorage : List Byte}
    {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {capacity nextLen : Nat}
    {value : BitVec 16} {allocated : Luffs.Runtime.TLSF.AllocateArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hnew : vecNewU16Arrays offsets sizes isFree prevFree count second first
      heads next previous capacity = some allocated)
    (hpush : vecPushU16 storage allocated.allocatedOffset 0 capacity value =
      some (nextStorage, nextLen)) :
    ∃ (hcapacity : 0 < capacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes Scalar.u16 capacity) <
            2 ^ firstLevelCount)
        (vecResult : Luffs.Containers.Vec.AllocResult)
        (nextHandle : Luffs.Containers.Vec.Handle),
      Luffs.Containers.Vec.allocate Scalar.u16 capacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some vecResult ∧
      allocated.allocatedOffset = vecResult.handle.block.offset ∧
      Luffs.Containers.Vec.push vecResult.handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage vecResult.handle.block.offset
        (Scalar.u16.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents (vecResult.handle.block.region pool).base
          (Scalar.u16.encode value) →
        contentsInterp (G := G) contents ∗ Ownership.OwnsFree pool blocks ==∗
          contentsInterp
              (insertBytes contents (vecResult.handle.block.region pool).base
                (Scalar.u16.encode value)) ∗
            (Luffs.Containers.Vec.Owns Scalar.u16 pool nextHandle [value] ∗
              Ownership.OwnsFree pool vecResult.state.physical) := by
  obtain ⟨hcapacity, hkeyMax, vecResult, halloc, hoffset, _, hlen, hcap,
      howns⟩ := vecNewU16Arrays_refines_vec (GF := GF) hvalid hsecond hfirst hbins
    hdisjoint hphysical hnew
  have hcapacityMax : capacity ≤ Luffs.Runtime.TLSF.usizeMax := by
    obtain ⟨_, hmul, _, _⟩ := vecNewArrays_result hnew
    simpa [Scalar.u16] using Nat.le_trans hmul
      (Nat.div_le_self Luffs.Runtime.TLSF.usizeMax 2)
  have hpush' : vecPushU16 storage vecResult.handle.block.offset
      vecResult.handle.len vecResult.handle.capacity value =
      some (nextStorage, nextLen) := by
    simpa [hoffset, hlen, hcap] using hpush
  have hcapacityMax' : vecResult.handle.capacity ≤
      Luffs.Runtime.TLSF.usizeMax := by simpa [hcap] using hcapacityMax
  obtain ⟨nextHandle, habstractPush, hnextLen, hstorage, hpushOwns⟩ :=
    vecPushU16_owns (GF := GF) (pool := pool) hcapacityMax' (values := [])
      hlen.symm hpush'
  simp only [Luffs.Containers.Vec.encodeValues, List.flatMap_nil,
    List.length_nil, Nat.add_zero, List.nil_append] at hpushOwns
  refine ⟨hcapacity, hkeyMax, vecResult, nextHandle, halloc, hoffset,
    habstractPush, hnextLen, ?_, ?_⟩
  · simpa [Luffs.Containers.Vec.encodeValues] using hstorage
  · intro contents hfresh
    iintro ⟨Hcontents, Hallocator⟩
    ihave ⟨Hvec, Hallocator⟩ := howns.mp $$ Hallocator
    icombine Hcontents Hvec as Hpush
    imod hpushOwns contents hfresh
      $$ Hpush with ⟨Hcontents, Hvec⟩
    imodintro
    isplitl [Hcontents]
    · iassumption
    · isplitl [Hvec]
      · iassumption
      · iassumption

set_option maxHeartbeats 1200000 in
/-- End-to-end first push for an allocator-backed `Vec<u32>`. The concrete
four-byte Luffs store is connected to the generic allocation and ownership
laws, so no untyped allocation capability is exposed between the operations. -/
theorem vecNewPushU32Arrays_owns
    {GF : Iris.BundledGFunctors} [Luffs.Memory.ByteRegionGS GF]
    [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {blocks : List Block} {state : Bins.State}
    {storage nextStorage : List Byte}
    {second : List (BitVec 32)} {first : BitVec 64}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {heads next previous : List Nat} {capacity nextLen : Nat}
    {value : BitVec 32} {allocated : Luffs.Runtime.TLSF.AllocateArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : Luffs.Runtime.TLSF.RepresentsSecondBitmap second state)
    (hfirst : Luffs.Runtime.TLSF.FirstBitmapRep first second)
    (hbins : Luffs.Runtime.TLSF.RepresentsBins { heads, next, previous } state)
    (hdisjoint : Luffs.Runtime.TLSF.BinsOffsetsDisjoint state)
    (hphysical : Luffs.Runtime.TLSF.RepresentsPhysicalArrays offsets sizes
      isFree prevFree count blocks)
    (hnew : vecNewU32Arrays offsets sizes isFree prevFree count second first
      heads next previous capacity = some allocated)
    (hpush : vecPushU32 storage allocated.allocatedOffset 0 capacity value =
      some (nextStorage, nextLen)) :
    ∃ (hcapacity : 0 < capacity)
        (hkeyMax : requestKey
          (Luffs.Containers.Vec.allocationBytes Scalar.u32 capacity) <
            2 ^ firstLevelCount)
        (vecResult : Luffs.Containers.Vec.AllocResult)
        (nextHandle : Luffs.Containers.Vec.Handle),
      Luffs.Containers.Vec.allocate Scalar.u32 capacity hcapacity
          { physical := blocks, bins := state } hkeyMax = some vecResult ∧
      allocated.allocatedOffset = vecResult.handle.block.offset ∧
      Luffs.Containers.Vec.push vecResult.handle = some nextHandle ∧
      nextLen = nextHandle.len ∧
      nextStorage = writeBytes storage vecResult.handle.block.offset
        (Scalar.u32.encode value) ∧
      ∀ contents : ContentsMap,
        CanInsertBytes contents (vecResult.handle.block.region pool).base
          (Scalar.u32.encode value) →
        contentsInterp (G := G) contents ∗ Ownership.OwnsFree pool blocks ==∗
          contentsInterp
              (insertBytes contents (vecResult.handle.block.region pool).base
                (Scalar.u32.encode value)) ∗
            (Luffs.Containers.Vec.Owns Scalar.u32 pool nextHandle [value] ∗
              Ownership.OwnsFree pool vecResult.state.physical) := by
  obtain ⟨hcapacity, hkeyMax, vecResult, halloc, hoffset, _, hlen, hcap,
      howns⟩ := vecNewArrays_refines_vec (GF := GF) (codec := Scalar.u32)
    hvalid hsecond hfirst hbins hdisjoint hphysical hnew
  have hcapacityMax : capacity ≤ Luffs.Runtime.TLSF.usizeMax := by
    obtain ⟨_, hmul, _, _⟩ := vecNewArrays_result hnew
    simpa [Scalar.u32] using Nat.le_trans hmul
      (Nat.div_le_self Luffs.Runtime.TLSF.usizeMax 4)
  have hpush' : vecPushU32 storage vecResult.handle.block.offset
      vecResult.handle.len vecResult.handle.capacity value =
      some (nextStorage, nextLen) := by
    simpa [hoffset, hlen, hcap] using hpush
  have hcapacityMax' : vecResult.handle.capacity ≤
      Luffs.Runtime.TLSF.usizeMax := by simpa [hcap] using hcapacityMax
  obtain ⟨nextHandle, habstractPush, hnextLen, hstorage, hpushOwns⟩ :=
    vecPushU32_owns (GF := GF) (pool := pool) hcapacityMax' (values := [])
      hlen.symm hpush'
  simp only [Luffs.Containers.Vec.encodeValues, List.flatMap_nil,
    List.length_nil, Nat.add_zero, List.nil_append] at hpushOwns
  refine ⟨hcapacity, hkeyMax, vecResult, nextHandle, halloc, hoffset,
    habstractPush, hnextLen, ?_, ?_⟩
  · simpa [Luffs.Containers.Vec.encodeValues] using hstorage
  · intro contents hfresh
    iintro ⟨Hcontents, Hallocator⟩
    ihave ⟨Hvec, Hallocator⟩ := howns.mp $$ Hallocator
    icombine Hcontents Hvec as Hpush
    imod hpushOwns contents hfresh $$ Hpush with ⟨Hcontents, Hvec⟩
    imodintro
    isplitl [Hcontents]
    · iassumption
    · isplitl [Hvec]
      · iassumption
      · iassumption

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

def vecGetU16 (storage : List Byte) (offset len index : Nat) :
    Option (BitVec 16) :=
  if index ≥ len then none
  else if index > Luffs.Runtime.TLSF.usizeMax / 2 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - index * 2 then none
  else if offset + index * 2 > Luffs.Runtime.TLSF.usizeMax - 2 then none
  else
    let address := offset + index * 2
    if address + 1 ≥ storage.length then none
    else do
      let low ← storage[address]?
      let high ← storage[address + 1]?
      Scalar.decode16 [low, high]

theorem vecGetU16_eq_generic (storage : List Byte) (offset len index : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    vecGetU16 storage offset len index =
      vecGet Scalar.u16 storage offset len index := by
  by_cases hindex : index ≥ len
  · simp [vecGetU16, vecGet, hindex]
  · by_cases hmul : index > Luffs.Runtime.TLSF.usizeMax / 2
    · simp [vecGetU16, vecGet, Scalar.u16, hindex, hmul]
    · by_cases hoffset : offset > Luffs.Runtime.TLSF.usizeMax - index * 2
      · simp [vecGetU16, vecGet, Scalar.u16, hindex, hmul, hoffset]
      · by_cases haddress : offset + index * 2 >
          Luffs.Runtime.TLSF.usizeMax - 2
        · simp [vecGetU16, vecGet, Scalar.u16, hindex, hmul, hoffset, haddress]
        · simp only [vecGetU16, hindex, ↓reduceIte, hmul, hoffset, haddress,
            vecGet, Scalar.u16, ↓reduceIte]
          have htwo : 2 ≤ Luffs.Runtime.TLSF.usizeMax := by
            decide
          have hmax : offset + index * 2 ≠ Luffs.Runtime.TLSF.usizeMax := by
            omega
          calc
            (if offset + index * 2 + 1 ≥ storage.length then none
              else do
                let low ← storage[offset + index * 2]?
                let high ← storage[offset + index * 2 + 1]?
                Scalar.decode16 [low, high]) =
                boxLoadU16 storage (offset + index * 2) := by
                  simp [boxLoadU16, hmax]
            _ = boxLoad Scalar.u16 storage (offset + index * 2) :=
              boxLoadU16_eq_generic storage (offset + index * 2) hstorageMax

theorem vecGetU16_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle}
    {values : List (BitVec 16)} {index : Nat} {value expected : BitVec 16}
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hsuccess : vecGetU16 storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some expected)
    (hencoded :
      (storage.drop (handle.block.offset + index * Scalar.u16.size)).take
          Scalar.u16.size = Scalar.u16.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns Scalar.u16 pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns Scalar.u16 pool handle values) ∗
          ⌜ReadSteps ((handle.block.region pool).base + index * Scalar.u16.size)
              (Scalar.u16.encode expected) mem ∧
            Scalar.u16.decode (Scalar.u16.encode expected) = some expected⌝) := by
  have hgeneric : vecGet Scalar.u16 storage handle.block.offset handle.len index =
      some value := by
    rw [← vecGetU16_eq_generic storage handle.block.offset handle.len index
      hstorageMax]
    exact hsuccess
  exact vecGet_owns Scalar.u16 hlen hgeneric hvalues hencoded hrep

def vecGetU32 (storage : List Byte) (offset len index : Nat) :
    Option (BitVec 32) :=
  if index ≥ len then none
  else if index > Luffs.Runtime.TLSF.usizeMax / 4 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - index * 4 then none
  else if offset + index * 4 > Luffs.Runtime.TLSF.usizeMax - 4 then none
  else
    let address := offset + index * 4
    if address + 3 ≥ storage.length then none
    else do
      let b0 ← storage[address]?
      let b1 ← storage[address + 1]?
      let b2 ← storage[address + 2]?
      let b3 ← storage[address + 3]?
      Scalar.decode32 [b0, b1, b2, b3]

theorem vecGetU32_eq_generic (storage : List Byte) (offset len index : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    vecGetU32 storage offset len index =
      vecGet Scalar.u32 storage offset len index := by
  by_cases hindex : index ≥ len
  · simp [vecGetU32, vecGet, hindex]
  · by_cases hmul : index > Luffs.Runtime.TLSF.usizeMax / 4
    · simp [vecGetU32, vecGet, Scalar.u32, hindex, hmul]
    · by_cases hoffset : offset > Luffs.Runtime.TLSF.usizeMax - index * 4
      · simp [vecGetU32, vecGet, Scalar.u32, hindex, hmul, hoffset]
      · by_cases haddress : offset + index * 4 >
          Luffs.Runtime.TLSF.usizeMax - 4
        · simp [vecGetU32, vecGet, Scalar.u32, hindex, hmul, hoffset, haddress]
        · simp only [vecGetU32, hindex, ↓reduceIte, hmul, hoffset, haddress,
            vecGet, Scalar.u32, ↓reduceIte]
          have hword : ¬offset + index * 4 >
              Luffs.Runtime.TLSF.usizeMax - 3 := by omega
          calc
            (if offset + index * 4 + 3 ≥ storage.length then none
              else do
                let b0 ← storage[offset + index * 4]?
                let b1 ← storage[offset + index * 4 + 1]?
                let b2 ← storage[offset + index * 4 + 2]?
                let b3 ← storage[offset + index * 4 + 3]?
                Scalar.decode32 [b0, b1, b2, b3]) =
                boxLoadU32 storage (offset + index * 4) := by
                  simp [boxLoadU32, hword]
            _ = boxLoad Scalar.u32 storage (offset + index * 4) :=
              boxLoadU32_eq_generic storage (offset + index * 4) hstorageMax

theorem vecGetU32_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle}
    {values : List (BitVec 32)} {index : Nat} {value expected : BitVec 32}
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hsuccess : vecGetU32 storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some expected)
    (hencoded :
      (storage.drop (handle.block.offset + index * Scalar.u32.size)).take
          Scalar.u32.size = Scalar.u32.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns Scalar.u32 pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns Scalar.u32 pool handle values) ∗
          ⌜ReadSteps ((handle.block.region pool).base + index * Scalar.u32.size)
              (Scalar.u32.encode expected) mem ∧
            Scalar.u32.decode (Scalar.u32.encode expected) = some expected⌝) := by
  have hgeneric : vecGet Scalar.u32 storage handle.block.offset handle.len index =
      some value := by
    rw [← vecGetU32_eq_generic storage handle.block.offset handle.len index
      hstorageMax]
    exact hsuccess
  exact vecGet_owns Scalar.u32 hlen hgeneric hvalues hencoded hrep

def vecGetU64 (storage : List Byte) (offset len index : Nat) :
    Option (BitVec 64) :=
  if index ≥ len then none
  else if index > Luffs.Runtime.TLSF.usizeMax / 8 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - index * 8 then none
  else if offset + index * 8 > Luffs.Runtime.TLSF.usizeMax - 8 then none
  else
    let address := offset + index * 8
    if address + 7 ≥ storage.length then none
    else do
      let b0 ← storage[address]?
      let b1 ← storage[address + 1]?
      let b2 ← storage[address + 2]?
      let b3 ← storage[address + 3]?
      let b4 ← storage[address + 4]?
      let b5 ← storage[address + 5]?
      let b6 ← storage[address + 6]?
      let b7 ← storage[address + 7]?
      Scalar.decode64 [b0, b1, b2, b3, b4, b5, b6, b7]

def vecGetU128 (storage : List Byte) (offset len index : Nat) :
    Option (BitVec 128) :=
  if index ≥ len then none
  else if index > Luffs.Runtime.TLSF.usizeMax / 16 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - index * 16 then none
  else if offset + index * 16 > Luffs.Runtime.TLSF.usizeMax - 16 then none
  else
    let address := offset + index * 16
    if address + 15 ≥ storage.length then none
    else do
      let b0 ← storage[address]?
      let b1 ← storage[address + 1]?
      let b2 ← storage[address + 2]?
      let b3 ← storage[address + 3]?
      let b4 ← storage[address + 4]?
      let b5 ← storage[address + 5]?
      let b6 ← storage[address + 6]?
      let b7 ← storage[address + 7]?
      let b8 ← storage[address + 8]?
      let b9 ← storage[address + 9]?
      let b10 ← storage[address + 10]?
      let b11 ← storage[address + 11]?
      let b12 ← storage[address + 12]?
      let b13 ← storage[address + 13]?
      let b14 ← storage[address + 14]?
      let b15 ← storage[address + 15]?
      Scalar.decode128 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
        b11, b12, b13, b14, b15]

theorem vecGetU64_eq_generic (storage : List Byte) (offset len index : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    vecGetU64 storage offset len index =
      vecGet Scalar.u64 storage offset len index := by
  by_cases hindex : index ≥ len
  · simp [vecGetU64, vecGet, hindex]
  · by_cases hmul : index > Luffs.Runtime.TLSF.usizeMax / 8
    · simp [vecGetU64, vecGet, Scalar.u64, hindex, hmul]
    · by_cases hoffset : offset > Luffs.Runtime.TLSF.usizeMax - index * 8
      · simp [vecGetU64, vecGet, Scalar.u64, hindex, hmul, hoffset]
      · by_cases haddress : offset + index * 8 >
          Luffs.Runtime.TLSF.usizeMax - 8
        · simp [vecGetU64, vecGet, Scalar.u64, hindex, hmul, hoffset, haddress]
        · simp only [vecGetU64, hindex, ↓reduceIte, hmul, hoffset, haddress,
            vecGet, Scalar.u64, ↓reduceIte]
          have hword : ¬offset + index * 8 >
              Luffs.Runtime.TLSF.usizeMax - 7 := by omega
          calc
            (if offset + index * 8 + 7 ≥ storage.length then none
              else do
                let b0 ← storage[offset + index * 8]?
                let b1 ← storage[offset + index * 8 + 1]?
                let b2 ← storage[offset + index * 8 + 2]?
                let b3 ← storage[offset + index * 8 + 3]?
                let b4 ← storage[offset + index * 8 + 4]?
                let b5 ← storage[offset + index * 8 + 5]?
                let b6 ← storage[offset + index * 8 + 6]?
                let b7 ← storage[offset + index * 8 + 7]?
                Scalar.decode64 [b0, b1, b2, b3, b4, b5, b6, b7]) =
                boxLoadU64 storage (offset + index * 8) := by
                  simp [boxLoadU64, hword]
            _ = boxLoad Scalar.u64 storage (offset + index * 8) :=
              boxLoadU64_eq_generic storage (offset + index * 8) hstorageMax

theorem vecGetU64_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle}
    {values : List (BitVec 64)} {index : Nat} {value expected : BitVec 64}
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hsuccess : vecGetU64 storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some expected)
    (hencoded :
      (storage.drop (handle.block.offset + index * Scalar.u64.size)).take
          Scalar.u64.size = Scalar.u64.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns Scalar.u64 pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns Scalar.u64 pool handle values) ∗
          ⌜ReadSteps ((handle.block.region pool).base + index * Scalar.u64.size)
              (Scalar.u64.encode expected) mem ∧
            Scalar.u64.decode (Scalar.u64.encode expected) = some expected⌝) := by
  have hgeneric : vecGet Scalar.u64 storage handle.block.offset handle.len index =
      some value := by
    rw [← vecGetU64_eq_generic storage handle.block.offset handle.len index
      hstorageMax]
    exact hsuccess
  exact vecGet_owns Scalar.u64 hlen hgeneric hvalues hencoded hrep

theorem vecGetU128_eq_generic (storage : List Byte) (offset len index : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    vecGetU128 storage offset len index =
      vecGet Scalar.u128 storage offset len index := by
  by_cases hindex : index ≥ len
  · simp [vecGetU128, vecGet, hindex]
  · by_cases hmul : index > Luffs.Runtime.TLSF.usizeMax / 16
    · simp [vecGetU128, vecGet, Scalar.u128, hindex, hmul]
    · by_cases hoffset : offset > Luffs.Runtime.TLSF.usizeMax - index * 16
      · simp [vecGetU128, vecGet, Scalar.u128, hindex, hmul, hoffset]
      · by_cases haddress : offset + index * 16 >
          Luffs.Runtime.TLSF.usizeMax - 16
        · simp [vecGetU128, vecGet, Scalar.u128, hindex, hmul, hoffset, haddress]
        · simp only [vecGetU128, hindex, ↓reduceIte, hmul, hoffset, haddress,
            vecGet, Scalar.u128, ↓reduceIte]
          have hword : ¬offset + index * 16 >
              Luffs.Runtime.TLSF.usizeMax - 15 := by omega
          calc
            (if offset + index * 16 + 15 ≥ storage.length then none
              else do
                let b0 ← storage[offset + index * 16]?
                let b1 ← storage[offset + index * 16 + 1]?
                let b2 ← storage[offset + index * 16 + 2]?
                let b3 ← storage[offset + index * 16 + 3]?
                let b4 ← storage[offset + index * 16 + 4]?
                let b5 ← storage[offset + index * 16 + 5]?
                let b6 ← storage[offset + index * 16 + 6]?
                let b7 ← storage[offset + index * 16 + 7]?
                let b8 ← storage[offset + index * 16 + 8]?
                let b9 ← storage[offset + index * 16 + 9]?
                let b10 ← storage[offset + index * 16 + 10]?
                let b11 ← storage[offset + index * 16 + 11]?
                let b12 ← storage[offset + index * 16 + 12]?
                let b13 ← storage[offset + index * 16 + 13]?
                let b14 ← storage[offset + index * 16 + 14]?
                let b15 ← storage[offset + index * 16 + 15]?
                Scalar.decode128 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
                  b10, b11, b12, b13, b14, b15]) =
                boxLoadU128 storage (offset + index * 16) := by
                  simp [boxLoadU128, hword]
            _ = boxLoad Scalar.u128 storage (offset + index * 16) :=
              boxLoadU128_eq_generic storage (offset + index * 16) hstorageMax

/-- The concrete sixteen-byte get returns only the owned logical u128,
preserves exclusive Vec ownership, and exposes the exact sixteen-read trace. -/
theorem vecGetU128_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle}
    {values : List (BitVec 128)} {index : Nat} {value expected : BitVec 128}
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hsuccess : vecGetU128 storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some expected)
    (hencoded :
      (storage.drop (handle.block.offset + index * Scalar.u128.size)).take
          Scalar.u128.size = Scalar.u128.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns Scalar.u128 pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns Scalar.u128 pool handle values) ∗
          ⌜ReadSteps
              ((handle.block.region pool).base + index * Scalar.u128.size)
              (Scalar.u128.encode expected) mem ∧
            Scalar.u128.decode (Scalar.u128.encode expected) = some expected⌝) := by
  have hgeneric : vecGet Scalar.u128 storage handle.block.offset handle.len index =
      some value := by
    rw [← vecGetU128_eq_generic storage handle.block.offset handle.len index
      hstorageMax]
    exact hsuccess
  exact vecGet_owns Scalar.u128 hlen hgeneric hvalues hencoded hrep

/-- Signed 128-bit loads decode the same two's-complement bit pattern as the
unsigned byte-level operation. -/
def vecGetI128 (storage : List Byte) (offset len index : Nat) :
    Option (BitVec 128) :=
  if index ≥ len then none
  else if index > Luffs.Runtime.TLSF.usizeMax / 16 then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - index * 16 then none
  else if offset + index * 16 > Luffs.Runtime.TLSF.usizeMax - 16 then none
  else
    let address := offset + index * 16
    if address + 15 ≥ storage.length then none
    else do
      let b0 ← storage[address]?
      let b1 ← storage[address + 1]?
      let b2 ← storage[address + 2]?
      let b3 ← storage[address + 3]?
      let b4 ← storage[address + 4]?
      let b5 ← storage[address + 5]?
      let b6 ← storage[address + 6]?
      let b7 ← storage[address + 7]?
      let b8 ← storage[address + 8]?
      let b9 ← storage[address + 9]?
      let b10 ← storage[address + 10]?
      let b11 ← storage[address + 11]?
      let b12 ← storage[address + 12]?
      let b13 ← storage[address + 13]?
      let b14 ← storage[address + 14]?
      let b15 ← storage[address + 15]?
      Scalar.decode128 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
        b11, b12, b13, b14, b15]

/-- Exact one-byte signed Vec get used by the Luffs source lowering. -/
def vecGetI8 (storage : List Byte) (offset len index : Nat) :
    Option (BitVec 8) :=
  if index ≥ len then none
  else if index > Luffs.Runtime.TLSF.usizeMax then none
  else if offset > Luffs.Runtime.TLSF.usizeMax - index then none
  else if offset + index > Luffs.Runtime.TLSF.usizeMax - 1 then none
  else if offset + index ≥ storage.length then none
  else do
    let byte ← storage[offset + index]?
    Scalar.decode8 [byte]

theorem vecGetI8_refines_generic {storage : List Byte} {offset len index : Nat}
    {value : BitVec 8}
    (hsuccess : vecGetI8 storage offset len index = some value) :
    vecGet Scalar.i8 storage offset len index = some value := by
  unfold vecGetI8 at hsuccess
  split at hsuccess <;> try contradiction
  next hindex =>
    split at hsuccess <;> try contradiction
    next hmul =>
      split at hsuccess <;> try contradiction
      next hoffset =>
        split at hsuccess <;> try contradiction
        next haddress =>
          split at hsuccess <;> try contradiction
          next hstorage =>
            have hbox : boxLoad Scalar.u8 storage (offset + index) =
                some value := by
              rw [← boxLoadI8_eq_generic]
              simpa [boxLoadI8, hstorage] using hsuccess
            simpa [vecGet, Scalar.i8, Scalar.u8, hindex, hmul, hoffset,
              haddress] using hbox

theorem vecGetI8_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle}
    {values : List (BitVec 8)} {index : Nat} {value expected : BitVec 8}
    (hlen : values.length = handle.len)
    (hsuccess : vecGetI8 storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some expected)
    (hencoded :
      (storage.drop (handle.block.offset + index * Scalar.i8.size)).take
          Scalar.i8.size = Scalar.i8.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns Scalar.i8 pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns Scalar.i8 pool handle values) ∗
          ⌜ReadSteps
              ((handle.block.region pool).base + index * Scalar.i8.size)
              (Scalar.i8.encode expected) mem ∧
            Scalar.i8.decode (Scalar.i8.encode expected) = some expected⌝) := by
  have hgeneric : vecGet Scalar.i8 storage handle.block.offset handle.len index =
      some value := by
    exact vecGetI8_refines_generic hsuccess
  exact vecGet_owns Scalar.i8 hlen hgeneric hvalues hencoded hrep

theorem vecGetI128_eq_u128 (storage : List Byte) (offset len index : Nat) :
    vecGetI128 storage offset len index = vecGetU128 storage offset len index := by
  rfl

theorem vecGetI128_eq_generic (storage : List Byte) (offset len index : Nat)
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax) :
    vecGetI128 storage offset len index =
      vecGet Scalar.i128 storage offset len index := by
  exact vecGetU128_eq_generic storage offset len index hstorageMax

/-- A concrete `Vec<i128>` get returns exactly the owned signed bit pattern,
preserves exclusive ownership, and exposes all sixteen ordered reads. -/
theorem vecGetI128_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {pool : Region} {storage : List Byte}
    {handle : Luffs.Containers.Vec.Handle}
    {values : List (BitVec 128)} {index : Nat} {value expected : BitVec 128}
    (hstorageMax : storage.length ≤ Luffs.Runtime.TLSF.usizeMax)
    (hlen : values.length = handle.len)
    (hsuccess : vecGetI128 storage handle.block.offset handle.len index =
      some value)
    (hvalues : values[index]? = some expected)
    (hencoded :
      (storage.drop (handle.block.offset + index * Scalar.i128.size)).take
          Scalar.i128.size = Scalar.i128.encode expected)
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    value = expected ∧
      (contentsInterp (G := G) contents ∗
          Luffs.Containers.Vec.Owns Scalar.i128 pool handle values ⊢
        (contentsInterp contents ∗
          Luffs.Containers.Vec.Owns Scalar.i128 pool handle values) ∗
          ⌜ReadSteps
              ((handle.block.region pool).base + index * Scalar.i128.size)
              (Scalar.i128.encode expected) mem ∧
            Scalar.i128.decode (Scalar.i128.encode expected) = some expected⌝) := by
  have hgeneric : vecGet Scalar.i128 storage handle.block.offset handle.len index =
      some value := by
    rw [← vecGetI128_eq_generic storage handle.block.offset handle.len index
      hstorageMax]
    exact hsuccess
  exact vecGet_owns Scalar.i128 hlen hgeneric hvalues hencoded hrep

/-- Direct signed-codec corollaries of the exact two-, four-, and eight-read
Iris rules. -/
def vecGetI16_owns := @vecGetU16_owns
def vecGetI32_owns := @vecGetU32_owns
def vecGetI64_owns := @vecGetU64_owns
def vecGetUsize_owns := @vecGetU64_owns
def vecGetIsize_owns := @vecGetU64_owns

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

theorem vecLenAfterPop_owns {GF : Iris.BundledGFunctors}
    [Luffs.Memory.ByteRegionGS GF] [G : Luffs.Memory.ByteContentsGS GF]
    {α : Type} (codec : Codec α) {pool : Region}
    {handle : Luffs.Containers.Vec.Handle} {nextLen : Nat}
    (initValues : List α) (last : α) (contents : ContentsMap)
    (hlen : handle.len = initValues.length + 1)
    (hpop : vecLenAfterPop handle.len = some nextLen) :
    contentsInterp (G := G) contents ∗
        Luffs.Containers.Vec.Owns codec pool handle (initValues ++ [last]) ==∗
      contentsInterp
          (deleteBytes contents
            ((handle.block.region pool).base +
              (Luffs.Containers.Vec.encodeValues codec initValues).length)
            (codec.encode last)) ∗
        (⌜nextLen = initValues.length⌝ ∗
          Luffs.Containers.Vec.Owns codec pool
            { handle with len := nextLen } initValues) := by
  have habstract := vecLenAfterPop_refines_handle (handle := handle) hpop
  exact Luffs.Containers.Vec.pop_owns codec initValues last contents hlen
    habstract

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
