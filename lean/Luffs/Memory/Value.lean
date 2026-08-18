import Luffs.Memory.TypedIris

set_option autoImplicit false

namespace Luffs.Memory

open Iris Iris.BI

/-- A verified byte representation for a Luffs value type. Container proofs
are generic over codecs; concrete integer codecs must discharge these laws. -/
structure Codec (α : Type) where
  size : Nat
  align : Nat
  size_pos : 0 < size
  align_pos : 0 < align
  encode : α -> List Byte
  decode : List Byte -> Option α
  encode_length : ∀ value, (encode value).length = size
  decode_encode : ∀ value, decode (encode value) = some value

def ValueRegion {α : Type} (codec : Codec α) (base : Addr) : Region :=
  { base, bytes := codec.size }

/-- Extensional connection between concrete machine memory and one encoded
value. This is the pure representation predicate used to connect operational
WPs to functional array models. -/
def Memory.EncodesAt {α : Type} (codec : Codec α) (mem : Memory)
    (base : Addr) (value : α) : Prop :=
  ∀ i, (hi : i < codec.size) →
    mem (base + i) = some ((codec.encode value).get
      ⟨i, by simpa [codec.encode_length] using hi⟩)

def Memory.EncodesArray {α : Type} (codec : Codec α) (mem : Memory)
    (base : Addr) (values : List α) : Prop :=
  ∀ index, (hindex : index < values.length) →
    mem.EncodesAt codec (base + index * codec.size) values[index]

def ArrayRegion {α : Type} (codec : Codec α) (base count : Nat) : Region :=
  { base, bytes := count * codec.size }

theorem Memory.writeBytes_encodesAt {α : Type} (codec : Codec α)
    (mem : Memory) (base : Addr) (value : α) :
    (mem.writeBytes base (codec.encode value)).EncodesAt codec base value := by
  intro i hi
  have hi' : i < (codec.encode value).length := by
    simpa [codec.encode_length] using hi
  simpa using writeBytes_get (mem := mem) (base := base) hi'

/-- A store outside an encoded value's region preserves its representation.
The pointwise premise is the arithmetic form generated from pairwise-disjoint
Rust mutable-slice regions. -/
theorem Memory.EncodesAt.writeBytes_of_outside {α : Type}
    {codec : Codec α} {mem : Memory} {valueBase writeBase : Addr}
    {value : α} {bytes : List Byte}
    (hencoded : mem.EncodesAt codec valueBase value)
    (houtside : ∀ i, i < codec.size →
      valueBase + i < writeBase ∨ writeBase + bytes.length ≤ valueBase + i) :
    (mem.writeBytes writeBase bytes).EncodesAt codec valueBase value := by
  intro i hi
  rw [writeBytes_eq_of_outside (houtside i hi)]
  exact hencoded i hi

theorem Memory.EncodesAt.writeBytes_of_disjoint {α : Type}
    {codec : Codec α} {mem : Memory} {valueBase writeBase : Addr}
    {value : α} {bytes : List Byte}
    (hencoded : mem.EncodesAt codec valueBase value)
    (hdisjoint : (Region.mk writeBase bytes.length).disjoint
      (ValueRegion codec valueBase)) :
    (mem.writeBytes writeBase bytes).EncodesAt codec valueBase value := by
  apply hencoded.writeBytes_of_outside
  intro i hi
  unfold Region.disjoint Region.endAddr ValueRegion at hdisjoint
  rcases hdisjoint with hbefore | hafter
  · exact Or.inr (Nat.le_trans hbefore (Nat.le_add_right valueBase i))
  · exact Or.inl (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi valueBase) hafter)

theorem Memory.writeElement_encodesAt {α : Type} (codec : Codec α)
    (mem : Memory) (base index : Nat) (value : α) :
    (mem.writeBytes (base + index * codec.size) (codec.encode value)).EncodesAt
      codec (base + index * codec.size) value :=
  Memory.writeBytes_encodesAt codec mem _ value

theorem Memory.EncodesAt.fillElements_of_disjoint {α : Type}
    {codec : Codec α} {mem : Memory} {valueBase base : Addr}
    {value : α} {bytes : List Byte} {width start count : Nat}
    (hencoded : mem.EncodesAt codec valueBase value)
    (hdisjoint : ∀ index, start ≤ index → index < start + count →
      (Region.mk (base + index * width) bytes.length).disjoint
        (ValueRegion codec valueBase)) :
    (Memory.fillElements mem base width start count bytes).EncodesAt
      codec valueBase value := by
  induction count generalizing mem start with
  | zero => exact hencoded
  | succ count ih =>
      simp only [Memory.fillElements]
      apply ih (mem := mem.writeBytes (base + start * width) bytes)
        (start := start + 1)
      · exact hencoded.writeBytes_of_disjoint
          (hdisjoint start (by omega) (by omega))
      · intro index hlo hhi
        exact hdisjoint index (by omega) (by omega)

/-- One bounded scalar fill establishes every element's encoded value. The
disjointness premise is discharged arithmetically for native fixed arrays. -/
theorem Memory.fillElements_encodesAt {α : Type} (codec : Codec α)
    (mem : Memory) (base start count index : Nat) (value : α)
    (hindex : start ≤ index ∧ index < start + count)
    (hdisjoint : ∀ other, start ≤ other → other < start + count →
      other ≠ index →
      (Region.mk (base + other * codec.size) codec.size).disjoint
        (ValueRegion codec (base + index * codec.size))) :
    (Memory.fillElements mem base codec.size start count
      (codec.encode value)).EncodesAt codec
        (base + index * codec.size) value := by
  induction count generalizing mem start with
  | zero => omega
  | succ count ih =>
      simp only [Memory.fillElements]
      by_cases heq : index = start
      · subst index
        apply Memory.EncodesAt.fillElements_of_disjoint
          (Memory.writeElement_encodesAt codec mem base start value)
        intro other hlo hhi
        simpa [codec.encode_length] using
          hdisjoint other (by omega) (by omega) (by omega)
      · apply ih (mem := mem.writeBytes
          (base + start * codec.size) (codec.encode value))
          (start := start + 1)
        · omega
        · intro other hlo hhi hne
          exact hdisjoint other (by omega) (by omega) hne

theorem ValueRegion.element_disjoint {α : Type} (codec : Codec α)
    (base left right : Nat) (hne : left ≠ right) :
    (ValueRegion codec (base + left * codec.size)).disjoint
      (ValueRegion codec (base + right * codec.size)) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · apply Or.inl
    unfold ValueRegion Region.endAddr
    change base + left * codec.size + codec.size ≤
      base + right * codec.size
    rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right codec.size (Nat.succ_le_of_lt hlt)) base
  · apply Or.inr
    unfold ValueRegion Region.endAddr
    change base + right * codec.size + codec.size ≤
      base + left * codec.size
    rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right codec.size (Nat.succ_le_of_lt hgt)) base

theorem ArrayRegion.disjoint_element {α : Type} (codec : Codec α)
    {base count index : Nat} (hindex : index < count) {other : Region}
    (hdisjoint : other.disjoint (ArrayRegion codec base count)) :
    other.disjoint (ValueRegion codec (base + index * codec.size)) := by
  change other.endAddr ≤ base ∨
    base + count * codec.size ≤ other.base at hdisjoint
  change other.endAddr ≤ base + index * codec.size ∨
    base + index * codec.size + codec.size ≤ other.base
  rcases hdisjoint with hbefore | hafter
  · exact Or.inl (Nat.le_trans hbefore (Nat.le_add_right _ _))
  · apply Or.inr
    apply Nat.le_trans _ hafter
    rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right codec.size (Nat.succ_le_of_lt hindex)) base

theorem ArrayRegion.element_disjoint {α : Type} (codec : Codec α)
    {base count index : Nat} (hindex : index < count) {other : Region}
    (hdisjoint : (ArrayRegion codec base count).disjoint other) :
    (ValueRegion codec (base + index * codec.size)).disjoint other := by
  have hother := ArrayRegion.disjoint_element codec hindex
    (disjoint_symmetric.mp hdisjoint)
  exact disjoint_symmetric.mp hother

theorem ArrayRegion.elements_disjoint {α β : Type}
    (leftCodec : Codec α) (rightCodec : Codec β)
    {leftBase leftCount leftIndex rightBase rightCount rightIndex : Nat}
    (hleft : leftIndex < leftCount) (hright : rightIndex < rightCount)
    (hdisjoint : (ArrayRegion leftCodec leftBase leftCount).disjoint
      (ArrayRegion rightCodec rightBase rightCount)) :
    (ValueRegion leftCodec (leftBase + leftIndex * leftCodec.size)).disjoint
      (ValueRegion rightCodec (rightBase + rightIndex * rightCodec.size)) := by
  have hleftRegion := ArrayRegion.element_disjoint leftCodec hleft hdisjoint
  exact ArrayRegion.disjoint_element rightCodec hright hleftRegion

theorem pairwiseDisjoint_of_mem {regions : List Region} {left right : Region}
    (hpairwise : regions.Pairwise Region.disjoint)
    (hleft : left ∈ regions) (hright : right ∈ regions) (hne : left ≠ right) :
    left.disjoint right := by
  induction regions generalizing left right with
  | nil => simp at hleft
  | cons head tail ih =>
      simp only [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with hright | hright
        · exact False.elim (hne hright.symm)
        · exact hpairwise.1 _ hright
      · rcases hright with rfl | hright
        · exact disjoint_symmetric.mp (hpairwise.1 _ hleft)
        · exact ih hpairwise.2 hleft hright hne

def ElementWrite.region (write : ElementWrite) : Region :=
  { base := write.base + write.index * write.width,
    bytes := write.bytes.length }

theorem Memory.EncodesAt.elementWrite_of_disjoint {α : Type}
    {codec : Codec α} {mem : Memory} {base : Nat} {value : α}
    {write : ElementWrite} (hencoded : mem.EncodesAt codec base value)
    (hdisjoint : write.region.disjoint (ValueRegion codec base)) :
    (write.apply mem).EncodesAt codec base value := by
  simpa [ElementWrite.apply, ElementWrite.region] using
    hencoded.writeBytes_of_disjoint hdisjoint

theorem Memory.EncodesAt.applyAll_of_disjoint {α : Type}
    {codec : Codec α} {mem : Memory} {base : Nat} {value : α}
    {writes : List ElementWrite} (hencoded : mem.EncodesAt codec base value)
    (hdisjoint : ∀ write, write ∈ writes →
      write.region.disjoint (ValueRegion codec base)) :
    (ElementWrite.applyAll writes mem).EncodesAt codec base value := by
  induction writes generalizing mem with
  | nil => exact hencoded
  | cons write rest ih =>
      apply ih (hencoded.elementWrite_of_disjoint
        (hdisjoint write (by simp)))
      intro tail htail
      exact hdisjoint tail (by simp [htail])

theorem ElementWrite.applyAll_append (left right : List ElementWrite)
    (mem : Memory) :
    ElementWrite.applyAll (left ++ right) mem =
      ElementWrite.applyAll right (ElementWrite.applyAll left mem) := by
  induction left generalizing mem with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.cons_append, ElementWrite.applyAll]
      exact ih (write.apply mem)

theorem Memory.EncodesArray.writeBytes_of_disjoint {α : Type}
    {codec : Codec α} {mem : Memory} {base writeBase : Nat}
    {values : List α} {bytes : List Byte}
    (hencoded : mem.EncodesArray codec base values)
    (hdisjoint : (Region.mk writeBase bytes.length).disjoint
      (ArrayRegion codec base values.length)) :
    (mem.writeBytes writeBase bytes).EncodesArray codec base values := by
  intro index hindex
  apply (hencoded index hindex).writeBytes_of_disjoint
  exact ArrayRegion.disjoint_element codec hindex hdisjoint

theorem Memory.EncodesArray.applyAll_of_disjoint {α : Type}
    {codec : Codec α} {mem : Memory} {base : Nat} {values : List α}
    {writes : List ElementWrite} (hencoded : mem.EncodesArray codec base values)
    (hdisjoint : ∀ write, write ∈ writes →
      write.region.disjoint (ArrayRegion codec base values.length)) :
    (ElementWrite.applyAll writes mem).EncodesArray codec base values := by
  induction writes generalizing mem with
  | nil => exact hencoded
  | cons write rest ih =>
      apply ih (hencoded.writeBytes_of_disjoint (by
        simpa [ElementWrite.apply, ElementWrite.region] using
          hdisjoint write (by simp)))
      intro tail htail
      exact hdisjoint tail (by simp [htail])

theorem Memory.EncodesArray.fillElements_of_disjoint {α β : Type}
    {codec : Codec α} {writeCodec : Codec β} {mem : Memory}
    {base writeBase : Nat} {values : List α} {value : β}
    {start count : Nat}
    (hencoded : mem.EncodesArray codec base values)
    (hdisjoint : ∀ index, start ≤ index → index < start + count →
      (ValueRegion writeCodec (writeBase + index * writeCodec.size)).disjoint
        (ArrayRegion codec base values.length)) :
    (Memory.fillElements mem writeBase writeCodec.size start count
      (writeCodec.encode value)).EncodesArray codec base values := by
  intro index hindex
  apply (hencoded index hindex).fillElements_of_disjoint
  intro writeIndex hlo hhi
  simpa [ValueRegion, writeCodec.encode_length] using
    ArrayRegion.disjoint_element codec hindex (hdisjoint writeIndex hlo hhi)

/-- A native element assignment updates exactly the corresponding entry of a
typed encoded array. This is the representation rule for Rust `array[i] = v`.
-/
theorem Memory.EncodesArray.writeElement {α : Type} {codec : Codec α}
    {mem : Memory} {base : Nat} {values : List α} {index : Nat} {value : α}
    (hencoded : mem.EncodesArray codec base values) (hindex : index < values.length) :
    (mem.writeBytes (base + index * codec.size) (codec.encode value)).EncodesArray
      codec base (values.set index value) := by
  intro other hother
  have hother' : other < values.length := by
    simpa [List.length_set] using hother
  by_cases heq : index = other
  · subst other
    rw [List.getElem_set_self]
    exact Memory.writeElement_encodesAt codec mem base index value
  · rw [List.getElem_set_ne heq]
    apply (hencoded other hother').writeBytes_of_disjoint
    simpa [ValueRegion, codec.encode_length] using
      ValueRegion.element_disjoint codec base index other heq

/-- An ordered heterogeneous transaction containing one typed array update.
All preceding writes frame the old array, the selected write performs the
`List.set`, and all following writes frame the updated array. -/
theorem Memory.EncodesArray.applyAll_update {α : Type} {codec : Codec α}
    {mem : Memory} {base : Nat} {values : List α} {index : Nat} {value : α}
    {before after : List ElementWrite}
    (hencoded : mem.EncodesArray codec base values) (hindex : index < values.length)
    (hbefore : ∀ write, write ∈ before →
      write.region.disjoint (ArrayRegion codec base values.length))
    (hafter : ∀ write, write ∈ after →
      write.region.disjoint (ArrayRegion codec base values.length)) :
    (ElementWrite.applyAll
      (before ++ (⟨base, codec.size, index, codec.encode value⟩ : ElementWrite) ::
        after) mem).EncodesArray codec base (values.set index value) := by
  rw [ElementWrite.applyAll_append]
  simp only [ElementWrite.applyAll]
  apply ((hencoded.applyAll_of_disjoint hbefore).writeElement hindex)
    |>.applyAll_of_disjoint
  intro write hwrite
  simpa [List.length_set] using hafter write hwrite

theorem Memory.fillElements_encodesArray {α : Type} (codec : Codec α)
    (mem : Memory) (base count : Nat) (value : α) :
    (Memory.fillElements mem base codec.size 0 count
      (codec.encode value)).EncodesArray codec base
        (List.replicate count value) := by
  intro index hindex
  have hindex' : index < count := by simpa using hindex
  have hencoded := Memory.fillElements_encodesAt codec mem base 0 count index
    value ⟨by omega, by omega⟩ (by
      intro other _ _ hne
      exact ValueRegion.element_disjoint codec base other index hne)
  simpa using hencoded

/-- Exclusive allocated storage together with authoritative knowledge of its
initialized byte contents. -/
def OwnsValue {GF : BundledGFunctors} [ByteRegionGS GF] [ByteContentsGS GF]
    {α : Type} (codec : Codec α) (base : Addr) (value : α) : IProp GF :=
  iprop(OwnsBytes (ValueRegion codec base) ∗
    PointsToBytes base (codec.encode value))

theorem ownsValue_exclusive {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (base : Addr) (left right : α) :
    OwnsValue (GF := GF) codec base left ∗ OwnsValue codec base right ⊢ False := by
  unfold OwnsValue
  iintro ⟨Hleft, Hright⟩
  icases Hleft with ⟨HleftBytes, _⟩
  icases Hright with ⟨HrightBytes, _⟩
  icombine HleftBytes HrightBytes as H
  iapply ownsBytes_exclusive (ValueRegion codec base) codec.size_pos $$ H

theorem ownsValue_lookup {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) (base : Addr) (value : α)
    {contents : ContentsMap} {i : Nat} (hi : i < codec.size) :
    contentsInterp (G := G) contents ∗ OwnsValue codec base value ⊢
      ⌜Std.PartialMap.get? contents (base + i) =
        some ((codec.encode value).get
          ⟨i, by simpa [codec.encode_length] using hi⟩)⌝ := by
  unfold OwnsValue
  iintro ⟨Hcontents, Hvalue⟩
  icases Hvalue with ⟨_, Hbytes⟩
  icombine Hcontents Hbytes as H
  have hi' : i < (codec.encode value).length := by
    simpa [codec.encode_length] using hi
  iapply pointsToBytes_lookup hi' $$ H

end Luffs.Memory
