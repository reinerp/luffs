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
    {value : α} {bytes : List Byte} {start count : Nat}
    (hencoded : mem.EncodesAt codec valueBase value)
    (hdisjoint : ∀ index, start ≤ index → index < start + count →
      (Region.mk (base + index * codec.size) bytes.length).disjoint
        (ValueRegion codec valueBase)) :
    (Memory.fillElements mem base codec.size start count bytes).EncodesAt
      codec valueBase value := by
  induction count generalizing mem start with
  | zero => exact hencoded
  | succ count ih =>
      simp only [Memory.fillElements]
      apply ih (mem := mem.writeBytes (base + start * codec.size) bytes)
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
