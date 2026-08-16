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
