import Luffs.Containers.Box

set_option autoImplicit false

namespace Luffs.Containers.Vec

open Luffs.Memory
open Luffs.Allocator.TLSF
open Iris Iris.BI

def encodeValues {α : Type} (codec : Codec α) (values : List α) : List Byte :=
  values.flatMap codec.encode

theorem encodeValues_append {α : Type} (codec : Codec α)
    (left right : List α) :
    encodeValues codec (left ++ right) =
      encodeValues codec left ++ encodeValues codec right := by
  simp [encodeValues, List.flatMap_append]

theorem encodeValues_length {α : Type} (codec : Codec α) (values : List α) :
    (encodeValues codec values).length = values.length * codec.size := by
  induction values with
  | nil => simp [encodeValues]
  | cons value rest ih =>
      change (codec.encode value ++ encodeValues codec rest).length =
        (rest.length + 1) * codec.size
      rw [List.length_append, codec.encode_length, ih, Nat.add_mul]
      omega

structure Handle where
  block : Block
  len : Nat
  capacity : Nat
deriving DecidableEq, Repr

def Valid {α : Type} (codec : Codec α) (handle : Handle) : Prop :=
  handle.len ≤ handle.capacity ∧
    handle.capacity * codec.size ≤ handle.block.bytes

def push (handle : Handle) : Option Handle :=
  if handle.len < handle.capacity then
    some { handle with len := handle.len + 1 }
  else none

def pop (handle : Handle) : Option Handle :=
  if 0 < handle.len then some { handle with len := handle.len - 1 } else none

theorem push_result {handle next : Handle} (hsuccess : push handle = some next) :
    handle.len < handle.capacity ∧ next = { handle with len := handle.len + 1 } := by
  unfold push at hsuccess
  split at hsuccess
  next hlt => exact ⟨hlt, Option.some.inj hsuccess |>.symm⟩
  next => contradiction

theorem push_preserves_valid {α : Type} {codec : Codec α}
    {handle next : Handle} (hvalid : Valid codec handle)
    (hsuccess : push handle = some next) : Valid codec next := by
  obtain ⟨hlt, rfl⟩ := push_result hsuccess
  rcases hvalid with ⟨hlen, hcapacity⟩
  exact ⟨by simp; omega, by simpa [Valid] using hcapacity⟩

theorem pop_result {handle next : Handle} (hsuccess : pop handle = some next) :
    0 < handle.len ∧ next = { handle with len := handle.len - 1 } := by
  unfold pop at hsuccess
  split at hsuccess
  next hpos => exact ⟨hpos, Option.some.inj hsuccess |>.symm⟩
  next => contradiction

theorem pop_preserves_valid {α : Type} {codec : Codec α}
    {handle next : Handle} (hvalid : Valid codec handle)
    (hsuccess : pop handle = some next) : Valid codec next := by
  obtain ⟨hpos, rfl⟩ := pop_result hsuccess
  rcases hvalid with ⟨hlen, hcapacity⟩
  exact ⟨by simp; omega, by simpa [Valid] using hcapacity⟩

def Owns {GF : BundledGFunctors} [ByteRegionGS GF] [ByteContentsGS GF]
    {α : Type} (codec : Codec α) (pool : Region) (handle : Handle)
    (values : List α) : IProp GF :=
  iprop(OwnsBytes (handle.block.region pool) ∗
    PointsToBytes (handle.block.region pool).base (encodeValues codec values))

theorem owns_exclusive {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle)
    (left right : List α) (hbytes : 0 < handle.block.bytes) :
    Owns (GF := GF) codec pool handle left ∗ Owns codec pool handle right ⊢
      False := by
  unfold Owns
  iintro ⟨Hleft, Hright⟩
  icases Hleft with ⟨HleftBytes, _⟩
  icases Hright with ⟨HrightBytes, _⟩
  icombine HleftBytes HrightBytes as H
  iapply ownsBytes_exclusive (handle.block.region pool) hbytes $$ H

theorem index_fits {α : Type} {codec : Codec α} {handle : Handle}
    (hvalid : Valid codec handle) {values : List α}
    (_hlen : values.length = handle.len) {i : Nat} (hi : i < handle.len) :
    i * codec.size + codec.size ≤ handle.block.bytes := by
  rcases hvalid with ⟨hlenCap, hcapacity⟩
  have hindex : i + 1 ≤ handle.capacity := by omega
  have := Nat.mul_le_mul_right codec.size hindex
  rw [Nat.add_mul] at this
  simpa using Nat.le_trans this hcapacity

theorem index_flat_lt {α : Type} (codec : Codec α) {handle : Handle}
    {values : List α} (hlen : values.length = handle.len)
    {i byteIndex : Nat} (hi : i < handle.len)
    (hbyte : byteIndex < codec.size) :
    i * codec.size + byteIndex < (encodeValues codec values).length := by
  rw [encodeValues_length, hlen]
  have hnext : i + 1 ≤ handle.len := by omega
  have hlocal : i * codec.size + byteIndex < (i + 1) * codec.size := by
    rw [Nat.add_mul]
    omega
  have hcapacity := Nat.mul_le_mul_right codec.size hnext
  exact Nat.lt_of_lt_of_le hlocal hcapacity

theorem index_byte {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {values : List α}
    (hlen : values.length = handle.len) {contents : ContentsMap} {mem : Memory}
    (hrep : ContentsRep contents mem) {i byteIndex : Nat}
    (hi : i < handle.len) (hbyte : byteIndex < codec.size) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ⊢
      ⌜PrimStep (.load ((handle.block.region pool).base +
          (i * codec.size + byteIndex))) mem
        (.byte ((encodeValues codec values).get
          ⟨i * codec.size + byteIndex,
            index_flat_lt codec hlen hi hbyte⟩)) mem⌝ := by
  simp only [Owns]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨_, Hpoints⟩
  icombine Hcontents Hpoints as H
  have hflat := index_flat_lt codec hlen hi hbyte
  iapply pointsToBytes_load_exact hrep hflat $$ H

theorem push_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle next : Handle}
    {values : List α} (value : α) (contents : ContentsMap)
    (hsuccess : push handle = some next)
    (hfresh : CanInsertBytes contents
      ((handle.block.region pool).base + (encodeValues codec values).length)
      (codec.encode value)) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ==∗
      contentsInterp (insertBytes contents
          ((handle.block.region pool).base + (encodeValues codec values).length)
          (codec.encode value)) ∗
        Owns codec pool next (values ++ [value]) := by
  obtain ⟨_, rfl⟩ := push_result hsuccess
  have hencoded : encodeValues codec (values ++ [value]) =
      encodeValues codec values ++ codec.encode value := by
    simp [encodeValues]
  simp only [Owns]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hold⟩
  imod pointsToBytes_insert contents
    ((handle.block.region pool).base + (encodeValues codec values).length)
    (codec.encode value) hfresh $$ Hcontents with ⟨Hcontents, Hnew⟩
  icombine Hold Hnew as Hpoints
  ihave Hpoints := (pointsToBytes_append
    (handle.block.region pool).base (encodeValues codec values)
      (codec.encode value)).mpr $$ Hpoints
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplitl [Hregion]
    · iassumption
    · rw [hencoded]
      iassumption

theorem pop_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle next : Handle}
    (initValues : List α) (last : α) (contents : ContentsMap)
    (hlen : handle.len = initValues.length + 1)
    (hsuccess : pop handle = some next) :
    contentsInterp (G := G) contents ∗
        Owns codec pool handle (initValues ++ [last]) ==∗
      contentsInterp (deleteBytes contents
          ((handle.block.region pool).base +
            (encodeValues codec initValues).length)
          (codec.encode last)) ∗
        (⌜next.len = initValues.length⌝ ∗ Owns codec pool next initValues) := by
  obtain ⟨_, hnext⟩ := pop_result hsuccess
  subst next
  have hencoded : encodeValues codec (initValues ++ [last]) =
      encodeValues codec initValues ++ codec.encode last := by
    simp [encodeValues]
  simp only [Owns]
  rw [hencoded]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hpoints⟩
  ihave Hsplit := (pointsToBytes_append
    (handle.block.region pool).base (encodeValues codec initValues)
      (codec.encode last)).mp $$ Hpoints
  icases Hsplit with ⟨Hprefix, Hlast⟩
  icombine Hcontents Hlast as Hdelete
  imod pointsToBytes_delete contents
    ((handle.block.region pool).base + (encodeValues codec initValues).length)
    (codec.encode last) $$ Hdelete with Hcontents
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplit
    · ipureintro
      simp [hlen]
    · isplitl [Hregion]
      · iassumption
      · iassumption

end Luffs.Containers.Vec
