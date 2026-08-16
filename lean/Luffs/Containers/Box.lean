import Luffs.Allocator.TLSF.Dealloc
import Luffs.Memory.Value

set_option autoImplicit false

namespace Luffs.Containers.Box

open Luffs.Memory
open Luffs.Allocator.TLSF
open Iris Iris.BI

def requestBytes (payload : Nat) : Nat := linearBinUpper payload

theorem requestBytes_positive {payload : Nat} (hpayload : 0 < payload) :
    0 < requestBytes payload := by
  have hle := (linear_sizeClass_covers payload hpayload).2
  exact Nat.lt_of_lt_of_le hpayload hle

theorem requestBytes_fits {payload : Nat} (hpayload : 0 < payload) :
    payload ≤ requestBytes payload :=
  (linear_sizeClass_covers payload hpayload).2

theorem requestBytes_aligned (payload : Nat) : alignment ∣ requestBytes payload := by
  exact ⟨linearBinNumber payload + 1, by
    simp [requestBytes, linearBinUpper, Nat.mul_comm]⟩

structure Result where
  block : Block
  state : Alloc.State

def allocate {α : Type} (codec : Codec α) (state : Alloc.State)
    (hkeyMax : requestKey (requestBytes codec.size) < 2 ^ firstLevelCount) :
    Option Result :=
  match Alloc.allocate state (requestBytes codec.size)
      (requestBytes_positive codec.size_pos) hkeyMax with
  | none => none
  | some result => some ⟨result.allocated, result.state⟩

theorem allocate_result {α : Type} {codec : Codec α} {state : Alloc.State}
    {hkeyMax : requestKey (requestBytes codec.size) < 2 ^ firstLevelCount}
    {result : Result} (hsuccess : allocate codec state hkeyMax = some result) :
    Alloc.allocate state (requestBytes codec.size)
        (requestBytes_positive codec.size_pos) hkeyMax =
      some ⟨result.block, result.state⟩ := by
  unfold allocate at hsuccess
  cases hraw : Alloc.allocate state (requestBytes codec.size)
      (requestBytes_positive codec.size_pos) hkeyMax with
  | none => simp [hraw] at hsuccess
  | some raw =>
      simp [hraw] at hsuccess
      subst result
      rfl

theorem allocate_safe {α : Type} {codec : Codec α} {pool : Region}
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (requestBytes codec.size) < 2 ^ firstLevelCount}
    {result : Result} (hsuccess : allocate codec state hkeyMax = some result) :
    result.block.free = false ∧ result.block.aligned ∧
      codec.size ≤ result.block.bytes ∧ Alloc.Valid pool result.state := by
  have hresult := allocate_result hsuccess
  have hsafe := Alloc.allocate_safe hvalid hresult
  have hpreserved := Alloc.allocate_preserves_valid hvalid
    (requestBytes_aligned codec.size) hresult
  exact ⟨hsafe.1, hsafe.2.1,
    Nat.le_trans (requestBytes_fits codec.size_pos) hsafe.2.2.1, hpreserved⟩

theorem allocate_complete {α : Type} {codec : Codec α} {pool : Region}
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (requestBytes codec.size) < 2 ^ firstLevelCount}
    (heligible : Bins.HasEligibleBin state.bins
      (searchSizeClass (requestBytes codec.size)
        (requestBytes_positive codec.size_pos) hkeyMax)) :
    ∃ result, allocate codec state hkeyMax = some result := by
  obtain ⟨raw, hraw⟩ := Alloc.allocate_complete hvalid
    (requestBytes_aligned codec.size) heligible
  exact ⟨⟨raw.allocated, raw.state⟩, by simp [allocate, hraw]⟩

def drop (pool : Region) (state : Alloc.State) (block : Block) :
    Option Alloc.State :=
  match Bins.findPhysicalIndex state.physical block with
  | none => none
  | some i => Dealloc.deallocate pool state i (block.region pool)

theorem drop_result {pool : Region} {state next : Alloc.State} {block : Block}
    (hsuccess : drop pool state block = some next) :
    ∃ i, Bins.findPhysicalIndex state.physical block = some i ∧
      Dealloc.deallocate pool state i (block.region pool) = some next := by
  unfold drop at hsuccess
  cases hfind : Bins.findPhysicalIndex state.physical block with
  | none => simp [hfind] at hsuccess
  | some i => exact ⟨i, rfl, by simpa [hfind] using hsuccess⟩

theorem drop_preserves_valid {pool : Region} {state next : Alloc.State}
    (hvalid : Alloc.Valid pool state) {block : Block}
    (hsuccess : drop pool state block = some next) : Alloc.Valid pool next := by
  obtain ⟨i, _, hdealloc⟩ := drop_result hsuccess
  exact Dealloc.deallocate_preserves_valid hvalid hdealloc

theorem drop_complete {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount) {block current : Block}
    (hcurrent : current ∈ state.physical) (hsame : Bins.SamePhysical current block)
    (hallocated : block.free = false) :
    ∃ next, drop pool state block = some next := by
  obtain ⟨i, hfind⟩ := Bins.findPhysicalIndex_complete hcurrent hsame
  obtain ⟨actual, hget, hactualBlock⟩ := Bins.findPhysicalIndex_sound hfind
  have hactualAllocated : actual.free = false :=
    (Bins.samePhysical_free hactualBlock).trans hallocated
  obtain ⟨next, hdrop⟩ := Dealloc.deallocate_complete hvalid hpoolMax hget
    hactualAllocated
  have hregion := Bins.samePhysical_region hactualBlock pool
  rw [hregion] at hdrop
  exact ⟨next, by simp [drop, hfind, hdrop]⟩

def Owns {GF : BundledGFunctors} [ByteRegionGS GF] [ByteContentsGS GF]
    {α : Type} (codec : Codec α) (pool : Region) (block : Block)
    (value : α) : IProp GF :=
  iprop(OwnsBytes (block.region pool) ∗
    PointsToBytes (block.region pool).base (codec.encode value))

theorem owns_exclusive {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (block : Block) (left right : α)
    (hbytes : 0 < block.bytes) :
    Owns (GF := GF) codec pool block left ∗ Owns codec pool block right ⊢ False := by
  unfold Owns
  iintro ⟨Hleft, Hright⟩
  icases Hleft with ⟨HleftBytes, _⟩
  icases Hright with ⟨HrightBytes, _⟩
  icombine HleftBytes HrightBytes as H
  iapply ownsBytes_exclusive (block.region pool) hbytes $$ H

theorem initialize_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (block : Block) (value : α)
    (contents : ContentsMap)
    (hfresh : CanInsertBytes contents (block.region pool).base
      (codec.encode value)) :
    contentsInterp (G := G) contents ∗ OwnsBytes (block.region pool) ==∗
      contentsInterp (insertBytes contents (block.region pool).base
        (codec.encode value)) ∗ Owns codec pool block value := by
  iintro ⟨Hcontents, Hregion⟩
  imod pointsToBytes_insert contents (block.region pool).base
    (codec.encode value) hfresh $$ Hcontents with ⟨Hcontents, Hpoints⟩
  imodintro
  isplitl [Hcontents]
  · iassumption
  · unfold Owns
    isplitl [Hregion]
    · iassumption
    · iassumption

theorem deref_byte {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {block : Block} {value : α}
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem)
    {i : Nat} (hi : i < codec.size) :
    contentsInterp (G := G) contents ∗ Owns codec pool block value ⊢
      ⌜PrimStep (.load ((block.region pool).base + i)) mem
        (.byte ((codec.encode value).get
          ⟨i, by simpa [codec.encode_length] using hi⟩)) mem⌝ := by
  simp only [Owns]
  iintro ⟨Hcontents, Hbox⟩
  icases Hbox with ⟨_, Hpoints⟩
  icombine Hcontents Hpoints as H
  have hi' : i < (codec.encode value).length := by
    simpa [codec.encode_length] using hi
  iapply pointsToBytes_load_exact hrep hi' $$ H

theorem decoded_value {α : Type} (codec : Codec α) (value : α) :
    codec.decode (codec.encode value) = some value :=
  codec.decode_encode value

theorem drop_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {state next : Alloc.State}
    {block : Block} (value : α) (contents : ContentsMap)
    (hdrop : drop pool state block = some next) :
    contentsInterp (G := G) contents ∗
        (Owns codec pool block value ∗
          Ownership.OwnsFree pool state.physical) ==∗
      contentsInterp (deleteBytes contents (block.region pool).base
          (codec.encode value)) ∗
        Ownership.OwnsFree pool next.physical := by
  unfold drop at hdrop
  cases hfind : Bins.findPhysicalIndex state.physical block with
  | none => simp [hfind] at hdrop
  | some i =>
      have hdealloc : Dealloc.deallocate pool state i (block.region pool) =
          some next := by simpa [hfind] using hdrop
      simp only [Owns]
      iintro ⟨Hcontents, Hrest⟩
      icases Hrest with ⟨Hbox, Hallocator⟩
      icases Hbox with ⟨Hregion, Hpoints⟩
      icombine Hcontents Hpoints as Hinitialized
      imod pointsToBytes_delete contents (block.region pool).base
        (codec.encode value) $$ Hinitialized with Hcontents
      icombine Hregion Hallocator as Hreturn
      ihave Hallocator :=
        (Dealloc.deallocate_ownsFree (PROP := IProp GF) hdealloc).mp $$ Hreturn
      imodintro
      isplitl [Hcontents]
      · iassumption
      · iassumption

end Luffs.Containers.Box
