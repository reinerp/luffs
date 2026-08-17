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

structure AllocResult where
  handle : Handle
  state : Alloc.State

def allocationBytes {α : Type} (codec : Codec α) (capacity : Nat) : Nat :=
  Box.requestBytes (capacity * codec.size)

theorem allocationBytes_positive {α : Type} (codec : Codec α) {capacity : Nat}
    (hcapacity : 0 < capacity) : 0 < allocationBytes codec capacity :=
  Box.requestBytes_positive (Nat.mul_pos hcapacity codec.size_pos)

theorem allocationBytes_fits {α : Type} (codec : Codec α) {capacity : Nat}
    (hcapacity : 0 < capacity) :
    capacity * codec.size ≤ allocationBytes codec capacity :=
  Box.requestBytes_fits (Nat.mul_pos hcapacity codec.size_pos)

def allocate {α : Type} (codec : Codec α) (capacity : Nat)
    (hcapacity : 0 < capacity) (state : Alloc.State)
    (hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount) : Option AllocResult :=
  match Alloc.allocate state (allocationBytes codec capacity)
      (allocationBytes_positive codec hcapacity) hkeyMax with
  | none => none
  | some result => some ⟨⟨result.allocated, 0, capacity⟩, result.state⟩

theorem allocate_result {α : Type} {codec : Codec α} {capacity : Nat}
    {hcapacity : 0 < capacity} {state : Alloc.State}
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount} {result : AllocResult}
    (hsuccess : allocate codec capacity hcapacity state hkeyMax = some result) :
    ∃ raw, Alloc.allocate state (allocationBytes codec capacity)
        (allocationBytes_positive codec hcapacity) hkeyMax = some raw ∧
      result.handle = ⟨raw.allocated, 0, capacity⟩ ∧
      result.state = raw.state := by
  unfold allocate at hsuccess
  cases hraw : Alloc.allocate state (allocationBytes codec capacity)
      (allocationBytes_positive codec hcapacity) hkeyMax with
  | none => simp [hraw] at hsuccess
  | some raw =>
      simp [hraw] at hsuccess
      subst result
      exact ⟨raw, rfl, rfl, rfl⟩

theorem allocate_safe {α : Type} {codec : Codec α} {capacity : Nat}
    {hcapacity : 0 < capacity} {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount} {result : AllocResult}
    (hsuccess : allocate codec capacity hcapacity state hkeyMax = some result) :
    Valid codec result.handle ∧ result.handle.block.free = false ∧
      result.handle.block.aligned ∧ Alloc.Valid pool result.state := by
  obtain ⟨raw, hraw, hhandle, hstate⟩ := allocate_result hsuccess
  rw [hhandle, hstate]
  have hsafe := Alloc.allocate_safe hvalid hraw
  have hpreserved := Alloc.allocate_preserves_valid hvalid
    (Box.requestBytes_aligned (capacity * codec.size)) hraw
  exact ⟨⟨by simp, Nat.le_trans (allocationBytes_fits codec hcapacity)
      hsafe.2.2.1⟩, hsafe.1, hsafe.2.1, hpreserved⟩

theorem allocate_complete {α : Type} {codec : Codec α} {capacity : Nat}
    {hcapacity : 0 < capacity} {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount}
    (heligible : Bins.HasEligibleBin state.bins
      (searchSizeClass (allocationBytes codec capacity)
        (allocationBytes_positive codec hcapacity) hkeyMax)) :
    ∃ result, allocate codec capacity hcapacity state hkeyMax = some result := by
  obtain ⟨raw, hraw⟩ := Alloc.allocate_complete hvalid
    (Box.requestBytes_aligned (capacity * codec.size)) heligible
  change Alloc.allocate state (allocationBytes codec capacity)
    (allocationBytes_positive codec hcapacity) hkeyMax = some raw at hraw
  exact ⟨⟨⟨raw.allocated, 0, capacity⟩, raw.state⟩, by
    simp [allocate, hraw]⟩

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

theorem owns_empty {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) :
    Owns (GF := GF) codec pool handle [] ⊣⊢
      OwnsBytes (handle.block.region pool) := by
  simp only [Owns, encodeValues, List.flatMap_nil, PointsToBytes]
  exact sep_emp

theorem allocate_ownsFree {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    {codec : Codec α} {capacity : Nat} {hcapacity : 0 < capacity}
    {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount} {result : AllocResult}
    (hsuccess : allocate codec capacity hcapacity state hkeyMax = some result) :
    Ownership.OwnsFree (PROP := IProp GF) pool state.physical ⊣⊢
      Owns codec pool result.handle [] ∗
        Ownership.OwnsFree pool result.state.physical := by
  obtain ⟨raw, hraw, hhandle, hstate⟩ := allocate_result hsuccess
  rw [hhandle, hstate]
  have htransfer := Ownership.allocate_ownsFree (PROP := IProp GF)
    pool hvalid hraw
  simpa [Owns, encodeValues, PointsToBytes] using
    htransfer.trans (sep_congr_left sep_emp.symm)

def drop (pool : Region) (state : Alloc.State) (handle : Handle) :
    Option Alloc.State :=
  Box.drop pool state handle.block

theorem drop_preserves_valid {pool : Region} {state next : Alloc.State}
    (hvalid : Alloc.Valid pool state) {handle : Handle}
    (hsuccess : drop pool state handle = some next) : Alloc.Valid pool next :=
  Box.drop_preserves_valid hvalid hsuccess

theorem drop_complete {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount) {handle : Handle}
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false) :
    ∃ next, drop pool state handle = some next := by
  exact Box.drop_complete hvalid hpoolMax hmember (Bins.samePhysical_refl _)
    hallocated

theorem drop_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {state next : Alloc.State}
    {handle : Handle} (values : List α) (contents : ContentsMap)
    (hdrop : drop pool state handle = some next) :
    contentsInterp (G := G) contents ∗
        (Owns codec pool handle values ∗
          Ownership.OwnsFree pool state.physical) ==∗
      contentsInterp (deleteBytes contents (handle.block.region pool).base
          (encodeValues codec values)) ∗
        Ownership.OwnsFree pool next.physical := by
  unfold drop at hdrop
  unfold Box.drop at hdrop
  cases hfind : Bins.findPhysicalIndex state.physical handle.block with
  | none => simp [hfind] at hdrop
  | some i =>
      have hdealloc : Dealloc.deallocate pool state i
          (handle.block.region pool) = some next := by
        simpa [hfind] using hdrop
      simp only [Owns]
      iintro ⟨Hcontents, Hrest⟩
      icases Hrest with ⟨Hvec, Hallocator⟩
      icases Hvec with ⟨Hregion, Hpoints⟩
      icombine Hcontents Hpoints as Hinitialized
      imod pointsToBytes_delete contents (handle.block.region pool).base
        (encodeValues codec values) $$ Hinitialized with Hcontents
      icombine Hregion Hallocator as Hreturn
      ihave Hallocator :=
        (Dealloc.deallocate_ownsFree (PROP := IProp GF) hdealloc).mp $$ Hreturn
      imodintro
      isplitl [Hcontents]
      · iassumption
      · iassumption

structure GrowResult where
  handle : Handle
  state : Alloc.State

/-- Allocate a replacement buffer and return the old buffer to TLSF. Byte
copying is specified separately by `grow_owns`; this pure transition changes
only allocator metadata. -/
def grow {α : Type} (codec : Codec α) (pool : Region) (handle : Handle)
    (newCapacity : Nat) (hcapacity : 0 < newCapacity) (state : Alloc.State)
    (hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount) : Option GrowResult :=
  match allocate codec newCapacity hcapacity state hkeyMax with
  | none => none
  | some allocated =>
      match drop pool allocated.state handle with
      | none => none
      | some next => some ⟨⟨allocated.handle.block, handle.len,
          newCapacity⟩, next⟩

theorem grow_result {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle} {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    {state : Alloc.State}
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {result : GrowResult}
    (hsuccess : grow codec pool handle newCapacity hcapacity state hkeyMax =
      some result) :
    ∃ allocated next,
      allocate codec newCapacity hcapacity state hkeyMax = some allocated ∧
      drop pool allocated.state handle = some next ∧
      result = ⟨⟨allocated.handle.block, handle.len, newCapacity⟩, next⟩ := by
  unfold grow at hsuccess
  cases halloc : allocate codec newCapacity hcapacity state hkeyMax with
  | none => simp [halloc] at hsuccess
  | some allocated =>
      cases hdrop : drop pool allocated.state handle with
      | none => simp [halloc, hdrop] at hsuccess
      | some next =>
          simp [halloc, hdrop] at hsuccess
          subst result
          exact ⟨allocated, next, rfl, hdrop, rfl⟩

theorem grow_preserves_valid {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle}
    {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    (hlen : handle.len ≤ newCapacity) {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {result : GrowResult}
    (hsuccess : grow codec pool handle newCapacity hcapacity state hkeyMax =
      some result) :
    Valid codec result.handle ∧ Alloc.Valid pool result.state := by
  obtain ⟨allocated, next, halloc, hdrop, rfl⟩ := grow_result hsuccess
  have hsafe := allocate_safe hvalid halloc
  have hnext := drop_preserves_valid hsafe.2.2.2 hdrop
  obtain ⟨raw, _, hallocated, _⟩ := allocate_result halloc
  have hcap : allocated.handle.capacity = newCapacity := by
    rw [hallocated]
  exact ⟨⟨hlen, by simpa [hcap] using hsafe.1.2⟩, hnext⟩

theorem grow_complete {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle} {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount}
    (heligible : Bins.HasEligibleBin state.bins
      (searchSizeClass (allocationBytes codec newCapacity)
        (allocationBytes_positive codec hcapacity) hkeyMax)) :
    ∃ result,
      grow codec pool handle newCapacity hcapacity state hkeyMax = some result := by
  obtain ⟨allocated, halloc⟩ :=
    allocate_complete (hcapacity := hcapacity) hvalid heligible
  obtain ⟨raw, hraw, hhandle, hstate⟩ :=
    allocate_result (hcapacity := hcapacity) halloc
  have hnextValid :=
    (allocate_safe (hcapacity := hcapacity) hvalid halloc).2.2.2
  obtain ⟨updated, hupdated, hsame, _⟩ :=
    Alloc.allocate_preserves_allocated (hrequest :=
      allocationBytes_positive codec hcapacity) hvalid hraw hmember hallocated
  rw [hstate] at hnextValid
  obtain ⟨next, hdrop⟩ := Box.drop_complete hnextValid hpoolMax hupdated
    hsame hallocated
  exact ⟨⟨⟨allocated.handle.block, handle.len, newCapacity⟩, next⟩, by
    simp [grow, halloc, drop, hstate, hdrop]⟩

theorem replacement_regions_disjoint {α : Type} {codec : Codec α}
    {pool : Region} {handle : Handle} {newCapacity : Nat}
    {hcapacity : 0 < newCapacity} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state) (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated) :
    (handle.block.region pool).disjoint
      (allocated.handle.block.region pool) := by
  obtain ⟨raw, hraw, hhandle, hstate⟩ :=
    allocate_result (hcapacity := hcapacity) halloc
  obtain ⟨updated, hupdated, hsame, hne⟩ :=
    Alloc.allocate_preserves_allocated (hrequest :=
      allocationBytes_positive codec hcapacity) hvalid hraw hmember hallocated
  have hnew : raw.allocated ∈ raw.state.physical :=
    Alloc.allocate_allocated_mem hraw
  have hnextValid :=
    (allocate_safe (hcapacity := hcapacity) hvalid halloc).2.2.2
  rw [hstate] at hnextValid
  have hdisjoint := wellFormed_regions_disjoint hnextValid.1 hupdated hnew hne
  have holdRegion := Bins.samePhysical_region hsame pool
  rw [← holdRegion, hhandle]
  exact hdisjoint

theorem grow_copy_steps {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle} (hhandle : Valid codec handle) {values : List α}
    (hlen : values.length = handle.len) {newCapacity : Nat}
    {hcapacity : 0 < newCapacity} (hlenCapacity : handle.len ≤ newCapacity)
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated) (mem : Memory)
    (hsrc : ∀ i value, (encodeValues codec values)[i]? = some value →
      mem ((handle.block.region pool).base + i) = some value)
    (hdst : ∀ i, i < (encodeValues codec values).length →
      mem.mapped ((allocated.handle.block.region pool).base + i)) :
    ∃ next, CopySteps (handle.block.region pool).base
      (allocated.handle.block.region pool).base (encodeValues codec values)
      mem next := by
  have hregions := replacement_regions_disjoint hvalid hmember hallocated halloc
  have holdFit : (encodeValues codec values).length ≤ handle.block.bytes := by
    rw [encodeValues_length, hlen]
    exact Nat.le_trans (Nat.mul_le_mul_right codec.size hhandle.1) hhandle.2
  have hnewSafe := (allocate_safe (hcapacity := hcapacity) hvalid halloc).1
  obtain ⟨raw, _, hnewHandle, _⟩ :=
    allocate_result (hcapacity := hcapacity) halloc
  have hnewFit : (encodeValues codec values).length ≤
      allocated.handle.block.bytes := by
    rw [encodeValues_length, hlen]
    have hcapBytes := Nat.mul_le_mul_right codec.size hlenCapacity
    have hcap : allocated.handle.capacity = newCapacity := by rw [hnewHandle]
    have hcapacityFit := hnewSafe.2
    rw [hcap] at hcapacityFit
    exact Nat.le_trans hcapBytes hcapacityFit
  apply copySteps_exists _ _ _ _ hsrc hdst
  intro i hi j hj heq
  have hiContains : (handle.block.region pool).contains
      ((handle.block.region pool).base + i) := by
    exact contains_offset _ _ (Nat.lt_of_lt_of_le hi holdFit)
  have hjContains : (allocated.handle.block.region pool).contains
      ((allocated.handle.block.region pool).base + j) := by
    exact contains_offset _ _ (Nat.lt_of_lt_of_le hj hnewFit)
  have hnot := not_contains_of_disjoint hregions hiContains
  apply hnot
  rw [heq]
  exact hjContains

theorem grow_owns_step {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle}
    {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult} {next : Alloc.State}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated)
    (hdrop : drop pool allocated.state handle = some next)
    (values : List α) (contents : ContentsMap)
    (hfresh : CanInsertBytes contents
      (allocated.handle.block.region pool).base (encodeValues codec values)) :
    contentsInterp (G := G) contents ∗
        (Owns codec pool handle values ∗
          Ownership.OwnsFree pool state.physical) ==∗
      contentsInterp
          (deleteBytes
            (insertBytes contents (allocated.handle.block.region pool).base
              (encodeValues codec values))
            (handle.block.region pool).base (encodeValues codec values)) ∗
        (Owns codec pool
            ⟨allocated.handle.block, handle.len, newCapacity⟩ values ∗
          Ownership.OwnsFree pool next.physical) := by
  iintro ⟨Hcontents, Hrest⟩
  icases Hrest with ⟨Hold, Hallocator⟩
  ihave Hallocated :=
    (allocate_ownsFree (GF := GF) hvalid halloc).mp $$ Hallocator
  icases Hallocated with ⟨Hempty, Hallocator⟩
  ihave HnewRegion := (owns_empty codec pool allocated.handle).mp $$ Hempty
  imod pointsToBytes_insert contents
    (allocated.handle.block.region pool).base (encodeValues codec values)
    hfresh $$ Hcontents with ⟨Hcontents, HnewPoints⟩
  icombine Hold Hallocator as HoldAndAllocator
  icombine Hcontents HoldAndAllocator as HdropInput
  imod drop_owns codec values
    (insertBytes contents (allocated.handle.block.region pool).base
      (encodeValues codec values)) hdrop $$ HdropInput with
    ⟨Hcontents, Hallocator⟩
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplitr [Hallocator]
    · unfold Owns
      isplitl [HnewRegion]
      · iassumption
      · iassumption
    · iassumption

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
