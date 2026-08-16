import Luffs.Allocator.TLSF.Bins

set_option autoImplicit false

namespace Luffs.Allocator.TLSF.Alloc

open Luffs.Memory
open Luffs.Allocator.TLSF
open Luffs.Allocator.TLSF.Bins

/-- Executable allocator state for one mmap-backed pool. -/
structure State where
  physical : List Block
  bins : Bins.State

def Valid (pool : Region) (state : State) : Prop :=
  PoolValid pool state.physical state.bins

/-- Intermediate state after removing a suitable bin head and locating the
physical header it represents. It is intentionally not exposed to clients. -/
structure Prepared where
  detached : Block
  physicalIndex : Nat
  bins : Bins.State

structure CoreResult where
  allocated : Block
  physical : List Block
  bins : Bins.State
  freeRemainder : Option Block

def prepare (state : State) (request : Nat) (hrequest : 0 < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount) : Option Prepared :=
  match state.bins.takeCandidate (searchSizeClass request hrequest hkeyMax) with
  | none => none
  | some (detached, nextBins) =>
      match findPhysicalIndex state.physical detached with
      | none => none
      | some i => some { detached, physicalIndex := i, bins := nextBins }

theorem prepare_result {state : State} {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {prepared : Prepared}
    (hprepare : prepare state request hrequest hkeyMax = some prepared) :
    state.bins.takeCandidate (searchSizeClass request hrequest hkeyMax) =
        some (prepared.detached, prepared.bins) ∧
      findPhysicalIndex state.physical prepared.detached =
        some prepared.physicalIndex := by
  unfold prepare at hprepare
  cases htake : state.bins.takeCandidate
      (searchSizeClass request hrequest hkeyMax) with
  | none => simp [htake] at hprepare
  | some result =>
      obtain ⟨detached, nextBins⟩ := result
      cases hfind : findPhysicalIndex state.physical detached with
      | none => simp [htake, hfind] at hprepare
      | some i =>
          simp [htake, hfind] at hprepare
          subst prepared
          exact ⟨rfl, hfind⟩

/-- Preparation has the complete safety facts needed by the physical mutation:
the indexed header is free, aligned, and large enough, and bin removal
preserved its structural invariant. -/
theorem prepare_safe {pool : Region} {state : State} (hvalid : Valid pool state)
    {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {prepared : Prepared}
    (hprepare : prepare state request hrequest hkeyMax = some prepared) :
    ∃ actual,
      state.physical[prepared.physicalIndex]? = some actual ∧
      SamePhysical actual prepared.detached ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes ∧
      actual.bytes < 2 ^ firstLevelCount ∧ Bins.Valid prepared.bins := by
  obtain ⟨htake, hfind⟩ := prepare_result hprepare
  obtain ⟨actual, hget, hsame⟩ := findPhysicalIndex_sound hfind
  have hdetached := takeCandidate_suitable hvalid request hrequest hkeyMax htake
  obtain ⟨_, _, _, hfree, haligned, hsuitable, hmax⟩ := hdetached
  have hactualFree : actual.free = true := (samePhysical_free hsame).trans hfree
  have hactualAligned := (samePhysical_aligned_iff hsame).2 haligned
  have hbytes : actual.bytes = prepared.detached.bytes := hsame.2.1
  exact ⟨actual, hget, hsame, hactualFree, hactualAligned,
    by simpa [hbytes] using hsuitable, by simpa [hbytes] using hmax,
    takeCandidate_valid hvalid.2.1 htake⟩

theorem prepare_complete {pool : Region} {state : State} (hvalid : Valid pool state)
    {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (heligible : HasEligibleBin state.bins
      (searchSizeClass request hrequest hkeyMax)) :
    ∃ prepared, prepare state request hrequest hkeyMax = some prepared := by
  obtain ⟨detached, nextBins, htake⟩ :=
    takeCandidate_complete hvalid.2.1 heligible
  obtain ⟨actual, hactual, hsame, _, _, _, _⟩ :=
    takeCandidate_suitable hvalid request hrequest hkeyMax htake
  obtain ⟨i, hfind⟩ := findPhysicalIndex_complete hactual hsame
  exact ⟨{ detached, physicalIndex := i, bins := nextBins }, by
    simp [prepare, htake, hfind]⟩

/-- Allocation through the physical mutation, before a split remainder is
reinserted into its bin. -/
def allocateCore (state : State) (request : Nat) (hrequest : 0 < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount) : Option CoreResult :=
  match prepare state request hrequest hkeyMax with
  | none => none
  | some prepared =>
      match allocateChosenAt state.physical prepared.physicalIndex request with
      | none => none
      | some (allocated, physical) =>
          some ⟨allocated, physical, prepared.bins,
            allocationRemainder state.physical prepared.physicalIndex request⟩

theorem allocateCore_result {state : State} {request : Nat}
    {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {result : CoreResult}
    (hsuccess : allocateCore state request hrequest hkeyMax = some result) :
    ∃ prepared,
      prepare state request hrequest hkeyMax = some prepared ∧
      allocateChosenAt state.physical prepared.physicalIndex request =
        some (result.allocated, result.physical) ∧
      result.bins = prepared.bins ∧
      result.freeRemainder = allocationRemainder state.physical
        prepared.physicalIndex request := by
  unfold allocateCore at hsuccess
  cases hprepare : prepare state request hrequest hkeyMax with
  | none => simp [hprepare] at hsuccess
  | some prepared =>
      cases hallocate : allocateChosenAt state.physical prepared.physicalIndex request with
      | none => simp [hprepare, hallocate] at hsuccess
      | some pair =>
          obtain ⟨allocated, physical⟩ := pair
          simp [hprepare, hallocate] at hsuccess
          subst result
          exact ⟨prepared, rfl, hallocate, rfl, rfl⟩

theorem allocateCore_safe {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {result : CoreResult}
    (hsuccess : allocateCore state request hrequest hkeyMax = some result) :
    result.allocated.free = false ∧ result.allocated.aligned ∧
      request ≤ result.allocated.bytes ∧
      partitions pool result.physical ∧ boundaryTags result.physical ∧
      Bins.Valid result.bins := by
  obtain ⟨prepared, hprepare, hallocate, hbins, _⟩ := allocateCore_result hsuccess
  obtain ⟨actual, hget, _, _, haligned, _, _, hbinsValid⟩ :=
    prepare_safe hvalid hprepare
  have hresult := allocateChosenAt_result hget haligned hallocate
  have hparts := allocateChosenAt_preserves_partitions hget hvalid.1.2.1 hallocate
  have htags := allocateChosenAt_preserves_boundaryTags hget hvalid.1.2.2.1 hallocate
  exact ⟨hresult.1, hresult.2.1, hresult.2.2.1, hparts, htags,
    by simpa [hbins] using hbinsValid⟩

theorem allocateCore_remainder_fresh {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {core : CoreResult}
    (hcore : allocateCore state request hrequest hkeyMax = some core)
    {remainder : Block} (hremainder : core.freeRemainder = some remainder)
    {cls : SizeClass} :
    remainder.offset ∉ (core.bins.chains cls).map Block.offset := by
  intro hoffset
  obtain ⟨prepared, hprepare, _hallocate, hbins, hremDef⟩ :=
    allocateCore_result hcore
  obtain ⟨htake, _hfind⟩ := prepare_result hprepare
  obtain ⟨selected, hselectedGet, _, _, _, _, _, _⟩ :=
    prepare_safe hvalid hprepare
  have hremSome : allocationRemainder state.physical
      prepared.physicalIndex request = some remainder := by
    rw [← hremDef]
    exact hremainder
  obtain ⟨original, horiginalGet, hcan, hremEq⟩ :=
    allocationRemainder_result hremSome
  have horiginal : original = selected := by
    rw [hselectedGet] at horiginalGet
    exact (Option.some.inj horiginalGet).symm
  subst original
  subst remainder
  have hforward := takeCandidate_preserves_forward_agreement
    hvalid.2.1 hvalid.2.2 htake
  obtain ⟨cached, hcached, hoffsetEq⟩ := List.mem_map.mp hoffset
  have hcachedPrepared : cached ∈ prepared.bins.chains cls := by
    rw [← hbins]
    exact hcached
  obtain ⟨other, hother, hsame⟩ := hforward cls cached hcachedPrepared
  have hotherOffset : other.offset = cached.offset := hsame.1
  have hlower : selected.offset < (splitBlock selected request).2.offset := by
    simp only [splitBlock]
    exact Nat.lt_add_of_pos_right hcan.1
  have hupper : (splitBlock selected request).2.offset <
      selected.offset + selected.bytes := by
    simp only [splitBlock]
    have hroom := hcan.2
    simp only [minimumBlockBytes] at hroom
    omega
  apply no_block_starts_inside hvalid.1
    (List.mem_iff_getElem?.2 ⟨prepared.physicalIndex, hselectedGet⟩) hother
    (by simpa [hotherOffset, hoffsetEq] using hlower)
    (by simpa [hotherOffset, hoffsetEq] using hupper)

theorem allocateCore_remainder_valid {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (hrequestAligned : alignment ∣ request) {core : CoreResult}
    (hcore : allocateCore state request hrequest hkeyMax = some core)
    {remainder : Block} (hremainder : core.freeRemainder = some remainder) :
    remainder.free = true ∧ remainder.aligned ∧ 0 < remainder.bytes ∧
      remainder.bytes < 2 ^ firstLevelCount := by
  obtain ⟨prepared, hprepare, _, _, hremDef⟩ := allocateCore_result hcore
  obtain ⟨selected, hselectedGet, _, _, hselectedAligned, _, hselectedMax, _⟩ :=
    prepare_safe hvalid hprepare
  have hremSome : allocationRemainder state.physical
      prepared.physicalIndex request = some remainder := by
    rw [← hremDef]
    exact hremainder
  obtain ⟨original, horiginalGet, hcan, rfl⟩ :=
    allocationRemainder_result hremSome
  have horiginal : original = selected := by
    rw [hselectedGet] at horiginalGet
    exact (Option.some.inj horiginalGet).symm
  subst original
  have haligned := (splitBlock_aligned hselectedAligned hrequestAligned).2
  have hpositive := (splitBlock_nonempty hcan).2
  have hmax : (splitBlock selected request).2.bytes < 2 ^ firstLevelCount := by
    simp only [splitBlock]
    omega
  exact ⟨rfl, haligned, hpositive, hmax⟩

theorem allocateCore_complete {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (haligned : alignment ∣ request)
    (heligible : HasEligibleBin state.bins
      (searchSizeClass request hrequest hkeyMax)) :
    ∃ result, allocateCore state request hrequest hkeyMax = some result := by
  obtain ⟨prepared, hprepare⟩ := prepare_complete hvalid heligible
  obtain ⟨actual, hget, _, hfree, _, hfits, _, _⟩ := prepare_safe hvalid hprepare
  obtain ⟨allocated, physical, hallocate⟩ :=
    allocateChosenAt_exists hget hfree hfits haligned
  exact ⟨⟨allocated, physical, prepared.bins,
      allocationRemainder state.physical prepared.physicalIndex request⟩, by
    simp [allocateCore, hprepare, hallocate]⟩

/-- Restore the bin projection after the physical mutation. Whole-block
allocation has no remainder; split allocation classifies and inserts the new
free remainder. -/
def finishCore (core : CoreResult) : Option State :=
  match core.freeRemainder with
  | none => some ⟨core.physical, core.bins⟩
  | some remainder =>
      match classifyBlock? remainder with
      | none => none
      | some cls => some ⟨core.physical, core.bins.insert cls remainder⟩

theorem finishCore_physical {core : CoreResult} {next : State}
    (hfinish : finishCore core = some next) : next.physical = core.physical := by
  unfold finishCore at hfinish
  split at hfinish
  next => cases hfinish; rfl
  next =>
    split at hfinish
    next => contradiction
    next => cases hfinish; rfl

structure Result where
  allocated : Block
  state : State

def allocate (state : State) (request : Nat) (hrequest : 0 < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount) : Option Result :=
  match allocateCore state request hrequest hkeyMax with
  | none => none
  | some core =>
      match finishCore core with
      | none => none
      | some next => some ⟨core.allocated, next⟩

theorem allocate_result {state : State} {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {result : Result}
    (hsuccess : allocate state request hrequest hkeyMax = some result) :
    ∃ core, allocateCore state request hrequest hkeyMax = some core ∧
      finishCore core = some result.state ∧ result.allocated = core.allocated := by
  unfold allocate at hsuccess
  cases hcore : allocateCore state request hrequest hkeyMax with
  | none => simp [hcore] at hsuccess
  | some core =>
      cases hfinish : finishCore core with
      | none => simp [hcore, hfinish] at hsuccess
      | some next =>
          simp [hcore, hfinish] at hsuccess
          subst result
          exact ⟨core, rfl, hfinish, rfl⟩

theorem finishCore_bins_valid {core : CoreResult} {next : State}
    (hvalid : Bins.Valid core.bins)
    (hfresh : ∀ remainder cls,
      core.freeRemainder = some remainder → classifyBlock? remainder = some cls →
      remainder.offset ∉ (core.bins.chains cls).map Block.offset)
    (hfinish : finishCore core = some next) : Bins.Valid next.bins := by
  unfold finishCore at hfinish
  cases hremainder : core.freeRemainder with
  | none =>
      simp [hremainder] at hfinish
      subst next
      exact hvalid
  | some remainder =>
      cases hclass : classifyBlock? remainder with
      | none => simp [hremainder, hclass] at hfinish
      | some cls =>
          simp [hremainder, hclass] at hfinish
          subst next
          exact insert_valid hvalid cls remainder (classifyBlock?_result hclass)
            (hfresh remainder cls hremainder hclass)

theorem finishCore_complete {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (hrequestAligned : alignment ∣ request) {core : CoreResult}
    (hcore : allocateCore state request hrequest hkeyMax = some core) :
    ∃ next, finishCore core = some next := by
  cases hremainder : core.freeRemainder with
  | none => exact ⟨⟨core.physical, core.bins⟩, by simp [finishCore, hremainder]⟩
  | some remainder =>
      have hremValid := allocateCore_remainder_valid hvalid hrequestAligned
        hcore hremainder
      obtain ⟨cls, hclass⟩ := classifyBlock?_complete hremValid.2.2.1
        hremValid.2.2.2
      exact ⟨⟨core.physical, core.bins.insert cls remainder⟩, by
        simp [finishCore, hremainder, hclass]⟩

theorem allocate_complete {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (hrequestAligned : alignment ∣ request)
    (heligible : HasEligibleBin state.bins
      (searchSizeClass request hrequest hkeyMax)) :
    ∃ result, allocate state request hrequest hkeyMax = some result := by
  obtain ⟨core, hcore⟩ := allocateCore_complete hvalid hrequestAligned heligible
  obtain ⟨next, hfinish⟩ := finishCore_complete hvalid hrequestAligned hcore
  exact ⟨⟨core.allocated, next⟩, by simp [allocate, hcore, hfinish]⟩

theorem allocate_safe_except_agreement {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {result : Result}
    (hfresh : ∀ core remainder cls,
      allocateCore state request hrequest hkeyMax = some core →
      core.freeRemainder = some remainder → classifyBlock? remainder = some cls →
      remainder.offset ∉ (core.bins.chains cls).map Block.offset)
    (hsuccess : allocate state request hrequest hkeyMax = some result) :
    result.allocated.free = false ∧ result.allocated.aligned ∧
      request ≤ result.allocated.bytes ∧ partitions pool result.state.physical ∧
      boundaryTags result.state.physical ∧ Bins.Valid result.state.bins := by
  obtain ⟨core, hcore, hfinish, hallocated⟩ := allocate_result hsuccess
  have hsafe := allocateCore_safe hvalid hcore
  have hbins := finishCore_bins_valid hsafe.2.2.2.2.2
    (fun remainder cls hr hc => hfresh core remainder cls hcore hr hc) hfinish
  have hphysical := finishCore_physical hfinish
  rw [hallocated, hphysical]
  exact ⟨hsafe.1, hsafe.2.1, hsafe.2.2.1, hsafe.2.2.2.1,
    hsafe.2.2.2.2.1, hbins⟩

theorem allocate_safe {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {result : Result}
    (hsuccess : allocate state request hrequest hkeyMax = some result) :
    result.allocated.free = false ∧ result.allocated.aligned ∧
      request ≤ result.allocated.bytes ∧ partitions pool result.state.physical ∧
      boundaryTags result.state.physical ∧ Bins.Valid result.state.bins := by
  exact allocate_safe_except_agreement hvalid
    (fun core remainder _ hcore hremainder _ =>
      allocateCore_remainder_fresh hvalid hcore hremainder) hsuccess

end Luffs.Allocator.TLSF.Alloc
