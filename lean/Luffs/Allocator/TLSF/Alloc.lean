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

theorem splitAt_preserves_other {blocks : List Block} {i wanted : Nat}
    {selected other : Block} (hget : blocks[i]? = some selected)
    (hmem : other ∈ blocks) (hne : ¬ SamePhysical selected other) :
    ∃ updated ∈ splitAt blocks i wanted, SamePhysical updated other := by
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | htail
          · subst other
            exact (hne (samePhysical_refl head)).elim
          · exact ⟨other, by simp [splitAt, htail], samePhysical_refl other⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | htail
          · subst other
            exact ⟨head, by simp [splitAt], samePhysical_refl head⟩
          · obtain ⟨updated, hupdated, hsame⟩ := ih hget htail hne
            exact ⟨updated, by simp [splitAt, hupdated], hsame⟩

theorem markAllocatedAt_preserves_other {blocks : List Block} {i : Nat}
    {selected other : Block} (hget : blocks[i]? = some selected)
    (hmem : other ∈ blocks) (hne : ¬ SamePhysical selected other) :
    ∃ updated ∈ markAllocatedAt blocks i, SamePhysical updated other := by
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | htail
          · subst other
            exact (hne (samePhysical_refl head)).elim
          · cases rest with
            | nil => simp at htail
            | cons next tail =>
                simp only [List.mem_cons] at htail
                rcases htail with heq | htail
                · subst other
                  exact ⟨{ next with prevFree := false }, by
                    simp [markAllocatedAt], by simp [SamePhysical]⟩
                · exact ⟨other, by simp [markAllocatedAt, htail],
                    samePhysical_refl other⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | htail
          · subst other
            exact ⟨head, by simp [markAllocatedAt], samePhysical_refl head⟩
          · obtain ⟨updated, hupdated, hsame⟩ := ih hget htail hne
            exact ⟨updated, by simp [markAllocatedAt, hupdated], hsame⟩

theorem allocateChosenAt_preserves_other {blocks next : List Block}
    {i wanted : Nat} {selected allocated other : Block}
    (hget : blocks[i]? = some selected)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next))
    (hmem : other ∈ blocks) (hne : ¬ SamePhysical selected other) :
    ∃ updated ∈ next, SamePhysical updated other := by
  obtain ⟨_, _, _, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hsuccess
  · rcases hsplit with ⟨_, _, rfl⟩
    exact splitAt_preserves_other hget hmem hne
  · rcases hwhole with ⟨_, _, rfl⟩
    exact markAllocatedAt_preserves_other hget hmem hne

theorem splitAt_free_origin {blocks : List Block} {i wanted : Nat}
    {selected current : Block} (hget : blocks[i]? = some selected)
    (hmem : current ∈ splitAt blocks i wanted) (hfree : current.free = true) :
    SamePhysical current (splitBlock selected wanted).2 ∨
      ∃ old ∈ blocks, SamePhysical current old := by
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          simp only [splitAt, List.mem_cons] at hmem
          rcases hmem with hallocated | htail
          · subst current
            simp [splitBlock] at hfree
          · rcases htail with hremainder | hrest
            · subst current
              exact Or.inl (samePhysical_refl _)
            · exact Or.inr ⟨current, by simp [hrest], samePhysical_refl current⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [splitAt, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · subst current
            exact Or.inr ⟨head, by simp, samePhysical_refl head⟩
          · rcases ih hget htail with hrem | ⟨old, hold, hsame⟩
            · exact Or.inl hrem
            · exact Or.inr ⟨old, by simp [hold], hsame⟩

theorem markAllocatedAt_free_origin {blocks : List Block} {i : Nat}
    {selected current : Block} (hget : blocks[i]? = some selected)
    (hmem : current ∈ markAllocatedAt blocks i) (hfree : current.free = true) :
    ∃ old ∈ blocks, SamePhysical current old := by
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          cases rest with
          | nil =>
              simp [markAllocatedAt, markAllocated] at hmem
              subst current
              simp at hfree
          | cons next tail =>
              simp only [markAllocatedAt, List.mem_cons] at hmem
              rcases hmem with hallocated | htail
              · subst current
                simp [markAllocated] at hfree
              · rcases htail with hnext | htail
                · subst current
                  exact ⟨next, by simp, by simp [SamePhysical]⟩
                · exact ⟨current, by simp [htail], samePhysical_refl current⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [markAllocatedAt, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · subst current
            exact ⟨head, by simp, samePhysical_refl head⟩
          · obtain ⟨old, hold, hsame⟩ := ih hget htail
            exact ⟨old, by simp [hold], hsame⟩

theorem allocateChosenAt_free_origin {blocks next : List Block}
    {i wanted : Nat} {selected allocated current : Block}
    (hget : blocks[i]? = some selected)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next))
    (hmem : current ∈ next) (hfree : current.free = true) :
    (∃ remainder, allocationRemainder blocks i wanted = some remainder ∧
        SamePhysical current remainder) ∨
      ∃ old ∈ blocks, SamePhysical current old := by
  obtain ⟨_, _, _, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hsuccess
  · rcases hsplit with ⟨hcan, _, rfl⟩
    rcases splitAt_free_origin hget hmem hfree with hrem | hold
    · exact Or.inl ⟨(splitBlock selected wanted).2, by
        simp [allocationRemainder, hget, hcan], hrem⟩
    · exact Or.inr hold
  · rcases hwhole with ⟨hnosplit, _, rfl⟩
    exact Or.inr (markAllocatedAt_free_origin hget hmem hfree)

theorem allocateChosenAt_allocated_mem {blocks next : List Block}
    {i wanted : Nat} {selected allocated : Block}
    (hget : blocks[i]? = some selected)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    allocated ∈ next ∧ allocated.offset = selected.offset ∧
      allocated.free = false := by
  obtain ⟨_, _, _, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hsuccess
  · rcases hsplit with ⟨_, rfl, rfl⟩
    exact ⟨splitAt_contains_allocated hget, rfl, rfl⟩
  · rcases hwhole with ⟨_, rfl, rfl⟩
    exact ⟨markAllocatedAt_contains hget, rfl, rfl⟩

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

theorem allocateCore_wellFormed {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {core : CoreResult}
    (hcore : allocateCore state request hrequest hkeyMax = some core) :
    wellFormed pool core.physical := by
  obtain ⟨prepared, hprepare, hallocate, _, _⟩ := allocateCore_result hcore
  obtain ⟨actual, hget, _, _, _, _, _, _⟩ := prepare_safe hvalid hprepare
  exact allocateChosenAt_preserves_wellFormed hget hvalid.1 hallocate

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

theorem allocateCore_remainder_mem {state : State} {request : Nat}
    {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {core : CoreResult}
    (hcore : allocateCore state request hrequest hkeyMax = some core)
    {remainder : Block} (hremainder : core.freeRemainder = some remainder) :
    remainder ∈ core.physical := by
  obtain ⟨prepared, _, hallocate, _, hremDef⟩ := allocateCore_result hcore
  have hremSome : allocationRemainder state.physical
      prepared.physicalIndex request = some remainder := by
    rw [← hremDef]
    exact hremainder
  obtain ⟨selected, hget, hcan, rfl⟩ := allocationRemainder_result hremSome
  obtain ⟨_, _, _, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hallocate
  · rcases hsplit with ⟨_, _, hphysical⟩
    rw [hphysical]
    exact splitAt_contains_remainder hget
  · exact (hwhole.1 hcan).elim

theorem allocateCore_forward_agreement {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {core : CoreResult}
    (hcore : allocateCore state request hrequest hkeyMax = some core) :
    ∀ cls cached, cached ∈ core.bins.chains cls →
      ∃ actual ∈ core.physical, SamePhysical actual cached := by
  obtain ⟨prepared, hprepare, hallocate, hbins, _⟩ := allocateCore_result hcore
  obtain ⟨htake, _⟩ := prepare_result hprepare
  obtain ⟨removedClass, rest, _, hremove, hpreparedBins⟩ :=
    takeCandidate_result htake
  obtain ⟨selected, hselectedGet, hselectedDetached, _, _, _, _, _⟩ :=
    prepare_safe hvalid hprepare
  have hforward := takeCandidate_preserves_forward_agreement
    hvalid.2.1 hvalid.2.2 htake
  intro cls cached hcached
  have hcachedPrepared : cached ∈ prepared.bins.chains cls := by
    rw [← hbins]
    exact hcached
  obtain ⟨old, hold, holdCached⟩ := hforward cls cached hcachedPrepared
  have hnotSelected : ¬ SamePhysical selected old := by
    intro hselectedOld
    have hremovedCached := samePhysical_trans (samePhysical_symm hselectedDetached)
      (samePhysical_trans hselectedOld holdCached)
    have hcachedAfter : cached ∈
        (state.bins.replaceChain removedClass rest).chains cls := by
      rw [← hpreparedBins]
      exact hcachedPrepared
    exact removeFront_removed_not_represented hvalid.2.1 hremove
      hcachedAfter hremovedCached
  obtain ⟨updated, hupdated, hupdatedOld⟩ :=
    allocateChosenAt_preserves_other hselectedGet hallocate hold hnotSelected
  exact ⟨updated, hupdated, samePhysical_trans hupdatedOld holdCached⟩

theorem allocateCore_free_origin {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {core : CoreResult}
    (hcore : allocateCore state request hrequest hkeyMax = some core)
    {current : Block} (hcurrent : current ∈ core.physical)
    (hfree : current.free = true) :
    (∃ remainder, core.freeRemainder = some remainder ∧
        SamePhysical current remainder) ∨
      ∃ cls cached, cached ∈ core.bins.chains cls ∧
        SamePhysical current cached := by
  obtain ⟨prepared, hprepare, hallocate, hbins, hremDef⟩ :=
    allocateCore_result hcore
  obtain ⟨htake, _⟩ := prepare_result hprepare
  obtain ⟨removedClass, rest, _, hremove, hpreparedBins⟩ :=
    takeCandidate_result htake
  obtain ⟨selected, hselectedGet, hselectedDetached, _, _, _, _, _⟩ :=
    prepare_safe hvalid hprepare
  have hnewWell := allocateChosenAt_preserves_wellFormed hselectedGet hvalid.1 hallocate
  rcases allocateChosenAt_free_origin hselectedGet hallocate hcurrent hfree with
      hrem | ⟨old, hold, hcurrentOld⟩
  · obtain ⟨remainder, hremainder, hsame⟩ := hrem
    rw [← hremDef] at hremainder
    exact Or.inl ⟨remainder, hremainder, hsame⟩
  · have hallocatedInfo := allocateChosenAt_allocated_mem hselectedGet hallocate
    have hnotSelected : ¬ SamePhysical selected old := by
      intro hselectedOld
      have hcurrentOffset : current.offset = core.allocated.offset := by
        have h₁ : current.offset = old.offset := hcurrentOld.1
        have h₂ : selected.offset = old.offset := hselectedOld.1
        rw [h₁, ← h₂, ← hallocatedInfo.2.1]
      have heq := wellFormed_same_offset hnewWell hcurrent hallocatedInfo.1
        hcurrentOffset
      have hcurrentAllocated : current.free = false := by
        simpa [heq] using hallocatedInfo.2.2
      simp [hfree] at hcurrentAllocated
    have holdFree : old.free = true :=
      (samePhysical_free hcurrentOld).symm.trans hfree
    obtain ⟨query, cached, hcached, holdCached⟩ :=
      hvalid.2.2.2 old hold holdFree
    have hremovedNotOld : ¬ SamePhysical prepared.detached old := by
      intro hsame
      exact hnotSelected (samePhysical_trans hselectedDetached hsame)
    obtain ⟨nextQuery, nextCached, hnextCached, holdNext⟩ :=
      removeFront_preserves_other_representation hvalid.2.1 hremove
        ⟨query, cached, hcached, holdCached⟩ hremovedNotOld
    have hnextPrepared : nextCached ∈ prepared.bins.chains nextQuery := by
      rw [hpreparedBins]
      exact hnextCached
    have hnextCore : nextCached ∈ core.bins.chains nextQuery := by
      rw [hbins]
      exact hnextPrepared
    exact Or.inr ⟨nextQuery, nextCached, hnextCore,
      samePhysical_trans hcurrentOld holdNext⟩

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

theorem finishCore_forward_agreement {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (hrequestAligned : alignment ∣ request) {core : CoreResult} {next : State}
    (hcore : allocateCore state request hrequest hkeyMax = some core)
    (hfinish : finishCore core = some next) :
    ∀ cls cached, cached ∈ next.bins.chains cls →
      ∃ actual ∈ next.physical, SamePhysical actual cached := by
  have hcoreForward := allocateCore_forward_agreement hvalid hcore
  have hcoreValid := (allocateCore_safe hvalid hcore).2.2.2.2.2
  cases hremainder : core.freeRemainder with
  | none =>
      simp [finishCore, hremainder] at hfinish
      subst next
      exact hcoreForward
  | some remainder =>
      cases hclass : classifyBlock? remainder with
      | none => simp [finishCore, hremainder, hclass] at hfinish
      | some cls =>
          simp [finishCore, hremainder, hclass] at hfinish
          subst next
          have hremValid := allocateCore_remainder_valid hvalid hrequestAligned
            hcore hremainder
          exact insert_preserves_forward_agreement hcoreValid hcoreForward
            hremValid.1 (allocateCore_remainder_mem hcore hremainder)
            (samePhysical_refl remainder)

theorem finishCore_backward_agreement {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (hrequestAligned : alignment ∣ request) {core : CoreResult} {next : State}
    (hcore : allocateCore state request hrequest hkeyMax = some core)
    (hfinish : finishCore core = some next) :
    ∀ actual, actual ∈ next.physical → actual.free = true →
      ∃ cls cached, cached ∈ next.bins.chains cls ∧
        SamePhysical actual cached := by
  have hphysical := finishCore_physical hfinish
  have hcoreValid := (allocateCore_safe hvalid hcore).2.2.2.2.2
  intro actual hactual hfree
  have hactualCore : actual ∈ core.physical := by
    rw [← hphysical]
    exact hactual
  rcases allocateCore_free_origin hvalid hcore hactualCore hfree with
      hrem | hold
  · obtain ⟨remainder, hremainder, hactualRem⟩ := hrem
    cases hcoreRem : core.freeRemainder with
    | none => rw [hcoreRem] at hremainder; contradiction
    | some inserted =>
        have hinserted : inserted = remainder := by
          rw [hcoreRem] at hremainder
          exact Option.some.inj hremainder
        subst remainder
        cases hclass : classifyBlock? inserted with
        | none => simp [finishCore, hcoreRem, hclass] at hfinish
        | some cls =>
            simp [finishCore, hcoreRem, hclass] at hfinish
            subst next
            have hremValid := allocateCore_remainder_valid hvalid hrequestAligned
              hcore hcoreRem
            obtain ⟨cached, hcached, hinsertedCached⟩ :=
              inserted_has_representation (state := core.bins) (cls := cls)
                hremValid.1
            exact ⟨cls, cached, hcached,
              samePhysical_trans hactualRem hinsertedCached⟩
  · cases hcoreRem : core.freeRemainder with
    | none =>
        simp [finishCore, hcoreRem] at hfinish
        subst next
        exact hold
    | some inserted =>
        cases hclass : classifyBlock? inserted with
        | none => simp [finishCore, hcoreRem, hclass] at hfinish
        | some cls =>
            simp [finishCore, hcoreRem, hclass] at hfinish
            subst next
            exact insert_preserves_representation hcoreValid hold

theorem finishCore_physicalAgreement {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (hrequestAligned : alignment ∣ request) {core : CoreResult} {next : State}
    (hcore : allocateCore state request hrequest hkeyMax = some core)
    (hfinish : finishCore core = some next) :
    PhysicalAgreement next.physical next.bins := by
  exact ⟨finishCore_forward_agreement hvalid hrequestAligned hcore hfinish,
    finishCore_backward_agreement hvalid hrequestAligned hcore hfinish⟩

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

/-- Allocation mutates only its selected free block. Every previously
allocated block remains represented by the same physical region, even when a
neighbor's boundary-tag cache changes. -/
theorem allocate_preserves_allocated {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {result : Result}
    (hsuccess : allocate state request hrequest hkeyMax = some result)
    {old : Block} (hold : old ∈ state.physical) (holdAllocated : old.free = false) :
    ∃ updated ∈ result.state.physical,
      SamePhysical updated old ∧ updated ≠ result.allocated := by
  obtain ⟨core, hcore, hfinish, hresultAllocated⟩ := allocate_result hsuccess
  obtain ⟨prepared, hprepare, hchosen, _, _⟩ := allocateCore_result hcore
  obtain ⟨selected, hget, _, hselectedFree, _, _, _, _⟩ :=
    prepare_safe hvalid hprepare
  have hother : ¬ SamePhysical selected old := by
    intro hsame
    have : selected.free = false := (samePhysical_free hsame).trans holdAllocated
    simp [hselectedFree] at this
  obtain ⟨updated, hupdated, hsame⟩ :=
    allocateChosenAt_preserves_other hget hchosen hold hother
  have hnew := allocateChosenAt_allocated_mem hget hchosen
  have hupdatedNe : updated ≠ core.allocated := by
    intro heq
    have hoffset : selected.offset = old.offset := by
      rw [← hnew.2.1, ← heq, hsame.1]
    have hselectedMem : selected ∈ state.physical :=
      List.mem_of_getElem? hget
    have heqOld := wellFormed_same_offset hvalid.1 hselectedMem hold hoffset
    subst old
    simp [hselectedFree] at holdAllocated
  rw [finishCore_physical hfinish]
  exact ⟨updated, hupdated, hsame, by simpa [hresultAllocated] using hupdatedNe⟩

theorem allocate_allocated_mem {state : State} {request : Nat}
    {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount} {result : Result}
    (hsuccess : allocate state request hrequest hkeyMax = some result) :
    result.allocated ∈ result.state.physical := by
  obtain ⟨core, hcore, hfinish, hallocated⟩ := allocate_result hsuccess
  obtain ⟨prepared, hprepare, hchosen, _, _⟩ := allocateCore_result hcore
  obtain ⟨_, hfind⟩ := prepare_result hprepare
  obtain ⟨selected, hget, _⟩ := findPhysicalIndex_sound hfind
  have hmem := (allocateChosenAt_allocated_mem hget hchosen).1
  rw [hallocated, finishCore_physical hfinish]
  exact hmem

/-- Main pure allocator preservation theorem. -/
theorem allocate_preserves_valid {pool : Region} {state : State}
    (hvalid : Valid pool state) {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (hrequestAligned : alignment ∣ request) {result : Result}
    (hsuccess : allocate state request hrequest hkeyMax = some result) :
    Valid pool result.state := by
  obtain ⟨core, hcore, hfinish, _⟩ := allocate_result hsuccess
  have hphysical := finishCore_physical hfinish
  have hwellCore := allocateCore_wellFormed hvalid hcore
  have hwell : wellFormed pool result.state.physical := by
    rw [hphysical]
    exact hwellCore
  have hbins := (allocate_safe hvalid hsuccess).2.2.2.2.2
  have hagreement := finishCore_physicalAgreement hvalid hrequestAligned hcore hfinish
  exact ⟨hwell, hbins, hagreement⟩

end Luffs.Allocator.TLSF.Alloc
