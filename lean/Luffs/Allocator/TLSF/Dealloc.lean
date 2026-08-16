import Luffs.Allocator.TLSF.Ownership

set_option autoImplicit false

namespace Luffs.Allocator.TLSF.Dealloc

open Luffs.Memory
open Luffs.Allocator.TLSF
open Luffs.Allocator.TLSF.Bins
open Iris Iris.BI

def freedBlock (b : Block) : Block :=
  { offset := b.offset, bytes := b.bytes, free := true,
    prevFree := b.prevFree, prevFreeLink := none, nextFreeLink := none }

theorem freedBlock_samePhysical (b : Block) :
    SamePhysical (freedBlock b) { b with free := true } := by
  simp [freedBlock, SamePhysical]

theorem freedBlock_aligned {b : Block} (h : b.aligned) :
    (freedBlock b).aligned := by
  simpa [freedBlock, Block.aligned] using h

theorem markFreeAt_contains {blocks : List Block} {i : Nat} {b : Block}
    (hget : blocks[i]? = some b) : freedBlock b ∈ markFreeAt blocks i := by
  induction blocks generalizing i b with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst b
          cases rest <;> simp [markFreeAt, freedBlock]
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp [markFreeAt, ih hget]

theorem blocksShaped_markFreeAt {blocks : List Block} {i : Nat}
    (hshape : blocksShaped blocks) : blocksShaped (markFreeAt blocks i) := by
  induction blocks generalizing i with
  | nil => simp [blocksShaped, markFreeAt]
  | cons head rest ih =>
      have hhead := hshape head (by simp)
      have hrest : blocksShaped rest := fun b hb => hshape b (by simp [hb])
      cases i with
      | zero =>
          cases rest with
          | nil =>
              intro b hb
              simp only [markFreeAt, List.mem_singleton] at hb
              subst b
              exact ⟨hhead.1, freedBlock_aligned hhead.2⟩
          | cons next tail =>
              intro b hb
              simp only [markFreeAt, List.mem_cons] at hb
              rcases hb with hb | hb
              · subst b
                exact ⟨hhead.1, freedBlock_aligned hhead.2⟩
              · rcases hb with hb | hb
                · subst b
                  exact hshape next (by simp)
                · exact hshape b (by simp [hb])
      | succ j =>
          intro b hb
          simp only [markFreeAt, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hhead
          · exact ih hrest b hb

theorem markFreeAt_preserves_other {blocks : List Block} {i : Nat}
    {selected other : Block} (hget : blocks[i]? = some selected)
    (hmem : other ∈ blocks) (hne : ¬ SamePhysical selected other) :
    ∃ updated ∈ markFreeAt blocks i, SamePhysical updated other := by
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · exact (hne (samePhysical_refl other)).elim
          · cases rest with
            | nil => simp at htail
            | cons next tail =>
                simp only [List.mem_cons] at htail
                rcases htail with rfl | htail
                · exact ⟨{ other with prevFree := true }, by simp [markFreeAt],
                    by simp [SamePhysical]⟩
                · exact ⟨other, by simp [markFreeAt, htail],
                    samePhysical_refl other⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · exact ⟨other, by simp [markFreeAt], samePhysical_refl other⟩
          · obtain ⟨updated, hupdated, hsame⟩ := ih hget htail hne
            exact ⟨updated, by simp [markFreeAt, hupdated], hsame⟩

theorem markFreeAt_free_origin {blocks : List Block} {i : Nat}
    {selected current : Block} (hget : blocks[i]? = some selected)
    (hmem : current ∈ markFreeAt blocks i) (hfree : current.free = true) :
    SamePhysical current (freedBlock selected) ∨
      ∃ old ∈ blocks, old.free = true ∧ SamePhysical current old := by
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          cases rest with
          | nil =>
              simp only [markFreeAt, List.mem_singleton] at hmem
              subst current
              exact Or.inl (by simp [freedBlock, SamePhysical])
          | cons next tail =>
              simp only [markFreeAt, List.mem_cons] at hmem
              rcases hmem with hnew | htail
              · subst current
                exact Or.inl (by simp [freedBlock, SamePhysical])
              · rcases htail with hnext | htail
                · subst current
                  exact Or.inr ⟨next, by simp, by simpa using hfree,
                    by simp [SamePhysical]⟩
                · exact Or.inr ⟨current, by simp [htail], hfree,
                    samePhysical_refl current⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [markFreeAt, List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · exact Or.inr ⟨current, by simp, hfree, samePhysical_refl current⟩
          · rcases ih hget htail with hnew | ⟨old, hold, holdFree, hsame⟩
            · exact Or.inl hnew
            · exact Or.inr ⟨old, by simp [hold], holdFree, hsame⟩

/-- First executable deallocation stage. It validates the exact returned
region, marks the physical header free, and inserts that header into its size
class. Neighbor coalescing is a following transition. -/
def deallocateUncoalesced (pool : Region) (state : Alloc.State) (i : Nat)
    (returned : Region) : Option Alloc.State :=
  match state.physical[i]? with
  | none => none
  | some selected =>
      match deallocateAt pool state.physical i returned with
      | none => none
      | some physical =>
          match classifyBlock? (freedBlock selected) with
          | none => none
          | some cls => some ⟨physical, state.bins.insert cls (freedBlock selected)⟩

theorem deallocateUncoalesced_result {pool : Region} {state : Alloc.State}
    {i : Nat} {returned : Region} {next : Alloc.State}
    (hsuccess : deallocateUncoalesced pool state i returned = some next) :
    ∃ selected cls,
      state.physical[i]? = some selected ∧
      deallocateAt pool state.physical i returned =
        some (markFreeAt state.physical i) ∧
      classifyBlock? (freedBlock selected) = some cls ∧
      next.physical = markFreeAt state.physical i ∧
      next.bins = state.bins.insert cls (freedBlock selected) := by
  unfold deallocateUncoalesced at hsuccess
  cases hget : state.physical[i]? with
  | none => simp [hget] at hsuccess
  | some selected =>
      cases hfree : deallocateAt pool state.physical i returned with
      | none => simp [hget, hfree] at hsuccess
      | some physical =>
          have hphysical : physical = markFreeAt state.physical i := by
            simp only [deallocateAt, hget] at hfree
            split at hfree <;> simp_all
          cases hclass : classifyBlock? (freedBlock selected) with
          | none => simp [hget, hfree, hclass] at hsuccess
          | some cls =>
              simp [hget, hfree, hclass] at hsuccess
              subst next
              exact ⟨selected, cls, rfl, by simp [hphysical] at hfree ⊢,
                hclass, hphysical, rfl⟩

/-- The public uncoalesced free stage consumes exactly the returned client
capability. Bin insertion changes only the pure projection, not byte ownership. -/
theorem deallocateUncoalesced_ownsFree
    {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    {pool : Region} {state next : Alloc.State} {i : Nat} {returned : Region}
    (hsuccess : deallocateUncoalesced pool state i returned = some next) :
    OwnsBytes (PROP := PROP) returned ∗
        Ownership.OwnsFree pool state.physical ⊣⊢
      Ownership.OwnsFree pool next.physical := by
  obtain ⟨selected, _, hget, hfree, _, hphysical, _⟩ :=
    deallocateUncoalesced_result hsuccess
  rw [hphysical]
  exact Ownership.deallocateAt_ownsFree pool hget hfree

theorem deallocateUncoalesced_wellFormed {pool : Region}
    {state next : Alloc.State} (hvalid : Alloc.Valid pool state)
    {i : Nat} {returned : Region}
    (hsuccess : deallocateUncoalesced pool state i returned = some next) :
    wellFormed pool next.physical := by
  obtain ⟨selected, _, hget, hfree, _, hphysical, _⟩ :=
    deallocateUncoalesced_result hsuccess
  rw [hphysical]
  exact wellFormed_of_partitions_boundary
    (deallocateAt_preserves_partitions hget hvalid.1.2.1 hfree)
    (deallocateAt_preserves_boundaryTags hget hvalid.1.2.2.1 hfree)
    (blocksShaped_markFreeAt (wellFormed_blocksShaped hvalid.1))

theorem deallocateUncoalesced_preserves_valid {pool : Region}
    {state next : Alloc.State} (hvalid : Alloc.Valid pool state)
    {i : Nat} {returned : Region}
    (hsuccess : deallocateUncoalesced pool state i returned = some next) :
    Alloc.Valid pool next := by
  obtain ⟨selected, cls, hget, hfreeResult, hclass, hphysical, hbins⟩ :=
    deallocateUncoalesced_result hsuccess
  have hpre := (deallocateAt_success_iff hget).1 hfreeResult
  have hselectedMem : selected ∈ state.physical :=
    List.mem_iff_getElem?.2 ⟨i, hget⟩
  have hfreedMem : freedBlock selected ∈ next.physical := by
    rw [hphysical]
    exact markFreeAt_contains hget
  have hbelongs : Belongs cls (freedBlock selected) :=
    classifyBlock?_result hclass
  have hfresh : (freedBlock selected).offset ∉
      (state.bins.chains cls).map Block.offset := by
    intro hoffset
    obtain ⟨cached, hcached, hcachedOffset⟩ := List.mem_map.mp hoffset
    obtain ⟨actual, hactual, hsame⟩ := hvalid.2.2.1 cls cached hcached
    have hoffset : actual.offset = selected.offset := by
      rw [hsame.1, hcachedOffset]
      rfl
    have heq : actual = selected :=
      wellFormed_same_offset hvalid.1 hactual hselectedMem hoffset
    have hcachedFree := member_free hvalid.2.1 hcached
    have hactualFree := samePhysical_free hsame |>.trans hcachedFree
    rw [heq, hpre.1] at hactualFree
    contradiction
  have hbinsValid : Bins.Valid next.bins := by
    rw [hbins]
    exact insert_valid hvalid.2.1 cls (freedBlock selected) hbelongs hfresh
  have hforwardBeforeInsert :
      ∀ query cached, cached ∈ state.bins.chains query →
        ∃ actual ∈ next.physical, SamePhysical actual cached := by
    intro query cached hcached
    obtain ⟨old, hold, holdCached⟩ := hvalid.2.2.1 query cached hcached
    have hnotSelected : ¬ SamePhysical selected old := by
      intro hsameSelected
      have hcachedFree := member_free hvalid.2.1 hcached
      have holdFree := samePhysical_free holdCached |>.trans hcachedFree
      have hselectedFree := samePhysical_free hsameSelected |>.trans holdFree
      rw [hpre.1] at hselectedFree
      contradiction
    obtain ⟨updated, hupdated, hsameUpdated⟩ :=
      markFreeAt_preserves_other hget hold hnotSelected
    exact ⟨updated, by simpa [hphysical] using hupdated,
      samePhysical_trans hsameUpdated holdCached⟩
  have hforward :
      ∀ query cached, cached ∈ next.bins.chains query →
        ∃ actual ∈ next.physical, SamePhysical actual cached := by
    rw [hbins]
    exact insert_preserves_forward_agreement hvalid.2.1 hforwardBeforeInsert
      rfl hfreedMem (samePhysical_refl _)
  have hbackward :
      ∀ actual, actual ∈ next.physical → actual.free = true →
        ∃ query cached, cached ∈ next.bins.chains query ∧
          SamePhysical actual cached := by
    intro actual hactual hactualFree
    have hactualMarked : actual ∈ markFreeAt state.physical i := by
      simpa [hphysical] using hactual
    rcases markFreeAt_free_origin hget hactualMarked hactualFree with
        hnew | ⟨old, hold, holdFree, hactualOld⟩
    · obtain ⟨cached, hcached, hfreedCached⟩ :=
        inserted_has_representation (state := state.bins) (cls := cls)
          (inserted := freedBlock selected) rfl
      exact ⟨cls, cached, by simpa [hbins] using hcached,
        samePhysical_trans hnew hfreedCached⟩
    · obtain ⟨query, cached, hcached, holdCached⟩ :=
        hvalid.2.2.2 old hold holdFree
      obtain ⟨nextQuery, nextCached, hnextCached, holdNext⟩ :=
        insert_preserves_representation hvalid.2.1
          (cls := cls) (inserted := freedBlock selected)
          ⟨query, cached, hcached, holdCached⟩
      exact ⟨nextQuery, nextCached, by simpa [hbins] using hnextCached,
        samePhysical_trans hactualOld holdNext⟩
  exact ⟨deallocateUncoalesced_wellFormed hvalid hsuccess,
    hbinsValid, hforward, hbackward⟩

end Luffs.Allocator.TLSF.Dealloc
