import Luffs.Allocator.TLSF.Bitmap
import Luffs.Allocator.TLSF.FreeList

set_option autoImplicit false

namespace Luffs.Allocator.TLSF.Bins

open Luffs.Allocator.TLSF

abbrev Chains := SizeClass -> List Block

/-- Cached two-level bitmap state together with its intrusive chains. -/
structure State where
  chains : Chains
  slSet : Fin firstLevelCount -> Fin secondLevelCount -> Bool
  flSet : Fin firstLevelCount -> Bool

/-- A block belongs to a class exactly when the verified classifier maps its
positive, addressable size to that class. -/
def Belongs (cls : SizeClass) (b : Block) : Prop :=
  ∃ (hsize : 0 < b.bytes) (hmax : b.bytes < 2 ^ firstLevelCount),
    sizeClass b.bytes hsize hmax = cls

def Valid (state : State) : Prop :=
  (∀ cls, FreeList.Valid (state.chains cls)) ∧
  (∀ cls b, b ∈ state.chains cls → Belongs cls b) ∧
  (∀ fl sl, state.slSet fl sl = true ↔ state.chains { fl, sl } ≠ []) ∧
  (∀ fl, state.flSet fl = true ↔ ∃ sl, state.chains { fl, sl } ≠ [])

private theorem linkedFrom_member_free {previous : Option Nat} {blocks : List Block}
    {b : Block} (hlinks : FreeList.linkedFrom previous blocks)
    (hmem : b ∈ blocks) : b.free = true := by
  induction blocks generalizing previous with
  | nil => simp at hmem
  | cons head rest ih =>
      change head.free = true ∧ head.prevFreeLink = previous ∧
        head.nextFreeLink = rest.head?.map Block.offset ∧
        FreeList.linkedFrom (some head.offset) rest at hlinks
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hlinks.1
      · exact ih hlinks.2.2.2 hmem

theorem member_free {state : State} (hvalid : Valid state) {cls : SizeClass}
    {b : Block} (hmem : b ∈ state.chains cls) : b.free = true :=
  linkedFrom_member_free (hvalid.1 cls).1 hmem

theorem member_belongs {state : State} (hvalid : Valid state)
    {cls : SizeClass} {b : Block} (hmem : b ∈ state.chains cls) :
    Belongs cls b := hvalid.2.1 cls b hmem

theorem sl_bit_iff_nonempty {state : State} (hvalid : Valid state)
    (fl : Fin firstLevelCount) (sl : Fin secondLevelCount) :
    state.slSet fl sl = true ↔ state.chains { fl, sl } ≠ [] :=
  hvalid.2.2.1 fl sl

theorem fl_bit_iff_nonempty {state : State} (hvalid : Valid state)
    (fl : Fin firstLevelCount) :
    state.flSet fl = true ↔ ∃ sl, state.chains { fl, sl } ≠ [] :=
  hvalid.2.2.2 fl

def slBitmap (state : State) (fl : Fin firstLevelCount) : List Bool :=
  List.ofFn (state.slSet fl)

def flBitmap (state : State) : List Bool := List.ofFn state.flSet

theorem slBitmap_length (state : State) (fl : Fin firstLevelCount) :
    (slBitmap state fl).length = secondLevelCount := by
  simp [slBitmap]

theorem flBitmap_length (state : State) :
    (flBitmap state).length = firstLevelCount := by
  simp [flBitmap]

/-- A successful second-level bitmap search selects a real nonempty intrusive
chain, not merely a set bit disconnected from allocator state. -/
theorem secondLevel_search_nonempty {state : State} (hvalid : Valid state)
    (fl : Fin firstLevelCount) (start found : Nat)
    (hsearch : firstSetFrom (slBitmap state fl) start = some found) :
    ∃ (hfound : found < secondLevelCount),
      state.chains { fl := fl, sl := ⟨found, hfound⟩ } ≠ [] := by
  have hsound := firstSetFrom_sound hsearch
  have hbound : found < secondLevelCount := by
    rw [slBitmap_length] at hsound
    exact hsound.2.1
  refine ⟨hbound, ?_⟩
  apply (sl_bit_iff_nonempty hvalid fl ⟨found, hbound⟩).1
  have hget := hsound.2.2
  have hvalue : (slBitmap state fl)[found]'hsound.2.1 = true :=
    (List.getElem?_eq_some_iff.mp hget).2
  simpa [slBitmap] using hvalue

theorem secondLevel_search_head {state : State} (hvalid : Valid state)
    (fl : Fin firstLevelCount) (start found : Nat)
    (hsearch : firstSetFrom (slBitmap state fl) start = some found) :
    ∃ (hfound : found < secondLevelCount) (head : Block) (rest : List Block),
      state.chains { fl := fl, sl := ⟨found, hfound⟩ } = head :: rest ∧
      head.free = true ∧ Belongs { fl := fl, sl := ⟨found, hfound⟩ } head := by
  obtain ⟨hfound, hnonempty⟩ := secondLevel_search_nonempty hvalid fl start found hsearch
  let cls : SizeClass := { fl := fl, sl := ⟨found, hfound⟩ }
  cases hchain : state.chains cls with
  | nil => exact (hnonempty hchain).elim
  | cons head rest =>
      have hmem : head ∈ state.chains cls := by simp [hchain]
      exact ⟨hfound, head, rest, hchain,
        member_free hvalid hmem, member_belongs hvalid hmem⟩

/-- Likewise, a successful first-level search identifies a first level with at
least one nonempty second-level chain. -/
theorem firstLevel_search_nonempty {state : State} (hvalid : Valid state)
    (start found : Nat)
    (hsearch : firstSetFrom (flBitmap state) start = some found) :
    ∃ (hfound : found < firstLevelCount) (sl : Fin secondLevelCount),
      state.chains { fl := ⟨found, hfound⟩, sl } ≠ [] := by
  have hsound := firstSetFrom_sound hsearch
  have hbound : found < firstLevelCount := by
    rw [flBitmap_length] at hsound
    exact hsound.2.1
  have hbit : state.flSet ⟨found, hbound⟩ = true := by
    have hvalue : (flBitmap state)[found]'hsound.2.1 = true :=
      (List.getElem?_eq_some_iff.mp hsound.2.2).2
    simpa [flBitmap] using hvalue
  obtain ⟨sl, hchain⟩ := (fl_bit_iff_nonempty hvalid ⟨found, hbound⟩).1 hbit
  exact ⟨hbound, sl, hchain⟩

end Luffs.Allocator.TLSF.Bins
