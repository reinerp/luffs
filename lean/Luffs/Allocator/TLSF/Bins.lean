import Luffs.Allocator.TLSF.Bitmap
import Luffs.Allocator.TLSF.FreeList

set_option autoImplicit false

namespace Luffs.Allocator.TLSF.Bins

open Luffs.Allocator.TLSF
open Luffs.Memory

abbrev Chains := SizeClass -> List Block

/-- Cached two-level bitmap state together with its intrusive chains. -/
structure State where
  chains : Chains
  slSet : Fin firstLevelCount -> Fin secondLevelCount -> Bool
  flSet : Fin firstLevelCount -> Bool

/-- Recompute both bitmap levels from the chains. Mutating operations use this
constructor after changing a chain, so stale cached bits are unrepresentable
at their proof boundary. -/
def State.fromChains (chains : Chains) : State :=
  { chains := chains
    slSet := fun fl sl => decide (chains { fl, sl } ≠ [])
    flSet := fun fl => decide (∃ sl, chains { fl, sl } ≠ []) }

def Chains.replace (chains : Chains) (target : SizeClass)
    (blocks : List Block) : Chains :=
  fun cls => if cls = target then blocks else chains cls

def State.replaceChain (state : State) (target : SizeClass)
    (blocks : List Block) : State :=
  State.fromChains (state.chains.replace target blocks)

@[simp] theorem replaceChain_target (state : State) (target : SizeClass)
    (blocks : List Block) :
    (state.replaceChain target blocks).chains target = blocks := by
  simp [State.replaceChain, State.fromChains, Chains.replace]

theorem replaceChain_other (state : State) {target cls : SizeClass}
    (blocks : List Block) (hne : cls ≠ target) :
    (state.replaceChain target blocks).chains cls = state.chains cls := by
  simp [State.replaceChain, State.fromChains, Chains.replace, hne]

/-- A block belongs to a class exactly when the verified classifier maps its
positive, addressable size to that class. -/
def Belongs (cls : SizeClass) (b : Block) : Prop :=
  ∃ (hsize : 0 < b.bytes) (hmax : b.bytes < 2 ^ firstLevelCount),
    sizeClass b.bytes hsize hmax = cls

/-- The non-cached obligations on a family of intrusive chains. -/
def ChainsValid (chains : Chains) : Prop :=
  (∀ cls, FreeList.Valid (chains cls)) ∧
  (∀ cls b, b ∈ chains cls → Belongs cls b)

def Valid (state : State) : Prop :=
  (∀ cls, FreeList.Valid (state.chains cls)) ∧
  (∀ cls b, b ∈ state.chains cls → Belongs cls b) ∧
  (∀ fl sl, state.slSet fl sl = true ↔ state.chains { fl, sl } ≠ []) ∧
  (∀ fl, state.flSet fl = true ↔ ∃ sl, state.chains { fl, sl } ≠ [])

theorem fromChains_valid {chains : Chains} (hchains : ChainsValid chains) :
    Valid (State.fromChains chains) := by
  refine ⟨hchains.1, hchains.2, ?_, ?_⟩
  · intro fl sl
    simp [State.fromChains]
  · intro fl
    simp [State.fromChains]

theorem belongs_withLinks (cls : SizeClass) (b : Block)
    (previous next : Option Nat) :
    Belongs cls (FreeList.withLinks b previous next) ↔ Belongs cls b := by
  simp [Belongs, FreeList.withLinks]

private theorem insertFront_belongs {cls : SizeClass} {b : Block}
    {blocks : List Block} (hb : Belongs cls b)
    (hblocks : ∀ old ∈ blocks, Belongs cls old) :
    ∀ inserted ∈ FreeList.insertFront b blocks, Belongs cls inserted := by
  cases blocks with
  | nil =>
      intro inserted hmem
      simp [FreeList.insertFront] at hmem
      subst inserted
      exact (belongs_withLinks cls b none none).2 hb
  | cons head rest =>
      intro inserted hmem
      simp only [FreeList.insertFront, List.mem_cons] at hmem
      rcases hmem with hnew | htail
      · subst inserted
        exact (belongs_withLinks cls b none (some head.offset)).2 hb
      · rcases htail with hnewHead | hrest
        · subst inserted
          exact (belongs_withLinks cls head (some b.offset) head.nextFreeLink).2
            (hblocks head (by simp))
        · exact hblocks inserted (by simp [hrest])

def State.insert (state : State) (cls : SizeClass) (b : Block) : State :=
  state.replaceChain cls (FreeList.insertFront b (state.chains cls))

/-- Inserting a freshly-offset block of the advertised class and rebuilding
the derived bitmaps preserves all structural and classification invariants. -/
theorem insert_valid {state : State} (hvalid : Valid state) (cls : SizeClass)
    (b : Block) (hbelongs : Belongs cls b)
    (hfresh : b.offset ∉ (state.chains cls).map Block.offset) :
    Valid (state.insert cls b) := by
  apply fromChains_valid
  constructor
  · intro query
    by_cases hquery : query = cls
    · subst query
      simpa [State.insert, Chains.replace] using
        FreeList.insertFront_valid b (state.chains cls) (hvalid.1 cls) hfresh
    · simp only [Chains.replace, hquery, ↓reduceIte]
      exact hvalid.1 query
  · intro query inserted hmem
    by_cases hquery : query = cls
    · subst query
      simp only [Chains.replace, ↓reduceIte] at hmem
      exact insertFront_belongs hbelongs (hvalid.2.1 cls) inserted hmem
    · simp only [Chains.replace, hquery, ↓reduceIte] at hmem
      exact hvalid.2.1 query inserted hmem

private theorem removeFront_belongs {cls : SizeClass} {blocks rest : List Block}
    {removed : Block} (hremove : FreeList.removeFront blocks = some (removed, rest))
    (hblocks : ∀ old ∈ blocks, Belongs cls old) :
    ∀ kept ∈ rest, Belongs cls kept := by
  cases blocks with
  | nil => simp [FreeList.removeFront] at hremove
  | cons head tail =>
      cases tail with
      | nil => simp [FreeList.removeFront] at hremove; simp_all
      | cons next more =>
          simp [FreeList.removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          intro kept hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with hnext | hmore
          · subst kept
            exact (belongs_withLinks cls next none next.nextFreeLink).2
              (hblocks next (by simp))
          · exact hblocks kept (by simp [hmore])

def State.removeFront (state : State) (cls : SizeClass) : Option (Block × State) :=
  match FreeList.removeFront (state.chains cls) with
  | none => none
  | some (removed, rest) => some (removed, state.replaceChain cls rest)

theorem removeFront_result {state : State} {cls : SizeClass}
    {removed : Block} {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest)) :
    state.removeFront cls = some (removed, state.replaceChain cls rest) := by
  simp [State.removeFront, hremove]

/-- Removing a nonempty bin head and rebuilding caches preserves validity. In
particular the relevant bitmap bits are cleared exactly when `rest` is empty. -/
theorem removeFront_valid {state : State} (hvalid : Valid state)
    {cls : SizeClass} {removed : Block} {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest)) :
    Valid (state.replaceChain cls rest) := by
  apply fromChains_valid
  constructor
  · intro query
    by_cases hquery : query = cls
    · subst query
      simpa [Chains.replace] using
        FreeList.removeFront_valid (hvalid.1 cls) hremove
    · simp only [Chains.replace, hquery, ↓reduceIte]
      exact hvalid.1 query
  · intro query kept hmem
    by_cases hquery : query = cls
    · subst query
      simp only [Chains.replace, ↓reduceIte] at hmem
      exact removeFront_belongs hremove (hvalid.2.1 cls) kept hmem
    · simp only [Chains.replace, hquery, ↓reduceIte] at hmem
      exact hvalid.2.1 query kept hmem

theorem removeFront_detached {state : State} {cls : SizeClass}
    {removed : Block} {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest)) :
    removed.free = true ∧ removed.prevFreeLink = none ∧
      removed.nextFreeLink = none :=
  FreeList.removeFront_detaches hremove

/-- Equality of the fields shared by the physical-layout and intrusive-chain
views of a header. Links live in the chain projection; offset, size, allocation
state, and the boundary tag live in both. -/
def SamePhysical (left right : Block) : Prop :=
  left.offset = right.offset ∧ left.bytes = right.bytes ∧
    left.free = right.free ∧ left.prevFree = right.prevFree

theorem samePhysical_refl (b : Block) : SamePhysical b b :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem samePhysical_symm {left right : Block}
    (h : SamePhysical left right) : SamePhysical right left := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm⟩

theorem samePhysical_trans {left middle right : Block}
    (hleft : SamePhysical left middle) (hright : SamePhysical middle right) :
    SamePhysical left right := by
  rcases hleft with ⟨h₁, h₂, h₃, h₄⟩
  rcases hright with ⟨h₁', h₂', h₃', h₄'⟩
  exact ⟨h₁.trans h₁', h₂.trans h₂', h₃.trans h₃', h₄.trans h₄'⟩

theorem samePhysical_withLinks (b : Block) (previous next : Option Nat)
    (hfree : b.free = true) :
    SamePhysical b (FreeList.withLinks b previous next) := by
  simp [SamePhysical, FreeList.withLinks, hfree]

theorem samePhysical_belongs_iff {left right : Block}
    (hsame : SamePhysical left right) (cls : SizeClass) :
    Belongs cls left ↔ Belongs cls right := by
  rcases hsame with ⟨_, hbytes, _, _⟩
  simp [Belongs, hbytes]

theorem samePhysical_aligned_iff {left right : Block}
    (hsame : SamePhysical left right) : left.aligned ↔ right.aligned := by
  rcases hsame with ⟨hoffset, hbytes, _, _⟩
  simp [Block.aligned, hoffset, hbytes]

theorem samePhysical_region {left right : Block}
    (hsame : SamePhysical left right) (pool : Region) :
    left.region pool = right.region pool := by
  rcases hsame with ⟨hoffset, hbytes, _, _⟩
  simp [Block.region, hoffset, hbytes]

theorem samePhysical_free {left right : Block}
    (hsame : SamePhysical left right) : left.free = right.free :=
  hsame.2.2.1

/-- Relates the cached bin projection to the authoritative physical block
sequence. Every cached header represents a physical header, and every free
physical header has a cached representative. -/
def PhysicalAgreement (physical : List Block) (state : State) : Prop :=
  (∀ cls cached, cached ∈ state.chains cls →
    ∃ actual ∈ physical, SamePhysical actual cached) ∧
  (∀ actual, actual ∈ physical → actual.free = true →
    ∃ cls cached, cached ∈ state.chains cls ∧ SamePhysical actual cached)

/-- Whole-pool pure invariant. Iris ownership is layered over this predicate
in the allocator proof; this component establishes that the physical layout
and the executable TLSF indices describe the same free blocks. -/
def PoolValid (pool : Region) (physical : List Block) (state : State) : Prop :=
  wellFormed pool physical ∧ Valid state ∧ PhysicalAgreement physical state

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

theorem member_physical {physical : List Block} {state : State}
    (hagrees : PhysicalAgreement physical state) {cls : SizeClass} {b : Block}
    (hmem : b ∈ state.chains cls) :
    ∃ actual ∈ physical, SamePhysical actual b :=
  hagrees.1 cls b hmem

theorem physical_free_member {physical : List Block} {state : State}
    (hagrees : PhysicalAgreement physical state) {b : Block}
    (hphysical : b ∈ physical) (hfree : b.free = true) :
    ∃ cls cached, cached ∈ state.chains cls ∧ SamePhysical b cached :=
  hagrees.2 b hphysical hfree

theorem physical_free_iff_member {physical : List Block} {state : State}
    (hvalid : Valid state) (hagrees : PhysicalAgreement physical state)
    {b : Block} (hphysical : b ∈ physical) :
    b.free = true ↔ ∃ cls cached,
      cached ∈ state.chains cls ∧ SamePhysical b cached := by
  constructor
  · exact physical_free_member hagrees hphysical
  · rintro ⟨cls, cached, hmem, hsame⟩
    have hcached := member_free hvalid hmem
    exact hsame.2.2.1.trans hcached

theorem allocated_not_member {state : State}
    (hvalid : Valid state) {b : Block} (hallocated : b.free = false) :
    ¬ ∃ cls, b ∈ state.chains cls := by
  rintro ⟨cls, hmem⟩
  have := member_free hvalid hmem
  simp_all

/-- Classification is functional, so the same physical block cannot be
represented in two different size classes. -/
theorem member_class_unique {state : State} (hvalid : Valid state)
    {left right : SizeClass} {b : Block}
    (hleft : b ∈ state.chains left) (hright : b ∈ state.chains right) :
    left = right := by
  obtain ⟨hsize, hmax, hclass⟩ := member_belongs hvalid hleft
  obtain ⟨_, _, hclass'⟩ := member_belongs hvalid hright
  rw [← hclass, ← hclass']

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

/-- Bitmap search is connected all the way back to the authoritative physical
layout: its returned free-list head represents an actual block in that layout. -/
theorem secondLevel_search_physical_head {pool : Region} {physical : List Block}
    {state : State} (hpool : PoolValid pool physical state)
    (fl : Fin firstLevelCount) (start found : Nat)
    (hsearch : firstSetFrom (slBitmap state fl) start = some found) :
    ∃ (hfound : found < secondLevelCount) (head actual : Block)
        (rest : List Block),
      state.chains { fl := fl, sl := ⟨found, hfound⟩ } = head :: rest ∧
      actual ∈ physical ∧ SamePhysical actual head ∧ actual.free = true ∧
      Belongs { fl := fl, sl := ⟨found, hfound⟩ } actual ∧
      head.free = true := by
  obtain ⟨hfound, head, rest, hchain, hfree, hbelongs⟩ :=
    secondLevel_search_head hpool.2.1 fl start found hsearch
  have hmem : head ∈ state.chains { fl := fl, sl := ⟨found, hfound⟩ } := by
    simp [hchain]
  obtain ⟨actual, hactual, hsame⟩ := member_physical hpool.2.2 hmem
  have hactualFree : actual.free = true := (samePhysical_free hsame).trans hfree
  have hactualBelongs := (samePhysical_belongs_iff hsame _).2 hbelongs
  exact ⟨hfound, head, actual, rest, hchain, hactual, hsame,
    hactualFree, hactualBelongs, hfree⟩

/-- End-to-end suitability for the linear TLSF range: beginning bitmap search
at the request's class returns a physical, aligned free block large enough for
the request. -/
theorem secondLevel_search_linear_suitable {pool : Region} {physical : List Block}
    {state : State} (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hrequestMax : request < 2 ^ firstLevelCount)
    (hlinear : request ≤ linearCutoff) (found : Nat)
    (hsearch : firstSetFrom
      (slBitmap state (sizeClass request hrequest hrequestMax).fl)
      (sizeClass request hrequest hrequestMax).sl.val = some found) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  let requestClass := sizeClass request hrequest hrequestMax
  obtain ⟨hfound, head, actual, rest, hchain, hactual, hsame,
      hactualFree, hbelongs, _⟩ :=
    secondLevel_search_physical_head hpool requestClass.fl
      requestClass.sl.val found hsearch
  obtain ⟨hblock, hblockMax, hblockClass⟩ := hbelongs
  have hrequestValues := linear_sizeClass_values request hrequest
    hrequestMax hlinear
  have hactualFl :
      (sizeClass actual.bytes hblock hblockMax).fl.val = 0 := by
    rw [hblockClass]
    exact hrequestValues.1
  have hblockLinear := sizeClass_fl_zero_linear actual.bytes hblock
    hblockMax hactualFl
  have hsearchSound := firstSetFrom_sound hsearch
  have hsl : (sizeClass request hrequest hrequestMax).sl.val ≤
      (sizeClass actual.bytes hblock hblockMax).sl.val := by
    rw [hblockClass]
    exact hsearchSound.1
  have haligned := (hpool.1.2.2.2 actual hactual).2.2
  have hsuitable := linear_later_class_suitable request actual.bytes
    hrequest hblock hrequestMax hblockMax hlinear hblockLinear
    haligned.2 hsl
  exact ⟨actual, hactual, hactualFree, haligned, hsuitable⟩

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
