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

def classifyBlock? (b : Block) : Option SizeClass :=
  if hsize : 0 < b.bytes then
    if hmax : b.bytes < 2 ^ firstLevelCount then
      some (sizeClass b.bytes hsize hmax)
    else none
  else none

theorem classifyBlock?_result {b : Block} {cls : SizeClass}
    (hclass : classifyBlock? b = some cls) : Belongs cls b := by
  unfold classifyBlock? at hclass
  split at hclass
  next hsize =>
    split at hclass
    next hmax =>
      simp only [Option.some.injEq] at hclass
      exact ⟨hsize, hmax, hclass⟩
    next => contradiction
  next => contradiction

theorem classifyBlock?_complete {b : Block} (hsize : 0 < b.bytes)
    (hmax : b.bytes < 2 ^ firstLevelCount) :
    ∃ cls, classifyBlock? b = some cls := by
  exact ⟨sizeClass b.bytes hsize hmax, by
    simp [classifyBlock?, hsize, hmax]⟩

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

def State.removeOffset (state : State) (cls : SizeClass) (offset : Nat) :
    Option (Block × State) :=
  match FreeList.removeOffset (state.chains cls) offset with
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
views of a header. Links live in the chain projection; boundary tags live in
the physical projection; offset, size, and allocation state live in both. -/
def SamePhysical (left right : Block) : Prop :=
  left.offset = right.offset ∧ left.bytes = right.bytes ∧
    left.free = right.free

instance (left right : Block) : Decidable (SamePhysical left right) := by
  unfold SamePhysical
  infer_instance

/-- Locate the physical header represented by a detached or linked chain
projection. The comparison intentionally ignores intrusive links. -/
def findPhysicalIndex : List Block -> Block -> Option Nat
  | [], _ => none
  | head :: rest, target =>
      if SamePhysical head target then some 0
      else (findPhysicalIndex rest target).map Nat.succ

theorem findPhysicalIndex_sound {physical : List Block} {target : Block}
    {i : Nat} (hfind : findPhysicalIndex physical target = some i) :
    ∃ actual, physical[i]? = some actual ∧ SamePhysical actual target := by
  induction physical generalizing i with
  | nil => simp [findPhysicalIndex] at hfind
  | cons head rest ih =>
      by_cases hsame : SamePhysical head target
      · simp [findPhysicalIndex, hsame] at hfind
        subst i
        exact ⟨head, rfl, hsame⟩
      · simp [findPhysicalIndex, hsame] at hfind
        obtain ⟨j, hj, rfl⟩ := hfind
        obtain ⟨actual, hget, hactual⟩ := ih hj
        exact ⟨actual, by simpa using hget, hactual⟩

theorem findPhysicalIndex_complete {physical : List Block} {target actual : Block}
    (hmem : actual ∈ physical) (hsame : SamePhysical actual target) :
    ∃ i, findPhysicalIndex physical target = some i := by
  induction physical with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      by_cases hhead : SamePhysical head target
      · exact ⟨0, by simp [findPhysicalIndex, hhead]⟩
      · rcases hmem with rfl | htail
        · exact (hhead hsame).elim
        · obtain ⟨i, hfind⟩ := ih htail
          exact ⟨i + 1, by simp [findPhysicalIndex, hhead, hfind]⟩

theorem samePhysical_refl (b : Block) : SamePhysical b b :=
  ⟨rfl, rfl, rfl⟩

theorem samePhysical_symm {left right : Block}
    (h : SamePhysical left right) : SamePhysical right left := by
  rcases h with ⟨h₁, h₂, h₃⟩
  exact ⟨h₁.symm, h₂.symm, h₃.symm⟩

theorem samePhysical_trans {left middle right : Block}
    (hleft : SamePhysical left middle) (hright : SamePhysical middle right) :
    SamePhysical left right := by
  rcases hleft with ⟨h₁, h₂, h₃⟩
  rcases hright with ⟨h₁', h₂', h₃'⟩
  exact ⟨h₁.trans h₁', h₂.trans h₂', h₃.trans h₃'⟩

theorem samePhysical_withLinks (b : Block) (previous next : Option Nat)
    (hfree : b.free = true) :
    SamePhysical b (FreeList.withLinks b previous next) := by
  simp [SamePhysical, FreeList.withLinks, hfree]

theorem samePhysical_belongs_iff {left right : Block}
    (hsame : SamePhysical left right) (cls : SizeClass) :
    Belongs cls left ↔ Belongs cls right := by
  rcases hsame with ⟨_, hbytes, _⟩
  simp [Belongs, hbytes]

theorem samePhysical_aligned_iff {left right : Block}
    (hsame : SamePhysical left right) : left.aligned ↔ right.aligned := by
  rcases hsame with ⟨hoffset, hbytes, _⟩
  simp [Block.aligned, hoffset, hbytes]

theorem samePhysical_region {left right : Block}
    (hsame : SamePhysical left right) (pool : Region) :
    left.region pool = right.region pool := by
  rcases hsame with ⟨hoffset, hbytes, _⟩
  simp [Block.region, hoffset, hbytes]

theorem samePhysical_free {left right : Block}
    (hsame : SamePhysical left right) : left.free = right.free :=
  hsame.2.2

theorem removeOffset_result {state : State} {cls : SizeClass} {offset : Nat}
    {removed : Block} {rest : List Block}
    (hremove : FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest)) :
    state.removeOffset cls offset =
      some (removed, state.replaceChain cls rest) := by
  simp [State.removeOffset, hremove]

theorem removeOffset_success {state next : State} {cls : SizeClass}
    {offset : Nat} {removed : Block}
    (hsuccess : state.removeOffset cls offset = some (removed, next)) :
    ∃ rest, FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest) ∧ next = state.replaceChain cls rest := by
  unfold State.removeOffset at hsuccess
  cases hremove : FreeList.removeOffset (state.chains cls) offset with
  | none => simp [hremove] at hsuccess
  | some result =>
      obtain ⟨found, rest⟩ := result
      simp [hremove] at hsuccess
      rcases hsuccess with ⟨rfl, rfl⟩
      exact ⟨rest, rfl, rfl⟩

theorem removeOffset_detached {state : State} {cls : SizeClass} {offset : Nat}
    {removed : Block} {rest : List Block}
    (hremove : FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest)) :
    removed.free = true ∧ removed.prevFreeLink = none ∧
      removed.nextFreeLink = none :=
  FreeList.removeOffset_detaches hremove

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

theorem removeOffset_valid {state : State} (hvalid : Valid state)
    {cls : SizeClass} {offset : Nat} {removed : Block} {rest : List Block}
    (hremove : FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest)) :
    Valid (state.replaceChain cls rest) := by
  have hrestValid := FreeList.removeOffset_valid (hvalid.1 cls) hremove
  unfold FreeList.removeOffset at hremove
  cases hfind : FreeList.findOffset? (state.chains cls) offset with
  | none => simp [hfind] at hremove
  | some found =>
      simp [hfind] at hremove
      rcases hremove with ⟨rfl, rfl⟩
      apply fromChains_valid
      constructor
      · intro query
        by_cases hquery : query = cls
        · subst query
          simpa [Chains.replace] using hrestValid
        · simp only [Chains.replace, hquery, ↓reduceIte]
          exact hvalid.1 query
      · intro query kept hmem
        by_cases hquery : query = cls
        · subst query
          simp only [Chains.replace, ↓reduceIte] at hmem
          have herasedFree :
              ∀ b ∈ FreeList.eraseOffset (state.chains cls) offset,
                b.free = true := by
            intro b hb
            exact member_free hvalid (FreeList.eraseOffset_member hb)
          obtain ⟨old, holdErased, hsame⟩ :=
            FreeList.relink_member_origin herasedFree hmem
          have hold : old ∈ state.chains cls :=
            FreeList.eraseOffset_member holdErased
          exact (samePhysical_belongs_iff hsame cls).2
            (member_belongs hvalid hold)
        · simp only [Chains.replace, hquery, ↓reduceIte] at hmem
          exact member_belongs hvalid hmem

theorem removeOffset_removed_origin {state : State} (hvalid : Valid state)
    {cls : SizeClass} {offset : Nat} {removed : Block} {rest : List Block}
    (hremove : FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest)) :
    ∃ old ∈ state.chains cls, old.offset = offset ∧
      SamePhysical old removed := by
  obtain ⟨old, hold, hoffset, hsame⟩ :=
    FreeList.removeOffset_removed_origin (hvalid.1 cls) hremove
  exact ⟨old, hold, hoffset, hsame⟩

theorem removeOffset_preserves_forward_agreement {physical : List Block}
    {state : State} (hvalid : Valid state)
    (hforward : ∀ query cached, cached ∈ state.chains query →
      ∃ actual ∈ physical, SamePhysical actual cached)
    {cls : SizeClass} {offset : Nat} {removed : Block} {rest : List Block}
    (hremove : FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest)) :
    ∀ query cached, cached ∈ (state.replaceChain cls rest).chains query →
      ∃ actual ∈ physical, SamePhysical actual cached := by
  unfold FreeList.removeOffset at hremove
  cases hfind : FreeList.findOffset? (state.chains cls) offset with
  | none => simp [hfind] at hremove
  | some found =>
      simp [hfind] at hremove
      rcases hremove with ⟨rfl, rfl⟩
      intro query cached hcached
      by_cases hquery : query = cls
      · subst query
        simp only [replaceChain_target] at hcached
        have herasedFree :
            ∀ b ∈ FreeList.eraseOffset (state.chains cls) offset,
              b.free = true := by
          intro b hb
          exact member_free hvalid (FreeList.eraseOffset_member hb)
        obtain ⟨old, holdErased, hcachedOld⟩ :=
          FreeList.relink_member_origin herasedFree hcached
        obtain ⟨actual, hactual, hactualOld⟩ :=
          hforward cls old (FreeList.eraseOffset_member holdErased)
        exact ⟨actual, hactual, samePhysical_trans hactualOld
          (samePhysical_symm hcachedOld)⟩
      · have hold : cached ∈ state.chains query := by
          rw [replaceChain_other state _ hquery] at hcached
          exact hcached
        exact hforward query cached hold

theorem removeOffset_member_origin {state : State} (hvalid : Valid state)
    {cls : SizeClass} {offset : Nat} {removed : Block} {rest : List Block}
    (hremove : FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest)) :
    ∀ query cached, cached ∈ (state.replaceChain cls rest).chains query →
      ∃ old ∈ state.chains query, SamePhysical old cached := by
  unfold FreeList.removeOffset at hremove
  cases hfind : FreeList.findOffset? (state.chains cls) offset with
  | none => simp [hfind] at hremove
  | some found =>
      simp [hfind] at hremove
      rcases hremove with ⟨rfl, rfl⟩
      intro query cached hcached
      by_cases hquery : query = cls
      · subst query
        simp only [replaceChain_target] at hcached
        have herasedFree :
            ∀ b ∈ FreeList.eraseOffset (state.chains cls) offset,
              b.free = true := by
          intro b hb
          exact member_free hvalid (FreeList.eraseOffset_member hb)
        obtain ⟨old, hold, hsame⟩ :=
          FreeList.relink_member_origin herasedFree hcached
        exact ⟨old, FreeList.eraseOffset_member hold,
          samePhysical_symm hsame⟩
      · exact ⟨cached, by
          rw [replaceChain_other state _ hquery] at hcached
          exact hcached, samePhysical_refl cached⟩

theorem removeOffset_preserves_other_representation {state : State}
    (hvalid : Valid state) {cls : SizeClass} {offset : Nat}
    {removed : Block} {rest : List Block}
    (hremove : FreeList.removeOffset (state.chains cls) offset =
      some (removed, rest)) {actual : Block}
    (hrepresented : ∃ query cached, cached ∈ state.chains query ∧
      SamePhysical actual cached) (hne : actual.offset ≠ offset) :
    ∃ query cached, cached ∈ (state.replaceChain cls rest).chains query ∧
      SamePhysical actual cached := by
  obtain ⟨query, cached, hcached, hactualCached⟩ := hrepresented
  by_cases hquery : query = cls
  · subst query
    have hcachedNe : cached.offset ≠ offset := by
      intro heq
      exact hne (hactualCached.1.trans heq)
    have hcachedErased := FreeList.eraseOffset_preserves hcached hcachedNe
    have hcachedFree := member_free hvalid hcached
    unfold FreeList.removeOffset at hremove
    cases hfind : FreeList.findOffset? (state.chains cls) offset with
    | none => simp [hfind] at hremove
    | some found =>
        simp [hfind] at hremove
        rcases hremove with ⟨rfl, rfl⟩
        obtain ⟨updated, hupdated, hcachedUpdated⟩ :=
          FreeList.relink_represents hcachedFree hcachedErased
        exact ⟨cls, updated, by simpa using hupdated,
          samePhysical_trans hactualCached hcachedUpdated⟩
  · exact ⟨query, cached, by
      rw [replaceChain_other state rest hquery]
      exact hcached, hactualCached⟩

theorem member_physical {physical : List Block} {state : State}
    (hagrees : PhysicalAgreement physical state) {cls : SizeClass} {b : Block}
    (hmem : b ∈ state.chains cls) :
    ∃ actual ∈ physical, SamePhysical actual b :=
  hagrees.1 cls b hmem

theorem removeFront_kept_origin {state : State} (hvalid : Valid state)
    {cls : SizeClass} {removed kept : Block} {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest))
    (hkept : kept ∈ rest) :
    ∃ old ∈ state.chains cls, SamePhysical old kept := by
  cases hchain : state.chains cls with
  | nil => simp [hchain, FreeList.removeFront] at hremove
  | cons head tail =>
      cases tail with
      | nil => simp [hchain, FreeList.removeFront] at hremove; simp_all
      | cons next more =>
          have hnextMem : next ∈ state.chains cls := by simp [hchain]
          have hnextFree := member_free hvalid hnextMem
          simp [hchain, FreeList.removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          simp only [List.mem_cons] at hkept
          rcases hkept with hnext | hmore
          · subst kept
            exact ⟨next, by simp,
              samePhysical_withLinks next none next.nextFreeLink hnextFree⟩
          · exact ⟨kept, by simp [hmore], samePhysical_refl kept⟩

theorem removeFront_preserves_forward_agreement {physical : List Block}
    {state : State} (hvalid : Valid state)
    (hagrees : PhysicalAgreement physical state) {cls : SizeClass}
    {removed : Block} {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest)) :
    ∀ query cached, cached ∈ (state.replaceChain cls rest).chains query →
      ∃ actual ∈ physical, SamePhysical actual cached := by
  intro query cached hmem
  by_cases hquery : query = cls
  · subst query
    rw [replaceChain_target] at hmem
    obtain ⟨old, hold, hsame⟩ :=
      removeFront_kept_origin hvalid hremove hmem
    obtain ⟨actual, hactual, hactualOld⟩ := hagrees.1 cls old hold
    exact ⟨actual, hactual, samePhysical_trans hactualOld hsame⟩
  · rw [replaceChain_other state rest hquery] at hmem
    exact hagrees.1 query cached hmem

theorem removeFront_removed_represents_member {state : State}
    (hvalid : Valid state) {cls : SizeClass} {removed : Block}
    {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest)) :
    ∃ head, head ∈ state.chains cls ∧ SamePhysical head removed := by
  cases hchain : state.chains cls with
  | nil => simp [hchain, FreeList.removeFront] at hremove
  | cons head tail =>
      have hmem : head ∈ state.chains cls := by simp [hchain]
      have hfree := member_free hvalid hmem
      cases tail with
      | nil =>
          simp [hchain, FreeList.removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          exact ⟨head, by simp, samePhysical_withLinks head none none hfree⟩
      | cons next more =>
          simp [hchain, FreeList.removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          exact ⟨head, by simp, samePhysical_withLinks head none none hfree⟩

theorem removeFront_removed_not_represented {state : State}
    (hvalid : Valid state) {cls : SizeClass} {removed : Block}
    {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest))
    {query : SizeClass} {cached : Block}
    (hcached : cached ∈ (state.replaceChain cls rest).chains query)
    (hsame : SamePhysical removed cached) : False := by
  obtain ⟨head, hhead, hheadRemoved⟩ :=
    removeFront_removed_represents_member hvalid hremove
  have hremovedBelongs : Belongs cls removed :=
    (samePhysical_belongs_iff hheadRemoved cls).1 (member_belongs hvalid hhead)
  have hcachedBelongs := member_belongs (removeFront_valid hvalid hremove) hcached
  have hremovedQuery : Belongs query removed :=
    (samePhysical_belongs_iff hsame query).2 hcachedBelongs
  obtain ⟨_, _, hcls⟩ := hremovedBelongs
  obtain ⟨_, _, hquery⟩ := hremovedQuery
  have hclasses : query = cls := by rw [← hquery, ← hcls]
  rw [hclasses] at hcached
  rw [replaceChain_target] at hcached
  have hremovedOffsets := FreeList.removeFront_removes_head hremove
  have hcachedOffsetMem : cached.offset ∈ rest.map Block.offset :=
    List.mem_map.mpr ⟨cached, hcached, rfl⟩
  rw [hremovedOffsets.2] at hcachedOffsetMem
  have hnodup := (hvalid.1 cls).2
  cases hoffsets : (state.chains cls).map Block.offset with
  | nil => simp [hoffsets] at hremovedOffsets
  | cons first tail =>
      simp [hoffsets] at hremovedOffsets hnodup hcachedOffsetMem
      have hoffsetEq : removed.offset = cached.offset := hsame.1
      exact hnodup.1 (by simpa [hremovedOffsets.1, hoffsetEq] using hcachedOffsetMem)

theorem removeFront_member_survives {state : State} (hvalid : Valid state)
    {cls : SizeClass} {removed old : Block} {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest))
    (hold : old ∈ state.chains cls) (hne : ¬ SamePhysical removed old) :
    ∃ kept ∈ rest, SamePhysical old kept := by
  cases hchain : state.chains cls with
  | nil => simp [hchain] at hold
  | cons head tail =>
      have hheadMem : head ∈ state.chains cls := by simp [hchain]
      have hheadFree := member_free hvalid hheadMem
      simp only [hchain, List.mem_cons] at hold
      cases tail with
      | nil =>
          rcases hold with heq | hold
          · subst old
            simp [hchain, FreeList.removeFront] at hremove
            rcases hremove with ⟨rfl, rfl⟩
            exact (hne (samePhysical_symm
              (samePhysical_withLinks head none none hheadFree))).elim
          · simp at hold
      | cons next more =>
          have hnextMem : next ∈ state.chains cls := by simp [hchain]
          have hnextFree := member_free hvalid hnextMem
          simp [hchain, FreeList.removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          rcases hold with heq | hold
          · subst old
            exact (hne (samePhysical_symm
              (samePhysical_withLinks head none none hheadFree))).elim
          · simp only [List.mem_cons] at hold
            rcases hold with heq | hold
            · subst old
              exact ⟨FreeList.withLinks next none next.nextFreeLink, by simp,
                samePhysical_withLinks next none next.nextFreeLink hnextFree⟩
            · exact ⟨old, by simp [hold], samePhysical_refl old⟩

theorem removeFront_preserves_other_representation {state : State}
    (hvalid : Valid state) {cls : SizeClass} {removed : Block} {rest : List Block}
    (hremove : FreeList.removeFront (state.chains cls) = some (removed, rest))
    {actual : Block}
    (hrepresented : ∃ query cached,
      cached ∈ state.chains query ∧ SamePhysical actual cached)
    (hne : ¬ SamePhysical removed actual) :
    ∃ query cached,
      cached ∈ (state.replaceChain cls rest).chains query ∧
        SamePhysical actual cached := by
  obtain ⟨query, cached, hcached, hactualCached⟩ := hrepresented
  by_cases hquery : query = cls
  · subst query
    have hremovedCached : ¬ SamePhysical removed cached := by
      intro hsame
      exact hne (samePhysical_trans hsame (samePhysical_symm hactualCached))
    obtain ⟨kept, hkept, hcachedKept⟩ :=
      removeFront_member_survives hvalid hremove hcached hremovedCached
    exact ⟨cls, kept, by simpa using hkept,
      samePhysical_trans hactualCached hcachedKept⟩
  · exact ⟨query, cached, by
      rw [replaceChain_other state rest hquery]
      exact hcached, hactualCached⟩

theorem insert_member_origin {state : State} (hvalid : Valid state)
    {cls : SizeClass} {inserted cached : Block} (hinsertedFree : inserted.free = true)
    (hmem : cached ∈ (state.insert cls inserted).chains cls) :
    SamePhysical inserted cached ∨
      ∃ old ∈ state.chains cls, SamePhysical old cached := by
  rw [show (state.insert cls inserted).chains cls =
      FreeList.insertFront inserted (state.chains cls) by
    simp [State.insert]] at hmem
  cases hchain : state.chains cls with
  | nil =>
      simp [hchain, FreeList.insertFront] at hmem
      subst cached
      exact Or.inl (samePhysical_withLinks inserted none none hinsertedFree)
  | cons head rest =>
      have hheadMem : head ∈ state.chains cls := by simp [hchain]
      have hheadFree := member_free hvalid hheadMem
      simp only [hchain, FreeList.insertFront, List.mem_cons] at hmem
      rcases hmem with hnew | htail
      · subst cached
        exact Or.inl
          (samePhysical_withLinks inserted none (some head.offset) hinsertedFree)
      · rcases htail with hhead | hrest
        · subst cached
          exact Or.inr ⟨head, by simp,
            samePhysical_withLinks head (some inserted.offset)
              head.nextFreeLink hheadFree⟩
        · exact Or.inr ⟨cached, by simp [hrest], samePhysical_refl cached⟩

theorem insert_preserves_forward_agreement {physical : List Block}
    {state : State} (hvalid : Valid state)
    (hforward : ∀ cls cached, cached ∈ state.chains cls →
      ∃ actual ∈ physical, SamePhysical actual cached)
    {cls : SizeClass} {inserted actualInserted : Block}
    (hinsertedFree : inserted.free = true) (hactual : actualInserted ∈ physical)
    (hsameInserted : SamePhysical actualInserted inserted) :
    ∀ query cached, cached ∈ (state.insert cls inserted).chains query →
      ∃ actual ∈ physical, SamePhysical actual cached := by
  intro query cached hmem
  by_cases hquery : query = cls
  · subst query
    rcases insert_member_origin hvalid hinsertedFree hmem with hnew | hold
    · exact ⟨actualInserted, hactual,
        samePhysical_trans hsameInserted hnew⟩
    · obtain ⟨old, holdMem, holdSame⟩ := hold
      obtain ⟨actual, hactualMem, hactualOld⟩ := hforward cls old holdMem
      exact ⟨actual, hactualMem, samePhysical_trans hactualOld holdSame⟩
  · have hold : cached ∈ state.chains query := by
      rw [show (state.insert cls inserted).chains query = state.chains query by
        exact replaceChain_other state
          (FreeList.insertFront inserted (state.chains cls)) hquery] at hmem
      exact hmem
    exact hforward query cached hold

theorem inserted_has_representation {state : State} {cls : SizeClass}
    {inserted : Block} (hfree : inserted.free = true) :
    ∃ cached, cached ∈ (state.insert cls inserted).chains cls ∧
      SamePhysical inserted cached := by
  cases hchain : state.chains cls with
  | nil =>
      exact ⟨FreeList.withLinks inserted none none, by
        simp [State.insert, hchain, FreeList.insertFront],
        samePhysical_withLinks inserted none none hfree⟩
  | cons head rest =>
      exact ⟨FreeList.withLinks inserted none (some head.offset), by
        simp [State.insert, hchain, FreeList.insertFront],
        samePhysical_withLinks inserted none (some head.offset) hfree⟩

theorem insert_preserves_representation {state : State} (hvalid : Valid state)
    {cls : SizeClass} {inserted actual : Block}
    (hrepresented : ∃ query cached,
      cached ∈ state.chains query ∧ SamePhysical actual cached) :
    ∃ query cached, cached ∈ (state.insert cls inserted).chains query ∧
      SamePhysical actual cached := by
  obtain ⟨query, cached, hcached, hactualCached⟩ := hrepresented
  by_cases hquery : query = cls
  · subst query
    cases hchain : state.chains cls with
    | nil => simp [hchain] at hcached
    | cons head rest =>
        simp only [hchain, List.mem_cons] at hcached
        rcases hcached with hhead | hrest
        · subst cached
          have hheadFree := member_free hvalid (show head ∈ state.chains cls by
            simp [hchain])
          exact ⟨cls, FreeList.withLinks head (some inserted.offset)
              head.nextFreeLink, by
            simp [State.insert, hchain, FreeList.insertFront],
            samePhysical_trans hactualCached
              (samePhysical_withLinks head (some inserted.offset)
                head.nextFreeLink hheadFree)⟩
        · exact ⟨cls, cached, by
            simp [State.insert, hchain, FreeList.insertFront, hrest],
            hactualCached⟩
  · exact ⟨query, cached, by
      rw [show (state.insert cls inserted).chains query = state.chains query by
        exact replaceChain_other state
          (FreeList.insertFront inserted (state.chains cls)) hquery]
      exact hcached, hactualCached⟩

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
    exact hsame.2.2.trans hcached

theorem represented_offset_class {pool : Region} {physical : List Block}
    {state : State} (hvalid : PoolValid pool physical state)
    {target : Block} (htarget : target ∈ physical) {targetClass : SizeClass}
    (htargetClass : classifyBlock? target = some targetClass)
    {query : SizeClass} {cached : Block} (hcached : cached ∈ state.chains query)
    (hoffset : cached.offset = target.offset) :
    query = targetClass ∧ SamePhysical target cached := by
  obtain ⟨actual, hactual, hactualCached⟩ := hvalid.2.2.1 query cached hcached
  have hactualOffset : actual.offset = target.offset :=
    hactualCached.1.trans hoffset
  have heq := wellFormed_same_offset hvalid.1 hactual htarget hactualOffset
  subst actual
  have htargetBelongs := classifyBlock?_result htargetClass
  have hcachedBelongs := member_belongs hvalid.2.1 hcached
  have htargetQuery : Belongs query target :=
    (samePhysical_belongs_iff hactualCached query).2 hcachedBelongs
  exact ⟨by
    obtain ⟨_, _, hquery⟩ := htargetQuery
    obtain ⟨_, _, hclass⟩ := htargetBelongs
    rw [← hquery, ← hclass], hactualCached⟩

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

/-- Executable two-level lookup. It first searches the request's first level
from its mapping-up second-level index, then searches later first levels and
starts their second-level search at zero. Raw indices are converted to `Fin`
only after an explicit bounds check. -/
def findCandidateIndices (state : State) (start : SizeClass) : Option (Nat × Nat) :=
  match firstSetFrom (slBitmap state start.fl) start.sl.val with
  | some foundSl => some (start.fl.val, foundSl)
  | none =>
      match firstSetFrom (flBitmap state) (start.fl.val + 1) with
      | none => none
      | some foundFl =>
          if hfl : foundFl < firstLevelCount then
            match firstSetFrom (slBitmap state ⟨foundFl, hfl⟩) 0 with
            | none => none
            | some foundSl => some (foundFl, foundSl)
          else none

def CandidateResult (state : State) (start : SizeClass) (fl sl : Nat) : Prop :=
  (fl = start.fl.val ∧
    firstSetFrom (slBitmap state start.fl) start.sl.val = some sl) ∨
  (∃ hfl : fl < firstLevelCount,
    firstSetFrom (flBitmap state) (start.fl.val + 1) = some fl ∧
    firstSetFrom (slBitmap state ⟨fl, hfl⟩) 0 = some sl)

def ClassOrdered (start found : SizeClass) : Prop :=
  start.fl.val < found.fl.val ∨
    (start.fl.val = found.fl.val ∧ start.sl.val ≤ found.sl.val)

theorem findCandidateIndices_result {state : State} {start : SizeClass}
    {fl sl : Nat} (hfind : findCandidateIndices state start = some (fl, sl)) :
    CandidateResult state start fl sl := by
  cases hsame : firstSetFrom (slBitmap state start.fl) start.sl.val with
  | some foundSl =>
      simp [findCandidateIndices, hsame] at hfind
      rcases hfind with ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, hsame⟩
  | none =>
      cases hfirst : firstSetFrom (flBitmap state) (start.fl.val + 1) with
      | none => simp [findCandidateIndices, hsame, hfirst] at hfind
      | some foundFl =>
          by_cases hfl : foundFl < firstLevelCount
          · cases hsecond : firstSetFrom (slBitmap state ⟨foundFl, hfl⟩) 0 with
            | none =>
                simp [findCandidateIndices, hsame, hfirst, hfl, hsecond] at hfind
            | some foundSl =>
                simp [findCandidateIndices, hsame, hfirst, hfl, hsecond] at hfind
                rcases hfind with ⟨rfl, rfl⟩
                exact Or.inr ⟨hfl, hfirst, hsecond⟩
          · simp [findCandidateIndices, hsame, hfirst, hfl] at hfind

theorem findCandidateIndices_bounds {state : State} {start : SizeClass}
    {fl sl : Nat} (hfind : findCandidateIndices state start = some (fl, sl)) :
    fl < firstLevelCount ∧ sl < secondLevelCount := by
  rcases findCandidateIndices_result hfind with hsame | hlater
  · rw [hsame.1]
    have hsound := firstSetFrom_sound hsame.2
    simp only [slBitmap, List.length_ofFn] at hsound
    exact ⟨start.fl.isLt, hsound.2.1⟩
  · obtain ⟨hfl, _, hsecond⟩ := hlater
    have hsound := firstSetFrom_sound hsecond
    simp only [slBitmap, List.length_ofFn] at hsound
    exact ⟨hfl, hsound.2.1⟩

/-- Checked class-valued facade used by allocation. -/
def findCandidate (state : State) (start : SizeClass) : Option SizeClass :=
  match findCandidateIndices state start with
  | none => none
  | some (fl, sl) =>
      if hfl : fl < firstLevelCount then
        if hsl : sl < secondLevelCount then
          some { fl := ⟨fl, hfl⟩, sl := ⟨sl, hsl⟩ }
        else none
      else none

theorem findCandidate_result {state : State} {start found : SizeClass}
    (hfind : findCandidate state start = some found) :
    findCandidateIndices state start = some (found.fl.val, found.sl.val) := by
  unfold findCandidate at hfind
  cases hindices : findCandidateIndices state start with
  | none => simp [hindices] at hfind
  | some pair =>
      obtain ⟨fl, sl⟩ := pair
      have hbounds := findCandidateIndices_bounds hindices
      simp [hindices, hbounds.1, hbounds.2] at hfind
      subst found
      rfl

theorem findCandidate_ordered {state : State} {start found : SizeClass}
    (hfind : findCandidate state start = some found) :
    ClassOrdered start found := by
  have hindices := findCandidate_result hfind
  rcases findCandidateIndices_result hindices with hsame | hlater
  · right
    constructor
    · exact hsame.1.symm
    · exact (firstSetFrom_sound hsame.2).1
  · left
    obtain ⟨_, hfirst, _⟩ := hlater
    exact Nat.lt_of_succ_le (firstSetFrom_sound hfirst).1

/-- Every aligned block classified into a returned class is suitable, not just
the particular physical witness chosen by an existential search theorem. -/
theorem ordered_search_class_suitable (request : Nat) (hrequest : 0 < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount)
    {found : SizeClass} {block : Block}
    (horder : ClassOrdered (searchSizeClass request hrequest hkeyMax) found)
    (hbelongs : Belongs found block) (haligned : alignment ∣ block.bytes) :
    request ≤ block.bytes := by
  unfold ClassOrdered at horder
  obtain ⟨hblock, hblockMax, hblockClass⟩ := hbelongs
  by_cases hlinear : request ≤ linearCutoff
  · have hrequestMax : request < 2 ^ firstLevelCount :=
      Nat.lt_of_le_of_lt (request_le_key request hrequest) hkeyMax
    have hstart := searchSizeClass_linear request hrequest hkeyMax hlinear
    by_cases hblockLinear : block.bytes ≤ linearCutoff
    · have hrequestFl :=
        (linear_sizeClass_values request hrequest hrequestMax hlinear).1
      have hblockFl :=
        (linear_sizeClass_values block.bytes hblock hblockMax hblockLinear).1
      have hsl : (sizeClass request hrequest hrequestMax).sl.val ≤
          (sizeClass block.bytes hblock hblockMax).sl.val := by
        rw [hblockClass]
        rw [hstart] at horder
        rcases horder with hfl | ⟨_, hsl⟩
        · rw [hrequestFl, ← hblockClass, hblockFl] at hfl
          omega
        · exact hsl
      exact linear_later_class_suitable request block.bytes hrequest hblock
        hrequestMax hblockMax hlinear hblockLinear haligned hsl
    · exact Nat.le_trans hlinear (Nat.le_of_lt (Nat.lt_of_not_ge hblockLinear))
  · have hrequestHigh : linearCutoff < request := Nat.lt_of_not_ge hlinear
    have hstart := searchSizeClass_high request hrequest hkeyMax hrequestHigh
    have hstartPositive : 0 <
        (searchSizeClass request hrequest hkeyMax).fl.val := by
      rw [hstart, show (requestSizeClass request hrequest hkeyMax).fl.val =
          (requestKey request).log2 by
        exact high_sizeClass_fl (requestKey request)
          (requestKey_positive request hrequest) hkeyMax
          (Nat.lt_of_lt_of_le hrequestHigh (request_le_key request hrequest))]
      exact Nat.lt_of_lt_of_le (by decide : 0 < 5)
        (high_log_at_least_five (requestKey request)
          (Nat.lt_of_lt_of_le hrequestHigh (request_le_key request hrequest)))
    have hblockHigh : linearCutoff < block.bytes := by
      apply Nat.lt_of_not_ge
      intro hblockLinear
      have hblockZero :=
        (linear_sizeClass_values block.bytes hblock hblockMax hblockLinear).1
      rw [hblockClass] at hblockZero
      rcases horder with hfl | ⟨hfl, _⟩
      · omega
      · omega
    have hclassOrder :
        (requestSizeClass request hrequest hkeyMax).fl.val <
            (sizeClass block.bytes hblock hblockMax).fl.val ∨
          ((requestSizeClass request hrequest hkeyMax).fl.val =
              (sizeClass block.bytes hblock hblockMax).fl.val ∧
            (requestSizeClass request hrequest hkeyMax).sl.val ≤
              (sizeClass block.bytes hblock hblockMax).sl.val) := by
      rw [hstart] at horder
      simpa [hblockClass] using horder
    exact high_request_later_class_suitable request block.bytes hrequest hblock
      hkeyMax hblockMax hrequestHigh hblockHigh hclassOrder

theorem slBitmap_length (state : State) (fl : Fin firstLevelCount) :
    (slBitmap state fl).length = secondLevelCount := by
  simp [slBitmap]

theorem flBitmap_length (state : State) :
    (flBitmap state).length = firstLevelCount := by
  simp [flBitmap]

theorem slBitmap_get (state : State) (fl : Fin firstLevelCount)
    (sl : Fin secondLevelCount) :
    (slBitmap state fl)[sl.val]? = some (state.slSet fl sl) := by
  simp [slBitmap]

theorem flBitmap_get (state : State) (fl : Fin firstLevelCount) :
    (flBitmap state)[fl.val]? = some (state.flSet fl) := by
  simp [flBitmap]

def HasEligibleBin (state : State) (start : SizeClass) : Prop :=
  (∃ sl : Fin secondLevelCount, start.sl.val ≤ sl.val ∧
    state.slSet start.fl sl = true) ∨
  (∃ fl : Fin firstLevelCount, start.fl.val < fl.val ∧
    state.flSet fl = true)

/-- Lookup does not fail spuriously: if either an eligible second-level bit in
the starting first level or any later first-level bit is set, the executable
wrapper returns a pair of indices. -/
theorem findCandidateIndices_complete {state : State} {start : SizeClass}
    (hvalid : Valid state) (heligible : HasEligibleBin state start) :
    ∃ fl sl, findCandidateIndices state start = some (fl, sl) := by
  rcases heligible with hsame | hlater
  · obtain ⟨sl, hstart, hbit⟩ := hsame
    have hget : (slBitmap state start.fl)[sl.val]? = some true := by
      rw [slBitmap_get]
      simp [hbit]
    obtain ⟨foundSl, hfoundSl⟩ := firstSetFrom_complete hstart hget
    exact ⟨start.fl.val, foundSl, by
      simp [findCandidateIndices, hfoundSl]⟩
  · obtain ⟨fl, hstart, hbit⟩ := hlater
    have hget : (flBitmap state)[fl.val]? = some true := by
      rw [flBitmap_get]
      simp [hbit]
    obtain ⟨foundFl, hfoundFl⟩ := firstSetFrom_complete
      (show start.fl.val + 1 ≤ fl.val by omega) hget
    have hfoundFlBound := (firstSetFrom_sound hfoundFl).2.1
    rw [flBitmap_length] at hfoundFlBound
    let selectedFl : Fin firstLevelCount := ⟨foundFl, hfoundFlBound⟩
    have hflBit : state.flSet selectedFl = true := by
      have hselectedGet := (firstSetFrom_sound hfoundFl).2.2
      have hview := flBitmap_get state selectedFl
      rw [hselectedGet] at hview
      exact (Option.some.inj hview).symm
    obtain ⟨sl, hchain⟩ := (fl_bit_iff_nonempty hvalid selectedFl).1 hflBit
    have hslBit := (sl_bit_iff_nonempty hvalid selectedFl sl).2 hchain
    have hslGet : (slBitmap state selectedFl)[sl.val]? = some true := by
      rw [slBitmap_get]
      simp [hslBit]
    obtain ⟨foundSl, hfoundSl⟩ := firstSetFrom_complete (Nat.zero_le _) hslGet
    cases hsameSearch : firstSetFrom (slBitmap state start.fl) start.sl.val with
    | some sameSl =>
        exact ⟨start.fl.val, sameSl, by
          simp [findCandidateIndices, hsameSearch]⟩
    | none =>
        exact ⟨foundFl, foundSl, by
          simp [findCandidateIndices, hsameSearch, hfoundFl, hfoundFlBound,
            hfoundSl, selectedFl]⟩

theorem findCandidateIndices_success_eligible {state : State} {start : SizeClass}
    {fl sl : Nat} (hfind : findCandidateIndices state start = some (fl, sl)) :
    HasEligibleBin state start := by
  rcases findCandidateIndices_result hfind with hsame | hlater
  · have hsound := firstSetFrom_sound hsame.2
    have hbound : sl < secondLevelCount := by
      rw [slBitmap_length] at hsound
      exact hsound.2.1
    let selectedSl : Fin secondLevelCount := ⟨sl, hbound⟩
    have hview := slBitmap_get state start.fl selectedSl
    rw [hsound.2.2] at hview
    have hbit : state.slSet start.fl selectedSl = true :=
      (Option.some.inj hview).symm
    exact Or.inl ⟨selectedSl, hsound.1, hbit⟩
  · obtain ⟨hbound, hfirst, _⟩ := hlater
    let selectedFl : Fin firstLevelCount := ⟨fl, hbound⟩
    have hsound := firstSetFrom_sound hfirst
    have hview := flBitmap_get state selectedFl
    rw [hsound.2.2] at hview
    have hbit : state.flSet selectedFl = true :=
      (Option.some.inj hview).symm
    exact Or.inr ⟨selectedFl, by
      change start.fl.val < fl
      omega, hbit⟩

theorem findCandidateIndices_none_iff {state : State} {start : SizeClass}
    (hvalid : Valid state) :
    findCandidateIndices state start = none ↔ ¬ HasEligibleBin state start := by
  constructor
  · intro hnone heligible
    obtain ⟨fl, sl, hsome⟩ := findCandidateIndices_complete hvalid heligible
    rw [hnone] at hsome
    contradiction
  · intro hnone
    cases hfind : findCandidateIndices state start with
    | none => rfl
    | some pair =>
        obtain ⟨fl, sl⟩ := pair
        exact (hnone (findCandidateIndices_success_eligible hfind)).elim

theorem findCandidate_none_iff {state : State} {start : SizeClass}
    (hvalid : Valid state) :
    findCandidate state start = none ↔ ¬ HasEligibleBin state start := by
  constructor
  · intro hcandidate
    apply (findCandidateIndices_none_iff hvalid).1
    cases hindices : findCandidateIndices state start with
    | none => rfl
    | some pair =>
        obtain ⟨fl, sl⟩ := pair
        have hbounds := findCandidateIndices_bounds hindices
        simp [findCandidate, hindices, hbounds.1, hbounds.2] at hcandidate
  · intro hnoEligible
    have hindices := (findCandidateIndices_none_iff hvalid).2 hnoEligible
    simp [findCandidate, hindices]

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

theorem findCandidate_nonempty {state : State} {start found : SizeClass}
    (hvalid : Valid state) (hfind : findCandidate state start = some found) :
    state.chains found ≠ [] := by
  have hindices := findCandidate_result hfind
  rcases findCandidateIndices_result hindices with hsame | hlater
  · obtain ⟨hbound, hchain⟩ := secondLevel_search_nonempty hvalid start.fl
      start.sl.val found.sl.val hsame.2
    have hfl : found.fl = start.fl := Fin.ext hsame.1
    have hcls : found = { fl := start.fl, sl := found.sl } := by
      cases found with
      | mk fl sl =>
          simp only at hfl ⊢
          subst fl
          rfl
    rw [hcls]
    simpa using hchain
  · obtain ⟨hflBound, _, hsecond⟩ := hlater
    obtain ⟨hslBound, hchain⟩ := secondLevel_search_nonempty hvalid
      ⟨found.fl.val, hflBound⟩ 0 found.sl.val hsecond
    simpa using hchain

def State.takeCandidate (state : State) (start : SizeClass) :
    Option (Block × State) :=
  match findCandidate state start with
  | none => none
  | some cls => state.removeFront cls

theorem takeCandidate_result {state next : State} {start : SizeClass}
    {removed : Block} (htake : state.takeCandidate start = some (removed, next)) :
    ∃ cls rest,
      findCandidate state start = some cls ∧
      FreeList.removeFront (state.chains cls) = some (removed, rest) ∧
      next = state.replaceChain cls rest := by
  unfold State.takeCandidate at htake
  cases hfind : findCandidate state start with
  | none => simp [hfind] at htake
  | some cls =>
      cases hremove : FreeList.removeFront (state.chains cls) with
      | none => simp [hfind, State.removeFront, hremove] at htake
      | some result =>
          obtain ⟨detached, rest⟩ := result
          simp [hfind, State.removeFront, hremove] at htake
          rcases htake with ⟨rfl, rfl⟩
          exact ⟨cls, rest, rfl, hremove, rfl⟩

theorem takeCandidate_valid {state next : State} {start : SizeClass}
    {removed : Block} (hvalid : Valid state)
    (htake : state.takeCandidate start = some (removed, next)) :
    Valid next := by
  obtain ⟨cls, rest, _, hremove, rfl⟩ := takeCandidate_result htake
  exact removeFront_valid hvalid hremove

theorem takeCandidate_preserves_forward_agreement {physical : List Block}
    {state next : State} (hvalid : Valid state)
    (hagrees : PhysicalAgreement physical state) {start : SizeClass}
    {removed : Block}
    (htake : state.takeCandidate start = some (removed, next)) :
    ∀ cls cached, cached ∈ next.chains cls →
      ∃ actual ∈ physical, SamePhysical actual cached := by
  obtain ⟨cls, rest, _, hremove, rfl⟩ := takeCandidate_result htake
  exact removeFront_preserves_forward_agreement hvalid hagrees hremove

theorem takeCandidate_detached {state next : State} {start : SizeClass}
    {removed : Block} (htake : state.takeCandidate start = some (removed, next)) :
    removed.free = true ∧ removed.prevFreeLink = none ∧
      removed.nextFreeLink = none := by
  obtain ⟨cls, rest, _, hremove, _⟩ := takeCandidate_result htake
  exact FreeList.removeFront_detaches hremove

/-- The exact detached head—not merely some witness in its class—is suitable
and still denotes the same authoritative physical header. -/
theorem takeCandidate_suitable {pool : Region} {physical : List Block}
    {state next : State} (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount)
    {removed : Block}
    (htake : state.takeCandidate
      (searchSizeClass request hrequest hkeyMax) = some (removed, next)) :
    ∃ actual, actual ∈ physical ∧ SamePhysical actual removed ∧
      removed.free = true ∧ removed.aligned ∧ request ≤ removed.bytes ∧
      removed.bytes < 2 ^ firstLevelCount := by
  obtain ⟨cls, rest, hfind, hremove, _⟩ := takeCandidate_result htake
  obtain ⟨head, hmem, hheadRemoved⟩ :=
    removeFront_removed_represents_member hpool.2.1 hremove
  obtain ⟨actual, hactual, hactualHead⟩ := member_physical hpool.2.2 hmem
  have hactualAligned := (hpool.1.2.2.2 actual hactual).2.2
  have hheadAligned := (samePhysical_aligned_iff hactualHead).1 hactualAligned
  have hremovedAligned := (samePhysical_aligned_iff hheadRemoved).1 hheadAligned
  have hremovedBelongs :=
    (samePhysical_belongs_iff hheadRemoved cls).1
      (member_belongs hpool.2.1 hmem)
  have horder := findCandidate_ordered hfind
  have hsuitable := ordered_search_class_suitable request hrequest hkeyMax
    horder hremovedBelongs hremovedAligned.2
  obtain ⟨_, hremovedMax, _⟩ := hremovedBelongs
  have hdetached := takeCandidate_detached htake
  exact ⟨actual, hactual, samePhysical_trans hactualHead hheadRemoved,
    hdetached.1, hremovedAligned, hsuitable, hremovedMax⟩

theorem takeCandidate_complete {state : State} {start : SizeClass}
    (hvalid : Valid state) (heligible : HasEligibleBin state start) :
    ∃ removed next, state.takeCandidate start = some (removed, next) := by
  cases hfind : findCandidate state start with
  | none =>
      exact ((findCandidate_none_iff hvalid).1 hfind heligible).elim
  | some cls =>
      have hnonempty := findCandidate_nonempty hvalid hfind
      obtain ⟨removed, rest, hremove⟩ := FreeList.removeFront_exists hnonempty
      exact ⟨removed, state.replaceChain cls rest, by
        simp [State.takeCandidate, hfind, State.removeFront, hremove]⟩

theorem takeCandidate_none_iff {state : State} {start : SizeClass}
    (hvalid : Valid state) :
    state.takeCandidate start = none ↔ ¬ HasEligibleBin state start := by
  constructor
  · intro hnone heligible
    obtain ⟨removed, next, hsome⟩ := takeCandidate_complete hvalid heligible
    rw [hnone] at hsome
    contradiction
  · intro hno
    have hfind := (findCandidate_none_iff hvalid).2 hno
    simp [State.takeCandidate, hfind]

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

/-- End-to-end suitability for a successful second-level search in the
mapping-up first level of a logarithmic request. -/
theorem secondLevel_search_high_suitable {pool : Region} {physical : List Block}
    {state : State} (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hrequestHigh : linearCutoff < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount) (found : Nat)
    (hsearch : firstSetFrom
      (slBitmap state (requestSizeClass request hrequest hkeyMax).fl)
      (requestSizeClass request hrequest hkeyMax).sl.val = some found) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  let requestClass := requestSizeClass request hrequest hkeyMax
  obtain ⟨hfound, head, actual, rest, hchain, hactual, hsame,
      hactualFree, hbelongs, _⟩ :=
    secondLevel_search_physical_head hpool requestClass.fl
      requestClass.sl.val found hsearch
  obtain ⟨hblock, hblockMax, hblockClass⟩ := hbelongs
  have hkey := requestKey_positive request hrequest
  have hkeyHigh : linearCutoff < requestKey request :=
    Nat.lt_of_lt_of_le hrequestHigh (request_le_key request hrequest)
  have hrequestFl : 0 < requestClass.fl.val := by
    rw [show requestClass.fl.val = (requestKey request).log2 by
      exact high_sizeClass_fl (requestKey request) hkey hkeyMax hkeyHigh]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 5)
      (high_log_at_least_five (requestKey request) hkeyHigh)
  have hblockHigh : linearCutoff < actual.bytes := by
    apply Nat.lt_of_not_ge
    intro hlinear
    have hzero := (linear_sizeClass_values actual.bytes hblock hblockMax hlinear).1
    rw [hblockClass] at hzero
    exact (Nat.ne_of_gt hrequestFl) hzero
  have hsearchSound := firstSetFrom_sound hsearch
  have horder :
      requestClass.fl.val <
          (sizeClass actual.bytes hblock hblockMax).fl.val ∨
        (requestClass.fl.val =
            (sizeClass actual.bytes hblock hblockMax).fl.val ∧
          requestClass.sl.val ≤
            (sizeClass actual.bytes hblock hblockMax).sl.val) := by
    right
    constructor
    · rw [hblockClass]
    · rw [hblockClass]
      exact hsearchSound.1
  have hsuitable := high_request_later_class_suitable request actual.bytes
    hrequest hblock hkeyMax hblockMax hrequestHigh hblockHigh horder
  have haligned := (hpool.1.2.2.2 actual hactual).2.2
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

/-- If the request's own first level has no suitable chain, searching later
first levels returns a physical free block that is necessarily large enough. -/
theorem firstLevel_search_high_suitable {pool : Region} {physical : List Block}
    {state : State} (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hrequestHigh : linearCutoff < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount) (found : Nat)
    (hsearch : firstSetFrom (flBitmap state)
      ((requestSizeClass request hrequest hkeyMax).fl.val + 1) = some found) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  let requestClass := requestSizeClass request hrequest hkeyMax
  obtain ⟨hfound, sl, hnonempty⟩ :=
    firstLevel_search_nonempty hpool.2.1 (requestClass.fl.val + 1) found hsearch
  let selected : SizeClass := { fl := ⟨found, hfound⟩, sl := sl }
  cases hchain : state.chains selected with
  | nil => exact (hnonempty hchain).elim
  | cons head rest =>
      have hmem : head ∈ state.chains selected := by simp [hchain]
      have hfree := member_free hpool.2.1 hmem
      obtain ⟨hblock, hblockMax, hblockClass⟩ := member_belongs hpool.2.1 hmem
      obtain ⟨actual, hactual, hsame⟩ := member_physical hpool.2.2 hmem
      have hactualFree : actual.free = true := (samePhysical_free hsame).trans hfree
      have hactualClass : Belongs selected actual :=
        (samePhysical_belongs_iff hsame selected).2 ⟨hblock, hblockMax, hblockClass⟩
      obtain ⟨hactualBytes, hactualMax, hactualClassEq⟩ := hactualClass
      have hsearchSound := firstSetFrom_sound hsearch
      have hflLater : requestClass.fl.val < found := by
        simpa [requestClass] using (Nat.lt_of_succ_le hsearchSound.1)
      have hblockHigh : linearCutoff < actual.bytes := by
        apply Nat.lt_of_not_ge
        intro hlinear
        have hzero :=
          (linear_sizeClass_values actual.bytes hactualBytes hactualMax hlinear).1
        rw [hactualClassEq] at hzero
        have : 0 < found := by omega
        exact (Nat.ne_of_gt this) hzero
      have horder :
          requestClass.fl.val <
              (sizeClass actual.bytes hactualBytes hactualMax).fl.val ∨
            (requestClass.fl.val =
                (sizeClass actual.bytes hactualBytes hactualMax).fl.val ∧
              requestClass.sl.val ≤
                (sizeClass actual.bytes hactualBytes hactualMax).sl.val) := by
        left
        rw [hactualClassEq]
        exact hflLater
      have hsuitable := high_request_later_class_suitable request actual.bytes
        hrequest hactualBytes hkeyMax hactualMax hrequestHigh hblockHigh horder
      have haligned := (hpool.1.2.2.2 actual hactual).2.2
      exact ⟨actual, hactual, hactualFree, haligned, hsuitable⟩

theorem firstLevel_search_linear_suitable {pool : Region}
    {physical : List Block} {state : State}
    (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hrequestMax : request < 2 ^ firstLevelCount)
    (hlinear : request ≤ linearCutoff) (found : Nat)
    (hsearch : firstSetFrom (flBitmap state)
      ((sizeClass request hrequest hrequestMax).fl.val + 1) = some found) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  obtain ⟨hfound, sl, hnonempty⟩ :=
    firstLevel_search_nonempty hpool.2.1
      ((sizeClass request hrequest hrequestMax).fl.val + 1) found hsearch
  let selected : SizeClass := { fl := ⟨found, hfound⟩, sl := sl }
  cases hchain : state.chains selected with
  | nil => exact (hnonempty hchain).elim
  | cons head rest =>
      have hmem : head ∈ state.chains selected := by simp [hchain]
      have hfree := member_free hpool.2.1 hmem
      obtain ⟨actual, hactual, hsame⟩ := member_physical hpool.2.2 hmem
      have hactualFree : actual.free = true := (samePhysical_free hsame).trans hfree
      have hbelongs := (samePhysical_belongs_iff hsame selected).2
        (member_belongs hpool.2.1 hmem)
      obtain ⟨hactualBytes, hactualMax, hactualClass⟩ := hbelongs
      have hfoundPositive : 0 < found := by
        have hsound := firstSetFrom_sound hsearch
        have hrequestFl :=
          (linear_sizeClass_values request hrequest hrequestMax hlinear).1
        omega
      have hblockHigh : linearCutoff < actual.bytes := by
        apply Nat.lt_of_not_ge
        intro hblockLinear
        have hzero :=
          (linear_sizeClass_values actual.bytes hactualBytes hactualMax
            hblockLinear).1
        rw [hactualClass] at hzero
        exact (Nat.ne_of_gt hfoundPositive) hzero
      have haligned := (hpool.1.2.2.2 actual hactual).2.2
      exact ⟨actual, hactual, hactualFree, haligned,
        Nat.le_trans hlinear (Nat.le_of_lt hblockHigh)⟩

/-- The executable two-level lookup wrapper inherits the high-range
suitability theorem in both of its successful branches. -/
theorem findCandidateIndices_high_suitable {pool : Region}
    {physical : List Block} {state : State}
    (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hrequestHigh : linearCutoff < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount)
    {foundFl foundSl : Nat}
    (hfind : findCandidateIndices state
      (requestSizeClass request hrequest hkeyMax) = some (foundFl, foundSl)) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  rcases findCandidateIndices_result hfind with hsame | hlater
  · exact secondLevel_search_high_suitable hpool request hrequest hrequestHigh
      hkeyMax foundSl hsame.2
  · obtain ⟨hfl, hfirst, _⟩ := hlater
    exact firstLevel_search_high_suitable hpool request hrequest hrequestHigh
      hkeyMax foundFl hfirst

theorem findCandidateIndices_linear_suitable {pool : Region}
    {physical : List Block} {state : State}
    (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hrequestMax : request < 2 ^ firstLevelCount)
    (hlinear : request ≤ linearCutoff) {foundFl foundSl : Nat}
    (hfind : findCandidateIndices state
      (sizeClass request hrequest hrequestMax) = some (foundFl, foundSl)) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  rcases findCandidateIndices_result hfind with hsame | hlater
  · exact secondLevel_search_linear_suitable hpool request hrequest hrequestMax
      hlinear foundSl hsame.2
  · obtain ⟨hfl, hfirst, _⟩ := hlater
    exact firstLevel_search_linear_suitable hpool request hrequest hrequestMax
      hlinear foundFl hfirst

/-- Unified safety contract of executable TLSF lookup. On success, regardless
of the linear/logarithmic branch or how many empty bins were skipped, the
candidate denotes an aligned free physical block large enough for the request. -/
theorem findCandidateIndices_suitable {pool : Region}
    {physical : List Block} {state : State}
    (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount)
    {foundFl foundSl : Nat}
    (hfind : findCandidateIndices state
      (searchSizeClass request hrequest hkeyMax) = some (foundFl, foundSl)) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  by_cases hlinear : request ≤ linearCutoff
  · have hrequestMax : request < 2 ^ firstLevelCount :=
      Nat.lt_of_le_of_lt (request_le_key request hrequest) hkeyMax
    apply findCandidateIndices_linear_suitable hpool request hrequest
      hrequestMax hlinear
    simpa [searchSizeClass_linear request hrequest hkeyMax hlinear] using hfind
  · have hhigh : linearCutoff < request := Nat.lt_of_not_ge hlinear
    apply findCandidateIndices_high_suitable hpool request hrequest hhigh hkeyMax
    simpa [searchSizeClass_high request hrequest hkeyMax hhigh] using hfind

theorem findCandidate_suitable {pool : Region} {physical : List Block}
    {state : State} (hpool : PoolValid pool physical state)
    (request : Nat) (hrequest : 0 < request)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount)
    {found : SizeClass}
    (hfind : findCandidate state (searchSizeClass request hrequest hkeyMax) =
      some found) :
    ∃ actual : Block, actual ∈ physical ∧ actual.free = true ∧
      actual.aligned ∧ request ≤ actual.bytes := by
  exact findCandidateIndices_suitable hpool request hrequest hkeyMax
    (findCandidate_result hfind)

end Luffs.Allocator.TLSF.Bins
