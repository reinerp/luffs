import Luffs.Allocator.TLSF.Alloc

set_option autoImplicit false

namespace Luffs.Allocator.TLSF.Ownership

open Luffs.Memory
open Luffs.Allocator.TLSF
open Iris Iris.BI

/-- Separation-logic ownership retained by the allocator. Allocated blocks are
tracked in the pure physical layout but their byte capability is held by the
client, so they contribute `emp`. -/
def OwnsFree {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) : List Block -> PROP
  | [] => iprop(emp)
  | b :: rest => iprop(
      (if b.free then OwnsBytes (PROP := PROP) (b.region pool) else emp) ∗
        OwnsFree (PROP := PROP) pool rest)

theorem ownsFree_samePhysical {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) {left right : Block} (hsame : Bins.SamePhysical left right) :
    (if left.free then OwnsBytes (PROP := PROP) (left.region pool) else emp) ⊣⊢
      (if right.free then OwnsBytes (PROP := PROP) (right.region pool) else emp) := by
  rw [Bins.samePhysical_free hsame, Bins.samePhysical_region hsame pool]
  exact .rfl

theorem ownsFree_split_head {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) (b : Block) (rest : List Block) (wanted : Nat)
    (hfree : b.free = true) (hwanted : wanted ≤ b.bytes) :
    OwnsFree (PROP := PROP) pool (b :: rest) ⊣⊢
      OwnsBytes ((splitBlock b wanted).1.region pool) ∗
        OwnsFree pool ((splitBlock b wanted).1 ::
          (splitBlock b wanted).2 :: rest) := by
  simp only [OwnsFree, hfree, if_pos, splitBlock]
  rw [(ownsBytes_splitBlock pool b wanted hwanted).to_eq]
  exact sep_assoc.trans (sep_congr_right emp_sep.symm)

theorem ownsFree_whole_head {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) (b : Block) (rest : List Block)
    (hfree : b.free = true) :
    OwnsFree (PROP := PROP) pool (b :: rest) ⊣⊢
      OwnsBytes ((markAllocated b).region pool) ∗
        OwnsFree pool (markAllocatedAt (b :: rest) 0) := by
  cases rest with
  | nil =>
      simp only [OwnsFree, hfree, if_pos, markAllocatedAt, markAllocated,
        Block.region]
      simp only [Bool.false_eq_true, if_false]
      exact sep_congr_right sep_emp.symm
  | cons next tail =>
      simp only [OwnsFree, hfree, if_pos, markAllocatedAt, markAllocated,
        Block.region]
      simp only [Bool.false_eq_true, if_false]
      exact sep_congr_right emp_sep.symm

/-- A successful physical allocation transfers exactly the selected region to
the client. All unselected free-block capabilities remain with the allocator. -/
theorem allocateChosenAt_ownsFree {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) {blocks next : List Block} {i wanted : Nat}
    {selected allocated : Block} (hget : blocks[i]? = some selected)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    OwnsFree (PROP := PROP) pool blocks ⊣⊢
      OwnsBytes (allocated.region pool) ∗ OwnsFree pool next := by
  induction blocks generalizing i selected allocated next with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          obtain ⟨hfree, hfits, _, hsplit | hwhole⟩ :=
            allocateChosenAt_success_cases (by rfl) hsuccess
          · rcases hsplit with ⟨_, rfl, rfl⟩
            exact ownsFree_split_head pool head rest wanted hfree hfits
          · rcases hwhole with ⟨_, rfl, rfl⟩
            exact ownsFree_whole_head pool head rest hfree
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [allocateChosenAt, List.getElem?_cons_succ, hget] at hsuccess
          split at hsuccess <;> try contradiction
          next hpre =>
            split at hsuccess
            next hcan =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hsuccess
              rcases hsuccess with ⟨hallocated, hnext⟩
              subst allocated
              subst next
              simp only [OwnsFree, splitAt]
              have htail : allocateChosenAt rest j wanted =
                  some ((splitBlock selected wanted).1,
                    splitAt rest j wanted) := by
                simp [allocateChosenAt, hget, hpre, hcan]
              refine (sep_congr_right (ih hget htail)).trans ?_
              exact sep_assoc.symm.trans
                ((sep_congr_left sep_comm).trans sep_assoc)
            next hcannot =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hsuccess
              rcases hsuccess with ⟨hallocated, hnext⟩
              subst allocated
              subst next
              simp only [OwnsFree, markAllocatedAt]
              have htail : allocateChosenAt rest j wanted =
                  some (markAllocated selected,
                    markAllocatedAt rest j) := by
                simp [allocateChosenAt, hget, hpre, hcannot]
              refine (sep_congr_right (ih hget htail)).trans ?_
              · exact sep_assoc.symm.trans
                  ((sep_congr_left sep_comm).trans sep_assoc)

/-- End-to-end ownership law for successful TLSF allocation. Together with
`Alloc.allocate_preserves_valid`, this says the allocator both preserves its
pure structural invariant and transfers exactly the returned byte region. -/
theorem allocate_ownsFree {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    {result : Alloc.Result}
    (hsuccess : Alloc.allocate state request hrequest hkeyMax = some result) :
    OwnsFree (PROP := PROP) pool state.physical ⊣⊢
      OwnsBytes (result.allocated.region pool) ∗
        OwnsFree pool result.state.physical := by
  obtain ⟨core, hcore, hfinish, hallocated⟩ := Alloc.allocate_result hsuccess
  obtain ⟨prepared, hprepare, hchosen, _, _⟩ := Alloc.allocateCore_result hcore
  obtain ⟨selected, hget, _, _, _, _, _, _⟩ := Alloc.prepare_safe hvalid hprepare
  have htransfer := allocateChosenAt_ownsFree (PROP := PROP) pool hget hchosen
  rw [hallocated, Alloc.finishCore_physical hfinish]
  exact htransfer

theorem deallocate_head_ownsFree {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) (b : Block) (rest : List Block)
    (hallocated : b.free = false) :
    OwnsBytes (PROP := PROP) (b.region pool) ∗ OwnsFree pool (b :: rest) ⊣⊢
      OwnsFree pool (markFreeAt (b :: rest) 0) := by
  cases rest with
  | nil =>
      simp only [OwnsFree, hallocated, markFreeAt, Block.region]
      simp only [if_true]
      exact sep_congr_right emp_sep
  | cons next tail =>
      simp only [OwnsFree, hallocated, markFreeAt, Block.region]
      simp only [if_true]
      exact sep_congr_right emp_sep

/-- Returning the exact live region consumes the client's capability and adds
it back to the allocator assertion. This is the ownership half of `dealloc`;
subsequent neighbor coalescing merely reassociates adjacent capabilities. -/
theorem deallocateAt_ownsFree {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) {blocks : List Block} {i : Nat} {selected : Block}
    {returned : Region} (hget : blocks[i]? = some selected)
    (hsuccess : deallocateAt pool blocks i returned =
      some (markFreeAt blocks i)) :
    OwnsBytes (PROP := PROP) returned ∗ OwnsFree pool blocks ⊣⊢
      OwnsFree pool (markFreeAt blocks i) := by
  have hpre := (deallocateAt_success_iff hget).1 hsuccess
  rw [hpre.2]
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          exact deallocate_head_ownsFree pool head rest hpre.1
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [OwnsFree, markFreeAt]
          have htail : deallocateAt pool rest j returned =
              some (markFreeAt rest j) :=
            (deallocateAt_success_iff hget).2 hpre
          have hih := ih hget htail hpre
          exact sep_assoc.symm.trans ((sep_congr_left sep_comm).trans
            (sep_assoc.trans (sep_congr_right hih)))

theorem coalesce_head_ownsFree {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) (left right : Block) (rest : List Block)
    (hcan : canCoalesce left right) :
    OwnsFree (PROP := PROP) pool (left :: right :: rest) ⊣⊢
      OwnsFree pool (coalesceBlocks left right :: rest) := by
  rcases hcan with ⟨hleftFree, hrightFree, hadjacent⟩
  simp only [OwnsFree, hleftFree, hrightFree, if_pos, coalesceBlocks]
  have hmerge := ownsBytes_coalesceBlocks (PROP := PROP)
    pool left right hadjacent
  exact sep_assoc.symm.trans (sep_congr_left hmerge)

theorem coalesceAt_ownsFree {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) {blocks : List Block} {i : Nat} {left right : Block}
    (hleft : blocks[i]? = some left) (hright : blocks[i + 1]? = some right)
    (hcan : canCoalesce left right) :
    OwnsFree (PROP := PROP) pool blocks ⊣⊢
      OwnsFree pool (coalesceAt blocks i) := by
  induction blocks generalizing i left right with
  | nil => simp at hleft
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
          subst left
          cases rest with
          | nil => simp at hright
          | cons next tail =>
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                Option.some.injEq] at hright
              subst right
              exact coalesce_head_ownsFree pool head next tail hcan
      | succ j =>
          simp only [List.getElem?_cons_succ] at hleft hright
          simp only [OwnsFree, coalesceAt]
          exact sep_congr_right (ih hleft (by simpa [Nat.add_assoc] using hright) hcan)

end Luffs.Allocator.TLSF.Ownership
