import Luffs.Allocator.TLSF.FreeList

set_option autoImplicit false

namespace Luffs.Runtime.TLSF

/-- Pure state used by the fixed parallel-array TLSF lowering. -/
structure Metadata where
  heads : List Nat
  next : List Nat
  previous : List Nat
deriving DecidableEq, Repr

def sentinel (state : Metadata) : Nat := state.next.length

/-- Exact pure effect of `tlsf_insert` in `stdlib/tlsf.luffs`. -/
def insert (state : Metadata) (bin block : Nat) : Option Metadata :=
  if bin ≥ state.heads.length then none
  else if block ≥ state.next.length then none
  else if block ≥ state.previous.length then none
  else
    let oldHead := state.heads[bin]?.getD 0
    let next := state.next.set block oldHead
    let previous := state.previous.set block state.next.length
    let previous :=
      if oldHead < state.previous.length then previous.set oldHead block
      else previous
    some { heads := state.heads.set bin block, next, previous }

/-- Array-tuple facade used by compiler-generated Luffs semantics. -/
def insertArrays (heads next previous : List Nat) (bin block : Nat) :
    Option (List Nat × List Nat × List Nat) :=
  match insert { heads, next, previous } bin block with
  | none => none
  | some state => some (state.heads, state.next, state.previous)

/-- Exact pure effect of `tlsf_remove` in `stdlib/tlsf.luffs`. -/
def remove (state : Metadata) (bin block : Nat) : Option Metadata :=
  if bin ≥ state.heads.length then none
  else if block ≥ state.next.length then none
  else if block ≥ state.previous.length then none
  else
    let successor := state.next[block]?.getD state.next.length
    let predecessor := state.previous[block]?.getD state.next.length
    let heads :=
      if predecessor ≥ state.next.length then state.heads.set bin successor
      else state.heads
    let next :=
      if predecessor < state.next.length then state.next.set predecessor successor
      else state.next
    let previous :=
      if successor < state.previous.length then state.previous.set successor predecessor
      else state.previous
    let next := next.set block state.next.length
    let previous := previous.set block state.previous.length
    some { heads, next, previous }

/-- Array-tuple facade used by compiler-generated removal semantics. -/
def removeArrays (heads next previous : List Nat) (bin block : Nat) :
    Option (List Nat × List Nat × List Nat) :=
  match remove { heads, next, previous } bin block with
  | none => none
  | some state => some (state.heads, state.next, state.previous)

def linked (state : Metadata) : Nat → List Nat → Prop
  | _, [] => True
  | expectedPrevious, block :: rest =>
      block < state.next.length ∧
      block < state.previous.length ∧
      state.previous[block]? = some expectedPrevious ∧
      state.next[block]? = some (rest.head?.getD state.next.length) ∧
      linked state block rest

/-- A logical bin chain is represented by the head table and intrusive links. -/
def RepresentsBin (state : Metadata) (bin : Nat) (chain : List Nat) : Prop :=
  bin < state.heads.length ∧
  state.next.length = state.previous.length ∧
  state.heads[bin]?.getD 0 = chain.head?.getD state.next.length ∧
  linked state state.next.length chain ∧
  chain.Nodup

theorem insert_result {state nextState : Metadata} {bin block : Nat}
    (hinsert : insert state bin block = some nextState) :
    bin < state.heads.length ∧ block < state.next.length ∧
      block < state.previous.length ∧
      nextState.heads = state.heads.set bin block ∧
      nextState.next = state.next.set block (state.heads[bin]?.getD 0) ∧
      nextState.previous =
        if state.heads[bin]?.getD 0 < state.previous.length then
          (state.previous.set block state.next.length).set (state.heads[bin]?.getD 0) block
        else state.previous.set block state.next.length := by
  unfold insert at hinsert
  split at hinsert <;> try contradiction
  next hbin =>
    split at hinsert <;> try contradiction
    next hblockNext =>
      split at hinsert <;> try contradiction
      next hblockPrevious =>
        dsimp at hinsert
        split at hinsert
        · simp only [Option.some.injEq] at hinsert
          subst nextState
          simp
          omega
        · simp only [Option.some.injEq] at hinsert
          subst nextState
          simp
          omega

theorem insert_links {state nextState : Metadata} {bin block : Nat}
    (hdistinct : state.heads[bin]?.getD 0 ≠ block)
    (hinsert : insert state bin block = some nextState) :
    nextState.heads[bin]? = some block ∧
      nextState.next[block]? = some (state.heads[bin]?.getD 0) ∧
      nextState.previous[block]? = some state.next.length ∧
      (state.heads[bin]?.getD 0 < state.previous.length →
        nextState.previous[state.heads[bin]?.getD 0]? = some block) := by
  have hresult := insert_result hinsert
  rcases hresult with ⟨hbin, hblockNext, hblockPrevious, hheads, hnext, hprevious⟩
  unfold insert at hinsert
  simp only [Nat.not_le.mpr hbin, Nat.not_le.mpr hblockNext,
    Nat.not_le.mpr hblockPrevious, if_false] at hinsert
  split at hinsert
  next holdHead =>
    simp only [Option.some.injEq] at hinsert
    subst nextState
    refine ⟨by simp [hbin], by simp [hblockNext], ?_, ?_⟩
    · simp [hdistinct, hblockPrevious]
    · intro
      simp [holdHead]
  next holdHead =>
    simp only [Option.some.injEq] at hinsert
    subst nextState
    refine ⟨by simp [hbin], by simp [hblockNext], by simp [hblockPrevious], ?_⟩
    intro hin
    exact (holdHead hin).elim

theorem insert_preserves_lengths {state nextState : Metadata} {bin block : Nat}
    (hinsert : insert state bin block = some nextState) :
    nextState.heads.length = state.heads.length ∧
      nextState.next.length = state.next.length ∧
      nextState.previous.length = state.previous.length := by
  unfold insert at hinsert
  split at hinsert <;> try contradiction
  next =>
    split at hinsert <;> try contradiction
    next =>
      split at hinsert <;> try contradiction
      next =>
        dsimp at hinsert
        split at hinsert
        · simp only [Option.some.injEq] at hinsert
          subst nextState
          simp
        · simp only [Option.some.injEq] at hinsert
          subst nextState
          simp

theorem linked_congr {state nextState : Metadata} {expectedPrevious : Nat}
    {chain : List Nat}
    (hnextLength : nextState.next.length = state.next.length)
    (hpreviousLength : nextState.previous.length = state.previous.length)
    (hnext : ∀ node ∈ chain, nextState.next[node]? = state.next[node]?)
    (hprevious : ∀ node ∈ chain,
      nextState.previous[node]? = state.previous[node]?)
    (hlinked : linked state expectedPrevious chain) :
    linked nextState expectedPrevious chain := by
  induction chain generalizing expectedPrevious with
  | nil => trivial
  | cons head tail ih =>
    simp only [linked] at hlinked ⊢
    rcases hlinked with ⟨hheadNext, hheadPrevious, hprev, hnxt, htail⟩
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · rw [hprevious head (by simp)]
      exact hprev
    · rw [hnext head (by simp), hnextLength]
      exact hnxt
    · apply ih
      · intro node hmem
        exact hnext node (by simp [hmem])
      · intro node hmem
        exact hprevious node (by simp [hmem])
      · exact htail

theorem insert_represents {state nextState : Metadata} {bin block : Nat}
    {chain : List Nat} (hrep : RepresentsBin state bin chain)
    (hfresh : block ∉ chain)
    (hinsert : insert state bin block = some nextState) :
    RepresentsBin nextState bin (block :: chain) := by
  rcases hrep with ⟨hbin, hlens, hhead, hlinked, hnodup⟩
  have hresult := insert_result hinsert
  rcases hresult with
    ⟨_, hblockNext, hblockPrevious, hheads, hnextState, hpreviousState⟩
  have hlengths := insert_preserves_lengths hinsert
  have hheadDistinct : state.heads[bin]?.getD 0 ≠ block := by
    rw [hhead]
    cases chain with
    | nil =>
      simp
      omega
    | cons head rest =>
      simp only [List.head?_cons, Option.getD_some]
      intro heq
      apply hfresh
      simp [heq]
  have hlinks := insert_links hheadDistinct hinsert
  refine ⟨by simpa [hlengths.1] using hbin, by omega, ?_, ?_,
    List.nodup_cons.2 ⟨hfresh, hnodup⟩⟩
  · simp [hlinks.1]
  · simp only [linked]
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · rw [hlengths.2.1]
      exact hlinks.2.2.1
    · rw [hlinks.2.1, hhead, hlengths.2.1]
    · cases chain with
      | nil => trivial
      | cons head rest =>
        simp only [List.head?_cons, Option.getD_some] at hhead
        simp only [linked] at hlinked
        rcases hlinked with ⟨hheadNext, hheadPrevious, hprev, hnxt, htail⟩
        have holdHead : state.heads[bin]?.getD 0 < state.previous.length := by
          simpa [hhead]
        have hheadBack := hlinks.2.2.2 holdHead
        rw [hhead] at hheadBack
        simp only [linked]
        refine ⟨by omega, by omega, hheadBack, ?_, ?_⟩
        · rw [hnextState]
          rw [List.getElem?_set_ne]
          · simpa using hnxt
          · intro heq
            apply hheadDistinct
            rw [hhead]
            exact heq.symm
        · apply linked_congr hlengths.2.1 hlengths.2.2
          · intro node hmem
            rw [hnextState]
            have hne : node ≠ block := by
              intro heq
              apply hfresh
              rw [← heq]
              simp [hmem]
            rw [List.getElem?_set_ne (Ne.symm hne)]
          · intro node hmem
            rw [hpreviousState]
            have hnodeBlock : node ≠ block := by
              intro heq
              apply hfresh
              rw [← heq]
              simp [hmem]
            have hnodeHead : node ≠ head := by
              intro heq
              exact (List.nodup_cons.mp hnodup).1 (by simpa [heq] using hmem)
            simp only [holdHead, if_true]
            rw [hhead]
            rw [List.getElem?_set_ne (Ne.symm hnodeHead),
              List.getElem?_set_ne (Ne.symm hnodeBlock)]
          · exact htail

theorem remove_result {state nextState : Metadata} {bin block : Nat}
    (hremove : remove state bin block = some nextState) :
    bin < state.heads.length ∧ block < state.next.length ∧
      block < state.previous.length := by
  unfold remove at hremove
  split at hremove <;> try contradiction
  next hbin =>
    split at hremove <;> try contradiction
    next hnext =>
      split at hremove <;> try contradiction
      next hprevious =>
        exact ⟨by omega, by omega, by omega⟩

theorem remove_preserves_lengths {state nextState : Metadata} {bin block : Nat}
    (hremove : remove state bin block = some nextState) :
    nextState.heads.length = state.heads.length ∧
      nextState.next.length = state.next.length ∧
      nextState.previous.length = state.previous.length := by
  unfold remove at hremove
  split at hremove <;> try contradiction
  next =>
    split at hremove <;> try contradiction
    next =>
      split at hremove <;> try contradiction
      next =>
        dsimp at hremove
        split at hremove <;> split at hremove <;> split at hremove <;>
          simp only [Option.some.injEq] at hremove
        all_goals subst nextState
        all_goals simp

theorem remove_detaches {state nextState : Metadata} {bin block : Nat}
    (hremove : remove state bin block = some nextState) :
    nextState.next[block]? = some state.next.length ∧
      nextState.previous[block]? = some state.previous.length := by
  have hbounds := remove_result hremove
  rcases hbounds with ⟨hbin, hblockNext, hblockPrevious⟩
  unfold remove at hremove
  simp only [Nat.not_le.mpr hbin, Nat.not_le.mpr hblockNext,
    Nat.not_le.mpr hblockPrevious, if_false] at hremove
  split at hremove <;> split at hremove <;> split at hremove <;>
    simp only [Option.some.injEq] at hremove
  all_goals subst nextState
  all_goals simp_all

theorem remove_front_complete {state : Metadata} {bin block : Nat}
    {rest : List Nat} (hrep : RepresentsBin state bin (block :: rest)) :
    ∃ nextState, remove state bin block = some nextState ∧
      RepresentsBin nextState bin rest ∧
      nextState.next[block]? = some state.next.length ∧
      nextState.previous[block]? = some state.previous.length := by
  rcases hrep with ⟨hbin, hlens, hhead, hlinked, hnodup⟩
  simp only [linked] at hlinked
  rcases hlinked with ⟨hblockNext, hblockPrevious, hprev, hnxt, htail⟩
  have hheadValue : state.heads[bin]?.getD 0 = block := by
    simpa using hhead
  have hprevValue : state.previous[block]?.getD state.next.length =
      state.next.length := by
    simp [hprev]
  have hnextValue : state.next[block]?.getD state.next.length =
      rest.head?.getD state.next.length := by
    simp [hnxt]
  unfold remove
  simp only [Nat.not_le.mpr hbin, Nat.not_le.mpr hblockNext,
    Nat.not_le.mpr hblockPrevious, if_false, hprevValue]
  simp only [ge_iff_le]
  simp
  cases rest with
  | nil =>
    simp only [List.head?_nil, Option.getD_none] at hnextValue
    have hsuccessorOut : ¬ state.next.length < state.previous.length := by omega
    simp only [hnextValue, hsuccessorOut, if_false]
    refine ⟨?_, ?_, ?_⟩
    · simp [RepresentsBin, linked, hbin, hlens]
    · simp [hblockNext]
    · simp [hblockPrevious]
  | cons successor tail =>
    simp only [List.head?_cons, Option.getD_some] at hnextValue
    simp only [linked] at htail
    rcases htail with
      ⟨hsuccessorNext, hsuccessorPrevious, hsuccessorPrev, hsuccessorNxt,
        htailLinked⟩
    have hsuccessorIn : successor < state.previous.length := hsuccessorPrevious
    simp only [hnextValue, hsuccessorIn, if_true]
    let nextState : Metadata := {
      heads := state.heads.set bin successor
      next := state.next.set block state.next.length
      previous := (state.previous.set successor state.next.length).set
        block state.previous.length
    }
    change RepresentsBin nextState bin (successor :: tail) ∧
      nextState.next[block]? = some state.next.length ∧
      nextState.previous[block]? = some state.previous.length
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨by simp [nextState, hbin], by simp [nextState, hlens],
        by simp [nextState, hbin], ?_, (List.nodup_cons.mp hnodup).2⟩
      simp only [linked]
      have hsuccessorBlock : successor ≠ block := by
        intro heq
        exact (List.nodup_cons.mp hnodup).1 (by simp [heq])
      refine ⟨by simp [nextState, hsuccessorNext],
        by simp [nextState, hsuccessorPrevious], ?_, ?_, ?_⟩
      · dsimp [nextState]
        rw [List.getElem?_set_ne (Ne.symm hsuccessorBlock),
          List.getElem?_set_self hsuccessorPrevious]
        simp
      · rw [show nextState.next = state.next.set block state.next.length from rfl,
          List.getElem?_set_ne (Ne.symm hsuccessorBlock)]
        simpa [nextState] using hsuccessorNxt
      · refine linked_congr (state := state) (nextState := nextState)
          (by simp [nextState]) (by simp [nextState]) ?_ ?_ htailLinked
        · intro node hmem
          have hnodeBlock : node ≠ block := by
            intro heq
            apply (List.nodup_cons.mp hnodup).1
            rw [← heq]
            simp [hmem]
          simp [nextState, List.getElem?_set_ne (Ne.symm hnodeBlock)]
        · intro node hmem
          have hnodeBlock : node ≠ block := by
            intro heq
            apply (List.nodup_cons.mp hnodup).1
            rw [← heq]
            simp [hmem]
          have hnodeSuccessor : node ≠ successor := by
            exact fun heq => (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
              (by simpa [heq] using hmem)
          simp [nextState, List.getElem?_set_ne (Ne.symm hnodeBlock),
            List.getElem?_set_ne (Ne.symm hnodeSuccessor)]
    · dsimp [nextState]
      simp [hblockNext]
    · dsimp [nextState]
      simp [hblockPrevious]

theorem remove_second_complete {state : Metadata} {bin head block : Nat}
    {rest : List Nat} (hrep : RepresentsBin state bin (head :: block :: rest)) :
    ∃ nextState, remove state bin block = some nextState ∧
      nextState.heads = state.heads ∧
      nextState.next =
        (state.next.set head (rest.head?.getD state.next.length)).set
          block state.next.length ∧
      nextState.previous =
        (if rest.head?.getD state.next.length < state.previous.length then
          state.previous.set (rest.head?.getD state.next.length) head
        else state.previous).set block state.previous.length ∧
      nextState.next[head]? = some (rest.head?.getD state.next.length) ∧
      nextState.next[block]? = some state.next.length ∧
      nextState.previous[block]? = some state.previous.length ∧
      (rest.head?.getD state.next.length < state.previous.length →
        nextState.previous[rest.head?.getD state.next.length]? = some head) := by
  rcases hrep with ⟨hbin, hlens, hbinHead, hlinked, hnodup⟩
  simp only [linked] at hlinked
  rcases hlinked with ⟨hheadNext, hheadPrevious, hheadPrev, hheadNxt,
    hblockLinked⟩
  rcases hblockLinked with ⟨hblockNext, hblockPrevious, hblockPrev,
    hblockNxt, htail⟩
  have hpredecessor : state.previous[block]?.getD state.next.length = head := by
    simp [hblockPrev]
  have hsuccessor : state.next[block]?.getD state.next.length =
      rest.head?.getD state.next.length := by
    simp [hblockNxt]
  have hheadBlock : head ≠ block := by
    intro heq
    exact (List.nodup_cons.mp hnodup).1 (by simp [heq])
  unfold remove
  simp only [Nat.not_le.mpr hbin, Nat.not_le.mpr hblockNext,
    Nat.not_le.mpr hblockPrevious, if_false, hpredecessor,
    Nat.not_le.mpr hheadNext, hheadNext, hsuccessor, if_true]
  by_cases hsuccessorIn : rest.head?.getD state.next.length < state.previous.length
  · simp only [hsuccessorIn, if_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [List.getElem?_set_ne (Ne.symm hheadBlock),
        List.getElem?_set_self hheadNext]
    · simp [hblockNext]
    · simp [hblockPrevious]
    · intro
      by_cases hsuccessorBlock : rest.head?.getD state.next.length = block
      · exfalso
        cases rest with
        | nil => simp at hsuccessorBlock; omega
        | cons successor tail =>
          simp only [List.head?_cons, Option.getD_some] at hsuccessorBlock
          apply (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
          simp [hsuccessorBlock]
      · change (((state.previous.set (rest.head?.getD state.next.length) head).set
            block state.previous.length)[rest.head?.getD state.next.length]?) = some head
        rw [List.getElem?_set_ne (Ne.symm hsuccessorBlock),
          List.getElem?_set_self hsuccessorIn]
  · simp only [hsuccessorIn, if_false]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [List.getElem?_set_ne (Ne.symm hheadBlock),
        List.getElem?_set_self hheadNext]
    · simp [hblockNext]
    · simp [hblockPrevious]
    · intro hin
      exact hin.elim

end Luffs.Runtime.TLSF
