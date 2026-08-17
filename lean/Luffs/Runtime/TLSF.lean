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
    let oldHead := state.heads[bin]!
    let next := state.next.set block oldHead
    let previous := state.previous.set block state.next.length
    let previous :=
      if oldHead < state.previous.length then previous.set oldHead block
      else previous
    some { heads := state.heads.set bin block, next, previous }

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
  state.heads[bin]! = chain.head?.getD state.next.length ∧
  linked state state.next.length chain ∧
  chain.Nodup

theorem insert_result {state nextState : Metadata} {bin block : Nat}
    (hinsert : insert state bin block = some nextState) :
    bin < state.heads.length ∧ block < state.next.length ∧
      block < state.previous.length ∧
      nextState.heads = state.heads.set bin block ∧
      nextState.next = state.next.set block state.heads[bin]! := by
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
    (hdistinct : state.heads[bin]! ≠ block)
    (hinsert : insert state bin block = some nextState) :
    nextState.heads[bin]? = some block ∧
      nextState.next[block]? = some state.heads[bin]! ∧
      nextState.previous[block]? = some state.next.length ∧
      (state.heads[bin]! < state.previous.length →
        nextState.previous[state.heads[bin]!]? = some block) := by
  have hresult := insert_result hinsert
  rcases hresult with ⟨hbin, hblockNext, hblockPrevious, hheads, hnext⟩
  unfold insert at hinsert
  simp only [Nat.not_le.mpr hbin, Nat.not_le.mpr hblockNext,
    Nat.not_le.mpr hblockPrevious, if_false] at hinsert
  split at hinsert
  next holdHead =>
    simp only [List.getElem!_eq_getElem?_getD, Nat.default_eq_zero] at holdHead hdistinct
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

end Luffs.Runtime.TLSF
