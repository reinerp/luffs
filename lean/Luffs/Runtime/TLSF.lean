import Luffs.Allocator.TLSF.FreeList
import Luffs.Allocator.TLSF.Bitmap

set_option autoImplicit false

namespace Luffs.Runtime.TLSF

open Luffs.Allocator.TLSF

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

/-- Exact list semantics of the current linear `tlsf_find_fit` fallback. -/
def findFit (sizes : List Nat) (flags : List (Fin 256))
    (request : Nat) : Option Nat :=
  match sizes, flags with
  | size :: moreSizes, flag :: moreFlags =>
      if flag.val ≠ 0 ∧ request ≤ size then some 0
      else (findFit moreSizes moreFlags request).map Nat.succ
  | _, _ => none

theorem findFit_sound {sizes : List Nat} {flags : List (Fin 256)}
    {request index : Nat}
    (hfind : findFit sizes flags request = some index) :
    ∃ size flag, sizes[index]? = some size ∧ flags[index]? = some flag ∧
      flag.val ≠ 0 ∧ request ≤ size := by
  induction sizes generalizing flags index with
  | nil => cases flags <;> simp [findFit] at hfind
  | cons size moreSizes ih =>
    cases flags with
    | nil => simp [findFit] at hfind
    | cons flag moreFlags =>
      by_cases hsuitable : flag.val ≠ 0 ∧ request ≤ size
      · simp [findFit, hsuitable] at hfind
        subst index
        exact ⟨size, flag, by simp [hsuitable]⟩
      · simp only [findFit, hsuitable, if_false] at hfind
        obtain ⟨tailIndex, htail, rfl⟩ := Option.map_eq_some_iff.mp hfind
        obtain ⟨foundSize, foundFlag, hsize, hflag, hnonzero, hbytes⟩ := ih htail
        exact ⟨foundSize, foundFlag, by simp [hsize, hflag, hnonzero, hbytes]⟩

theorem findFit_complete {sizes : List Nat} {flags : List (Fin 256)}
    {request index size : Nat} {flag : Fin 256}
    (hsize : sizes[index]? = some size) (hflag : flags[index]? = some flag)
    (hnonzero : flag.val ≠ 0) (hbytes : request ≤ size) :
    ∃ found, findFit sizes flags request = some found := by
  induction sizes generalizing flags index with
  | nil => simp at hsize
  | cons head moreSizes ih =>
    cases flags with
    | nil => simp at hflag
    | cons headFlag moreFlags =>
      cases index with
      | zero =>
        simp at hsize hflag
        subst head
        subst headFlag
        exact ⟨0, by simp [findFit, hnonzero, hbytes]⟩
      | succ tailIndex =>
        simp only [List.getElem?_cons_succ] at hsize hflag
        by_cases hsuitable : headFlag.val ≠ 0 ∧ request ≤ head
        · exact ⟨0, by simp [findFit, hsuitable]⟩
        · obtain ⟨found, hfound⟩ := ih hsize hflag
          exact ⟨found + 1, by
            simp only [findFit, hsuitable, if_false, hfound, Option.map_some]⟩

def wordBits (word : BitVec 64) : List Bool :=
  List.ofFn fun bit : Fin 64 => word.getLsbD bit.val

def bitmapBits : List (BitVec 64) → List Bool
  | [] => []
  | word :: rest => wordBits word ++ bitmapBits rest

/-- Flat semantics of the four-word nonempty-bin bitmap search. -/
def findNonemptyBin (words : List (BitVec 64)) (start : Nat) : Option Nat :=
  firstSetFrom (bitmapBits words) start

theorem wordBits_length (word : BitVec 64) : (wordBits word).length = 64 := by
  simp [wordBits]

theorem wordBits_get (word : BitVec 64) (index : Nat) (hindex : index < 64) :
    (wordBits word)[index]? = some (word.getLsbD index) := by
  simp only [wordBits, List.getElem?_ofFn, hindex, dite_true]

theorem firstTrueIndex_wordBits_ctz {word : BitVec 64} (hnonzero : word ≠ 0) :
    firstTrueIndex (wordBits word) = some word.ctz.toNat := by
  have hctzBound : word.ctz.toNat < 64 := by
    exact (BitVec.ctz_lt_iff_ne_zero (x := word)).2 hnonzero
  have hctzBit : (wordBits word)[word.ctz.toNat]? = some true := by
    rw [wordBits_get word word.ctz.toNat hctzBound]
    exact congrArg some (BitVec.getLsbD_true_ctz_of_ne_zero hnonzero)
  obtain ⟨found, hfound⟩ := firstTrueIndex_complete hctzBit
  have hfoundBit := firstTrueIndex_sound hfound
  have hfoundBound := firstTrueIndex_lt_length hfound
  have hnotBefore : ¬ found < word.ctz.toNat := by
    intro hbefore
    have hfalse := BitVec.getLsbD_false_of_lt_ctz (x := word) hbefore
    have hfound64 : found < 64 := by simpa [wordBits_length] using hfoundBound
    rw [wordBits_get word found hfound64, hfalse] at hfoundBit
    contradiction
  have hnotAfter : ¬ word.ctz.toNat < found := by
    intro hafter
    have hfalse := firstTrueIndex_minimal hfound hafter
    rw [hctzBit] at hfalse
    contradiction
  have : found = word.ctz.toNat := by omega
  simpa [this] using hfound

def maskFrom (bit : Nat) : BitVec 64 := BitVec.allOnes 64 <<< bit

theorem maskFrom_getLsbD (bit index : Nat) :
    (maskFrom bit).getLsbD index = decide (bit ≤ index ∧ index < 64) := by
  simp only [maskFrom, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases hindex : index < 64 <;> by_cases hbit : bit ≤ index
  · have : index - bit < 64 := by omega
    simp [hindex, hbit, this]
  · simp [hindex, hbit]
  · simp [hindex]
  · simp [hindex]

theorem maskedWord_getLsbD (word : BitVec 64) (bit index : Nat) :
    (word &&& maskFrom bit).getLsbD index =
      if bit ≤ index ∧ index < 64 then word.getLsbD index else false := by
  rw [BitVec.getLsbD_and, maskFrom_getLsbD]
  split <;> simp_all

theorem wordBits_masked_get (word : BitVec 64) (bit index : Nat)
    (hindex : index < 64) :
    (wordBits (word &&& maskFrom bit))[index]? =
      some (if bit ≤ index then word.getLsbD index else false) := by
  rw [wordBits_get _ index hindex, maskedWord_getLsbD]
  simp [hindex]

/-- The Rust lowering for searching within the first bitmap word—masking away
the prefix and taking `trailing_zeros`—implements the logical suffix search. -/
theorem firstSetFrom_wordBits_eq_masked_ctz (word : BitVec 64) (bit : Nat)
    (hnonzero : word &&& maskFrom bit ≠ 0) :
    firstSetFrom (wordBits word) bit =
      some (word &&& maskFrom bit).ctz.toNat := by
  let masked := word &&& maskFrom bit
  have hctzBound : masked.ctz.toNat < 64 := by
    exact (BitVec.ctz_lt_iff_ne_zero (x := masked)).2 hnonzero
  have hmaskedTrue : masked.getLsbD masked.ctz.toNat = true :=
    BitVec.getLsbD_true_ctz_of_ne_zero hnonzero
  have hcondition : bit ≤ masked.ctz.toNat ∧ masked.ctz.toNat < 64 := by
    by_cases hcondition : bit ≤ masked.ctz.toNat ∧ masked.ctz.toNat < 64
    · exact hcondition
    · have hmaskedFalse : masked.getLsbD masked.ctz.toNat = false := by
        simpa [masked, hcondition] using
          maskedWord_getLsbD word bit masked.ctz.toNat
      simp [hmaskedFalse] at hmaskedTrue
  have hstart : bit ≤ masked.ctz.toNat := hcondition.1
  have horiginalTrue : word.getLsbD masked.ctz.toNat = true := by
    have hmaskedFormula := maskedWord_getLsbD word bit masked.ctz.toNat
    rw [← show word &&& maskFrom bit = masked from rfl] at hmaskedFormula
    have hboth :
        (bit ≤ masked.ctz.toNat ∧ masked.ctz.toNat < 64) ∧
          word.getLsbD masked.ctz.toNat = true := by
      simpa [masked] using hmaskedFormula.symm.trans hmaskedTrue
    exact hboth.2
  have hwordBit : (wordBits word)[masked.ctz.toNat]? = some true := by
    rw [wordBits_get word masked.ctz.toNat hctzBound, horiginalTrue]
  obtain ⟨found, hfound⟩ := firstSetFrom_complete hstart hwordBit
  have hfoundFacts := firstSetFrom_sound hfound
  have hnotBefore : ¬ found < masked.ctz.toNat := by
    intro hbefore
    have hmaskedFalse := BitVec.getLsbD_false_of_lt_ctz
      (x := masked) hbefore
    have hfoundBound : found < 64 := by
      simpa [wordBits_length] using hfoundFacts.2.1
    have hfoundOriginal : word.getLsbD found = true := by
      have hget := hfoundFacts.2.2
      rw [wordBits_get word found hfoundBound] at hget
      exact Option.some.inj hget
    have hmaskedTrueAtFound : masked.getLsbD found = true := by
      dsimp [masked]
      rw [maskedWord_getLsbD]
      simp [hfoundFacts.1, hfoundBound, hfoundOriginal]
    simp [hmaskedFalse] at hmaskedTrueAtFound
  have hnotAfter : ¬ masked.ctz.toNat < found := by
    intro hafter
    have hfalse := firstSetFrom_minimal hfound hstart hafter
    rw [hwordBit] at hfalse
    contradiction
  have : found = masked.ctz.toNat := by omega
  simpa [masked, this] using hfound

theorem bitmapBits_length (words : List (BitVec 64)) :
    (bitmapBits words).length = words.length * 64 := by
  induction words with
  | nil => rfl
  | cons word rest => simp [bitmapBits, wordBits_length, *]; omega

theorem findNonemptyBin_sound {words : List (BitVec 64)} {start found : Nat}
    (hfind : findNonemptyBin words start = some found) :
    start ≤ found ∧ found < words.length * 64 ∧
      (bitmapBits words)[found]? = some true := by
  have hsound := firstSetFrom_sound hfind
  simpa [findNonemptyBin, bitmapBits_length] using hsound

theorem findNonemptyBin_bounded {words : List (BitVec 64)} {start found : Nat}
    (hwords : words.length ≤ 4)
    (hfind : findNonemptyBin words start = some found) : found < 256 := by
  have hsound := findNonemptyBin_sound hfind
  omega

theorem findNonemptyBin_complete {words : List (BitVec 64)} {start index : Nat}
    (hstart : start ≤ index)
    (hset : (bitmapBits words)[index]? = some true) :
    ∃ found, findNonemptyBin words start = some found := by
  exact firstSetFrom_complete hstart hset

theorem findNonemptyBin_minimal {words : List (BitVec 64)} {start found earlier : Nat}
    (hfind : findNonemptyBin words start = some found)
    (hstart : start ≤ earlier) (hearlier : earlier < found) :
    (bitmapBits words)[earlier]? = some false := by
  exact firstSetFrom_minimal hfind hstart hearlier

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

theorem remove_second_represents {state : Metadata} {bin head block : Nat}
    {rest : List Nat} (hrep : RepresentsBin state bin (head :: block :: rest)) :
    ∃ nextState, remove state bin block = some nextState ∧
      RepresentsBin nextState bin (head :: rest) := by
  obtain ⟨nextState, hremove, hheads, hnextState, hpreviousState,
    hheadNextValue, _, _, hsuccessorPrevious⟩ := remove_second_complete hrep
  rcases hrep with ⟨hbin, hlens, hbinHead, hlinked, hnodup⟩
  have hlengths := remove_preserves_lengths hremove
  simp only [linked] at hlinked
  rcases hlinked with ⟨hheadNext, hheadPrevious, hheadPrev, _, hblockLinked⟩
  rcases hblockLinked with ⟨_, _, _, _, htail⟩
  have hheadBlock : head ≠ block := by
    intro heq
    exact (List.nodup_cons.mp hnodup).1 (by simp [heq])
  have hheadNotRest : head ∉ rest := by
    intro hmem
    exact (List.nodup_cons.mp hnodup).1 (by simp [hmem])
  have hblockNotRest : block ∉ rest :=
    (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
  have hrestNodup : rest.Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).2
  refine ⟨nextState, hremove, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · omega
  · omega
  · rw [hheads]
    simpa using hbinHead
  · simp only [linked]
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · rw [hpreviousState]
      cases rest with
      | nil =>
        rw [show ([].head?.getD state.next.length) = state.next.length by simp]
        have hout : ¬ state.next.length < state.previous.length := by omega
        simp only [hout, if_false]
        rw [List.getElem?_set_ne (Ne.symm hheadBlock), hlengths.2.1]
        exact hheadPrev
      | cons successor tail =>
        simp only [List.head?_cons, Option.getD_some]
        have hsuccessorBound : successor < state.previous.length := by
          simp only [linked] at htail
          exact htail.2.1
        have hheadSuccessor : head ≠ successor := by
          exact fun heq => hheadNotRest (by simp [heq])
        simp only [hsuccessorBound, if_true]
        rw [List.getElem?_set_ne (Ne.symm hheadBlock),
          List.getElem?_set_ne (Ne.symm hheadSuccessor), hlengths.2.1]
        exact hheadPrev
    · rw [hlengths.2.1]
      exact hheadNextValue
    · cases rest with
      | nil => trivial
      | cons successor tail =>
        simp only [linked] at htail ⊢
        rcases htail with ⟨hsuccessorNext, hsuccessorPreviousBound, _,
          hsuccessorNxt, htailLinked⟩
        have hsuccessorHead : successor ≠ head := by
          exact fun heq => hheadNotRest (by simp [heq])
        have hsuccessorBlock : successor ≠ block := by
          exact fun heq => hblockNotRest (by simp [heq])
        refine ⟨by omega, by omega, ?_, ?_, ?_⟩
        · exact hsuccessorPrevious (by simpa)
        · rw [hnextState, List.getElem?_set_ne (Ne.symm hsuccessorBlock),
            List.getElem?_set_ne (Ne.symm hsuccessorHead)]
          simpa using hsuccessorNxt
        · apply linked_congr (state := state) (nextState := nextState)
            hlengths.2.1 hlengths.2.2
          · intro node hmem
            have hnodeHead : head ≠ node := by
              intro heq
              exact hheadNotRest
                (List.mem_cons_of_mem successor (heq.symm ▸ hmem))
            have hnodeBlock : block ≠ node := by
              intro heq
              exact hblockNotRest
                (List.mem_cons_of_mem successor (heq.symm ▸ hmem))
            rw [hnextState, List.getElem?_set_ne hnodeBlock,
              List.getElem?_set_ne hnodeHead]
          · intro node hmem
            rw [hpreviousState]
            simp only [List.head?_cons, Option.getD_some,
              hsuccessorPreviousBound, if_true]
            have hnodeBlock : block ≠ node := by
              intro heq
              exact hblockNotRest
                (List.mem_cons_of_mem successor (heq.symm ▸ hmem))
            have hnodeSuccessor : successor ≠ node := by
              intro heq
              exact (List.nodup_cons.mp hrestNodup).1 (heq.symm ▸ hmem)
            rw [List.getElem?_set_ne hnodeBlock,
              List.getElem?_set_ne hnodeSuccessor]
          · exact htailLinked
  · exact List.nodup_cons.mpr ⟨hheadNotRest, hrestNodup⟩

end Luffs.Runtime.TLSF
