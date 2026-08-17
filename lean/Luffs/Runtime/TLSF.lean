import Luffs.Allocator.TLSF.FreeList
import Luffs.Allocator.TLSF.Bitmap
import Luffs.Allocator.TLSF.Bins
import Luffs.Allocator.TLSF.Dealloc

set_option autoImplicit false

namespace Luffs.Runtime.TLSF

open Luffs.Allocator.TLSF
open Luffs.Allocator.TLSF.Bins

def encodeSizeClass (cls : SizeClass) : Nat :=
  cls.fl.val * secondLevelCount + cls.sl.val

/-- The 64-bit executable mapping-down classifier used by free-list insertion.
The source computes this with `leading_zeros`, shifts, and checked arithmetic;
its source-shape refinement declaration targets this proof-oriented form. -/
def classifySizeBin (size : Nat) : Option Nat :=
  if hsize : 0 < size then
    if hmax : size < 2 ^ firstLevelCount then
      some (encodeSizeClass (sizeClass size hsize hmax))
    else none
  else none

theorem classifySizeBin_result {size encoded : Nat}
    (hclass : classifySizeBin size = some encoded) :
    ∃ (hsize : 0 < size) (hmax : size < 2 ^ firstLevelCount),
      encoded = encodeSizeClass (sizeClass size hsize hmax) ∧ encoded < 2048 := by
  unfold classifySizeBin at hclass
  split at hclass <;> try contradiction
  next hsize =>
    split at hclass <;> try contradiction
    next hmax =>
      simp only [Option.some.injEq] at hclass
      subst encoded
      refine ⟨hsize, hmax, rfl, ?_⟩
      have hfl := (sizeClass size hsize hmax).fl.isLt
      have hsl := (sizeClass size hsize hmax).sl.isLt
      simp only [encodeSizeClass, firstLevelCount, secondLevelCount] at hfl hsl ⊢
      omega

theorem classifySizeBin_refines_block {block : Block} {encoded : Nat}
    (hclass : classifySizeBin block.bytes = some encoded) :
    ∃ cls, Bins.classifyBlock? block = some cls ∧
      encoded = encodeSizeClass cls := by
  obtain ⟨hsize, hmax, hencoded, _⟩ := classifySizeBin_result hclass
  let cls := sizeClass block.bytes hsize hmax
  refine ⟨cls, ?_, hencoded⟩
  simp [Bins.classifyBlock?, cls, hsize, hmax]

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

def setWordBit (bitmap : BitVec 64) (bit : Nat) : BitVec 64 :=
  bitmap ||| (BitVec.ofNat 64 1 <<< bit)

def setSecondBit (bitmap : BitVec 32) (bit : Nat) : BitVec 32 :=
  bitmap ||| (BitVec.ofNat 32 1 <<< bit)

structure InsertClassResult where
  second : List (BitVec 32)
  first : BitVec 64
  heads : List Nat
  next : List Nat
  previous : List Nat
deriving DecidableEq, Repr

/-- Exact effect of `tlsf_insert_class`: intrusive insertion followed by
setting the selected second- and first-level cache bits. -/
def insertClassArrays (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (bin block : Nat) :
    Option InsertClassResult :=
  if bin ≥ heads.length then none
  else
    let fl := bin / 32
    let sl := bin % 32
    if fl ≥ second.length then none
    else if block ≥ next.length then none
    else if block ≥ previous.length then none
    else
      match insert { heads, next, previous } bin block with
      | none => none
      | some metadata =>
          let oldSecond := second[fl]?.getD 0
          some {
            second := second.set fl (setSecondBit oldSecond sl)
            first := setWordBit first fl
            heads := metadata.heads
            next := metadata.next
            previous := metadata.previous }

theorem insertClassArrays_result
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : InsertClassResult}
    (hinsert : insertClassArrays second first heads next previous bin block =
      some result) :
    bin < heads.length ∧ bin / 32 < second.length ∧
      block < next.length ∧ block < previous.length ∧
      insert { heads, next, previous } bin block =
        some (Metadata.mk result.heads result.next result.previous) ∧
      result.second = second.set (bin / 32)
        (setSecondBit (second[bin / 32]?.getD 0) (bin % 32)) ∧
      result.first = setWordBit first (bin / 32) := by
  unfold insertClassArrays at hinsert
  split at hinsert <;> try contradiction
  next hbin =>
    dsimp only at hinsert
    split at hinsert <;> try contradiction
    next hfl =>
      split at hinsert <;> try contradiction
      next hnext =>
        split at hinsert <;> try contradiction
        next hprevious =>
          cases hmetadata : insert { heads, next, previous } bin block with
          | none => simp [hmetadata] at hinsert
          | some metadata =>
              simp only [hmetadata, Option.some.injEq] at hinsert
              subst result
              exact ⟨Nat.lt_of_not_ge hbin, Nat.lt_of_not_ge hfl,
                Nat.lt_of_not_ge hnext, Nat.lt_of_not_ge hprevious,
                rfl, rfl, rfl⟩

theorem setSecondBit_selected (bitmap : BitVec 32) {bit : Nat}
    (hbit : bit < 32) : (setSecondBit bitmap bit).getLsbD bit = true := by
  simp [setSecondBit, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, hbit]

theorem setWordBit_selected (bitmap : BitVec 64) {bit : Nat}
    (hbit : bit < 64) : (setWordBit bitmap bit).getLsbD bit = true := by
  simp [setWordBit, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, hbit]

theorem setSecondBit_getLsbD (bitmap : BitVec 32) (bit index : Nat) :
    (setSecondBit bitmap bit).getLsbD index =
      if index = bit ∧ index < 32 then true else bitmap.getLsbD index := by
  simp only [setSecondBit, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat]
  by_cases hindex : index < 32 <;> by_cases heq : index = bit
  · subst bit
    simp [hindex]
  · by_cases hbefore : index < bit
    · simp [hindex, heq, hbefore]
    · have htestFalse : Nat.testBit 1 (index - bit) = false := by
        cases htest : Nat.testBit 1 (index - bit) with
        | false => rfl
        | true =>
            have hzero := Nat.testBit_one_eq_true_iff_self_eq_zero.mp htest
            omega
      simp [hindex, heq, hbefore, htestFalse]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]

theorem setWordBit_getLsbD (bitmap : BitVec 64) (bit index : Nat) :
    (setWordBit bitmap bit).getLsbD index =
      if index = bit ∧ index < 64 then true else bitmap.getLsbD index := by
  simp only [setWordBit, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat]
  by_cases hindex : index < 64 <;> by_cases heq : index = bit
  · subst bit
    simp [hindex]
  · by_cases hbefore : index < bit
    · simp [hindex, heq, hbefore]
    · have htestFalse : Nat.testBit 1 (index - bit) = false := by
        cases htest : Nat.testBit 1 (index - bit) with
        | false => rfl
        | true =>
            have hzero := Nat.testBit_one_eq_true_iff_self_eq_zero.mp htest
            omega
      simp [hindex, heq, hbefore, htestFalse]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]

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

theorem removeArrays_result {heads next previous : List Nat} {bin block : Nat}
    {nextHeads nextLinks nextPrevious : List Nat}
    (hremove : removeArrays heads next previous bin block =
      some (nextHeads, nextLinks, nextPrevious)) :
    remove { heads, next, previous } bin block =
      some (Metadata.mk nextHeads nextLinks nextPrevious) := by
  unfold removeArrays at hremove
  cases hstate : remove { heads, next, previous } bin block with
  | none => simp [hstate] at hremove
  | some state =>
      simp only [hstate, Option.some.injEq] at hremove
      obtain ⟨rfl, rfl, rfl⟩ := hremove
      simpa using hstate

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

theorem firstSetFrom_wordBits_eq_none_of_masked_eq_zero
    (word : BitVec 64) (bit : Nat) (hzero : word &&& maskFrom bit = 0) :
    firstSetFrom (wordBits word) bit = none := by
  cases hfind : firstSetFrom (wordBits word) bit with
  | none => rfl
  | some found =>
    have hfoundFacts := firstSetFrom_sound hfind
    have hfoundBound : found < 64 := by
      simpa [wordBits_length] using hfoundFacts.2.1
    have horiginal : word.getLsbD found = true := by
      have hget := hfoundFacts.2.2
      rw [wordBits_get word found hfoundBound] at hget
      exact Option.some.inj hget
    have hmasked : (word &&& maskFrom bit).getLsbD found = true := by
      rw [maskedWord_getLsbD]
      simp [hfoundFacts.1, hfoundBound, horiginal]
    rw [hzero] at hmasked
    simp at hmasked

theorem firstTrueIndex_wordBits_zero :
    firstTrueIndex (wordBits (0 : BitVec 64)) = none := by
  native_decide

/-- Exact semantics of the subsequent-word Rust loop: zero words are skipped;
the first nonzero word is resolved with `trailing_zeros`. -/
def findNonzeroWords : List (BitVec 64) → Nat → Option Nat
  | [], _ => none
  | word :: rest, base =>
      if word = (0 : BitVec 64) then findNonzeroWords rest (base + 64)
      else some (base + word.ctz.toNat)

theorem findNonzeroWords_refines (words : List (BitVec 64)) (base : Nat) :
    findNonzeroWords words base =
      (firstTrueIndex (bitmapBits words)).map (base + ·) := by
  induction words generalizing base with
  | nil => simp [findNonzeroWords, bitmapBits, firstTrueIndex]
  | cons word rest ih =>
    rw [bitmapBits, firstTrueIndex_append]
    by_cases hzero : word = (0 : BitVec 64)
    · subst word
      rw [firstTrueIndex_wordBits_zero]
      simp only [findNonzeroWords, if_pos rfl, ih, Option.map_map]
      cases hrest : firstTrueIndex (bitmapBits rest) with
      | none => simp [hrest]
      | some offset =>
        simp only [hrest, Option.map_some]
        congr 1
        simp [wordBits_length, Function.comp_def]
        omega
    · rw [firstTrueIndex_wordBits_ctz hzero]
      rw [findNonzeroWords, if_neg hzero]
      rfl

theorem bitmapBits_length (words : List (BitVec 64)) :
    (bitmapBits words).length = words.length * 64 := by
  induction words with
  | nil => rfl
  | cons word rest => simp [bitmapBits, wordBits_length, *]; omega

theorem bitmapBits_drop (words : List (BitVec 64)) (count : Nat) :
    bitmapBits (words.drop count) =
      (bitmapBits words).drop (count * 64) := by
  induction words generalizing count with
  | nil => simp [bitmapBits]
  | cons word rest ih =>
    cases count with
    | zero => simp
    | succ count =>
      simp only [List.drop_succ_cons, bitmapBits]
      rw [ih]
      rw [Nat.succ_mul]
      symm
      calc
        (wordBits word ++ bitmapBits rest).drop (count * 64 + 64) =
            (wordBits word).drop (count * 64 + 64) ++
              (bitmapBits rest).drop ((count * 64 + 64) - 64) := by
                exact List.drop_append
        _ = (bitmapBits rest).drop (count * 64) := by
          have hsub : count * 64 + 64 - 64 = count * 64 := by omega
          simp [wordBits_length, hsub]

/-- Chunk-level semantics of the bounded word loop. It searches the first word
from the intra-word offset, then searches the remaining complete words. -/
def findNonemptyBinChunked (words : List (BitVec 64)) (start : Nat) : Option Nat :=
  let wordIndex := start / 64
  let bit := start % 64
  match words.drop wordIndex with
  | [] => none
  | word :: rest =>
      match firstSetFrom (wordBits word) bit with
      | some offset => some (wordIndex * 64 + offset)
      | none =>
          (firstTrueIndex (bitmapBits rest)).map
            ((wordIndex + 1) * 64 + ·)

/-- Exact arithmetic and control-flow semantics of the Luffs/Rust bitmap
lookup, including its masked first word and `ctz`-based subsequent-word loop. -/
def findNonemptyBinLowered (words : List (BitVec 64)) (start : Nat) : Option Nat :=
  let wordIndex := start / 64
  let bit := start % 64
  match words.drop wordIndex with
  | [] => none
  | word :: rest =>
      let masked := word &&& maskFrom bit
      if masked ≠ 0 then some (wordIndex * 64 + masked.ctz.toNat)
      else findNonzeroWords rest ((wordIndex + 1) * 64)

theorem findNonemptyBinLowered_eq_chunked
    (words : List (BitVec 64)) (start : Nat) :
    findNonemptyBinLowered words start = findNonemptyBinChunked words start := by
  unfold findNonemptyBinLowered findNonemptyBinChunked
  simp only
  cases hdrop : words.drop (start / 64) with
  | nil => rfl
  | cons word rest =>
    change
      (if word &&& maskFrom (start % 64) ≠ 0 then
          some (start / 64 * 64 + (word &&& maskFrom (start % 64)).ctz.toNat)
        else findNonzeroWords rest ((start / 64 + 1) * 64)) =
      match firstSetFrom (wordBits word) (start % 64) with
      | some offset => some (start / 64 * 64 + offset)
      | none =>
          (firstTrueIndex (bitmapBits rest)).map
            ((start / 64 + 1) * 64 + ·)
    by_cases hmasked : word &&& maskFrom (start % 64) = 0
    · rw [if_neg (not_not_intro hmasked),
        firstSetFrom_wordBits_eq_none_of_masked_eq_zero word _ hmasked,
        findNonzeroWords_refines]
    · rw [if_pos hmasked,
        firstSetFrom_wordBits_eq_masked_ctz word _ hmasked]

theorem findNonemptyBinChunked_refines (words : List (BitVec 64)) (start : Nat) :
    findNonemptyBinChunked words start = findNonemptyBin words start := by
  have hbit : start % 64 ≤ (wordBits (0 : BitVec 64)).length := by
    simp [wordBits_length]
    exact Nat.le_of_lt (Nat.mod_lt start (by omega))
  have hsplit : start = (start / 64) * 64 + start % 64 := by
    omega
  have hremainder : start % 64 < 64 := Nat.mod_lt start (by omega)
  have hquotient :
      ((start / 64) * 64 + start % 64) / 64 = start / 64 := by
    rw [Nat.mul_comm (start / 64) 64, Nat.mul_add_div (by omega)]
    simp [Nat.div_eq_of_lt hremainder]
  have hmodulo :
      ((start / 64) * 64 + start % 64) % 64 = start % 64 := by
    rw [Nat.mul_comm (start / 64) 64, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hremainder
  unfold findNonemptyBin
  rw [hsplit, firstSetFrom_add]
  rw [← bitmapBits_drop words (start / 64)]
  unfold findNonemptyBinChunked
  simp only [hquotient, hmodulo]
  cases hdrop : words.drop (start / 64) with
  | nil => simp [bitmapBits, firstSetFrom, firstTrueIndex]
  | cons word rest =>
    rw [bitmapBits]
    rw [firstSetFrom_append _ _ _ (by simpa [wordBits_length] using hbit)]
    cases hfirst : firstSetFrom (wordBits word) (start % 64) with
    | some offset => simp [hdrop, hfirst]
    | none =>
      simp only [hdrop, hfirst, Option.map_none, Option.map_map,
        List.length_append, wordBits_length]
      congr 1
      funext offset
      simp [Function.comp_def, hquotient]
      omega

theorem findNonemptyBinLowered_refines
    (words : List (BitVec 64)) (start : Nat) :
    findNonemptyBinLowered words start = findNonemptyBin words start := by
  rw [findNonemptyBinLowered_eq_chunked, findNonemptyBinChunked_refines]

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

def secondWordBits (word : BitVec 32) : List Bool :=
  List.ofFn fun bit : Fin 32 => word.getLsbD bit.val

def classBits : List (BitVec 32) → List Bool
  | [] => []
  | word :: rest => secondWordBits word ++ classBits rest

/-- Logical lookup over the actual TLSF 64 × 32 class space. -/
def findNonemptyClass (second : List (BitVec 32))
    (startFl startSl : Nat) : Option Nat :=
  firstSetFrom (classBits second) (startFl * 32 + startSl)

theorem secondWordBits_length (word : BitVec 32) :
    (secondWordBits word).length = 32 := by
  simp [secondWordBits]

theorem secondWordBits_get (word : BitVec 32) (index : Nat)
    (hindex : index < 32) :
    (secondWordBits word)[index]? = some (word.getLsbD index) := by
  simp only [secondWordBits, List.getElem?_ofFn, hindex, dite_true]

def maskFrom32 (bit : Nat) : BitVec 32 := BitVec.allOnes 32 <<< bit

theorem maskFrom32_getLsbD (bit index : Nat) :
    (maskFrom32 bit).getLsbD index = decide (bit ≤ index ∧ index < 32) := by
  simp only [maskFrom32, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases hindex : index < 32 <;> by_cases hbit : bit ≤ index
  · have : index - bit < 32 := by omega
    simp [hindex, hbit, this]
  · simp [hindex, hbit]
  · simp [hindex]
  · simp [hindex]

theorem maskedWord32_getLsbD (word : BitVec 32) (bit index : Nat) :
    (word &&& maskFrom32 bit).getLsbD index =
      if bit ≤ index ∧ index < 32 then word.getLsbD index else false := by
  rw [BitVec.getLsbD_and, maskFrom32_getLsbD]
  split <;> simp_all

theorem firstTrueIndex_secondWordBits_ctz {word : BitVec 32}
    (hnonzero : word ≠ 0) :
    firstTrueIndex (secondWordBits word) = some word.ctz.toNat := by
  have hctzBound : word.ctz.toNat < 32 := by
    exact (BitVec.ctz_lt_iff_ne_zero (x := word)).2 hnonzero
  have hctzBit : (secondWordBits word)[word.ctz.toNat]? = some true := by
    rw [secondWordBits_get word word.ctz.toNat hctzBound]
    exact congrArg some (BitVec.getLsbD_true_ctz_of_ne_zero hnonzero)
  obtain ⟨found, hfound⟩ := firstTrueIndex_complete hctzBit
  have hfoundBit := firstTrueIndex_sound hfound
  have hfoundBound := firstTrueIndex_lt_length hfound
  have hnotBefore : ¬ found < word.ctz.toNat := by
    intro hbefore
    have hfalse := BitVec.getLsbD_false_of_lt_ctz (x := word) hbefore
    have hfound32 : found < 32 := by
      simpa [secondWordBits_length] using hfoundBound
    rw [secondWordBits_get word found hfound32, hfalse] at hfoundBit
    contradiction
  have hnotAfter : ¬ word.ctz.toNat < found := by
    intro hafter
    have hfalse := firstTrueIndex_minimal hfound hafter
    rw [hctzBit] at hfalse
    contradiction
  have : found = word.ctz.toNat := by omega
  simpa [this] using hfound

theorem maskedWord32_ctz_facts {word : BitVec 32} {bit : Nat}
    (hnonzero : word &&& maskFrom32 bit ≠ 0) :
    bit ≤ (word &&& maskFrom32 bit).ctz.toNat ∧
      (word &&& maskFrom32 bit).ctz.toNat < 32 ∧
      word.getLsbD (word &&& maskFrom32 bit).ctz.toNat = true := by
  let masked := word &&& maskFrom32 bit
  have hbound : masked.ctz.toNat < 32 :=
    (BitVec.ctz_lt_iff_ne_zero (x := masked)).2 hnonzero
  have htrue := BitVec.getLsbD_true_ctz_of_ne_zero hnonzero
  have hformula := maskedWord32_getLsbD word bit masked.ctz.toNat
  rw [← show word &&& maskFrom32 bit = masked from rfl] at hformula
  by_cases hcondition : bit ≤ masked.ctz.toNat ∧ masked.ctz.toNat < 32
  · have hboth :
        (bit ≤ masked.ctz.toNat ∧ masked.ctz.toNat < 32) ∧
          word.getLsbD masked.ctz.toNat = true := by
      simpa [masked] using hformula.symm.trans htrue
    have horiginal := hboth.2
    exact ⟨hcondition.1, hbound, horiginal⟩
  · have himpossible := hformula.symm.trans htrue
    simp [masked, hcondition] at himpossible

theorem firstSetFrom_secondWordBits_eq_masked_ctz
    (word : BitVec 32) (bit : Nat)
    (hnonzero : word &&& maskFrom32 bit ≠ 0) :
    firstSetFrom (secondWordBits word) bit =
      some (word &&& maskFrom32 bit).ctz.toNat := by
  let masked := word &&& maskFrom32 bit
  obtain ⟨hstart, hctzBound, horiginalTrue⟩ :=
    maskedWord32_ctz_facts hnonzero
  have hwordBit :
      (secondWordBits word)[masked.ctz.toNat]? = some true := by
    rw [secondWordBits_get word masked.ctz.toNat hctzBound, horiginalTrue]
  obtain ⟨found, hfound⟩ := firstSetFrom_complete hstart hwordBit
  have hfoundFacts := firstSetFrom_sound hfound
  have hnotBefore : ¬ found < masked.ctz.toNat := by
    intro hbefore
    have hmaskedFalse := BitVec.getLsbD_false_of_lt_ctz
      (x := masked) hbefore
    have hfoundBound : found < 32 := by
      simpa [secondWordBits_length] using hfoundFacts.2.1
    have hfoundOriginal : word.getLsbD found = true := by
      have hget := hfoundFacts.2.2
      rw [secondWordBits_get word found hfoundBound] at hget
      exact Option.some.inj hget
    have hmaskedTrue : masked.getLsbD found = true := by
      dsimp [masked]
      rw [maskedWord32_getLsbD]
      simp [hfoundFacts.1, hfoundBound, hfoundOriginal]
    simp [hmaskedFalse] at hmaskedTrue
  have hnotAfter : ¬ masked.ctz.toNat < found := by
    intro hafter
    have hfalse := firstSetFrom_minimal hfound hstart hafter
    rw [hwordBit] at hfalse
    contradiction
  have : found = masked.ctz.toNat := by omega
  simpa [masked, this] using hfound

theorem firstSetFrom_secondWordBits_eq_none_of_masked_eq_zero
    (word : BitVec 32) (bit : Nat) (hzero : word &&& maskFrom32 bit = 0) :
    firstSetFrom (secondWordBits word) bit = none := by
  cases hfind : firstSetFrom (secondWordBits word) bit with
  | none => rfl
  | some found =>
    have hfoundFacts := firstSetFrom_sound hfind
    have hfoundBound : found < 32 := by
      simpa [secondWordBits_length] using hfoundFacts.2.1
    have horiginal : word.getLsbD found = true := by
      have hget := hfoundFacts.2.2
      rw [secondWordBits_get word found hfoundBound] at hget
      exact Option.some.inj hget
    have hmasked : (word &&& maskFrom32 bit).getLsbD found = true := by
      rw [maskedWord32_getLsbD]
      simp [hfoundFacts.1, hfoundBound, horiginal]
    rw [hzero] at hmasked
    simp at hmasked

theorem classBits_get {second : List (BitVec 32)} {fl sl : Nat}
    {word : BitVec 32} (hword : second[fl]? = some word) (hsl : sl < 32) :
    (classBits second)[fl * 32 + sl]? = some (word.getLsbD sl) := by
  induction second generalizing fl with
  | nil => simp at hword
  | cons head rest ih =>
    cases fl with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hword
      subst head
      rw [classBits, List.getElem?_append_left (by
        simpa [secondWordBits_length] using hsl)]
      simpa using secondWordBits_get word sl hsl
    | succ fl =>
      simp only [List.getElem?_cons_succ] at hword
      rw [classBits, List.getElem?_append_right (by
        rw [secondWordBits_length]
        omega), secondWordBits_length]
      have hindex : (fl + 1) * 32 + sl - 32 = fl * 32 + sl := by omega
      rw [hindex]
      exact ih hword

theorem insertClassArrays_sets_cache
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : InsertClassResult}
    (hsecondLength : second.length = 64)
    (hinsert : insertClassArrays second first heads next previous bin block =
      some result) :
    result.second.length = second.length ∧
      (classBits result.second)[bin]? = some true ∧
      result.first.getLsbD (bin / 32) = true := by
  have hresult := insertClassArrays_result hinsert
  rcases hresult with ⟨_, hfl, _, _, _, hsecond, hfirst⟩
  have hsl : bin % 32 < 32 := Nat.mod_lt bin (by decide)
  have hfl64 : bin / 32 < 64 := by omega
  have hword : result.second[bin / 32]? =
      some (setSecondBit (second[bin / 32]?.getD 0) (bin % 32)) := by
    rw [hsecond]
    simp [hfl]
  have hclass := classBits_get hword hsl
  rw [setSecondBit_selected _ hsl] at hclass
  rw [Nat.mul_comm (bin / 32) 32, Nat.div_add_mod] at hclass
  exact ⟨by simp [hsecond], hclass, by
    rw [hfirst, setWordBit_selected _ hfl64]⟩

def secondNonzeroBits (second : List (BitVec 32)) : List Bool :=
  second.map fun word => decide (word ≠ 0)

def FirstBitmapRep (first : BitVec 64) (second : List (BitVec 32)) : Prop :=
  second.length = 64 ∧ wordBits first = secondNonzeroBits second

theorem secondNonzeroBits_length (second : List (BitVec 32)) :
    (secondNonzeroBits second).length = second.length := by
  simp [secondNonzeroBits]

theorem secondNonzeroBits_get {second : List (BitVec 32)} {index : Nat}
    {word : BitVec 32} (hget : second[index]? = some word) :
    (secondNonzeroBits second)[index]? = some (decide (word ≠ 0)) := by
  simp [secondNonzeroBits, List.getElem?_map, hget]

theorem FirstBitmapRep.point {first : BitVec 64} {second : List (BitVec 32)}
    (hrep : FirstBitmapRep first second) {index : Nat} (hindex : index < 64) :
    first.getLsbD index = decide (second[index]?.getD 0 ≠ 0) := by
  have hlength := hrep.1
  have hi : index < second.length := by omega
  have hfirst := wordBits_get first index hindex
  have hsecond : second[index]? = some (second[index]'hi) := by simp
  have hnonzero := secondNonzeroBits_get hsecond
  rw [hrep.2] at hfirst
  rw [hnonzero] at hfirst
  simpa [hsecond] using (Option.some.inj hfirst).symm

theorem firstBitmapRep_of_point {first : BitVec 64}
    {second : List (BitVec 32)} (hlength : second.length = 64)
    (hpoint : ∀ index, index < 64 →
      first.getLsbD index = decide (second[index]?.getD 0 ≠ 0)) :
    FirstBitmapRep first second := by
  refine ⟨hlength, ?_⟩
  apply List.ext_getElem?
  intro index
  by_cases hindex : index < 64
  · have hi : index < second.length := by omega
    have hfirst := wordBits_get first index hindex
    have hsecond : second[index]? = some (second[index]'hi) := by simp
    have hnonzero := secondNonzeroBits_get hsecond
    rw [hfirst, hnonzero]
    simpa [hsecond] using congrArg some (hpoint index hindex)
  · have hwordLength := wordBits_length first
    have hsecondLength := secondNonzeroBits_length second
    rw [List.getElem?_eq_none_iff.mpr (by omega),
      List.getElem?_eq_none_iff.mpr (by omega)]

/-- Exact pure control flow of `tlsf_find_nonempty_class`. -/
def findNonemptyClassLowered (second : List (BitVec 32)) (first : BitVec 64)
    (startFl startSl : Nat) : Option Nat :=
  if startFl ≥ second.length then none else
  if startSl ≥ 32 then none else
  let secondBitmap := second[startFl]?.getD 0
  let secondMasked := secondBitmap &&& maskFrom32 startSl
  if secondMasked ≠ 0 then
    some (startFl * 32 + secondMasked.ctz.toNat)
  else
    let nextFl := startFl + 1
    if nextFl ≥ 64 then none else
    let firstMasked := first &&& maskFrom nextFl
    if firstMasked = 0 then none else
    let foundFl := firstMasked.ctz.toNat
    if foundFl ≥ second.length then none else
    let foundSecond := second[foundFl]?.getD 0
    if foundSecond = 0 then none else
    some (foundFl * 32 + foundSecond.ctz.toNat)

theorem maskedWord64_ctz_facts {word : BitVec 64} {bit : Nat}
    (hnonzero : word &&& maskFrom bit ≠ 0) :
    bit ≤ (word &&& maskFrom bit).ctz.toNat ∧
      (word &&& maskFrom bit).ctz.toNat < 64 ∧
      word.getLsbD (word &&& maskFrom bit).ctz.toNat = true := by
  let masked := word &&& maskFrom bit
  have hbound : masked.ctz.toNat < 64 :=
    (BitVec.ctz_lt_iff_ne_zero (x := masked)).2 hnonzero
  have htrue := BitVec.getLsbD_true_ctz_of_ne_zero hnonzero
  have hformula := maskedWord_getLsbD word bit masked.ctz.toNat
  rw [← show word &&& maskFrom bit = masked from rfl] at hformula
  by_cases hcondition : bit ≤ masked.ctz.toNat ∧ masked.ctz.toNat < 64
  · have hboth :
        (bit ≤ masked.ctz.toNat ∧ masked.ctz.toNat < 64) ∧
          word.getLsbD masked.ctz.toNat = true := by
      simpa [masked] using hformula.symm.trans htrue
    exact ⟨hcondition.1, hbound, hboth.2⟩
  · have himpossible := hformula.symm.trans htrue
    simp [masked, hcondition] at himpossible

theorem findNonemptyClassLowered_sound {second : List (BitVec 32)}
    {first : BitVec 64} {startFl startSl found : Nat}
    (hfind : findNonemptyClassLowered second first startFl startSl = some found) :
    startFl * 32 + startSl ≤ found ∧ found < second.length * 32 ∧
      (classBits second)[found]? = some true := by
  unfold findNonemptyClassLowered at hfind
  split at hfind <;> try contradiction
  next hstartFl =>
    split at hfind <;> try contradiction
    next hstartSl =>
      dsimp only at hfind
      split at hfind
      next hsame =>
        simp only [Option.some.injEq] at hfind
        subst found
        have hword : second[startFl]? =
            some (second[startFl]?.getD 0) := by
          cases hget : second[startFl]? with
          | none =>
            have := List.getElem?_eq_none_iff.mp hget
            omega
          | some word => simp [hget]
        obtain ⟨hoffset, hoffsetBound, hbit⟩ :=
          maskedWord32_ctz_facts hsame
        exact ⟨by omega, by omega, by
          rw [classBits_get hword hoffsetBound, hbit]⟩
      next hsameEmpty =>
        split at hfind <;> try contradiction
        next hnextFl =>
          split at hfind <;> try contradiction
          next hfirstMasked =>
            split at hfind <;> try contradiction
            next hfoundFl =>
              split at hfind <;> try contradiction
              next hfoundSecond =>
                simp only [Option.some.injEq] at hfind
                subst found
                have hfirstNonzero : first &&& maskFrom (startFl + 1) ≠ 0 :=
                  hfirstMasked
                obtain ⟨hflStart, hflBound, _⟩ :=
                  maskedWord64_ctz_facts hfirstNonzero
                have hword : second[(first &&& maskFrom (startFl + 1)).ctz.toNat]? =
                    some (second[(first &&& maskFrom (startFl + 1)).ctz.toNat]?.getD 0) := by
                  cases hget : second[(first &&& maskFrom (startFl + 1)).ctz.toNat]? with
                  | none =>
                    have := List.getElem?_eq_none_iff.mp hget
                    omega
                  | some word => simp [hget]
                have hslBound :
                    (second[(first &&& maskFrom (startFl + 1)).ctz.toNat]?.getD 0).ctz.toNat < 32 :=
                  (BitVec.ctz_lt_iff_ne_zero
                    (x := second[(first &&& maskFrom (startFl + 1)).ctz.toNat]?.getD 0)).2
                      hfoundSecond
                have hslBit := BitVec.getLsbD_true_ctz_of_ne_zero hfoundSecond
                exact ⟨by omega, by omega, by
                  rw [classBits_get hword hslBound, hslBit]⟩

theorem classBits_length (second : List (BitVec 32)) :
    (classBits second).length = second.length * 32 := by
  induction second with
  | nil => rfl
  | cons word rest => simp [classBits, secondWordBits_length, *]; omega

theorem classBits_drop (second : List (BitVec 32)) (count : Nat) :
    classBits (second.drop count) =
      (classBits second).drop (count * 32) := by
  induction second generalizing count with
  | nil => simp [classBits]
  | cons word rest ih =>
    cases count with
    | zero => simp
    | succ count =>
      simp only [List.drop_succ_cons, classBits]
      rw [ih]
      rw [Nat.succ_mul]
      symm
      calc
        (secondWordBits word ++ classBits rest).drop (count * 32 + 32) =
            (secondWordBits word).drop (count * 32 + 32) ++
              (classBits rest).drop ((count * 32 + 32) - 32) := by
                exact List.drop_append
        _ = (classBits rest).drop (count * 32) := by
          have hsub : count * 32 + 32 - 32 = count * 32 := by omega
          simp [secondWordBits_length, hsub]

def findNonemptyClassChunked (second : List (BitVec 32))
    (startFl startSl : Nat) : Option Nat :=
  match second.drop startFl with
  | [] => none
  | word :: rest =>
      match firstSetFrom (secondWordBits word) startSl with
      | some offset => some (startFl * 32 + offset)
      | none =>
          (firstTrueIndex (classBits rest)).map ((startFl + 1) * 32 + ·)

theorem findNonemptyClassChunked_refines (second : List (BitVec 32))
    (startFl startSl : Nat) (hstartSl : startSl < 32) :
    findNonemptyClassChunked second startFl startSl =
      findNonemptyClass second startFl startSl := by
  unfold findNonemptyClass
  rw [show startFl * 32 + startSl = startFl * 32 + startSl from rfl,
    firstSetFrom_add]
  rw [← classBits_drop second startFl]
  unfold findNonemptyClassChunked
  cases hdrop : second.drop startFl with
  | nil => simp [classBits, firstSetFrom, firstTrueIndex]
  | cons word rest =>
    rw [classBits]
    rw [firstSetFrom_append _ _ _ (by
      simp [secondWordBits_length]
      omega)]
    cases hfirst : firstSetFrom (secondWordBits word) startSl with
    | some offset => simp [hfirst]
    | none =>
      simp only [hfirst, Option.map_none, Option.map_map,
        secondWordBits_length]
      congr 1
      funext offset
      simp [Function.comp_def]
      omega

def findNonzeroClassWords : List (BitVec 32) → Nat → Option Nat
  | [], _ => none
  | word :: rest, base =>
      if word = 0 then findNonzeroClassWords rest (base + 32)
      else some (base + word.ctz.toNat)

theorem findNonzeroClassWords_refines (second : List (BitVec 32))
    (base : Nat) :
    findNonzeroClassWords second base =
      (firstTrueIndex (classBits second)).map (base + ·) := by
  induction second generalizing base with
  | nil => simp [findNonzeroClassWords, classBits, firstTrueIndex]
  | cons word rest ih =>
    rw [classBits, firstTrueIndex_append]
    by_cases hzero : word = (0 : BitVec 32)
    · subst word
      have hwordZero : firstTrueIndex (secondWordBits (0 : BitVec 32)) = none := by
        native_decide
      rw [hwordZero]
      simp only [findNonzeroClassWords, if_pos rfl, ih, Option.map_map]
      cases hrest : firstTrueIndex (classBits rest) with
      | none => simp
      | some offset =>
        simp only [Option.map_some]
        congr 1
        simp [secondWordBits_length]
        omega
    · rw [firstTrueIndex_secondWordBits_ctz hzero]
      rw [findNonzeroClassWords, if_neg hzero]
      rfl

def findNonzeroViaBits (second : List (BitVec 32)) (start : Nat) : Option Nat :=
  match firstSetFrom (secondNonzeroBits second) start with
  | none => none
  | some fl =>
      let word := second[fl]?.getD 0
      if word = 0 then none else some (fl * 32 + word.ctz.toNat)

def findNonzeroClassOffset : List (BitVec 32) → Option Nat
  | [] => none
  | word :: rest =>
      if word = 0 then (findNonzeroClassOffset rest).map (32 + ·)
      else some word.ctz.toNat

def firstClassFromNonzero (second : List (BitVec 32)) : Option Nat :=
  match firstTrueIndex (secondNonzeroBits second) with
  | none => none
  | some fl =>
      let word := second[fl]?.getD 0
      if word = 0 then none else some (fl * 32 + word.ctz.toNat)

theorem firstClassFromNonzero_refines (second : List (BitVec 32)) :
    firstClassFromNonzero second = firstTrueIndex (classBits second) := by
  induction second with
  | nil => simp [firstClassFromNonzero, secondNonzeroBits, classBits,
      firstTrueIndex]
  | cons word rest ih =>
    by_cases hzero : word = (0 : BitVec 32)
    · subst word
      have hwordZero : firstTrueIndex (secondWordBits (0 : BitVec 32)) = none := by
        native_decide
      have hnonzeroIndex :
          firstTrueIndex (secondNonzeroBits ((0 : BitVec 32) :: rest)) =
            (firstTrueIndex (secondNonzeroBits rest)).map Nat.succ := by
        simp [secondNonzeroBits, firstTrueIndex]
      rw [classBits, firstTrueIndex_append, hwordZero]
      unfold firstClassFromNonzero
      rw [hnonzeroIndex]
      cases hfind : firstTrueIndex (secondNonzeroBits rest) with
      | none =>
        have hi := ih
        unfold firstClassFromNonzero at hi
        rw [hfind] at hi
        simp only at hi
        rw [← hi]
        simp
      | some fl =>
        simp only [Option.map_some, List.getElem?_cons_succ]
        have hselectedBits := firstTrueIndex_sound hfind
        cases hget : rest[fl]? with
        | none =>
          simp [secondNonzeroBits, List.getElem?_map, hget] at hselectedBits
        | some selected =>
          have hselected : selected ≠ 0 := by
            simp [secondNonzeroBits, List.getElem?_map, hget] at hselectedBits
            exact hselectedBits
          have hi := ih
          unfold firstClassFromNonzero at hi
          rw [hfind] at hi
          simp only [hget, Option.getD_some, if_neg hselected] at hi
          rw [← hi]
          simp only [Option.getD_some]
          rw [if_neg hselected]
          simp [secondWordBits_length]
          omega
    · rw [classBits, firstTrueIndex_append,
        firstTrueIndex_secondWordBits_ctz hzero]
      have hnonzeroIndex :
          firstTrueIndex (secondNonzeroBits (word :: rest)) = some 0 := by
        have hzero' : word ≠ (0 : BitVec 32) := by simpa only using hzero
        have hdecide : decide (word ≠ (0 : BitVec 32)) = true := by
          exact decide_eq_true hzero'
        simp only [secondNonzeroBits, List.map_cons, firstTrueIndex]
        rw [hdecide]
        rfl
      unfold firstClassFromNonzero
      rw [hnonzeroIndex]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      rw [if_neg hzero]
      simp

theorem secondNonzeroBits_drop (second : List (BitVec 32)) (start : Nat) :
    secondNonzeroBits (second.drop start) =
      (secondNonzeroBits second).drop start := by
  simp [secondNonzeroBits, List.map_drop]

theorem findNonzeroViaBits_refines (second : List (BitVec 32)) (start : Nat) :
    findNonzeroViaBits second start =
      (firstTrueIndex (classBits (second.drop start))).map
        (start * 32 + ·) := by
  unfold findNonzeroViaBits firstSetFrom
  rw [← secondNonzeroBits_drop]
  cases hfind : firstTrueIndex (secondNonzeroBits (second.drop start)) with
  | none =>
    have href := firstClassFromNonzero_refines (second.drop start)
    unfold firstClassFromNonzero at href
    rw [hfind] at href
    simp only at href
    simp [hfind, ← href]
  | some offset =>
    have href := firstClassFromNonzero_refines (second.drop start)
    unfold firstClassFromNonzero at href
    rw [hfind] at href
    simp only at href
    have hget : second[start + offset]? = (second.drop start)[offset]? := by
      rw [List.getElem?_drop]
    simp only [hfind, Option.map_some]
    rw [hget]
    rw [← href]
    split
    next hzero => simp only [hzero, if_true, Option.map_none]
    next hnonzero =>
      simp only [hnonzero, if_false, Option.map_some]
      congr 1
      omega

def findNonzeroViaFirst (second : List (BitVec 32)) (first : BitVec 64)
    (start : Nat) : Option Nat :=
  match firstSetFrom (wordBits first) start with
  | none => none
  | some fl =>
      let word := second[fl]?.getD 0
      if word = 0 then none else some (fl * 32 + word.ctz.toNat)

theorem findNonzeroViaFirst_refines {second : List (BitVec 32)}
    {first : BitVec 64} (hrep : FirstBitmapRep first second) (start : Nat) :
    findNonzeroViaFirst second first start = findNonzeroViaBits second start := by
  unfold findNonzeroViaFirst findNonzeroViaBits
  rw [hrep.2]

def findNonemptyClassCached (second : List (BitVec 32)) (first : BitVec 64)
    (startFl startSl : Nat) : Option Nat :=
  if startFl ≥ second.length then none else
  if startSl ≥ 32 then none else
  let word := second[startFl]?.getD 0
  match firstSetFrom (secondWordBits word) startSl with
  | some sl => some (startFl * 32 + sl)
  | none => findNonzeroViaFirst second first (startFl + 1)

theorem findNonemptyClassCached_eq_chunked {second : List (BitVec 32)}
    {first : BitVec 64} (hrep : FirstBitmapRep first second)
    (startFl startSl : Nat) (hstartSl : startSl < 32) :
    findNonemptyClassCached second first startFl startSl =
      findNonemptyClassChunked second startFl startSl := by
  unfold findNonemptyClassCached findNonemptyClassChunked
  by_cases hfl : startFl < second.length
  · rw [if_neg (by omega), if_neg (by omega),
      List.drop_eq_getElem_cons hfl]
    simp only [List.getElem?_eq_getElem hfl, Option.getD_some]
    cases hfirst : firstSetFrom (secondWordBits second[startFl]) startSl with
    | some sl => simp [hfirst]
    | none =>
      simp only [hfirst]
      rw [findNonzeroViaFirst_refines hrep,
        findNonzeroViaBits_refines]
  · rw [if_pos (by omega)]
    have hdrop : second.drop startFl = [] :=
      List.drop_eq_nil_of_le (by omega)
    rw [hdrop]

theorem findNonemptyClassLowered_eq_cached {second : List (BitVec 32)}
    {first : BitVec 64} (hrep : FirstBitmapRep first second)
    (startFl startSl : Nat) :
    findNonemptyClassLowered second first startFl startSl =
      findNonemptyClassCached second first startFl startSl := by
  unfold findNonemptyClassLowered findNonemptyClassCached
  by_cases hfl : startFl < second.length
  · have hnfl : ¬ startFl ≥ second.length := by omega
    simp only [hnfl, if_false]
    by_cases hsl : startSl < 32
    · have hnsl : ¬ startSl ≥ 32 := by omega
      simp only [hnsl, if_false]
      by_cases hsecond :
          second[startFl]?.getD 0 &&& maskFrom32 startSl = 0
      · rw [if_neg (not_not_intro hsecond),
          firstSetFrom_secondWordBits_eq_none_of_masked_eq_zero _ _ hsecond]
        by_cases hnext : startFl + 1 < 64
        · rw [if_neg (by omega)]
          by_cases hfirst : first &&& maskFrom (startFl + 1) = 0
          · rw [if_pos hfirst]
            unfold findNonzeroViaFirst
            rw [firstSetFrom_wordBits_eq_none_of_masked_eq_zero _ _ hfirst]
          · rw [if_neg hfirst]
            have hfirstSet :=
              firstSetFrom_wordBits_eq_masked_ctz first (startFl + 1) hfirst
            have hfoundBound :
                (first &&& maskFrom (startFl + 1)).ctz.toNat < second.length := by
              rw [hrep.1]
              exact (maskedWord64_ctz_facts hfirst).2.1
            rw [if_neg (by omega)]
            unfold findNonzeroViaFirst
            rw [hfirstSet]
        · rw [if_pos (by omega)]
          unfold findNonzeroViaFirst firstSetFrom
          have hdrop : (wordBits first).drop (startFl + 1) = [] := by
            apply List.drop_eq_nil_of_le
            rw [wordBits_length]
            omega
          rw [hdrop]
          rfl
      · rw [if_pos hsecond,
          firstSetFrom_secondWordBits_eq_masked_ctz _ _ hsecond]
    · have hgesl : startSl ≥ 32 := by omega
      simp only [hgesl, if_true]
  · have hgefl : startFl ≥ second.length := by omega
    simp only [hgefl, if_true]

theorem findNonemptyClassLowered_refines {second : List (BitVec 32)}
    {first : BitVec 64} (hrep : FirstBitmapRep first second)
    (startFl startSl : Nat) (hstartSl : startSl < 32) :
    findNonemptyClassLowered second first startFl startSl =
      findNonemptyClass second startFl startSl := by
  rw [findNonemptyClassLowered_eq_cached hrep,
    findNonemptyClassCached_eq_chunked hrep _ _ hstartSl,
    findNonemptyClassChunked_refines _ _ _ hstartSl]

theorem findNonemptyClassLowered_complete {second : List (BitVec 32)}
    {first : BitVec 64} (hrep : FirstBitmapRep first second)
    {startFl startSl index : Nat} (hstartSl : startSl < 32)
    (hstart : startFl * 32 + startSl ≤ index)
    (hset : (classBits second)[index]? = some true) :
    ∃ found, findNonemptyClassLowered second first startFl startSl = some found := by
  rw [findNonemptyClassLowered_refines hrep _ _ hstartSl]
  exact firstSetFrom_complete hstart hset

theorem findNonemptyClassLowered_minimal {second : List (BitVec 32)}
    {first : BitVec 64} (hrep : FirstBitmapRep first second)
    {startFl startSl found earlier : Nat} (hstartSl : startSl < 32)
    (hfind : findNonemptyClassLowered second first startFl startSl = some found)
    (hstart : startFl * 32 + startSl ≤ earlier) (hearlier : earlier < found) :
    (classBits second)[earlier]? = some false := by
  rw [findNonemptyClassLowered_refines hrep _ _ hstartSl] at hfind
  exact firstSetFrom_minimal hfind hstart hearlier

theorem findNonemptyClass_sound {second : List (BitVec 32)}
    {startFl startSl found : Nat}
    (hfind : findNonemptyClass second startFl startSl = some found) :
    startFl * 32 + startSl ≤ found ∧ found < second.length * 32 ∧
      (classBits second)[found]? = some true := by
  have hsound := firstSetFrom_sound hfind
  simpa [findNonemptyClass, classBits_length] using hsound

theorem findNonemptyClass_indices {second : List (BitVec 32)}
    {startFl startSl found : Nat} (hsecond : second.length ≤ 64)
    (hfind : findNonemptyClass second startFl startSl = some found) :
    found / 32 < 64 ∧ found % 32 < 32 ∧
      found = (found / 32) * 32 + found % 32 := by
  have hbound := (findNonemptyClass_sound hfind).2.1
  have hmod : found % 32 < 32 := Nat.mod_lt found (by decide)
  constructor
  · apply Nat.div_lt_of_lt_mul
    omega
  exact ⟨hmod, by omega⟩

def classOfBin? (bin : Nat) : Option SizeClass :=
  if hfl : bin / 32 < firstLevelCount then
    if hsl : bin % 32 < secondLevelCount then
      some { fl := ⟨bin / 32, hfl⟩, sl := ⟨bin % 32, hsl⟩ }
    else none
  else none

theorem classIndex_injective {left right : SizeClass}
    (heq : left.fl.val * secondLevelCount + left.sl.val =
      right.fl.val * secondLevelCount + right.sl.val) :
    left = right := by
  have hleftSl := left.sl.isLt
  have hrightSl := right.sl.isLt
  simp only [secondLevelCount] at heq hleftSl hrightSl
  have hflVal : left.fl.val = right.fl.val := by
    have hdiv := congrArg (fun value : Nat => value / 32) heq
    omega
  have hslVal : left.sl.val = right.sl.val := by omega
  have hfl : left.fl = right.fl := Fin.ext hflVal
  have hsl : left.sl = right.sl := Fin.ext hslVal
  cases left
  cases right
  simp_all

theorem classOfBin?_index {bin : Nat} {cls : SizeClass}
    (hclass : classOfBin? bin = some cls) :
    bin = cls.fl.val * secondLevelCount + cls.sl.val := by
  unfold classOfBin? at hclass
  split at hclass <;> try contradiction
  next hfl =>
    split at hclass <;> try contradiction
    next hsl =>
      simp only [Option.some.injEq] at hclass
      subst cls
      simp only [secondLevelCount]
      simpa [Nat.mul_comm] using (Nat.div_add_mod bin 32).symm

theorem classOfBin?_of_bound {bin : Nat}
    (hbound : bin < firstLevelCount * secondLevelCount) :
    ∃ cls, classOfBin? bin = some cls ∧
      cls.fl.val = bin / secondLevelCount ∧
      cls.sl.val = bin % secondLevelCount ∧
      bin = cls.fl.val * secondLevelCount + cls.sl.val := by
  have hfl : bin / 32 < firstLevelCount := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    simpa [secondLevelCount] using hbound
  have hsl : bin % 32 < secondLevelCount := by
    simpa [secondLevelCount] using Nat.mod_lt bin (by decide : 0 < 32)
  let cls : SizeClass := SizeClass.mk ⟨bin / 32, hfl⟩ ⟨bin % 32, hsl⟩
  exact ⟨cls, by simp [classOfBin?, hfl, hsl, cls], rfl, rfl, by
    simpa [secondLevelCount, cls, Nat.mul_comm] using
      (Nat.div_add_mod bin 32).symm⟩

theorem classOfBin?_of_findNonemptyClass {second : List (BitVec 32)}
    {startFl startSl found : Nat} (hsecond : second.length ≤ firstLevelCount)
    (hfind : findNonemptyClass second startFl startSl = some found) :
    ∃ cls, classOfBin? found = some cls ∧
      cls.fl.val = found / secondLevelCount ∧
      cls.sl.val = found % secondLevelCount ∧
      found = cls.fl.val * secondLevelCount + cls.sl.val := by
  have hindices := findNonemptyClass_indices (by
    simpa [firstLevelCount] using hsecond) hfind
  have hfl : found / 32 < firstLevelCount := by
    simpa [firstLevelCount] using hindices.1
  have hsl : found % 32 < secondLevelCount := by
    simpa [secondLevelCount] using hindices.2.1
  let cls : SizeClass := SizeClass.mk ⟨found / 32, hfl⟩
    ⟨found % 32, hsl⟩
  exact ⟨cls, by simp [classOfBin?, hfl, hsl, cls], rfl, rfl, by
    simpa [secondLevelCount, cls] using hindices.2.2⟩

/-- Abstraction relation from the concrete packed second-level bitmap to the
cached second-level bits of the abstract allocator. -/
def RepresentsSecondBitmap (second : List (BitVec 32))
    (state : Bins.State) : Prop :=
  second.length = firstLevelCount ∧
    ∀ cls : SizeClass,
      (classBits second)[cls.fl.val * secondLevelCount + cls.sl.val]? =
        some (state.slSet cls.fl cls.sl)

theorem slSet_eq_decide_nonempty {state : Bins.State}
    (hvalid : Bins.Valid state) (cls : SizeClass) :
    state.slSet cls.fl cls.sl = decide (state.chains cls ≠ []) := by
  by_cases hne : state.chains cls ≠ []
  · have hbit := (hvalid.2.2.1 cls.fl cls.sl).2 hne
    simp [hbit, hne]
  · have hbit : state.slSet cls.fl cls.sl = false := by
      cases hvalue : state.slSet cls.fl cls.sl with
      | false => rfl
      | true => exact (hne ((hvalid.2.2.1 cls.fl cls.sl).1 hvalue)).elim
    simp [hbit, hne]

theorem findNonemptyClassLowered_selects_nonempty
    {second : List (BitVec 32)} {first : BitVec 64}
    {state : Bins.State} (hrep : RepresentsSecondBitmap second state)
    (hvalid : Bins.Valid state) {startFl startSl found : Nat}
    (hfind : findNonemptyClassLowered second first startFl startSl = some found) :
    ∃ cls, classOfBin? found = some cls ∧
      found = cls.fl.val * secondLevelCount + cls.sl.val ∧
      state.chains cls ≠ [] := by
  have hlogical := findNonemptyClassLowered_sound hfind
  obtain ⟨cls, hclass, _, _, hencode⟩ := classOfBin?_of_bound (by
    rw [hrep.1] at hlogical
    simpa [firstLevelCount, secondLevelCount] using hlogical.2.1)
  have hrepresented := hrep.2 cls
  rw [← hencode, hlogical.2.2] at hrepresented
  have hset : state.slSet cls.fl cls.sl = true := Option.some.inj hrepresented.symm
  exact ⟨cls, hclass, hencode, (hvalid.2.2.1 cls.fl cls.sl).mp hset⟩

theorem findNonemptyClassLowered_eq_findCandidate
    {second : List (BitVec 32)} {first : BitVec 64}
    {state : Bins.State} (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second) (hvalid : Bins.Valid state)
    (start selected : SizeClass) {bin : Nat}
    (hfind : findNonemptyClassLowered second first start.fl.val start.sl.val =
      some bin) (hclass : classOfBin? bin = some selected) :
    Bins.findCandidate state start = some selected := by
  have hbin := classOfBin?_index hclass
  have hlogical : findNonemptyClass second start.fl.val start.sl.val = some bin := by
    rw [← findNonemptyClassLowered_refines hfirst _ _ start.sl.isLt]
    exact hfind
  have hsound := findNonemptyClass_sound hlogical
  have hselectedBit := hsecond.2 selected
  rw [← hbin, hsound.2.2] at hselectedBit
  have hselectedSet : state.slSet selected.fl selected.sl = true :=
    Option.some.inj hselectedBit.symm
  have hselectedNonempty := (hvalid.2.2.1 selected.fl selected.sl).1 hselectedSet
  have heligible : Bins.HasEligibleBin state start := by
    by_cases hfl : selected.fl.val = start.fl.val
    · left
      have hflEq : selected.fl = start.fl := Fin.ext hfl
      refine ⟨selected.sl, ?_, ?_⟩
      have hstartSl := start.sl.isLt
      have hselectedSl := selected.sl.isLt
      rw [hbin] at hsound
      simp only [secondLevelCount] at hsound hstartSl hselectedSl
      omega
      · simpa [hflEq] using hselectedSet
    · right
      have hflAfter : start.fl.val < selected.fl.val := by
        have hstartSl := start.sl.isLt
        have hselectedSl := selected.sl.isLt
        rw [hbin] at hsound
        simp only [secondLevelCount] at hsound hstartSl hselectedSl
        omega
      refine ⟨selected.fl, hflAfter, ?_⟩
      exact (hvalid.2.2.2 selected.fl).2 ⟨selected.sl, hselectedNonempty⟩
  cases habstract : Bins.findCandidate state start with
  | none =>
      exact (((Bins.findCandidate_none_iff hvalid).1 habstract) heligible).elim
  | some abstract =>
      have habstractNonempty := Bins.findCandidate_nonempty hvalid habstract
      have hselectedStart :
          start.fl.val * secondLevelCount + start.sl.val ≤
            selected.fl.val * secondLevelCount + selected.sl.val := by
        rw [← hbin]
        simpa [secondLevelCount] using hsound.1
      have habstractMinimal := Bins.findCandidate_encoded_minimal hvalid habstract
        hselectedNonempty hselectedStart
      have habstractNotBefore : ¬
          abstract.fl.val * secondLevelCount + abstract.sl.val < bin := by
        intro habstractEarlier
        have habstractStart :
            start.fl.val * 32 + start.sl.val ≤
              abstract.fl.val * 32 + abstract.sl.val := by
          have horder := Bins.findCandidate_ordered habstract
          rcases horder with hflOrder | hsameOrder
          · have hstartSl := start.sl.isLt
            have habstractSl := abstract.sl.isLt
            simp only [secondLevelCount] at hflOrder hstartSl habstractSl
            omega
          · simp only [secondLevelCount] at hsameOrder
            omega
        have habstractEarlier32 :
            abstract.fl.val * 32 + abstract.sl.val < bin := by
          simpa [secondLevelCount] using habstractEarlier
        have hfalse := findNonemptyClassLowered_minimal hfirst start.sl.isLt
          hfind habstractStart habstractEarlier32
        have habstractRep := hsecond.2 abstract
        have habstractSet :=
          (hvalid.2.2.1 abstract.fl abstract.sl).2 habstractNonempty
        rw [habstractSet] at habstractRep
        have habstractRep32 :
            (classBits second)[abstract.fl.val * 32 + abstract.sl.val]? =
              some true := by
          simpa [secondLevelCount] using habstractRep
        rw [habstractRep32] at hfalse
        contradiction
      have hindexEq :
          abstract.fl.val * secondLevelCount + abstract.sl.val = bin := by
        rw [← hbin] at habstractMinimal
        omega
      have habstractEq : abstract = selected := by
        apply classIndex_injective
        rw [hindexEq, hbin]
      simpa [habstractEq] using habstract

def clearWordBit (bitmap : BitVec 64) (bit : Nat) : BitVec 64 :=
  bitmap &&& ~~~(BitVec.ofNat 64 1 <<< bit)

def clearBinBit (words : List (BitVec 64)) (bin : Nat) : List (BitVec 64) :=
  let wordIndex := bin / 64
  let bit := bin % 64
  let bitmap := words[wordIndex]?.getD 0
  words.set wordIndex (clearWordBit bitmap bit)

theorem clearWordBit_getLsbD (bitmap : BitVec 64) (bit index : Nat) :
    (clearWordBit bitmap bit).getLsbD index =
      if index = bit ∧ index < 64 then false else bitmap.getLsbD index := by
  simp only [clearWordBit, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  by_cases hindex : index < 64 <;> by_cases heq : index = bit
  · subst bit
    simp [hindex]
  ·
    by_cases hbefore : index < bit
    · simp [hindex, heq, hbefore]
    · have htestFalse : Nat.testBit 1 (index - bit) = false := by
        cases htest : Nat.testBit 1 (index - bit) with
        | false => rfl
        | true =>
          have hzero := Nat.testBit_one_eq_true_iff_self_eq_zero.mp htest
          omega
      simp [hindex, heq, hbefore, htestFalse]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]

theorem clearBinBit_length (words : List (BitVec 64)) (bin : Nat) :
    (clearBinBit words bin).length = words.length := by
  simp [clearBinBit]

theorem clearBinBit_selected_word {words : List (BitVec 64)} {bin : Nat}
    {bitmap : BitVec 64} (hget : words[bin / 64]? = some bitmap) :
    (clearBinBit words bin)[bin / 64]? =
      some (clearWordBit bitmap (bin % 64)) := by
  have hbound := (List.getElem?_eq_some_iff.mp hget).1
  simp [clearBinBit, hget, List.getElem?_set_self hbound]

theorem clearBinBit_other_word {words : List (BitVec 64)} {bin index : Nat}
    (hne : index ≠ bin / 64) :
    (clearBinBit words bin)[index]? = words[index]? := by
  unfold clearBinBit
  exact List.getElem?_set_ne (Ne.symm hne)

theorem clearBinBit_selected_false {words : List (BitVec 64)} {bin : Nat}
    {bitmap : BitVec 64} (hget : words[bin / 64]? = some bitmap) :
    ((clearBinBit words bin)[bin / 64]?.getD 0).getLsbD (bin % 64) = false := by
  rw [clearBinBit_selected_word hget]
  simp only [Option.getD_some]
  rw [clearWordBit_getLsbD]
  have hbit : bin % 64 < 64 := Nat.mod_lt bin (by decide)
  simp [hbit]

theorem clearBinBit_preserves_other_bit {words : List (BitVec 64)} {bin : Nat}
    {bitmap : BitVec 64} (hget : words[bin / 64]? = some bitmap)
    {index : Nat} (hne : index ≠ bin % 64) :
    ((clearBinBit words bin)[bin / 64]?.getD 0).getLsbD index =
      bitmap.getLsbD index := by
  rw [clearBinBit_selected_word hget]
  simp only [Option.getD_some]
  rw [clearWordBit_getLsbD]
  simp [hne]

def setClassBit (second : List (BitVec 32)) (bin : Nat) :
    List (BitVec 32) :=
  let fl := bin / 32
  let sl := bin % 32
  let bitmap := second[fl]?.getD 0
  second.set fl (setSecondBit bitmap sl)

theorem setClassBit_length (second : List (BitVec 32)) (bin : Nat) :
    (setClassBit second bin).length = second.length := by
  simp [setClassBit]

theorem setClassBit_selected_true {second : List (BitVec 32)} {bin : Nat}
    (hfl : bin / 32 < second.length) :
    (classBits (setClassBit second bin))[bin]? = some true := by
  have hsl : bin % 32 < 32 := Nat.mod_lt bin (by decide)
  have hset : (setClassBit second bin)[bin / 32]? =
      some (setSecondBit second[bin / 32] (bin % 32)) := by
    simp [setClassBit, hfl]
  have hclass := classBits_get hset hsl
  rw [setSecondBit_selected _ hsl] at hclass
  rw [Nat.mul_comm (bin / 32) 32, Nat.div_add_mod] at hclass
  exact hclass

theorem setClassBit_preserves_other {second : List (BitVec 32)}
    {bin other : Nat} (hfl : bin / 32 < second.length)
    (hother : other < second.length * 32) (hne : other ≠ bin) :
    (classBits (setClassBit second bin))[other]? =
      (classBits second)[other]? := by
  have hotherFl : other / 32 < second.length := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    exact hother
  have hotherSl : other % 32 < 32 := Nat.mod_lt other (by decide)
  have hold : second[other / 32]? = some second[other / 32] := by
    simp [hotherFl]
  by_cases hword : other / 32 = bin / 32
  · have hnew : (setClassBit second bin)[other / 32]? =
        some (setSecondBit second[other / 32] (bin % 32)) := by
      simp [setClassBit, hfl, hword]
    have hnewBit := classBits_get hnew hotherSl
    have holdBit := classBits_get hold hotherSl
    have hslNe : other % 32 ≠ bin % 32 := by
      intro hsl
      apply hne
      have hotherEq := Nat.div_add_mod other 32
      have hbinEq := Nat.div_add_mod bin 32
      omega
    rw [setSecondBit_getLsbD] at hnewBit
    simp [hslNe] at hnewBit
    have heq := hnewBit.trans holdBit.symm
    rw [Nat.mul_comm (other / 32) 32, Nat.div_add_mod] at heq
    exact heq
  · have hnew : (setClassBit second bin)[other / 32]? =
        some second[other / 32] := by
      simp [setClassBit, hfl, List.getElem?_set_ne (Ne.symm hword), hold]
    have hnewBit := classBits_get hnew hotherSl
    have holdBit := classBits_get hold hotherSl
    have heq := hnewBit.trans holdBit.symm
    rw [Nat.mul_comm (other / 32) 32, Nat.div_add_mod] at heq
    exact heq

theorem setClassBit_preserves_firstBitmapRep
    {second : List (BitVec 32)} {first : BitVec 64} {bin : Nat}
    (hrep : FirstBitmapRep first second) (hfl : bin / 32 < second.length) :
    FirstBitmapRep (setWordBit first (bin / 32))
      (setClassBit second bin) := by
  apply firstBitmapRep_of_point
  · simpa [setClassBit_length] using hrep.1
  · intro index hindex
    have hlength : second.length = 64 := by
      simpa [FirstBitmapRep] using hrep.1
    have hfl64 : bin / 32 < 64 := by omega
    by_cases hselected : index = bin / 32
    · subst index
      have hsl : bin % 32 < 32 := Nat.mod_lt bin (by decide)
      have hget : (setClassBit second bin)[bin / 32]? =
          some (setSecondBit second[bin / 32] (bin % 32)) := by
        simp [setClassBit, hfl]
      have hnonzero : (setClassBit second bin)[bin / 32]?.getD 0 ≠ 0 := by
        rw [hget]
        simp only [Option.getD_some]
        intro hzero
        have hbit := setSecondBit_selected second[bin / 32] hsl
        rw [hzero] at hbit
        simp at hbit
      rw [setWordBit_getLsbD]
      simp only [hfl64, and_self, if_true]
      exact (decide_eq_true hnonzero).symm
    · have hold := hrep.point hindex
      have hnextGet :
          (setClassBit second bin)[index]? = second[index]? := by
        unfold setClassBit
        exact List.getElem?_set_ne (Ne.symm hselected)
      rw [setWordBit_getLsbD]
      simp only [hselected, false_and, if_false, hnextGet]
      exact hold

theorem setClassBit_represents_insert
    {second : List (BitVec 32)} {state : Bins.State}
    (hrep : RepresentsSecondBitmap second state) (hvalid : Bins.Valid state)
    (cls : SizeClass)
    (block : Block) :
    RepresentsSecondBitmap
      (setClassBit second (encodeSizeClass cls)) (state.insert cls block) := by
  constructor
  · simpa [setClassBit_length] using hrep.1
  · intro query
    by_cases hquery : query = cls
    · subst query
      have hlength : second.length = 64 := by
        simpa [firstLevelCount] using hrep.1
      have hdecode : encodeSizeClass cls / 32 = cls.fl.val := by
        simp only [encodeSizeClass, secondLevelCount]
        rw [Nat.mul_comm cls.fl.val 32,
          Nat.mul_add_div (by decide : 0 < 32)]
        simp [Nat.div_eq_of_lt cls.sl.isLt]
      have hfl : encodeSizeClass cls / 32 < second.length := by
        rw [hdecode, hlength]
        exact cls.fl.isLt
      have hselected := setClassBit_selected_true hfl
      change (classBits (setClassBit second (encodeSizeClass cls)))[encodeSizeClass cls]? =
        some ((state.insert cls block).slSet cls.fl cls.sl)
      have hnonempty : FreeList.insertFront block (state.chains cls) ≠ [] := by
        cases state.chains cls <;> simp [FreeList.insertFront]
      have hset : (state.insert cls block).slSet cls.fl cls.sl = true := by
        simp [Bins.State.insert, Bins.State.replaceChain,
          Bins.State.fromChains, Bins.Chains.replace, hnonempty]
      rw [hset]
      exact hselected
    · have hotherBound :
          encodeSizeClass query < second.length * 32 := by
        have hlength : second.length = 64 := by
          simpa [firstLevelCount] using hrep.1
        change query.fl.val * 32 + query.sl.val < second.length * 32
        rw [hlength]
        have hflBound := query.fl.isLt
        have hslBound := query.sl.isLt
        simp only [firstLevelCount] at hflBound
        simp only [secondLevelCount] at hslBound
        omega
      have hindexNe : encodeSizeClass query ≠ encodeSizeClass cls := by
        intro heq
        exact hquery (classIndex_injective heq)
      have hpreserve := setClassBit_preserves_other
        (bin := encodeSizeClass cls) (other := encodeSizeClass query)
        (by
          have hlength : second.length = 64 := by
            simpa [firstLevelCount] using hrep.1
          have hdecode : encodeSizeClass cls / 32 = cls.fl.val := by
            simp only [encodeSizeClass, secondLevelCount]
            rw [Nat.mul_comm cls.fl.val 32,
              Nat.mul_add_div (by decide : 0 < 32)]
            simp [Nat.div_eq_of_lt cls.sl.isLt]
          rw [hdecode, hlength]
          exact cls.fl.isLt)
        hotherBound hindexNe
      change (classBits (setClassBit second (encodeSizeClass cls)))[encodeSizeClass query]? =
        some ((state.insert cls block).slSet query.fl query.sl)
      rw [hpreserve]
      have hold := hrep.2 query
      change (classBits second)[encodeSizeClass query]? =
        some (state.slSet query.fl query.sl) at hold
      rw [hold]
      have hslEq : (state.insert cls block).slSet query.fl query.sl =
          state.slSet query.fl query.sl := by
        rw [slSet_eq_decide_nonempty hvalid query]
        simp [Bins.State.insert, Bins.State.replaceChain,
          Bins.State.fromChains, Bins.Chains.replace, hquery]
      rw [hslEq]

theorem insertClassArrays_preserves_bitmaps
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : InsertClassResult} {state : Bins.State} {cls : SizeClass}
    {inserted : Block}
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second) (hvalid : Bins.Valid state)
    (hbin : bin = encodeSizeClass cls)
    (hinsert : insertClassArrays second first heads next previous bin block =
      some result) :
    RepresentsSecondBitmap result.second (state.insert cls inserted) ∧
      FirstBitmapRep result.first result.second := by
  have hresult := insertClassArrays_result hinsert
  rcases hresult with ⟨_, hfl, _, _, _, hsecondEq, hfirstEq⟩
  have hsecondSet : result.second = setClassBit second bin := by
    rw [hsecondEq]
    rfl
  constructor
  · rw [hsecondSet, hbin]
    exact setClassBit_represents_insert hsecond hvalid cls inserted
  · rw [hsecondSet, hfirstEq]
    exact setClassBit_preserves_firstBitmapRep hfirst hfl

def clearSecondBit (bitmap : BitVec 32) (bit : Nat) : BitVec 32 :=
  bitmap &&& ~~~(BitVec.ofNat 32 1 <<< bit)

theorem clearSecondBit_getLsbD (bitmap : BitVec 32) (bit index : Nat) :
    (clearSecondBit bitmap bit).getLsbD index =
      if index = bit ∧ index < 32 then false else bitmap.getLsbD index := by
  simp only [clearSecondBit, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  by_cases hindex : index < 32 <;> by_cases heq : index = bit
  · subst bit
    simp [hindex]
  ·
    by_cases hbefore : index < bit
    · simp [hindex, heq, hbefore]
    · have htestFalse : Nat.testBit 1 (index - bit) = false := by
        cases htest : Nat.testBit 1 (index - bit) with
        | false => rfl
        | true =>
          have hzero := Nat.testBit_one_eq_true_iff_self_eq_zero.mp htest
          omega
      simp [hindex, heq, hbefore, htestFalse]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]
  · have hbitmap := BitVec.getLsbD_of_ge bitmap index (by omega)
    simp [hindex, hbitmap]

def clearClassBit (second : List (BitVec 32)) (bin : Nat) :
    List (BitVec 32) :=
  let fl := bin / 32
  let sl := bin % 32
  let bitmap := second[fl]?.getD 0
  second.set fl (clearSecondBit bitmap sl)

theorem clearClassBit_length (second : List (BitVec 32)) (bin : Nat) :
    (clearClassBit second bin).length = second.length := by
  simp [clearClassBit]

theorem clearClassBit_selected_false {second : List (BitVec 32)} {bin : Nat}
    (hfl : bin / 32 < second.length) :
    (classBits (clearClassBit second bin))[bin]? = some false := by
  have hsl : bin % 32 < 32 := Nat.mod_lt bin (by decide)
  have hset : (clearClassBit second bin)[bin / 32]? =
      some (clearSecondBit second[bin / 32] (bin % 32)) := by
    simp [clearClassBit, hfl]
  have hclass := classBits_get hset hsl
  rw [clearSecondBit_getLsbD] at hclass
  simp [hsl] at hclass
  rw [Nat.mul_comm (bin / 32) 32, Nat.div_add_mod] at hclass
  exact hclass

theorem clearClassBit_preserves_other {second : List (BitVec 32)}
    {bin other : Nat} (hfl : bin / 32 < second.length)
    (hother : other < second.length * 32) (hne : other ≠ bin) :
    (classBits (clearClassBit second bin))[other]? =
      (classBits second)[other]? := by
  have hotherFl : other / 32 < second.length := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    exact hother
  have hotherSl : other % 32 < 32 := Nat.mod_lt other (by decide)
  have hold : second[other / 32]? = some second[other / 32] := by
    simp [hotherFl]
  by_cases hword : other / 32 = bin / 32
  · have hnew : (clearClassBit second bin)[other / 32]? =
        some (clearSecondBit second[other / 32] (bin % 32)) := by
      simp [clearClassBit, hfl, hword]
    have hnewBit := classBits_get hnew hotherSl
    have holdBit := classBits_get hold hotherSl
    have hslNe : other % 32 ≠ bin % 32 := by
      intro hsl
      apply hne
      have hotherEq := Nat.div_add_mod other 32
      have hbinEq := Nat.div_add_mod bin 32
      omega
    rw [clearSecondBit_getLsbD] at hnewBit
    simp [hslNe] at hnewBit
    have heq := hnewBit.trans holdBit.symm
    rw [Nat.mul_comm (other / 32) 32, Nat.div_add_mod] at heq
    exact heq
  · have hnew : (clearClassBit second bin)[other / 32]? =
        some second[other / 32] := by
      simp [clearClassBit, hfl, List.getElem?_set_ne (Ne.symm hword), hold]
    have hnewBit := classBits_get hnew hotherSl
    have holdBit := classBits_get hold hotherSl
    have heq := hnewBit.trans holdBit.symm
    rw [Nat.mul_comm (other / 32) 32, Nat.div_add_mod] at heq
    exact heq

theorem clearClassBit_preserves_firstBitmapRep
    {second : List (BitVec 32)} {first : BitVec 64} (bin : Nat)
    (hrep : FirstBitmapRep first second) (hfl : bin / 32 < second.length) :
    let nextSecond := clearClassBit second bin
    let fl := bin / 32
    let nextFirst :=
      if nextSecond[fl]?.getD 0 = 0 then clearWordBit first fl else first
    FirstBitmapRep nextFirst nextSecond := by
  dsimp only
  apply firstBitmapRep_of_point
  · simpa [clearClassBit_length] using hrep.1
  · intro index hindex
    have hlength := hrep.1
    have hfl64 : bin / 32 < 64 := by omega
    by_cases hselected : index = bin / 32
    · subst index
      by_cases hzero :
          (clearClassBit second bin)[bin / 32]?.getD 0 = 0
      · simp only [hzero, if_true]
        rw [clearWordBit_getLsbD]
        simp [hfl64, hzero]
      · simp only [hzero, if_false]
        have hold := hrep.point hfl64
        have holdNonzero : second[bin / 32]?.getD 0 ≠ 0 := by
          intro holdZero
          apply hzero
          have hget : second[bin / 32]? = some second[bin / 32] := by
            simp [hfl]
          have hzElem : second[bin / 32] = 0 := by
            simpa [hget] using holdZero
          simp [clearClassBit, hfl, hzElem, clearSecondBit]
        have holdDecide :
            decide (second[bin / 32]?.getD 0 ≠ 0) = true := by
          exact decide_eq_true holdNonzero
        rw [holdDecide] at hold
        have nextDecide :
            decide ((clearClassBit second bin)[bin / 32]?.getD 0 ≠ 0) =
              true := by
          exact decide_eq_true hzero
        rw [nextDecide]
        exact hold
    · have hnextGet :
          (clearClassBit second bin)[index]? = second[index]? := by
        unfold clearClassBit
        exact List.getElem?_set_ne (Ne.symm hselected)
      by_cases hzero :
          (clearClassBit second bin)[bin / 32]?.getD 0 = 0
      · simp only [hzero, if_true]
        rw [clearWordBit_getLsbD]
        have hold := hrep.point hindex
        simpa [hselected, hnextGet] using hold
      · simp only [hzero, if_false]
        have hold := hrep.point hindex
        simpa [hnextGet] using hold

theorem clearClassBit_represents_replace_empty
    {second : List (BitVec 32)} {state : Bins.State}
    (hrep : RepresentsSecondBitmap second state) (hvalid : Bins.Valid state)
    (target : SizeClass) :
    RepresentsSecondBitmap
      (clearClassBit second
        (target.fl.val * secondLevelCount + target.sl.val))
      (state.replaceChain target []) := by
  let bin := target.fl.val * secondLevelCount + target.sl.val
  have hbinFl : bin / 32 = target.fl.val := by
    dsimp [bin]
    have hsl := target.sl.isLt
    simp only [secondLevelCount] at hsl ⊢
    omega
  have hbinBound : bin < second.length * 32 := by
    rw [hrep.1]
    dsimp [bin]
    have hfl := target.fl.isLt
    have hsl := target.sl.isLt
    simp only [firstLevelCount, secondLevelCount] at hfl hsl ⊢
    omega
  refine ⟨by simp [clearClassBit_length, hrep.1], ?_⟩
  intro query
  by_cases hquery : query = target
  · subst query
    have hfalse := clearClassBit_selected_false
      (second := second) (bin := bin) (by simpa [hbinFl, hrep.1])
    simpa [Bins.State.replaceChain, Bins.State.fromChains,
      Bins.Chains.replace, bin] using hfalse
  · have hindexNe :
        query.fl.val * secondLevelCount + query.sl.val ≠ bin := by
      intro heq
      apply hquery
      have hqsl := query.sl.isLt
      have htsl := target.sl.isLt
      have hflVal : query.fl.val = target.fl.val := by
        dsimp [bin] at heq
        simp only [secondLevelCount] at heq hqsl htsl
        have hdiv := congrArg (fun value : Nat => value / 32) heq
        omega
      have hslVal : query.sl.val = target.sl.val := by
        dsimp [bin] at heq
        simp only [secondLevelCount] at heq hqsl htsl
        omega
      have hfl : query.fl = target.fl := Fin.ext hflVal
      have hsl : query.sl = target.sl := Fin.ext hslVal
      cases query
      cases target
      simp_all
    have hqueryBound :
        query.fl.val * secondLevelCount + query.sl.val < second.length * 32 := by
      rw [hrep.1]
      have hfl := query.fl.isLt
      have hsl := query.sl.isLt
      simp only [firstLevelCount, secondLevelCount] at hfl hsl ⊢
      omega
    rw [clearClassBit_preserves_other
      (by simpa [hbinFl, hrep.1]) hqueryBound hindexNe, hrep.2 query]
    rw [slSet_eq_decide_nonempty hvalid query]
    simp [Bins.State.replaceChain, Bins.State.fromChains,
      Bins.Chains.replace, hquery]

theorem representsSecondBitmap_replace_nonempty
    {second : List (BitVec 32)} {state : Bins.State}
    (hrep : RepresentsSecondBitmap second state) (hvalid : Bins.Valid state)
    (target : SizeClass) {rest : List Block} (hrest : rest ≠ [])
    (hold : state.chains target ≠ []) :
    RepresentsSecondBitmap second (state.replaceChain target rest) := by
  refine ⟨hrep.1, ?_⟩
  intro query
  by_cases hquery : query = target
  · subst query
    rw [hrep.2 target]
    have holdSet := (hvalid.2.2.1 target.fl target.sl).2 hold
    simp [Bins.State.replaceChain, Bins.State.fromChains,
      Bins.Chains.replace, holdSet, hrest]
  · rw [hrep.2 query]
    rw [slSet_eq_decide_nonempty hvalid query]
    simp [Bins.State.replaceChain, Bins.State.fromChains,
      Bins.Chains.replace, hquery]

structure RemoveClassResult where
  second : List (BitVec 32)
  first : BitVec 64
  heads : List Nat
  next : List Nat
  previous : List Nat
deriving DecidableEq, Repr

/-- Remove a known (not necessarily head) free-list node and keep both TLSF
bitmap levels synchronized. This is the metadata operation needed before
coalescing a physical neighbor. -/
def removeClassArrays (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (bin block : Nat) :
    Option RemoveClassResult :=
  if bin ≥ heads.length then none else
  let fl := bin / 32
  if fl ≥ second.length then none else
  if block ≥ next.length then none else
  if block ≥ previous.length then none else
  let successor := next[block]?.getD next.length
  let predecessor := previous[block]?.getD next.length
  match removeArrays heads next previous bin block with
  | none => none
  | some (nextHeads, nextLinks, nextPrevious) =>
      if predecessor ≥ next.length ∧ successor ≥ next.length then
        let nextSecond := clearClassBit second bin
        let nextFirst :=
          if nextSecond[fl]?.getD 0 = 0 then clearWordBit first fl
          else first
        some (RemoveClassResult.mk nextSecond nextFirst nextHeads nextLinks
          nextPrevious)
      else
        some (RemoveClassResult.mk second first nextHeads nextLinks nextPrevious)

theorem removeClassArrays_result
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : RemoveClassResult}
    (hremove : removeClassArrays second first heads next previous bin block =
      some result) :
    bin < heads.length ∧ bin / 32 < second.length ∧
      block < next.length ∧ block < previous.length ∧
      removeArrays heads next previous bin block =
        some (result.heads, result.next, result.previous) ∧
      if previous[block]?.getD next.length ≥ next.length ∧
          next[block]?.getD next.length ≥ next.length then
        result.second = clearClassBit second bin ∧
          result.first =
            if result.second[bin / 32]?.getD 0 = 0 then
              clearWordBit first (bin / 32)
            else first
      else result.second = second ∧ result.first = first := by
  unfold removeClassArrays at hremove
  split at hremove <;> try contradiction
  next hbin =>
    dsimp only at hremove
    split at hremove <;> try contradiction
    next hfl =>
      split at hremove <;> try contradiction
      next hnext =>
        split at hremove <;> try contradiction
        next hprevious =>
          split at hremove <;> try contradiction
          next nextHeads nextLinks nextPrevious hmetadata =>
            split at hremove
            next hsuccessor =>
              simp only [Option.some.injEq] at hremove
              subst result
              exact ⟨Nat.lt_of_not_ge hbin, Nat.lt_of_not_ge hfl,
                Nat.lt_of_not_ge hnext, Nat.lt_of_not_ge hprevious,
                hmetadata, by simp [hsuccessor]⟩
            next hsuccessor =>
              simp only [Option.some.injEq] at hremove
              subst result
              exact ⟨Nat.lt_of_not_ge hbin, Nat.lt_of_not_ge hfl,
                Nat.lt_of_not_ge hnext, Nat.lt_of_not_ge hprevious,
                hmetadata, by simp [hsuccessor]⟩

structure ClassCandidateResult where
  block : Nat
  bin : Nat
  second : List (BitVec 32)
  first : BitVec 64
  heads : List Nat
  next : List Nat
  previous : List Nat
deriving DecidableEq, Repr

/-- Exact pure effect of the real 64 × 32 `tlsf_take_candidate_class`
lowering. The first-level cache is cleared only when removing the last member
also empties the selected second-level word. -/
def takeCandidateClassArrays (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (startFl startSl : Nat) :
    Option ClassCandidateResult :=
  match findNonemptyClassLowered second first startFl startSl with
  | none => none
  | some bin =>
      if bin ≥ heads.length then none else
      let fl := bin / 32
      if fl ≥ second.length then none else
      let block := heads[bin]?.getD next.length
      if block ≥ next.length then none else
      if block ≥ previous.length then none else
      let successor := next[block]?.getD next.length
      match removeArrays heads next previous bin block with
      | none => none
      | some (nextHeads, nextLinks, nextPrevious) =>
          if successor ≥ next.length then
            let nextSecond := clearClassBit second bin
            let nextFirst :=
              if nextSecond[fl]?.getD 0 = 0 then clearWordBit first fl
              else first
            some (ClassCandidateResult.mk block bin nextSecond nextFirst
              nextHeads nextLinks nextPrevious)
          else
            some (ClassCandidateResult.mk block bin second first nextHeads
              nextLinks nextPrevious)

theorem takeCandidateClassArrays_result
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {startFl startSl : Nat}
    {result : ClassCandidateResult}
    (htake : takeCandidateClassArrays second first heads next previous
      startFl startSl = some result) :
    findNonemptyClassLowered second first startFl startSl = some result.bin ∧
      result.bin < heads.length ∧ result.bin / 32 < second.length ∧
      result.block = heads[result.bin]?.getD next.length ∧
      result.block < next.length ∧ result.block < previous.length ∧
      removeArrays heads next previous result.bin result.block =
        some (result.heads, result.next, result.previous) ∧
      if next[result.block]?.getD next.length ≥ next.length then
        result.second = clearClassBit second result.bin ∧
          result.first =
            if result.second[result.bin / 32]?.getD 0 = 0 then
              clearWordBit first (result.bin / 32)
            else first
      else result.second = second ∧ result.first = first := by
  unfold takeCandidateClassArrays at htake
  split at htake <;> try contradiction
  next bin hfind =>
    split at htake <;> try contradiction
    next hbin =>
      dsimp only at htake
      split at htake <;> try contradiction
      next hfl =>
        split at htake <;> try contradiction
        next hnext =>
          split at htake <;> try contradiction
          next hprevious =>
            cases hremove : removeArrays heads next previous bin
                (heads[bin]?.getD next.length) with
            | none => simp [hremove] at htake
            | some arrays =>
              obtain ⟨nextHeads, nextLinks, nextPrevious⟩ := arrays
              simp only [hremove] at htake
              split at htake
              · split at htake <;> simp only [Option.some.injEq] at htake
                all_goals subst result
                all_goals simp_all [ClassCandidateResult.mk.injEq]
              · simp only [Option.some.injEq] at htake
                subst result
                simp_all [ClassCandidateResult.mk.injEq] <;> omega

structure CandidateResult where
  block : Nat
  bin : Nat
  words : List (BitVec 64)
  heads : List Nat
  next : List Nat
  previous : List Nat
deriving DecidableEq, Repr

/-- Exact pure effect of `tlsf_take_candidate`: all checks precede removal,
and an exhausted chain clears its cached nonempty bit. -/
def takeCandidateArrays (words : List (BitVec 64))
    (heads next previous : List Nat) (start : Nat) : Option CandidateResult :=
  match findNonemptyBinLowered words start with
  | none => none
  | some bin =>
      if bin ≥ heads.length then none else
      let wordIndex := bin / 64
      if wordIndex ≥ words.length then none else
      let block := heads[bin]?.getD next.length
      if block ≥ next.length then none else
      if block ≥ previous.length then none else
      let successor := next[block]?.getD next.length
      match removeArrays heads next previous bin block with
      | none => none
      | some (nextHeads, nextLinks, nextPrevious) =>
          let nextWords :=
            if successor ≥ next.length then clearBinBit words bin else words
          some (CandidateResult.mk block bin nextWords nextHeads nextLinks
            nextPrevious)

theorem takeCandidateArrays_result {words : List (BitVec 64)}
    {heads next previous : List Nat} {start : Nat} {result : CandidateResult}
    (htake : takeCandidateArrays words heads next previous start = some result) :
    findNonemptyBinLowered words start = some result.bin ∧
      start ≤ result.bin ∧ result.bin < words.length * 64 ∧
      (bitmapBits words)[result.bin]? = some true ∧
      result.bin < heads.length ∧ result.bin / 64 < words.length ∧
      result.block = heads[result.bin]?.getD next.length ∧
      result.block < next.length ∧ result.block < previous.length ∧
      removeArrays heads next previous result.bin result.block =
        some (result.heads, result.next, result.previous) ∧
      result.words =
        if next[result.block]?.getD next.length ≥ next.length then
          clearBinBit words result.bin else words := by
  unfold takeCandidateArrays at htake
  split at htake <;> try contradiction
  next bin hfind =>
    split at htake <;> try contradiction
    next hbin =>
      dsimp only at htake
      split at htake <;> try contradiction
      next hword =>
        split at htake <;> try contradiction
        next hnext =>
          split at htake <;> try contradiction
          next hprevious =>
            cases hremove : removeArrays heads next previous bin
                (heads[bin]?.getD next.length) with
            | none => simp [hremove] at htake
            | some arrays =>
              obtain ⟨nextHeads, nextLinks, nextPrevious⟩ := arrays
              simp only [hremove, Option.some.injEq] at htake
              subst result
              have hlogical : findNonemptyBin words start = some bin := by
                rw [← findNonemptyBinLowered_refines]
                exact hfind
              obtain ⟨hstart, hbound, hset⟩ := findNonemptyBin_sound hlogical
              simp only [CandidateResult.bin, CandidateResult.block,
                CandidateResult.words, CandidateResult.heads,
                CandidateResult.next, CandidateResult.previous]
              exact ⟨hfind, hstart, hbound, hset, by omega, by omega, trivial,
                by omega, by omega, hremove, trivial⟩

def linked (state : Metadata) : Nat → List Nat → Prop
  | _, [] => True
  | expectedPrevious, block :: rest =>
      block < state.next.length ∧
      block < state.previous.length ∧
      state.previous[block]? = some expectedPrevious ∧
      state.next[block]? = some (rest.head?.getD state.next.length) ∧
      linked state block rest

def chainPrevious : Nat → List Nat → Nat
  | expected, [] => expected
  | _, head :: tail => chainPrevious head tail

theorem chainPrevious_mem {expected : Nat} {pre : List Nat}
    (hnonempty : pre ≠ []) : chainPrevious expected pre ∈ pre := by
  induction pre generalizing expected with
  | nil => contradiction
  | cons head tail ih =>
      cases tail with
      | nil => simp [chainPrevious]
      | cons next more =>
        simp only [chainPrevious]
        exact List.mem_cons_of_mem head (ih (expected := head) (by simp))

theorem linked_member_bounds {state : Metadata} {expected : Nat}
    {chain : List Nat} (hlinked : linked state expected chain)
    {node : Nat} (hmem : node ∈ chain) :
    node < state.next.length ∧ node < state.previous.length := by
  induction chain generalizing expected with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [linked] at hlinked
      rcases hlinked with ⟨hheadNext, hheadPrevious, _, _, hrest⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact ⟨hheadNext, hheadPrevious⟩
      · exact ih hrest htail

theorem linked_decomposition_links {state : Metadata} {expected block : Nat}
    (pre rest : List Nat)
    (hlinked : linked state expected (pre ++ block :: rest)) :
    block < state.next.length ∧ block < state.previous.length ∧
      state.previous[block]? = some (chainPrevious expected pre) ∧
      state.next[block]? = some (rest.head?.getD state.next.length) := by
  induction pre generalizing expected with
  | nil =>
      simp only [List.nil_append, linked] at hlinked
      exact ⟨hlinked.1, hlinked.2.1,
        by simpa [chainPrevious] using hlinked.2.2.1,
        hlinked.2.2.2.1⟩
  | cons head tail ih =>
      simp only [List.cons_append, linked] at hlinked
      have htail := hlinked.2.2.2.2
      have result := ih (expected := head) htail
      simpa [chainPrevious] using result

theorem linked_decomposition_successor_is_sentinel_iff
    {state : Metadata} {expected block : Nat} (pre rest : List Nat)
    (hlinked : linked state expected (pre ++ block :: rest)) :
    state.next[block]?.getD state.next.length ≥ state.next.length ↔
      rest = [] := by
  have hlinks := linked_decomposition_links pre rest hlinked
  rw [hlinks.2.2.2]
  cases rest with
  | nil => simp
  | cons successor tail =>
      have hbound : successor < state.next.length :=
        (linked_member_bounds hlinked (by simp)).1
      simp [hbound]

theorem linked_decomposition_predecessor_is_sentinel_iff
    {state : Metadata} {block : Nat} (pre rest : List Nat)
    (hlinked : linked state state.next.length (pre ++ block :: rest)) :
    state.previous[block]?.getD state.next.length ≥ state.next.length ↔
      pre = [] := by
  have hlinks := linked_decomposition_links pre rest hlinked
  rw [hlinks.2.2.1]
  constructor
  · intro hsentinel
    cases pre with
    | nil => rfl
    | cons head tail =>
      exfalso
      have hmem : chainPrevious state.next.length (head :: tail) ∈
          (head :: tail) ++ block :: rest := by
        exact List.mem_append_left _ (chainPrevious_mem (by simp))
      have hbound := (linked_member_bounds hlinked hmem).1
      simp only [Option.getD_some] at hsentinel
      omega
  · intro hempty
    subst pre
    simp [chainPrevious]

theorem linked_decomposition_is_singleton_iff
    {state : Metadata} {block : Nat} (pre rest : List Nat)
    (hlinked : linked state state.next.length (pre ++ block :: rest)) :
    (state.previous[block]?.getD state.next.length ≥ state.next.length ∧
        state.next[block]?.getD state.next.length ≥ state.next.length) ↔
      pre = [] ∧ rest = [] := by
  rw [linked_decomposition_predecessor_is_sentinel_iff pre rest hlinked,
    linked_decomposition_successor_is_sentinel_iff pre rest hlinked]

theorem erase_decomposition_of_nodup {pre rest : List Nat} {block : Nat}
    (hnodup : (pre ++ block :: rest).Nodup) :
    (pre ++ block :: rest).erase block = pre ++ rest := by
  induction pre with
  | nil => simp
  | cons head tail ih =>
      change (head :: (tail ++ block :: rest)).Nodup at hnodup
      have hparts := List.nodup_cons.mp hnodup
      have hheadBlock : head ≠ block := by
        exact fun heq => hparts.1 (by simp [heq])
      have htail : (tail ++ block :: rest).Nodup := hparts.2
      simp [hheadBlock, ih htail]

theorem removeOffset_replacement_empty_iff_decomposition
    {blocks replacement : List Block} {removed : Block}
    {pre rest : List Nat} {block : Nat}
    (hvalid : FreeList.Valid blocks)
    (hchain : blocks.map Block.offset = pre ++ block :: rest)
    (hremove : FreeList.removeOffset blocks block =
      some (removed, replacement)) :
    replacement = [] ↔ pre = [] ∧ rest = [] := by
  have hoffsets := FreeList.removeOffset_offsets hremove
  have hnodup : (pre ++ block :: rest).Nodup := by
    rw [← hchain]
    exact hvalid.2
  rw [hchain, erase_decomposition_of_nodup hnodup] at hoffsets
  constructor
  · intro hempty
    rw [hempty] at hoffsets
    simp only [List.map_nil] at hoffsets
    exact List.append_eq_nil_iff.mp hoffsets.symm
  · rintro ⟨rfl, rfl⟩
    simp only [List.append_nil] at hoffsets
    exact List.map_eq_nil_iff.mp hoffsets

set_option maxHeartbeats 400000 in
/-- Removing an arbitrary represented node preserves both bitmap levels,
provided the abstract replacement chain is empty exactly when that node was
the bin's sole member.  Intrusive-link refinement supplies this equivalence
when it identifies the replacement with the old chain with `block` erased. -/
theorem removeClassArrays_preserves_bitmaps_of_decomposition
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : RemoveClassResult} {state : Bins.State} {cls : SizeClass}
    {pre rest : List Nat} {replacement : List Block}
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second) (hvalid : Bins.Valid state)
    (hbin : bin = encodeSizeClass cls)
    (hlinked : linked { heads, next, previous } next.length
      (pre ++ block :: rest))
    (hold : state.chains cls ≠ [])
    (hempty : replacement = [] ↔ pre = [] ∧ rest = [])
    (hremove : removeClassArrays second first heads next previous bin block =
      some result) :
    RepresentsSecondBitmap result.second
        (state.replaceChain cls replacement) ∧
      FirstBitmapRep result.first result.second := by
  have heffect := (removeClassArrays_result hremove).2.2.2.2.2
  have hsingleton := linked_decomposition_is_singleton_iff pre rest hlinked
  have hfl : bin / 32 < second.length :=
    (removeClassArrays_result hremove).2.1
  have hfirstClear := clearClassBit_preserves_firstBitmapRep bin hfirst hfl
  by_cases hsole : pre = [] ∧ rest = []
  · have hsentinel := hsingleton.2 hsole
    rw [if_pos hsentinel] at heffect
    have hreplacement : replacement = [] := hempty.2 hsole
    constructor
    · rw [heffect.1, hreplacement, hbin]
      exact clearClassBit_represents_replace_empty hsecond hvalid cls
    · rw [heffect.2, heffect.1]
      exact hfirstClear
  · have hnotsentinel : ¬(previous[block]?.getD next.length ≥ next.length ∧
        next[block]?.getD next.length ≥ next.length) := by
      exact fun hsentinel => hsole (hsingleton.1 hsentinel)
    rw [if_neg hnotsentinel] at heffect
    have hreplacement : replacement ≠ [] := by
      exact fun h => hsole (hempty.1 h)
    rw [heffect.1, heffect.2]
    exact ⟨representsSecondBitmap_replace_nonempty hsecond hvalid cls
      hreplacement hold, hfirst⟩

/-- A logical bin chain is represented by the head table and intrusive links. -/
def RepresentsBin (state : Metadata) (bin : Nat) (chain : List Nat) : Prop :=
  bin < state.heads.length ∧
  state.next.length = state.previous.length ∧
  state.heads[bin]?.getD 0 = chain.head?.getD state.next.length ∧
  linked state state.next.length chain ∧
  chain.Nodup

def RepresentsBins (metadata : Metadata) (state : Bins.State) : Prop :=
  ∀ cls : SizeClass,
    RepresentsBin metadata
      (cls.fl.val * secondLevelCount + cls.sl.val)
      ((state.chains cls).map Block.offset)

/-- End-to-end bitmap refinement for arbitrary class removal.  The abstract
free-list operation itself supplies the singleton/non-singleton fact consumed
by the lowered predecessor/successor test. -/
theorem removeClassArrays_preserves_bitmaps
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : RemoveClassResult} {state nextState : Bins.State}
    {cls : SizeClass} {removed : Block}
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second) (hvalid : Bins.Valid state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hbin : bin = encodeSizeClass cls)
    (habstract : state.removeOffset cls block = some (removed, nextState))
    (hremove : removeClassArrays second first heads next previous bin block =
      some result) :
    RepresentsSecondBitmap result.second nextState ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨replacement, hremoveOffset, rfl⟩ :=
    Bins.removeOffset_success habstract
  have horigin := FreeList.removeOffset_removed_origin (hvalid.1 cls) hremoveOffset
  obtain ⟨old, holdMem, holdOffset, _⟩ := horigin
  have hmember : block ∈ (state.chains cls).map Block.offset := by
    rw [← holdOffset]
    exact List.mem_map_of_mem holdMem
  obtain ⟨pre, rest, hshape⟩ := List.mem_iff_append.mp hmember
  have hrep := hbins cls
  have hlinked := hrep.2.2.2.1
  rw [hshape] at hlinked
  exact removeClassArrays_preserves_bitmaps_of_decomposition hsecond hfirst
    hvalid hbin hlinked (by exact fun hempty => by simp [hempty] at hmember)
    (removeOffset_replacement_empty_iff_decomposition (hvalid.1 cls)
      hshape hremoveOffset) hremove

def BinsOffsetsDisjoint (state : Bins.State) : Prop :=
  ∀ {left right : SizeClass}, left ≠ right → ∀ offset,
    offset ∈ (state.chains left).map Block.offset →
    offset ∈ (state.chains right).map Block.offset → False

theorem represented_front_successor_is_sentinel_iff
    {state : Metadata} {bin block : Nat} {rest : List Nat}
    (hrep : RepresentsBin state bin (block :: rest)) :
    state.next[block]?.getD state.next.length ≥ state.next.length ↔
      rest = [] := by
  rcases hrep with ⟨_, _, _, hlinked, _⟩
  simp only [linked] at hlinked
  rcases hlinked with ⟨_, _, _, hnext, hrestLinked⟩
  constructor
  · intro hsentinel
    cases rest with
    | nil => rfl
    | cons successor more =>
        simp only [List.head?_cons, Option.getD_some] at hnext
        simp only [linked] at hrestLinked
        have hsuccessor := hrestLinked.1
        have hvalue : state.next[block]?.getD state.next.length =
            successor := by simp [hnext]
        rw [hvalue] at hsentinel
        omega
  · intro hempty
    subst rest
    have hvalue : state.next[block]?.getD state.next.length =
        state.next.length := by simp [hnext]
    omega

theorem takeCandidateClassArrays_preserves_bitmaps
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {startFl startSl : Nat}
    {result : ClassCandidateResult} {state : Bins.State}
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second) (hvalid : Bins.Valid state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (htake : takeCandidateClassArrays second first heads next previous
      startFl startSl = some result) :
    ∃ cls removed rest,
      classOfBin? result.bin = some cls ∧
      FreeList.removeFront (state.chains cls) = some (removed, rest) ∧
      result.block = removed.offset ∧
      RepresentsSecondBitmap result.second (state.replaceChain cls rest) ∧
      FirstBitmapRep result.first result.second := by
  have hresult := takeCandidateClassArrays_result htake
  rcases hresult with ⟨hfind, _, hfl, hblock, _, _, hremove, heffect⟩
  obtain ⟨cls, hclass, hbin, hnonempty⟩ :=
    findNonemptyClassLowered_selects_nonempty hsecond hvalid hfind
  obtain ⟨removed, rest, hremoveFront⟩ :=
    FreeList.removeFront_exists hnonempty
  refine ⟨cls, removed, rest, hclass, hremoveFront, ?_, ?_, ?_⟩
  · have hfront := FreeList.removeFront_removes_head hremoveFront
    have hrep := hbins cls
    rw [← hbin] at hrep
    have hheadsGet : heads[result.bin]? = some heads[result.bin] := by
      simp [hrep.1]
    have hhead := hrep.2.2.1
    rw [hheadsGet, hfront.1] at hhead
    simp only [Option.getD_some] at hhead
    rw [hblock, hheadsGet]
    simpa using hhead
  · have hfront := FreeList.removeFront_removes_head hremoveFront
    have hrep := hbins cls
    rw [← hbin] at hrep
    have hblockEq : result.block = removed.offset := by
      have hheadsGet : heads[result.bin]? = some heads[result.bin] := by
        simp [hrep.1]
      have hhead := hrep.2.2.1
      rw [hheadsGet, hfront.1] at hhead
      simp only [Option.getD_some] at hhead
      rw [hblock, hheadsGet]
      simpa using hhead
    have hchainShape :
        (state.chains cls).map Block.offset =
          result.block :: rest.map Block.offset := by
      cases hchain : state.chains cls with
      | nil => exact (hnonempty hchain).elim
      | cons head tail =>
        have htail := hfront.2
        simp only [hchain, List.map_cons, List.head?_cons,
          List.tail_cons, Option.some.injEq] at hfront htail
        simp [hchain, hblockEq, hfront.1, htail]
    rw [hchainShape] at hrep
    have hsentinel := represented_front_successor_is_sentinel_iff hrep
    have hrestIff :
        next[result.block]?.getD next.length ≥ next.length ↔ rest = [] := by
      rw [hsentinel]
      simp
    by_cases hempty : rest = []
    · have hsent : next[result.block]?.getD next.length ≥ next.length :=
        hrestIff.2 hempty
      rw [if_pos hsent] at heffect
      rw [heffect.1, hempty, hbin]
      exact clearClassBit_represents_replace_empty hsecond hvalid cls
    · have hnonsent : ¬next[result.block]?.getD next.length ≥ next.length :=
        fun h => hempty (hrestIff.1 h)
      rw [if_neg hnonsent] at heffect
      exact heffect.1 ▸ representsSecondBitmap_replace_nonempty
        hsecond hvalid cls hempty hnonempty
  · have hfront := FreeList.removeFront_removes_head hremoveFront
    have hrep := hbins cls
    rw [← hbin] at hrep
    have hblockEq : result.block = removed.offset := by
      have hheadsGet : heads[result.bin]? = some heads[result.bin] := by
        simp [hrep.1]
      have hhead := hrep.2.2.1
      rw [hheadsGet, hfront.1] at hhead
      simp only [Option.getD_some] at hhead
      rw [hblock, hheadsGet]
      simpa using hhead
    have hchainShape :
        (state.chains cls).map Block.offset =
          result.block :: rest.map Block.offset := by
      cases hchain : state.chains cls with
      | nil => exact (hnonempty hchain).elim
      | cons head tail =>
        have htail := hfront.2
        simp only [hchain, List.map_cons, List.head?_cons,
          List.tail_cons, Option.some.injEq] at hfront htail
        simp [hchain, hblockEq, hfront.1, htail]
    rw [hchainShape] at hrep
    have hsentinel := represented_front_successor_is_sentinel_iff hrep
    by_cases hempty : rest = []
    · have hsent : next[result.block]?.getD next.length ≥ next.length := by
        rw [hsentinel]
        simp [hempty]
      rw [if_pos hsent] at heffect
      have hsecondEq := heffect.1
      have hfirstEq := heffect.2
      rw [hsecondEq] at hfirstEq ⊢
      rw [hfirstEq]
      exact clearClassBit_preserves_firstBitmapRep result.bin hfirst hfl
    · have hnonsent : ¬next[result.block]?.getD next.length ≥ next.length := by
        rw [hsentinel]
        simp [hempty]
      rw [if_neg hnonsent] at heffect
      rw [heffect.1, heffect.2]
      exact hfirst

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

theorem insertClassArrays_preserves_metadata_lengths
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : InsertClassResult}
    (hinsert : insertClassArrays second first heads next previous bin block =
      some result) :
    result.heads.length = heads.length ∧ result.next.length = next.length ∧
      result.previous.length = previous.length := by
  have hresult := insertClassArrays_result hinsert
  rcases hresult with ⟨_, _, _, _, hmetadata, _, _⟩
  exact insert_preserves_lengths hmetadata

theorem insert_frames_other_bin
    {state nextState : Metadata} {bin otherBin block : Nat}
    {selectedChain otherChain : List Nat}
    (hselected : RepresentsBin state bin selectedChain)
    (hother : RepresentsBin state otherBin otherChain)
    (hbinsNe : otherBin ≠ bin)
    (hblockFresh : block ∉ otherChain)
    (hchainsDisjoint : ∀ offset, offset ∈ selectedChain →
      offset ∈ otherChain → False)
    (hinsert : insert state bin block = some nextState) :
    RepresentsBin nextState otherBin otherChain := by
  rcases hselected with
    ⟨_, hselectedLengths, hselectedHead, hselectedLinked, _⟩
  rcases hother with
    ⟨hotherBin, hotherLengths, hotherHead, hotherLinked, hotherNodup⟩
  have hresult := insert_result hinsert
  rcases hresult with
    ⟨_, _, _, hheads, hnext, hprevious⟩
  have hlengths := insert_preserves_lengths hinsert
  let oldHead := state.heads[bin]?.getD 0
  have holdHeadFresh : oldHead ∉ otherChain := by
    cases hchain : selectedChain with
    | nil =>
        have holdSentinel : oldHead = state.next.length := by
          simpa [oldHead, hchain] using hselectedHead
        intro hmem
        have hbound := (linked_member_bounds hotherLinked hmem).1
        rw [holdSentinel] at hbound
        omega
    | cons head rest =>
        have holdHead : oldHead = head := by
          simpa [oldHead, hchain] using hselectedHead
        intro hmem
        apply hchainsDisjoint oldHead
        · rw [holdHead]
          simp [hchain]
        · exact hmem
  refine ⟨by omega, by omega, ?_, ?_, hotherNodup⟩
  · rw [hheads, List.getElem?_set_ne (Ne.symm hbinsNe)]
    rw [hlengths.2.1]
    exact hotherHead
  · rw [hlengths.2.1]
    apply linked_congr hlengths.2.1 hlengths.2.2
    · intro node hmem
      rw [hnext, List.getElem?_set_ne]
      intro heq
      apply hblockFresh
      rw [heq]
      exact hmem
    · intro node hmem
      rw [hprevious]
      have hnodeBlock : node ≠ block := by
        intro heq
        apply hblockFresh
        rw [← heq]
        exact hmem
      have hnodeHead : node ≠ oldHead := by
        intro heq
        apply holdHeadFresh
        rw [← heq]
        exact hmem
      change node ≠ state.heads[bin]?.getD 0 at hnodeHead
      split
      · rw [List.getElem?_set_ne (Ne.symm hnodeHead),
          List.getElem?_set_ne (Ne.symm hnodeBlock)]
      · rw [List.getElem?_set_ne (Ne.symm hnodeBlock)]
    · exact hotherLinked

theorem insertClassArrays_represents_selected
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : InsertClassResult} {chain : List Nat}
    (hrep : RepresentsBin { heads, next, previous } bin chain)
    (hfresh : block ∉ chain)
    (hinsert : insertClassArrays second first heads next previous bin block =
      some result) :
    RepresentsBin (Metadata.mk result.heads result.next result.previous)
      bin (block :: chain) := by
  have hresult := insertClassArrays_result hinsert
  rcases hresult with ⟨_, _, _, _, hmetadata, _, _⟩
  exact insert_represents hrep hfresh hmetadata

theorem insertClassArrays_preserves_bins
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : InsertClassResult} {state : Bins.State} {cls : SizeClass}
    {inserted : Block}
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, inserted.offset ∉
      (state.chains query).map Block.offset)
    (hblock : block = inserted.offset)
    (hbin : bin = encodeSizeClass cls)
    (hinsert : insertClassArrays second first heads next previous bin block =
      some result) :
    RepresentsBins (Metadata.mk result.heads result.next result.previous)
      (state.insert cls inserted) := by
  subst bin
  intro query
  by_cases hquery : query = cls
  · subst query
    have hselected := insertClassArrays_represents_selected
      (hrep := hbins cls) (hfresh := by simpa [hblock] using hfresh cls)
      hinsert
    have hchain :
        ((state.insert cls inserted).chains cls).map Block.offset =
          inserted.offset :: (state.chains cls).map Block.offset := by
      cases hcurrent : state.chains cls <;>
        simp [Bins.State.insert, Bins.State.replaceChain,
          Bins.State.fromChains, Bins.Chains.replace,
          FreeList.insertFront, FreeList.withLinks, hcurrent]
    change RepresentsBin (Metadata.mk result.heads result.next result.previous)
      (encodeSizeClass cls)
      (((state.insert cls inserted).chains cls).map Block.offset)
    rw [hchain, ← hblock]
    exact hselected
  · have hresult := insertClassArrays_result hinsert
    rcases hresult with ⟨_, _, _, _, hmetadata, _, _⟩
    have hindexNe : encodeSizeClass query ≠ encodeSizeClass cls := by
      intro heq
      exact hquery (classIndex_injective heq)
    have hframe := insert_frames_other_bin
      (hselected := hbins cls) (hother := hbins query)
      (hbinsNe := hindexNe)
      (hblockFresh := by simpa [hblock] using hfresh query)
      (hchainsDisjoint := by
        intro offset hselectedMem hqueryMem
        exact hdisjoint (Ne.symm hquery) offset hselectedMem hqueryMem)
      hmetadata
    have hchain : (state.insert cls inserted).chains query =
        state.chains query := by
      simp [Bins.State.insert, Bins.State.replaceChain,
        Bins.State.fromChains, Bins.Chains.replace, hquery]
    change RepresentsBin (Metadata.mk result.heads result.next result.previous)
      (encodeSizeClass query)
      (((state.insert cls inserted).chains query).map Block.offset)
    rw [hchain]
    exact hframe

theorem insert_preserves_offsets_disjoint
    {state : Bins.State} {cls : SizeClass} {inserted : Block}
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, inserted.offset ∉
      (state.chains query).map Block.offset) :
    BinsOffsetsDisjoint (state.insert cls inserted) := by
  have hselected : ((state.insert cls inserted).chains cls).map Block.offset =
      inserted.offset :: (state.chains cls).map Block.offset := by
    cases hcurrent : state.chains cls <;>
      simp [Bins.State.insert, Bins.State.replaceChain,
        Bins.State.fromChains, Bins.Chains.replace,
        FreeList.insertFront, FreeList.withLinks, hcurrent]
  intro left right hne offset hleft hright
  by_cases hleftCls : left = cls
  · subst left
    have hrightCls : right ≠ cls := fun h => hne h.symm
    rw [hselected] at hleft
    have hrightOld : offset ∈ (state.chains right).map Block.offset := by
      simpa [Bins.State.insert,
        Bins.replaceChain_other state (FreeList.insertFront inserted
          (state.chains cls)) hrightCls] using hright
    simp only [List.mem_cons] at hleft
    rcases hleft with hoffset | hleftOld
    · exact (hfresh right) (by simpa [hoffset] using hrightOld)
    · exact hdisjoint hne offset hleftOld hrightOld
  · by_cases hrightCls : right = cls
    · subst right
      have hleftOld : offset ∈ (state.chains left).map Block.offset := by
        simpa [Bins.State.insert,
          Bins.replaceChain_other state (FreeList.insertFront inserted
            (state.chains cls)) hleftCls] using hleft
      rw [hselected] at hright
      simp only [List.mem_cons] at hright
      rcases hright with hoffset | hrightOld
      · exact (hfresh left) (by simpa [hoffset] using hleftOld)
      · exact hdisjoint hne offset hleftOld hrightOld
    · have hleftOld : offset ∈ (state.chains left).map Block.offset := by
        simpa [Bins.State.insert,
          Bins.replaceChain_other state (FreeList.insertFront inserted
            (state.chains cls)) hleftCls] using hleft
      have hrightOld : offset ∈ (state.chains right).map Block.offset := by
        simpa [Bins.State.insert,
          Bins.replaceChain_other state (FreeList.insertFront inserted
            (state.chains cls)) hrightCls] using hright
      exact hdisjoint hne offset hleftOld hrightOld

/-- End-to-end refinement of the concrete Luffs class insertion to the
abstract TLSF bin transition, including intrusive chains and both cache levels. -/
theorem insertClassArrays_refines_insert
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : InsertClassResult} {state : Bins.State} {cls : SizeClass}
    {inserted : Block}
    (hvalid : Bins.Valid state)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, inserted.offset ∉
      (state.chains query).map Block.offset)
    (hbelongs : Bins.Belongs cls inserted)
    (hblock : block = inserted.offset)
    (hbin : bin = encodeSizeClass cls)
    (hinsert : insertClassArrays second first heads next previous bin block =
      some result) :
    Bins.Valid (state.insert cls inserted) ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
        (state.insert cls inserted) ∧
      RepresentsSecondBitmap result.second (state.insert cls inserted) ∧
      FirstBitmapRep result.first result.second := by
  have hbitmaps := insertClassArrays_preserves_bitmaps
    (inserted := inserted) hsecond hfirst hvalid hbin hinsert
  exact ⟨Bins.insert_valid hvalid cls inserted hbelongs (hfresh cls),
    insertClassArrays_preserves_bins hbins hdisjoint hfresh hblock hbin hinsert,
    hbitmaps.1, hbitmaps.2⟩

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

theorem remove_effect {state nextState : Metadata} {bin block : Nat}
    (hremove : remove state bin block = some nextState) :
    let successor := state.next[block]?.getD state.next.length
    let predecessor := state.previous[block]?.getD state.next.length
    nextState.heads =
        (if predecessor ≥ state.next.length then state.heads.set bin successor
        else state.heads) ∧
      nextState.next =
        ((if predecessor < state.next.length then
          state.next.set predecessor successor else state.next).set
            block state.next.length) ∧
      nextState.previous =
        (if successor < state.previous.length then
          state.previous.set successor predecessor else state.previous).set
            block state.previous.length := by
  have hbounds := remove_result hremove
  rcases hbounds with ⟨hbin, hnext, hprevious⟩
  unfold remove at hremove
  simp only [Nat.not_le.mpr hbin, Nat.not_le.mpr hnext,
    Nat.not_le.mpr hprevious, if_false] at hremove
  simp only [Option.some.injEq] at hremove
  subst nextState
  exact ⟨rfl, rfl, rfl⟩

theorem remove_preserves_other_node {state nextState : Metadata}
    {bin block node : Nat}
    (hremove : remove state bin block = some nextState)
    (hblock : node ≠ block)
    (hpredecessor : node ≠ state.previous[block]?.getD state.next.length)
    (hsuccessor : node ≠ state.next[block]?.getD state.next.length) :
    nextState.next[node]? = state.next[node]? ∧
      nextState.previous[node]? = state.previous[node]? := by
  have heffect := remove_effect hremove
  dsimp only at heffect
  rcases heffect with ⟨_, hnext, hprevious⟩
  constructor
  · rw [hnext]
    split
    · rw [List.getElem?_set_ne (Ne.symm hblock),
        List.getElem?_set_ne (Ne.symm hpredecessor)]
    · rw [List.getElem?_set_ne (Ne.symm hblock)]
  · rw [hprevious]
    split
    · rw [List.getElem?_set_ne (Ne.symm hblock),
        List.getElem?_set_ne (Ne.symm hsuccessor)]
    · rw [List.getElem?_set_ne (Ne.symm hblock)]

theorem remove_preserves_next {state nextState : Metadata}
    {bin block node : Nat}
    (hremove : remove state bin block = some nextState)
    (hblock : node ≠ block)
    (hpredecessor : node ≠ state.previous[block]?.getD state.next.length) :
    nextState.next[node]? = state.next[node]? := by
  have heffect := (remove_effect hremove).2.1
  rw [heffect]
  split
  · rw [List.getElem?_set_ne (Ne.symm hblock),
      List.getElem?_set_ne (Ne.symm hpredecessor)]
  · rw [List.getElem?_set_ne (Ne.symm hblock)]

theorem remove_preserves_previous {state nextState : Metadata}
    {bin block node : Nat}
    (hremove : remove state bin block = some nextState)
    (hblock : node ≠ block)
    (hsuccessor : node ≠ state.next[block]?.getD state.next.length) :
    nextState.previous[node]? = state.previous[node]? := by
  have heffect := (remove_effect hremove).2.2
  rw [heffect]
  split
  · rw [List.getElem?_set_ne (Ne.symm hblock),
      List.getElem?_set_ne (Ne.symm hsuccessor)]
  · rw [List.getElem?_set_ne (Ne.symm hblock)]

theorem remove_heads_of_predecessor_lt {state nextState : Metadata}
    {bin block : Nat} (hremove : remove state bin block = some nextState)
    (hpredecessor : state.previous[block]?.getD state.next.length <
      state.next.length) :
    nextState.heads = state.heads := by
  have heffect := (remove_effect hremove).1
  rw [heffect]
  simp [Nat.not_le.mpr hpredecessor]

theorem remove_bypasses_predecessor {state nextState : Metadata}
    {bin block predecessor successor : Nat}
    (hremove : remove state bin block = some nextState)
    (hpred : state.previous[block]? = some predecessor)
    (hsucc : state.next[block]? = some successor)
    (hpredecessorBound : predecessor < state.next.length)
    (hne : predecessor ≠ block) :
    nextState.next[predecessor]? = some successor := by
  have heffect := (remove_effect hremove).2.1
  rw [heffect]
  have hpredValue : state.previous[block]?.getD state.next.length =
      predecessor := by simp [hpred]
  have hsuccValue : state.next[block]?.getD state.next.length = successor := by
    simp [hsucc]
  simp only [hpredValue, hsuccValue, hpredecessorBound, if_true]
  rw [List.getElem?_set_ne (Ne.symm hne),
    List.getElem?_set_self hpredecessorBound]

theorem remove_bypasses_successor {state nextState : Metadata}
    {bin block predecessor successor : Nat}
    (hremove : remove state bin block = some nextState)
    (hpred : state.previous[block]? = some predecessor)
    (hsucc : state.next[block]? = some successor)
    (hsuccessorBound : successor < state.previous.length)
    (hne : successor ≠ block) :
    nextState.previous[successor]? = some predecessor := by
  have heffect := (remove_effect hremove).2.2
  rw [heffect]
  have hpredValue : state.previous[block]?.getD state.next.length =
      predecessor := by simp [hpred]
  have hsuccValue : state.next[block]?.getD state.next.length = successor := by
    simp [hsucc]
  simp only [hpredValue, hsuccValue, hsuccessorBound, if_true]
  rw [List.getElem?_set_ne (Ne.symm hne),
    List.getElem?_set_self hsuccessorBound]

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

/-- Local splice lemma for removing the first node after a known predecessor.
The predecessor may be the bin sentinel or an earlier node in the same chain. -/
theorem linked_remove_first {state nextState : Metadata} {bin block expected : Nat}
    {rest : List Nat}
    (hremove : remove state bin block = some nextState)
    (hlinked : linked state expected (block :: rest))
    (hnodup : (block :: rest).Nodup)
    (hexpected : expected ∉ block :: rest) :
    linked nextState expected rest := by
  simp only [linked] at hlinked
  rcases hlinked with ⟨hblockNext, hblockPrevious, hpred, hsucc, hrest⟩
  cases rest with
  | nil => trivial
  | cons successor tail =>
      simp only [List.head?_cons, Option.getD_some] at hsucc
      simp only [linked] at hrest
      rcases hrest with
        ⟨hsuccessorNext, hsuccessorPrevious, hsuccessorPred,
          hsuccessorSucc, htail⟩
      have hlens := remove_preserves_lengths hremove
      have hsuccessorBlock : successor ≠ block := by
        exact fun heq => (List.nodup_cons.mp hnodup).1 (by simp [heq])
      have hsuccessorExpected : successor ≠ expected := by
        exact fun heq => hexpected (by simp [← heq])
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩
      · exact remove_bypasses_successor hremove hpred hsucc
          hsuccessorPrevious hsuccessorBlock
      · rw [remove_preserves_next hremove hsuccessorBlock
          (by simpa [hpred] using hsuccessorExpected)]
        simpa [hlens.2.1] using hsuccessorSucc
      · refine linked_congr (state := state) (nextState := nextState)
          hlens.2.1 hlens.2.2 ?_ ?_ htail
        · intro node hnode
          have hnodeBlock : node ≠ block := by
            exact fun heq => (List.nodup_cons.mp hnodup).1 (by
              simp [← heq, hnode])
          have hnodeExpected : node ≠ expected := by
            exact fun heq => hexpected (by simp [← heq, hnode])
          exact remove_preserves_next hremove hnodeBlock
            (by simpa [hpred] using hnodeExpected)
        · intro node hnode
          have hnodeBlock : node ≠ block := by
            exact fun heq => (List.nodup_cons.mp hnodup).1 (by
              simp [← heq, hnode])
          have hnodeSuccessor : node ≠ successor := by
            exact fun heq =>
              (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1 (by
                simpa [← heq] using hnode)
          exact remove_preserves_previous hremove hnodeBlock
            (by simpa [hsucc] using hnodeSuccessor)

/-- Splicing an arbitrary node out of a well-formed intrusive chain preserves
the chain order of the prefix and suffix. -/
theorem linked_remove_decomposition {state nextState : Metadata}
    {bin block expected : Nat} {pre rest : List Nat}
    (hremove : remove state bin block = some nextState)
    (hlinked : linked state expected (pre ++ block :: rest))
    (hnodup : (pre ++ block :: rest).Nodup)
    (hexpected : expected ∉ pre ++ block :: rest) :
    linked nextState expected (pre ++ rest) := by
  induction pre generalizing expected with
  | nil =>
      exact linked_remove_first hremove hlinked hnodup hexpected
  | cons head tail ih =>
      simp only [List.cons_append, linked] at hlinked
      rcases hlinked with
        ⟨hheadNext, hheadPrevious, hheadPred, hheadSucc, htailLinked⟩
      change (head :: (tail ++ block :: rest)).Nodup at hnodup
      have hparts := List.nodup_cons.mp hnodup
      have htailResult := ih htailLinked hparts.2 hparts.1
      have hlens := remove_preserves_lengths hremove
      have hheadBlock : head ≠ block := by
        exact fun heq => hparts.1 (by simp [heq])
      cases tail with
      | nil =>
          have hlinks := linked_decomposition_links ([] : List Nat) rest
            htailLinked
          have hsuccessorNe :
              head ≠ state.next[block]?.getD state.next.length := by
            rw [hlinks.2.2.2]
            cases rest with
            | nil =>
                simp only [List.head?_nil, Option.getD_none]
                exact Nat.ne_of_lt hheadNext
            | cons successor more =>
                exact fun heq => hparts.1 (by simp [heq])
          refine ⟨by omega, by omega, ?_, ?_, htailResult⟩
          · rw [remove_preserves_previous hremove hheadBlock hsuccessorNe]
            exact hheadPred
          · have hbypass := remove_bypasses_predecessor hremove
                hlinks.2.2.1 hlinks.2.2.2 hheadNext hheadBlock
            simpa [chainPrevious, hlens.2.1] using hbypass
      | cons first more =>
          have hlinks := linked_decomposition_links (first :: more) rest
            (by simpa using htailLinked)
          have hpredecessorNe :
              head ≠ state.previous[block]?.getD state.next.length := by
            rw [hlinks.2.2.1]
            exact fun heq => hparts.1 (by
              have hmem := chainPrevious_mem (expected := head)
                (pre := first :: more) (by simp)
              rw [heq]
              exact List.mem_append_left (block :: rest) hmem)
          have hsuccessorNe :
              head ≠ state.next[block]?.getD state.next.length := by
            rw [hlinks.2.2.2]
            cases rest with
            | nil =>
                simp only [List.head?_nil, Option.getD_none]
                exact Nat.ne_of_lt hheadNext
            | cons successor suffix =>
                exact fun heq => hparts.1 (by simp [heq])
          refine ⟨by omega, by omega, ?_, ?_, htailResult⟩
          · rw [remove_preserves_previous hremove hheadBlock hsuccessorNe]
            exact hheadPred
          · rw [remove_preserves_next hremove hheadBlock hpredecessorNe]
            simpa [hlens.2.1] using hheadSucc

/-- Arbitrary removal preserves the complete selected-bin representation and
detaches the removed node. -/
theorem remove_decomposition_preserves_bin {state nextState : Metadata}
    {bin block : Nat} {pre rest : List Nat}
    (hrep : RepresentsBin state bin (pre ++ block :: rest))
    (hremove : remove state bin block = some nextState) :
    RepresentsBin nextState bin (pre ++ rest) ∧
      nextState.next[block]? = some state.next.length ∧
      nextState.previous[block]? = some state.previous.length := by
  rcases hrep with ⟨hbin, hlens, hhead, hlinked, hnodup⟩
  have hlengths := remove_preserves_lengths hremove
  have hsentinelAbsent : state.next.length ∉ pre ++ block :: rest := by
    intro hmem
    have hbound := (linked_member_bounds hlinked hmem).1
    omega
  have hnextLinked := linked_remove_decomposition hremove hlinked hnodup
    hsentinelAbsent
  have hnextLinked' : linked nextState nextState.next.length (pre ++ rest) := by
    rw [hlengths.2.1]
    exact hnextLinked
  have hnextNodup : (pre ++ rest).Nodup := by
    have herased := hnodup.erase block
    rwa [erase_decomposition_of_nodup hnodup] at herased
  refine ⟨⟨by omega, hlengths.2.1.trans (hlens.trans hlengths.2.2.symm),
    ?_, hnextLinked', hnextNodup⟩, (remove_detaches hremove).1,
    (remove_detaches hremove).2⟩
  cases pre with
  | nil =>
      have hlinks := linked_decomposition_links ([] : List Nat) rest hlinked
      have heffect := (remove_effect hremove).1
      have hpredSentinel :
          state.previous[block]?.getD state.next.length ≥ state.next.length := by
        simp [hlinks.2.2.1, chainPrevious]
      rw [heffect, if_pos hpredSentinel, List.getElem?_set_self hbin]
      simp only [Option.getD_some]
      rw [hlinks.2.2.2]
      simp [hlengths.2.1]
  | cons head tail =>
      have hlinks := linked_decomposition_links (head :: tail) rest
        (by simpa using hlinked)
      have hpredBound :
          state.previous[block]?.getD state.next.length < state.next.length := by
        rw [hlinks.2.2.1]
        exact (linked_member_bounds hlinked (List.mem_append_left _
          (chainPrevious_mem (expected := state.next.length) (by simp)))).1
      rw [remove_heads_of_predecessor_lt hremove hpredBound]
      simpa [hlengths.2.1] using hhead

theorem remove_decomposition_preserves_other {state nextState : Metadata}
    {bin otherBin block : Nat} {pre rest chain : List Nat}
    (hselected : RepresentsBin state bin (pre ++ block :: rest))
    (hother : RepresentsBin state otherBin chain) (hbins : otherBin ≠ bin)
    (hdisjoint : ∀ node ∈ chain, node ∉ pre ++ block :: rest)
    (hremove : remove state bin block = some nextState) :
    RepresentsBin nextState otherBin chain := by
  rcases hselected with ⟨_, _, _, hselectedLinked, _⟩
  rcases hother with ⟨hotherBin, hotherLens, hotherHead,
    hotherLinked, hotherNodup⟩
  have hlengths := remove_preserves_lengths hremove
  have hlinks := linked_decomposition_links pre rest hselectedLinked
  have hotherLinked' : linked state nextState.next.length chain := by
    rw [hlengths.2.1]
    exact hotherLinked
  refine ⟨by omega, hlengths.2.1.trans (hotherLens.trans hlengths.2.2.symm),
    ?_, ?_, hotherNodup⟩
  · have hheads := (remove_effect hremove).1
    rw [hheads]
    split
    · rw [List.getElem?_set_ne (Ne.symm hbins)]
      simpa [hlengths.2.1] using hotherHead
    · simpa [hlengths.2.1] using hotherHead
  · refine linked_congr (state := state) (nextState := nextState)
      hlengths.2.1 hlengths.2.2 ?_ ?_ hotherLinked'
    · intro node hnode
      have hnodeBlock : node ≠ block := by
        exact fun heq => hdisjoint node hnode (by simp [heq])
      have hnodePred :
          node ≠ state.previous[block]?.getD state.next.length := by
        rw [hlinks.2.2.1]
        cases pre with
        | nil =>
            simp only [chainPrevious]
            exact Nat.ne_of_lt (linked_member_bounds hotherLinked hnode).1
        | cons head tail =>
            intro heq
            apply hdisjoint node hnode
            rw [heq]
            exact List.mem_append_left (block :: rest)
              (chainPrevious_mem (expected := state.next.length) (by simp))
      exact remove_preserves_next hremove hnodeBlock hnodePred
    · intro node hnode
      have hnodeBlock : node ≠ block := by
        exact fun heq => hdisjoint node hnode (by simp [heq])
      have hnodeSuccessor :
          node ≠ state.next[block]?.getD state.next.length := by
        rw [hlinks.2.2.2]
        cases rest with
        | nil =>
            simp only [List.head?_nil, Option.getD_none]
            exact Nat.ne_of_lt (linked_member_bounds hotherLinked hnode).1
        | cons successor tail =>
            intro heq
            apply hdisjoint node hnode
            rw [heq]
            simp
      exact remove_preserves_previous hremove hnodeBlock hnodeSuccessor

theorem removeClassArrays_preserves_bins
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : RemoveClassResult} {state : Bins.State} {cls : SizeClass}
    {removed : Block} {replacement : List Block}
    (hvalid : Bins.Valid state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hbin : bin = encodeSizeClass cls)
    (habstract : FreeList.removeOffset (state.chains cls) block =
      some (removed, replacement))
    (hremove : removeClassArrays second first heads next previous bin block =
      some result) :
    RepresentsBins (Metadata.mk result.heads result.next result.previous)
      (state.replaceChain cls replacement) := by
  have horigin := FreeList.removeOffset_removed_origin (hvalid.1 cls) habstract
  obtain ⟨old, holdMem, holdOffset, _⟩ := horigin
  have hmember : block ∈ (state.chains cls).map Block.offset := by
    rw [← holdOffset]
    exact List.mem_map_of_mem holdMem
  obtain ⟨pre, rest, hshape⟩ := List.mem_iff_append.mp hmember
  have hselected := hbins cls
  have hbinEq : bin = cls.fl.val * secondLevelCount + cls.sl.val := by
    simpa [encodeSizeClass] using hbin
  rw [← hbinEq, hshape] at hselected
  have hresult := removeClassArrays_result hremove
  have hmetadata :
      remove { heads, next, previous } bin block =
        some (Metadata.mk result.heads result.next result.previous) :=
    removeArrays_result hresult.2.2.2.2.1
  have hselectedNext :=
    (remove_decomposition_preserves_bin hselected hmetadata).1
  have hreplacementOffsets := FreeList.removeOffset_offsets habstract
  have hnodup : (pre ++ block :: rest).Nodup := by
    rw [← hshape]
    exact (hvalid.1 cls).2
  rw [hshape, erase_decomposition_of_nodup hnodup] at hreplacementOffsets
  intro query
  by_cases hquery : query = cls
  · subst query
    change RepresentsBin (Metadata.mk result.heads result.next result.previous)
      (cls.fl.val * secondLevelCount + cls.sl.val)
      (((state.replaceChain cls replacement).chains cls).map Block.offset)
    have hreplace : (state.replaceChain cls replacement).chains cls =
        replacement := by
      simp [Bins.State.replaceChain, Bins.State.fromChains,
        Bins.Chains.replace]
    rw [hreplace, hreplacementOffsets, ← hbinEq]
    exact hselectedNext
  · have hqueryBin :
        query.fl.val * secondLevelCount + query.sl.val ≠ bin := by
      intro heq
      apply hquery
      apply classIndex_injective
      rw [← hbinEq]
      exact heq
    have hother := hbins query
    have hnodes : ∀ node ∈ (state.chains query).map Block.offset,
        node ∉ pre ++ block :: rest := by
      intro node hnode hselectedNode
      exact hdisjoint hquery node hnode (by
        rw [hshape]
        exact hselectedNode)
    have hframe := remove_decomposition_preserves_other hselected hother
      hqueryBin hnodes hmetadata
    change RepresentsBin (Metadata.mk result.heads result.next result.previous)
      (query.fl.val * secondLevelCount + query.sl.val)
      (((state.replaceChain cls replacement).chains query).map Block.offset)
    simpa [Bins.replaceChain_other state replacement hquery] using hframe

theorem removeOffset_preserves_offsets_disjoint
    {state : Bins.State} {cls : SizeClass} {block : Nat}
    {removed : Block} {replacement : List Block}
    (hdisjoint : BinsOffsetsDisjoint state)
    (hremove : FreeList.removeOffset (state.chains cls) block =
      some (removed, replacement)) :
    BinsOffsetsDisjoint (state.replaceChain cls replacement) := by
  have hoffsets := FreeList.removeOffset_offsets hremove
  have hsubset : ∀ offset, offset ∈ replacement.map Block.offset →
      offset ∈ (state.chains cls).map Block.offset := by
    intro offset hmem
    rw [hoffsets] at hmem
    exact List.mem_of_mem_erase hmem
  intro left right hne offset hleft hright
  by_cases hleftCls : left = cls
  · subst left
    have hrightCls : right ≠ cls := by exact fun h => hne h.symm
    have hleftOld : offset ∈ (state.chains cls).map Block.offset := by
      apply hsubset offset
      simpa [Bins.State.replaceChain, Bins.State.fromChains,
        Bins.Chains.replace] using hleft
    have hrightOld : offset ∈ (state.chains right).map Block.offset := by
      simpa [Bins.replaceChain_other state replacement hrightCls] using hright
    exact hdisjoint hne offset hleftOld hrightOld
  · by_cases hrightCls : right = cls
    · subst right
      have hleftOld : offset ∈ (state.chains left).map Block.offset := by
        simpa [Bins.replaceChain_other state replacement hleftCls] using hleft
      have hrightOld : offset ∈ (state.chains cls).map Block.offset := by
        apply hsubset offset
        simpa [Bins.State.replaceChain, Bins.State.fromChains,
          Bins.Chains.replace] using hright
      exact hdisjoint hne offset hleftOld hrightOld
    · have hleftOld : offset ∈ (state.chains left).map Block.offset := by
        simpa [Bins.replaceChain_other state replacement hleftCls] using hleft
      have hrightOld : offset ∈ (state.chains right).map Block.offset := by
        simpa [Bins.replaceChain_other state replacement hrightCls] using hright
      exact hdisjoint hne offset hleftOld hrightOld

/-- End-to-end refinement of arbitrary concrete class removal to the abstract
TLSF operation, including validity, intrusive bins, disjointness, and both
bitmap cache levels. -/
theorem removeClassArrays_refines_removeOffset
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : RemoveClassResult} {state nextState : Bins.State}
    {cls : SizeClass} {removed : Block}
    (hvalid : Bins.Valid state)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hbin : bin = encodeSizeClass cls)
    (habstract : state.removeOffset cls block = some (removed, nextState))
    (hremove : removeClassArrays second first heads next previous bin block =
      some result) :
    Bins.Valid nextState ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
        nextState ∧
      BinsOffsetsDisjoint nextState ∧
      RepresentsSecondBitmap result.second nextState ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨replacement, hremoveOffset, rfl⟩ :=
    Bins.removeOffset_success habstract
  have hbitmaps := removeClassArrays_preserves_bitmaps hsecond hfirst hvalid
    hbins hbin habstract hremove
  exact ⟨Bins.removeOffset_valid hvalid hremoveOffset,
    removeClassArrays_preserves_bins hvalid hbins hdisjoint hbin
      hremoveOffset hremove,
    removeOffset_preserves_offsets_disjoint hdisjoint hremoveOffset,
    hbitmaps.1, hbitmaps.2⟩

/-- Compositional bin proof for the remove-left/remove-right/insert-merged core
of coalescing. -/
theorem removeRemoveInsert_refines
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {leftBin rightBin mergedBin leftOffset rightOffset : Nat}
    {withoutLeft withoutRight : RemoveClassResult}
    {inserted : InsertClassResult}
    {state afterLeft afterRight : Bins.State}
    {leftClass rightClass mergedClass : SizeClass}
    {removedLeft removedRight merged : Block}
    (hvalid : Bins.Valid state)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hleftBin : leftBin = encodeSizeClass leftClass)
    (hrightBin : rightBin = encodeSizeClass rightClass)
    (hmergedBin : mergedBin = encodeSizeClass mergedClass)
    (hmergedOffset : leftOffset = merged.offset)
    (hremoveLeftAbstract : state.removeOffset leftClass leftOffset =
      some (removedLeft, afterLeft))
    (hremoveRightAbstract : afterLeft.removeOffset rightClass rightOffset =
      some (removedRight, afterRight))
    (hbelongs : Bins.Belongs mergedClass merged)
    (hfresh : ∀ query, merged.offset ∉
      (afterRight.chains query).map Block.offset)
    (hremoveLeft : removeClassArrays second first heads next previous
      leftBin leftOffset = some withoutLeft)
    (hremoveRight : removeClassArrays withoutLeft.second withoutLeft.first
      withoutLeft.heads withoutLeft.next withoutLeft.previous
      rightBin rightOffset = some withoutRight)
    (hinsert : insertClassArrays withoutRight.second withoutRight.first
      withoutRight.heads withoutRight.next withoutRight.previous
      mergedBin leftOffset = some inserted) :
    let finalState := afterRight.insert mergedClass merged
    Bins.Valid finalState ∧
      RepresentsBins (Metadata.mk inserted.heads inserted.next inserted.previous)
        finalState ∧
      BinsOffsetsDisjoint finalState ∧
      RepresentsSecondBitmap inserted.second finalState ∧
      FirstBitmapRep inserted.first inserted.second := by
  have hleft := removeClassArrays_refines_removeOffset hvalid hsecond hfirst
    hbins hdisjoint hleftBin hremoveLeftAbstract hremoveLeft
  have hright := removeClassArrays_refines_removeOffset hleft.1 hleft.2.2.2.1
    hleft.2.2.2.2 hleft.2.1 hleft.2.2.1 hrightBin
    hremoveRightAbstract hremoveRight
  have hinsertion := insertClassArrays_refines_insert hright.1
    hright.2.2.2.1 hright.2.2.2.2 hright.2.1 hright.2.2.1 hfresh
    hbelongs hmergedOffset hmergedBin hinsert
  exact ⟨hinsertion.1, hinsertion.2.1,
    insert_preserves_offsets_disjoint hright.2.2.1 hfresh,
    hinsertion.2.2.1, hinsertion.2.2.2⟩

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

theorem remove_front_preserves_other {state nextState : Metadata}
    {bin otherBin block : Nat} {rest chain : List Nat}
    (hselected : RepresentsBin state bin (block :: rest))
    (hother : RepresentsBin state otherBin chain) (hbins : otherBin ≠ bin)
    (hdisjoint : ∀ node ∈ chain, node ∉ block :: rest)
    (hremove : remove state bin block = some nextState) :
    RepresentsBin nextState otherBin chain := by
  rcases hselected with ⟨hbin, hlens, _, hselectedLinked, _⟩
  rcases hother with ⟨hotherBin, hotherLens, hotherHead,
    hotherLinked, hotherNodup⟩
  simp only [linked] at hselectedLinked
  rcases hselectedLinked with
    ⟨hblockNext, hblockPrevious, hblockPrev, hblockNxt, hrestLinked⟩
  have hprevValue : state.previous[block]?.getD state.next.length =
      state.next.length := by simp [hblockPrev]
  have hnextValue : state.next[block]?.getD state.next.length =
      rest.head?.getD state.next.length := by simp [hblockNxt]
  unfold remove at hremove
  simp only [Nat.not_le.mpr hbin, Nat.not_le.mpr hblockNext,
    Nat.not_le.mpr hblockPrevious, if_false, hprevValue,
    ge_iff_le] at hremove
  simp at hremove
  cases rest with
  | nil =>
      simp only [List.head?_nil, Option.getD_none] at hnextValue
      have hsuccessorOut : ¬state.next.length < state.previous.length := by omega
      simp only [hnextValue, hsuccessorOut, if_false,
        Option.some.injEq] at hremove
      subst nextState
      refine ⟨by simp [hotherBin], by simp [hotherLens], ?_, ?_,
        hotherNodup⟩
      · rw [List.getElem?_set_ne (Ne.symm hbins)]
        simpa using hotherHead
      · have hpreserved := linked_congr (state := state)
          (nextState := {
            heads := state.heads.set bin state.next.length
            next := state.next.set block state.next.length
            previous := state.previous.set block state.previous.length })
          (by simp) (by simp)
          (by
            intro node hnode
            have hne : node ≠ block := by
              intro heq
              exact hdisjoint node hnode (by simp [heq])
            simp [List.getElem?_set_ne (Ne.symm hne)])
          (by
            intro node hnode
            have hne : node ≠ block := by
              intro heq
              exact hdisjoint node hnode (by simp [heq])
            simp [List.getElem?_set_ne (Ne.symm hne)]) hotherLinked
        simpa using hpreserved
  | cons successor tail =>
      simp only [List.head?_cons, Option.getD_some] at hnextValue
      simp only [linked] at hrestLinked
      have hsuccessorIn : successor < state.previous.length :=
        hrestLinked.2.1
      simp only [hnextValue, hsuccessorIn, if_true,
        Option.some.injEq] at hremove
      subst nextState
      refine ⟨by simp [hotherBin], by simp [hotherLens], ?_, ?_,
        hotherNodup⟩
      · rw [List.getElem?_set_ne (Ne.symm hbins)]
        simpa using hotherHead
      · have hpreserved := linked_congr (state := state)
          (nextState := {
            heads := state.heads.set bin successor
            next := state.next.set block state.next.length
            previous := (state.previous.set successor state.next.length).set
              block state.previous.length })
          (by simp) (by simp)
          (by
            intro node hnode
            have hne : node ≠ block := by
              intro heq
              exact hdisjoint node hnode (by simp [heq])
            simp [List.getElem?_set_ne (Ne.symm hne)])
          (by
            intro node hnode
            have hblockNe : node ≠ block := by
              intro heq
              exact hdisjoint node hnode (by simp [heq])
            have hsuccessorNe : node ≠ successor := by
              intro heq
              exact hdisjoint node hnode (by simp [heq])
            simp [List.getElem?_set_ne (Ne.symm hblockNe),
              List.getElem?_set_ne (Ne.symm hsuccessorNe)]) hotherLinked
        simpa using hpreserved

theorem takeCandidateClassArrays_preserves_bins
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {startFl startSl : Nat}
    {result : ClassCandidateResult} {state : Bins.State}
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second) (hvalid : Bins.Valid state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (htake : takeCandidateClassArrays second first heads next previous
      startFl startSl = some result) :
    ∃ cls removed rest,
      classOfBin? result.bin = some cls ∧
      FreeList.removeFront (state.chains cls) = some (removed, rest) ∧
      result.block = removed.offset ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
        (state.replaceChain cls rest) ∧
      RepresentsSecondBitmap result.second (state.replaceChain cls rest) ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨cls, removed, rest, hclass, hremoveFront, hblock,
    hsecondNext, hfirstNext⟩ := takeCandidateClassArrays_preserves_bitmaps
      hsecond hfirst hvalid hbins htake
  have hbin := classOfBin?_index hclass
  have hresult := takeCandidateClassArrays_result htake
  rcases hresult with ⟨_, _, _, _, _, _, hremoveArrays, _⟩
  have hremove : remove { heads, next, previous } result.bin result.block =
      some (Metadata.mk result.heads result.next result.previous) :=
    removeArrays_result hremoveArrays
  have hfront := FreeList.removeFront_removes_head hremoveFront
  have hselected := hbins cls
  rw [← hbin] at hselected
  have hchainShape :
      (state.chains cls).map Block.offset =
        result.block :: rest.map Block.offset := by
    cases hchain : state.chains cls with
    | nil => simp [FreeList.removeFront, hchain] at hremoveFront
    | cons head tail =>
      have htail := hfront.2
      simp only [hchain, List.map_cons, List.head?_cons,
        List.tail_cons, Option.some.injEq] at hfront htail
      simp [hchain, hblock, hfront.1, htail]
  rw [hchainShape] at hselected
  obtain ⟨selectedMetadata, hselectedRemove, hselectedNext, _, _⟩ :=
    remove_front_complete hselected
  have hmetadata : selectedMetadata =
      Metadata.mk result.heads result.next result.previous := by
    rw [hremove] at hselectedRemove
    exact (Option.some.inj hselectedRemove).symm
  subst selectedMetadata
  refine ⟨cls, removed, rest, hclass, hremoveFront, hblock, ?_, hsecondNext,
    hfirstNext⟩
  intro query
  by_cases hquery : query = cls
  · subst query
    rw [← hbin]
    simpa using hselectedNext
  · have hqueryBin :
        query.fl.val * secondLevelCount + query.sl.val ≠ result.bin := by
      intro heq
      apply hquery
      apply classIndex_injective
      omega
    have hother := hbins query
    have hnodes : ∀ node ∈ (state.chains query).map Block.offset,
        node ∉ result.block :: rest.map Block.offset := by
      intro node hnode hselectedNode
      exact hdisjoint hquery node hnode (by
        rw [hchainShape]
        exact hselectedNode)
    have hpreserved := remove_front_preserves_other hselected hother
      hqueryBin hnodes hremove
    simpa [Bins.replaceChain_other state rest hquery] using hpreserved

theorem takeCandidateClassArrays_refines_takeCandidate
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : ClassCandidateResult}
    {state : Bins.State} (start : SizeClass)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second) (hvalid : Bins.Valid state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (htake : takeCandidateClassArrays second first heads next previous
      start.fl.val start.sl.val = some result) :
    ∃ cls removed rest,
      state.takeCandidate start = some (removed, state.replaceChain cls rest) ∧
      result.block = removed.offset ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
        (state.replaceChain cls rest) ∧
      RepresentsSecondBitmap result.second (state.replaceChain cls rest) ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨cls, removed, rest, hclass, hremoveFront, hblock, hnextBins,
    hnextSecond, hnextFirst⟩ := takeCandidateClassArrays_preserves_bins
      hsecond hfirst hvalid hbins hdisjoint htake
  have hresult := takeCandidateClassArrays_result htake
  have hfindAbstract := findNonemptyClassLowered_eq_findCandidate
    hsecond hfirst hvalid start cls hresult.1 hclass
  have habstractTake :
      state.takeCandidate start = some (removed, state.replaceChain cls rest) := by
    simp [Bins.State.takeCandidate, hfindAbstract, Bins.State.removeFront,
      hremoveFront]
  exact ⟨cls, removed, rest, habstractTake, hblock, hnextBins,
    hnextSecond, hnextFirst⟩

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

/-- Exact parallel-array effect of the Luffs deallocation marking stage.
All validation precedes both writes, matching the generated Rust operation. -/
def markFreeArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (block returnedOffset returnedBytes : Nat) :
    Option (List (Fin 256) × List (Fin 256)) :=
  if block ≥ offsets.length then none
  else if block ≥ sizes.length then none
  else if block ≥ isFree.length then none
  else if block ≥ prevFree.length then none
  else if isFree[block]? != some 0 then none
  else if offsets[block]? != some returnedOffset then none
  else if sizes[block]? != some returnedBytes then none
  else
    let nextIsFree := isFree.set block 1
    let successor := block + 1
    let nextPrevFree :=
      if successor < prevFree.length then prevFree.set successor 1 else prevFree
    some (nextIsFree, nextPrevFree)

theorem markFreeArrays_result {isFree prevFree nextIsFree nextPrevFree : List (Fin 256)}
    {offsets sizes : List Nat} {block returnedOffset returnedBytes : Nat}
    (hmark : markFreeArrays offsets sizes isFree prevFree block
      returnedOffset returnedBytes =
      some (nextIsFree, nextPrevFree)) :
    block < offsets.length ∧ block < sizes.length ∧
      block < isFree.length ∧ block < prevFree.length ∧
      isFree[block]? = some 0 ∧
      offsets[block]? = some returnedOffset ∧
      sizes[block]? = some returnedBytes ∧
    nextIsFree = isFree.set block 1 ∧
      nextPrevFree = if block + 1 < prevFree.length then
        prevFree.set (block + 1) 1 else prevFree := by
  unfold markFreeArrays at hmark
  split at hmark <;> simp_all [List.getElem?_eq_some_iff]
  next =>
    exact ⟨hmark.2.2.2.1.choose_spec,
      hmark.2.2.2.2.2.1.choose_spec⟩

theorem markFreeArrays_lengths {isFree prevFree nextIsFree nextPrevFree : List (Fin 256)}
    {offsets sizes : List Nat} {block returnedOffset returnedBytes : Nat}
    (hmark : markFreeArrays offsets sizes isFree prevFree block
      returnedOffset returnedBytes =
      some (nextIsFree, nextPrevFree)) :
    nextIsFree.length = isFree.length ∧
      nextPrevFree.length = prevFree.length := by
  obtain ⟨_, _, _, _, _, _, _, rfl, rfl⟩ := markFreeArrays_result hmark
  split <;> simp_all

def freeFlags (blocks : List Block) : List (Fin 256) :=
  blocks.map fun block => if block.free then 1 else 0

def prevFreeFlags (blocks : List Block) : List (Fin 256) :=
  blocks.map fun block => if block.prevFree then 1 else 0

def blockOffsets (blocks : List Block) : List Nat := blocks.map Block.offset

def blockSizes (blocks : List Block) : List Nat := blocks.map Block.bytes

/-- Representation of the active prefix of the fixed physical-header arrays.
Slots at or above `count` are spare capacity and are deliberately excluded
from allocator operations. This is the deletion model needed by coalescing. -/
def RepresentsPhysicalArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (blocks : List Block) : Prop :=
  count = blocks.length ∧
  count ≤ offsets.length ∧ count ≤ sizes.length ∧
  count ≤ isFree.length ∧ count ≤ prevFree.length ∧
  offsets.take count = blockOffsets blocks ∧
  sizes.take count = blockSizes blocks ∧
  isFree.take count = freeFlags blocks ∧
  prevFree.take count = prevFreeFlags blocks

theorem canonical_representsPhysicalArrays (blocks : List Block) :
    RepresentsPhysicalArrays (blockOffsets blocks) (blockSizes blocks)
      (freeFlags blocks) (prevFreeFlags blocks) blocks.length blocks := by
  refine ⟨rfl, by simp [blockOffsets], by simp [blockSizes],
    by simp [freeFlags], by simp [prevFreeFlags], ?_, ?_, ?_, ?_⟩
  · simpa only [blockOffsets, List.length_map] using
      (List.take_length (l := blockOffsets blocks))
  · simpa only [blockSizes, List.length_map] using
      (List.take_length (l := blockSizes blocks))
  · simpa only [freeFlags, List.length_map] using
      (List.take_length (l := freeFlags blocks))
  · simpa only [prevFreeFlags, List.length_map] using
      (List.take_length (l := prevFreeFlags blocks))

structure DeallocateUncoalescedResult where
  isFree : List (Fin 256)
  prevFree : List (Fin 256)
  insertion : InsertClassResult
deriving DecidableEq, Repr

def compactActive {α : Type} [Inhabited α] (values : List α) (count removed : Nat) :
    List α :=
  values.take removed ++
    (values.drop (removed + 1)).take (count - removed - 1) ++
    values.drop (count - 1)

theorem compactActive_append_pair {α : Type} [Inhabited α]
    (pre : List α) (left right : α) (rest : List α) :
    (compactActive (pre ++ left :: right :: rest)
      (pre ++ left :: right :: rest).length (pre.length + 1)).take
        ((pre ++ left :: right :: rest).length - 1) =
      pre ++ left :: rest := by
  have hremaining :
      pre.length + (rest.length + 1 + 1) - (pre.length + 1) - 1 =
        rest.length := by omega
  have hlast :
      pre.length + (rest.length + 1 + 1) -
          (pre.length + (rest.length + 1)) = 1 := by omega
  have htake :
      (pre ++ left :: right :: rest).take (pre.length + 1) =
        pre ++ [left] := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have hdrop :
      (pre ++ left :: right :: rest).drop (pre.length + 1 + 1) = rest := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
    have htwo : pre.length + 1 + 1 - pre.length = 2 := by omega
    rw [htwo]
    rfl
  rw [compactActive, htake, hdrop]
  simp only [List.length_append, List.length_cons]
  rw [hremaining]
  have hpre : pre.take (pre.length + (rest.length + 1)) = pre :=
    List.take_of_length_le (by omega)
  simp [List.take_append, hpre]

theorem compactActive_append_pair_length {α : Type} [Inhabited α]
    (pre : List α) (left right : α) (rest : List α) :
    (compactActive (pre ++ left :: right :: rest)
      (pre ++ left :: right :: rest).length (pre.length + 1)).length =
      (pre ++ left :: right :: rest).length := by
  have hremaining :
      pre.length + (rest.length + 1 + 1) - (pre.length + 1) - 1 =
        rest.length := by omega
  have hdropcount :
      pre.length + (rest.length + 1 + 1) - (pre.length + 1 + 1) =
        rest.length := by omega
  simp [compactActive, hremaining, hdropcount]
  omega

structure CoalescePhysicalResult where
  offsets : List Nat
  sizes : List Nat
  isFree : List (Fin 256)
  prevFree : List (Fin 256)
  count : Nat
deriving DecidableEq, Repr

structure CoalesceClassResult where
  offsets : List Nat
  sizes : List Nat
  isFree : List (Fin 256)
  prevFree : List (Fin 256)
  count : Nat
  second : List (BitVec 32)
  first : BitVec 64
  heads : List Nat
  next : List Nat
  previous : List Nat
deriving DecidableEq, Repr

/-- Exact fixed-array effect of `tlsf_coalesce_physical`. The active right
header is deleted by left-compacting the suffix; the final array slot is spare
capacity and therefore need not be cleared. -/
def coalescePhysicalArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count left : Nat) :
    Option CoalescePhysicalResult :=
  if count ≤ offsets.length ∧ count ≤ sizes.length ∧
      count ≤ isFree.length ∧ count ≤ prevFree.length then
    let right := left + 1
    if right ≥ count then none
    else if isFree[left]? = some 0 then none
    else if isFree[right]? = some 0 then none
    else match offsets[left]?, sizes[left]?, offsets[right]?, sizes[right]? with
      | some leftOffset, some leftSize, some rightOffset, some rightSize =>
          if leftOffset + leftSize != rightOffset then none
          else
            let sizes := sizes.set left (leftSize + rightSize)
            some {
              offsets := compactActive offsets count right
              sizes := compactActive sizes count right
              isFree := compactActive isFree count right
              prevFree := compactActive prevFree count right
              count := count - 1 }
      | _, _, _, _ => none
  else none

theorem coalescePhysicalArrays_result {offsets sizes : List Nat}
    {isFree prevFree : List (Fin 256)} {count left : Nat}
    {result : CoalescePhysicalResult}
    (hsuccess : coalescePhysicalArrays offsets sizes isFree prevFree count left =
      some result) :
    result.count = count - 1 ∧ left + 1 < count ∧
      isFree[left]? ≠ some 0 ∧ isFree[left + 1]? ≠ some 0 ∧
      ∃ leftOffset leftSize rightSize,
        offsets[left]? = some leftOffset ∧ sizes[left]? = some leftSize ∧
        offsets[left + 1]? = some (leftOffset + leftSize) ∧
        sizes[left + 1]? = some rightSize := by
  unfold coalescePhysicalArrays at hsuccess
  split at hsuccess <;> try contradiction
  next =>
    dsimp only at hsuccess
    split at hsuccess <;> try contradiction
    next hright =>
      split at hsuccess <;> try contradiction
      next hleftFree =>
        split at hsuccess <;> try contradiction
        next hrightFree =>
          cases hleftOffset : offsets[left]? with
          | none => simp [hleftOffset] at hsuccess
          | some leftOffset =>
            cases hleftSize : sizes[left]? with
            | none => simp [hleftOffset, hleftSize] at hsuccess
            | some leftSize =>
              cases hrightOffset : offsets[left + 1]? with
              | none => simp [hleftOffset, hleftSize, hrightOffset] at hsuccess
              | some rightOffset =>
                cases hrightSize : sizes[left + 1]? with
                | none =>
                    simp [hleftOffset, hleftSize, hrightOffset,
                      hrightSize] at hsuccess
                | some rightSize =>
                  simp only [hleftOffset, hleftSize, hrightOffset,
                    hrightSize, Option.getD_some] at hsuccess
                  split at hsuccess <;> try contradiction
                  next hadjacent =>
                    simp only [Option.some.injEq] at hsuccess
                    subst result
                    have hoffset : leftOffset + leftSize = rightOffset := by
                      simpa using hadjacent
                    exact ⟨rfl, Nat.lt_of_not_ge hright, hleftFree,
                      hrightFree, leftOffset, leftSize, rightSize,
                      rfl, rfl, by simpa [hoffset], rfl⟩

/-- The concrete active-prefix compaction is already the abstract head
coalescing transition. The old final active slot becomes spare capacity and is
therefore outside `RepresentsPhysicalArrays` after the count decrement. -/
theorem coalescePhysicalArrays_refines_head (left right : Block)
    (rest : List Block) (hcan : canCoalesce left right) :
    ∃ result,
      coalescePhysicalArrays
        (blockOffsets (left :: right :: rest))
        (blockSizes (left :: right :: rest))
        (freeFlags (left :: right :: rest))
        (prevFreeFlags (left :: right :: rest))
        (left :: right :: rest).length 0 = some result ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
        result.prevFree result.count
        (coalesceAt (left :: right :: rest) 0) := by
  rcases hcan with ⟨hleftFree, hrightFree, hadjacent⟩
  simp [coalescePhysicalArrays, compactActive, blockOffsets, blockSizes,
    freeFlags, prevFreeFlags, hleftFree, hrightFree, hadjacent,
    RepresentsPhysicalArrays, coalesceAt, coalesceBlocks]
  exact ⟨by simpa only [List.length_map] using
      (List.take_length (l := rest.map Block.offset)),
    by simpa only [List.length_map] using
      (List.take_length (l := rest.map Block.bytes)),
    by simpa only [List.length_map] using
      (List.take_length (l := rest.map fun block =>
        if block.free then (1 : Fin 256) else 0)),
    by simpa only [List.length_map] using
      (List.take_length (l := rest.map fun block =>
        if block.prevFree then (1 : Fin 256) else 0))⟩

theorem coalesceAt_append_pair (pre : List Block) (left right : Block)
    (rest : List Block) :
    coalesceAt (pre ++ left :: right :: rest) pre.length =
      pre ++ coalesceBlocks left right :: rest := by
  induction pre with
  | nil => simp [coalesceAt]
  | cons head tail ih => simp [coalesceAt, ih]

/-- Concrete physical-array coalescing refines the abstract transition at any
active adjacent pair, expressed by splitting the physical list at that pair. -/
theorem coalescePhysicalArrays_refines_append (pre : List Block)
    (left right : Block) (rest : List Block)
    (hcan : canCoalesce left right) :
    ∃ result,
      coalescePhysicalArrays
        (blockOffsets (pre ++ left :: right :: rest))
        (blockSizes (pre ++ left :: right :: rest))
        (freeFlags (pre ++ left :: right :: rest))
        (prevFreeFlags (pre ++ left :: right :: rest))
        (pre ++ left :: right :: rest).length pre.length = some result ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
        result.prevFree result.count
        (coalesceAt (pre ++ left :: right :: rest) pre.length) := by
  rcases hcan with ⟨hleftFree, hrightFree, hadjacent⟩
  have hoffsets := compactActive_append_pair
    (pre.map Block.offset) left.offset (left.offset + left.bytes)
      (rest.map Block.offset)
  have hsizes := compactActive_append_pair
    (pre.map Block.bytes) (left.bytes + right.bytes) right.bytes
      (rest.map Block.bytes)
  have hfree := compactActive_append_pair
    (pre.map fun block => if block.free then (1 : Fin 256) else 0)
      (1 : Fin 256) (1 : Fin 256)
      (rest.map fun block => if block.free then (1 : Fin 256) else 0)
  have hprev := compactActive_append_pair
    (pre.map fun block => if block.prevFree then (1 : Fin 256) else 0)
      (if left.prevFree then (1 : Fin 256) else 0)
      (if right.prevFree then (1 : Fin 256) else 0)
      (rest.map fun block => if block.prevFree then (1 : Fin 256) else 0)
  have hoffsetsLen := compactActive_append_pair_length
    (pre.map Block.offset) left.offset (left.offset + left.bytes)
      (rest.map Block.offset)
  have hsizesLen := compactActive_append_pair_length
    (pre.map Block.bytes) (left.bytes + right.bytes) right.bytes
      (rest.map Block.bytes)
  have hfreeLen := compactActive_append_pair_length
    (pre.map fun block => if block.free then (1 : Fin 256) else 0)
      (1 : Fin 256) (1 : Fin 256)
      (rest.map fun block => if block.free then (1 : Fin 256) else 0)
  have hprevLen := compactActive_append_pair_length
    (pre.map fun block => if block.prevFree then (1 : Fin 256) else 0)
      (if left.prevFree then (1 : Fin 256) else 0)
      (if right.prevFree then (1 : Fin 256) else 0)
      (rest.map fun block => if block.prevFree then (1 : Fin 256) else 0)
  simp only [List.length_map, List.length_append, List.length_cons] at hoffsets hsizes hfree hprev hoffsetsLen hsizesLen hfreeLen hprevLen
  have hactive :
      pre.length + (rest.length + 1 + 1) - 1 =
        pre.length + (rest.length + 1) := by omega
  rw [hactive] at hoffsets hsizes hfree hprev
  simp [coalescePhysicalArrays, blockOffsets, blockSizes,
    freeFlags, prevFreeFlags, hleftFree, hrightFree, hadjacent,
    RepresentsPhysicalArrays, coalesceAt_append_pair, coalesceBlocks,
    hoffsets, hsizes, hfree, hprev, hoffsetsLen, hsizesLen, hfreeLen, hprevLen]

/-- Full metadata transaction for coalescing an adjacent free pair: detach both
old size-class nodes, compact the physical headers, and insert the merged node
into its newly classified bin. -/
def coalesceClassArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count left : Nat) : Option CoalesceClassResult := do
  let right := left + 1
  let leftOffset ← offsets[left]?
  let rightOffset ← offsets[right]?
  let leftSize ← sizes[left]?
  let rightSize ← sizes[right]?
  let leftBin ← classifySizeBin leftSize
  let rightBin ← classifySizeBin rightSize
  let withoutLeft ← removeClassArrays second first heads next previous
    leftBin leftOffset
  let withoutRight ← removeClassArrays withoutLeft.second withoutLeft.first
    withoutLeft.heads withoutLeft.next withoutLeft.previous rightBin rightOffset
  let physical ← coalescePhysicalArrays offsets sizes isFree prevFree count left
  let mergedSize ← physical.sizes[left]?
  let mergedBin ← classifySizeBin mergedSize
  let inserted ← insertClassArrays withoutRight.second withoutRight.first
    withoutRight.heads withoutRight.next withoutRight.previous mergedBin leftOffset
  pure {
    offsets := physical.offsets, sizes := physical.sizes,
    isFree := physical.isFree, prevFree := physical.prevFree,
    count := physical.count, second := inserted.second, first := inserted.first,
    heads := inserted.heads, next := inserted.next,
    previous := inserted.previous }

theorem coalesceClassArrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {count left : Nat}
    {result : CoalesceClassResult}
    (hsuccess : coalesceClassArrays offsets sizes isFree prevFree second first
      heads next previous count left = some result) :
    ∃ leftOffset rightOffset leftSize rightSize leftBin rightBin
        withoutLeft withoutRight physical mergedSize mergedBin inserted,
      offsets[left]? = some leftOffset ∧
      offsets[left + 1]? = some rightOffset ∧
      sizes[left]? = some leftSize ∧ sizes[left + 1]? = some rightSize ∧
      classifySizeBin leftSize = some leftBin ∧
      classifySizeBin rightSize = some rightBin ∧
      removeClassArrays second first heads next previous leftBin leftOffset =
        some withoutLeft ∧
      removeClassArrays withoutLeft.second withoutLeft.first withoutLeft.heads
        withoutLeft.next withoutLeft.previous rightBin rightOffset =
        some withoutRight ∧
      coalescePhysicalArrays offsets sizes isFree prevFree count left =
        some physical ∧
      physical.sizes[left]? = some mergedSize ∧
      classifySizeBin mergedSize = some mergedBin ∧
      insertClassArrays withoutRight.second withoutRight.first withoutRight.heads
        withoutRight.next withoutRight.previous mergedBin leftOffset =
        some inserted ∧
      result.offsets = physical.offsets ∧ result.sizes = physical.sizes ∧
      result.isFree = physical.isFree ∧ result.prevFree = physical.prevFree ∧
      result.count = physical.count ∧ result.second = inserted.second ∧
      result.first = inserted.first ∧ result.heads = inserted.heads ∧
      result.next = inserted.next ∧ result.previous = inserted.previous := by
  unfold coalesceClassArrays at hsuccess
  cases hleftOffset : offsets[left]? with
  | none => simp [hleftOffset] at hsuccess
  | some leftOffset =>
    cases hrightOffset : offsets[left + 1]? with
    | none => simp [hleftOffset, hrightOffset] at hsuccess
    | some rightOffset =>
      cases hleftSize : sizes[left]? with
      | none => simp [hleftOffset, hrightOffset, hleftSize] at hsuccess
      | some leftSize =>
        cases hrightSize : sizes[left + 1]? with
        | none =>
          simp [hleftOffset, hrightOffset, hleftSize, hrightSize] at hsuccess
        | some rightSize =>
          cases hleftBin : classifySizeBin leftSize with
          | none => simp [hleftOffset, hrightOffset, hleftSize, hrightSize,
              hleftBin] at hsuccess
          | some leftBin =>
            cases hrightBin : classifySizeBin rightSize with
            | none => simp [hleftOffset, hrightOffset, hleftSize, hrightSize,
                hleftBin, hrightBin] at hsuccess
            | some rightBin =>
              cases hwithoutLeft : removeClassArrays second first heads next
                  previous leftBin leftOffset with
              | none => simp [hleftOffset, hrightOffset, hleftSize, hrightSize,
                  hleftBin, hrightBin, hwithoutLeft] at hsuccess
              | some withoutLeft =>
                cases hwithoutRight : removeClassArrays withoutLeft.second
                    withoutLeft.first withoutLeft.heads withoutLeft.next
                    withoutLeft.previous rightBin rightOffset with
                | none => simp [hleftOffset, hrightOffset, hleftSize, hrightSize,
                    hleftBin, hrightBin, hwithoutLeft, hwithoutRight] at hsuccess
                | some withoutRight =>
                  cases hphysical : coalescePhysicalArrays offsets sizes isFree
                      prevFree count left with
                  | none => simp [hleftOffset, hrightOffset, hleftSize,
                      hrightSize, hleftBin, hrightBin, hwithoutLeft,
                      hwithoutRight, hphysical] at hsuccess
                  | some physical =>
                    cases hmergedSize : physical.sizes[left]? with
                    | none => simp [hleftOffset, hrightOffset, hleftSize,
                        hrightSize, hleftBin, hrightBin, hwithoutLeft,
                        hwithoutRight, hphysical, hmergedSize] at hsuccess
                    | some mergedSize =>
                      cases hmergedBin : classifySizeBin mergedSize with
                      | none => simp [hleftOffset, hrightOffset, hleftSize,
                          hrightSize, hleftBin, hrightBin, hwithoutLeft,
                          hwithoutRight, hphysical, hmergedSize,
                          hmergedBin] at hsuccess
                      | some mergedBin =>
                        cases hinserted : insertClassArrays withoutRight.second
                            withoutRight.first withoutRight.heads
                            withoutRight.next withoutRight.previous mergedBin
                            leftOffset with
                        | none => simp [hleftOffset, hrightOffset, hleftSize,
                            hrightSize, hleftBin, hrightBin, hwithoutLeft,
                            hwithoutRight, hphysical, hmergedSize, hmergedBin,
                            hinserted] at hsuccess
                        | some inserted =>
                          simp [hleftOffset, hrightOffset, hleftSize, hrightSize,
                            hleftBin, hrightBin, hwithoutLeft, hwithoutRight,
                            hphysical, hmergedSize, hmergedBin, hinserted] at hsuccess
                          subst result
                          exact ⟨leftOffset, rightOffset, leftSize, rightSize,
                            leftBin, rightBin, withoutLeft, withoutRight,
                            physical, mergedSize, mergedBin, inserted,
                            rfl, rfl, rfl, rfl,
                            hleftBin, hrightBin, hwithoutLeft, hwithoutRight,
                            rfl, hmergedSize, hmergedBin, hinserted,
                            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The full class transaction carries the already-proved physical refinement:
bin unlink/relink operations cannot change the physical active prefix. -/
theorem coalesceClassArrays_refines_physical_append
    (pre : List Block) (leftBlock rightBlock : Block) (rest : List Block)
    (hcan : canCoalesce leftBlock rightBlock)
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hsuccess : coalesceClassArrays
      (blockOffsets (pre ++ leftBlock :: rightBlock :: rest))
      (blockSizes (pre ++ leftBlock :: rightBlock :: rest))
      (freeFlags (pre ++ leftBlock :: rightBlock :: rest))
      (prevFreeFlags (pre ++ leftBlock :: rightBlock :: rest))
      second first heads next previous
      (pre ++ leftBlock :: rightBlock :: rest).length pre.length = some result) :
    RepresentsPhysicalArrays result.offsets result.sizes result.isFree
      result.prevFree result.count
      (coalesceAt (pre ++ leftBlock :: rightBlock :: rest) pre.length) := by
  obtain ⟨_, _, _, _, _, _, _, _, physical, _, _, _, _, _, _, _, _, _, _, _,
      hphysical, _, _, _, hoffsets, hsizes, hfree, hprevFree, hcount, _⟩ :=
    coalesceClassArrays_result hsuccess
  obtain ⟨expected, hexpected, hrep⟩ :=
    coalescePhysicalArrays_refines_append pre leftBlock rightBlock rest hcan
  have heq : physical = expected := by
    exact Option.some.inj (hphysical.symm.trans hexpected)
  subst expected
  simpa [hoffsets, hsizes, hfree, hprevFree, hcount] using hrep

theorem coalesceClassArrays_ownsFree_append
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    (pool : Luffs.Memory.Region) (pre : List Block)
    (leftBlock rightBlock : Block) (rest : List Block)
    (hcan : canCoalesce leftBlock rightBlock)
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hsuccess : coalesceClassArrays
      (blockOffsets (pre ++ leftBlock :: rightBlock :: rest))
      (blockSizes (pre ++ leftBlock :: rightBlock :: rest))
      (freeFlags (pre ++ leftBlock :: rightBlock :: rest))
      (prevFreeFlags (pre ++ leftBlock :: rightBlock :: rest))
      second first heads next previous
      (pre ++ leftBlock :: rightBlock :: rest).length pre.length = some result) :
    RepresentsPhysicalArrays result.offsets result.sizes result.isFree
        result.prevFree result.count
        (coalesceAt (pre ++ leftBlock :: rightBlock :: rest) pre.length) ∧
      (Luffs.Allocator.TLSF.Ownership.OwnsFree (PROP := PROP) pool
          (pre ++ leftBlock :: rightBlock :: rest) ⊣⊢
        Luffs.Allocator.TLSF.Ownership.OwnsFree pool
          (coalesceAt (pre ++ leftBlock :: rightBlock :: rest) pre.length)) := by
  constructor
  · exact coalesceClassArrays_refines_physical_append pre leftBlock rightBlock
      rest hcan hsuccess
  · apply Luffs.Allocator.TLSF.Ownership.coalesceAt_ownsFree pool
      (left := leftBlock) (right := rightBlock)
    · simp
    · simp
    · exact hcan

/-- Exact all-or-nothing array semantics of the first deallocation stage.
The source lowering preflights the same three component operations before its
first write; this pure model makes their successful composition explicit. -/
def deallocateUncoalescedArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count block returnedOffset returnedBytes : Nat) :
    Option DeallocateUncoalescedResult := do
  if count ≤ offsets.length ∧ count ≤ sizes.length ∧
      count ≤ isFree.length ∧ count ≤ prevFree.length ∧ block < count then
    let (nextIsFree, nextPrevFree) ←
      markFreeArrays offsets sizes isFree prevFree block returnedOffset returnedBytes
    let bin ← classifySizeBin returnedBytes
    let insertion ← insertClassArrays second first heads next previous bin returnedOffset
    pure { isFree := nextIsFree, prevFree := nextPrevFree, insertion }
  else none

/-- The concrete flag writes are exactly the projection of the abstract
`markFreeAt` physical-header transition. This includes the successor boundary
tag and frames every other physical header. -/
theorem markFreeArrays_refines_markFreeAt {blocks : List Block} {i : Nat}
    {selected : Block} (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false) :
    markFreeArrays (blockOffsets blocks) (blockSizes blocks)
      (freeFlags blocks) (prevFreeFlags blocks) i selected.offset selected.bytes =
      some (freeFlags (markFreeAt blocks i),
        prevFreeFlags (markFreeAt blocks i)) := by
  induction blocks generalizing i selected with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst selected
          cases rest <;>
            simp [markFreeArrays, blockOffsets, blockSizes, freeFlags,
              prevFreeFlags, markFreeAt,
              hallocated]
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          have htail := ih hget hallocated
          obtain ⟨_, _, hj, _, _, _, _, hfree, hprev⟩ :=
            markFreeArrays_result htail
          have hj' : j < rest.length := by simpa [freeFlags] using hj
          have hfree' : (freeFlags rest).set j 1 =
              freeFlags (markFreeAt rest j) := hfree.symm
          have hprev' :
              (if j + 1 < rest.length then
                (prevFreeFlags rest).set (j + 1) 1 else prevFreeFlags rest) =
                prevFreeFlags (markFreeAt rest j) := by
            simpa [prevFreeFlags] using hprev.symm
          have hjblock : rest[j].free = false := by
            rw [(List.getElem?_eq_some_iff.mp hget).2]
            exact hallocated
          have hjselected : rest[j] = selected :=
            (List.getElem?_eq_some_iff.mp hget).2
          simp [markFreeArrays, blockOffsets, blockSizes, freeFlags,
            prevFreeFlags, markFreeAt,
            hget, hallocated, hj', hjblock, hjselected, hfree',
            show j + 1 + 1 < rest.length + 1 ↔
              j + 1 < rest.length by omega]
          by_cases hs : j + 1 < rest.length <;>
            simp [hs, prevFreeFlags] at hprev' ⊢
          all_goals
            exact ⟨by simpa [freeFlags] using hfree', hprev'⟩

/-- The combined Luffs transaction refines the abstract uncoalesced TLSF
transition: its physical flags are `markFreeAt`, and its links and both bitmap
levels represent insertion of the newly freed block in its verified class. -/
theorem deallocateUncoalescedArrays_refines
    {blocks : List Block} {i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : DeallocateUncoalescedResult}
    {state : Bins.State}
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hvalid : Bins.Valid state)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hsuccess : deallocateUncoalescedArrays
      (blockOffsets blocks) (blockSizes blocks)
      (freeFlags blocks) (prevFreeFlags blocks) second first
      heads next previous blocks.length i selected.offset selected.bytes = some result) :
    ∃ cls,
      classifyBlock? (Dealloc.freedBlock selected) = some cls ∧
      result.isFree = freeFlags (markFreeAt blocks i) ∧
      result.prevFree = prevFreeFlags (markFreeAt blocks i) ∧
      Bins.Valid (state.insert cls (Dealloc.freedBlock selected)) ∧
      RepresentsBins
        { heads := result.insertion.heads,
          next := result.insertion.next,
          previous := result.insertion.previous }
        (state.insert cls (Dealloc.freedBlock selected)) ∧
      RepresentsSecondBitmap result.insertion.second
        (state.insert cls (Dealloc.freedBlock selected)) ∧
      FirstBitmapRep result.insertion.first result.insertion.second := by
  have hmark := markFreeArrays_refines_markFreeAt hget hallocated
  unfold deallocateUncoalescedArrays at hsuccess
  have hi : i < blocks.length := (List.getElem?_eq_some_iff.mp hget).1
  have hpre : blocks.length ≤ (blockOffsets blocks).length ∧
      blocks.length ≤ (blockSizes blocks).length ∧
      blocks.length ≤ (freeFlags blocks).length ∧
      blocks.length ≤ (prevFreeFlags blocks).length ∧ i < blocks.length := by
    simp [blockOffsets, blockSizes, freeFlags, prevFreeFlags, hi]
  rw [if_pos hpre] at hsuccess
  rw [hmark] at hsuccess
  cases hclass : classifySizeBin selected.bytes with
  | none => simp [hclass] at hsuccess
  | some bin =>
      cases hinsert : insertClassArrays second first heads next previous
          bin selected.offset with
      | none => simp [hclass, hinsert] at hsuccess
      | some insertion =>
          simp [hclass, hinsert] at hsuccess
          subst result
          obtain ⟨hsize, hmax, hbin, _⟩ := classifySizeBin_result hclass
          let cls := sizeClass selected.bytes hsize hmax
          have habstract : classifyBlock? (Dealloc.freedBlock selected) = some cls := by
            simp [classifyBlock?, Dealloc.freedBlock, cls, hsize, hmax]
          have hbelongs : Bins.Belongs cls (Dealloc.freedBlock selected) :=
            classifyBlock?_result habstract
          have hrefine := insertClassArrays_refines_insert
            (inserted := Dealloc.freedBlock selected) hvalid hsecond hfirst
            hbins hdisjoint (by simpa [Dealloc.freedBlock] using hfresh)
            hbelongs (by simp [Dealloc.freedBlock]) hbin hinsert
          exact ⟨cls, habstract, rfl, rfl, hrefine⟩

/-- Iris ownership corollary for the concrete Luffs transaction. A successful
array execution witnesses the corresponding abstract allocator transition;
that transition consumes exactly the client's returned byte capability and
adds it to the allocator's free-region ownership. -/
theorem deallocateUncoalescedArrays_ownsFree
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    {pool : Luffs.Memory.Region} {blocks : List Block} {i : Nat}
    {selected : Block} {state : Bins.State}
    {isFree prevFree : List (Fin 256)} {second : List (BitVec 32)}
    {first : BitVec 64} {heads next previous : List Nat}
    {result : DeallocateUncoalescedResult}
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hsuccess : deallocateUncoalescedArrays
      (blockOffsets blocks) (blockSizes blocks) isFree prevFree second first
      heads next previous blocks.length i selected.offset selected.bytes = some result) :
    ∃ cls abstractNext,
      Dealloc.deallocateUncoalesced pool ⟨blocks, state⟩ i
          (selected.region pool) = some abstractNext ∧
      abstractNext.physical = markFreeAt blocks i ∧
      abstractNext.bins = state.insert cls (Dealloc.freedBlock selected) ∧
      (Luffs.Memory.OwnsBytes (PROP := PROP) (selected.region pool) ∗
          Luffs.Allocator.TLSF.Ownership.OwnsFree pool blocks ⊣⊢
        Luffs.Allocator.TLSF.Ownership.OwnsFree pool abstractNext.physical) := by
  unfold deallocateUncoalescedArrays at hsuccess
  split at hsuccess <;> try contradiction
  cases hmark : markFreeArrays (blockOffsets blocks) (blockSizes blocks)
      isFree prevFree i selected.offset selected.bytes with
  | none => simp [hmark] at hsuccess
  | some flags =>
      cases hclass : classifySizeBin selected.bytes with
      | none => simp [hmark, hclass] at hsuccess
      | some bin =>
          cases hinsert : insertClassArrays second first heads next previous
              bin selected.offset with
          | none => simp [hmark, hclass, hinsert] at hsuccess
          | some insertion =>
              obtain ⟨hsize, hmax, _, _⟩ := classifySizeBin_result hclass
              let cls := sizeClass selected.bytes hsize hmax
              have hclassAbstract :
                  classifyBlock? (Dealloc.freedBlock selected) = some cls := by
                simp [classifyBlock?, Dealloc.freedBlock, cls, hsize, hmax]
              let abstractNext : Luffs.Allocator.TLSF.Alloc.State :=
                ⟨markFreeAt blocks i,
                  state.insert cls (Dealloc.freedBlock selected)⟩
              have habstract : Dealloc.deallocateUncoalesced pool
                  ⟨blocks, state⟩ i (selected.region pool) = some abstractNext := by
                simp [Dealloc.deallocateUncoalesced, hget, deallocateAt,
                  hallocated, hclassAbstract, abstractNext]
              refine ⟨cls, abstractNext, habstract, rfl, rfl, ?_⟩
              exact Dealloc.deallocateUncoalesced_ownsFree habstract

end Luffs.Runtime.TLSF
