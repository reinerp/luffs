import Luffs.Allocator.TLSF.FreeList
import Luffs.Allocator.TLSF.Bitmap
import Luffs.Allocator.TLSF.Bins
import Luffs.Allocator.TLSF.Dealloc

set_option autoImplicit false

namespace Luffs.Runtime.TLSF

open Iris Iris.BI Luffs.Allocator.TLSF

/-- Checked conversion at the public mmap-backed pool boundary. Internal TLSF
metadata stores offsets; a raw address becomes usable only after this check. -/
def pointerToOffset (poolBase poolBytes pointer : Nat) : Option Nat :=
  if pointer < poolBase then none
  else
    let offset := pointer - poolBase
    if offset ≥ poolBytes then none else some offset

theorem pointerToOffset_result {poolBase poolBytes pointer offset : Nat}
    (hsuccess : pointerToOffset poolBase poolBytes pointer = some offset) :
    pointer = poolBase + offset ∧ offset < poolBytes := by
  by_cases hbelow : pointer < poolBase
  · simp [pointerToOffset, hbelow] at hsuccess
  · by_cases houtside : pointer - poolBase ≥ poolBytes
    · simp [pointerToOffset, hbelow, houtside] at hsuccess
    · simp [pointerToOffset, hbelow, houtside] at hsuccess
      subst offset
      exact ⟨(Nat.add_sub_of_le (Nat.le_of_not_gt hbelow)).symm,
        Nat.lt_of_not_ge houtside⟩

theorem pointerToOffset_complete {poolBase poolBytes pointer : Nat}
    (hcontains : poolBase ≤ pointer ∧ pointer < poolBase + poolBytes) :
    pointerToOffset poolBase poolBytes pointer = some (pointer - poolBase) := by
  have hbelow : ¬pointer < poolBase := Nat.not_lt.mpr hcontains.1
  have hoffset : pointer - poolBase < poolBytes := by omega
  simp [pointerToOffset, hbelow, Nat.not_le.mpr hoffset]
open Luffs.Allocator.TLSF.Bins

def usizeMax : Nat := 2 ^ 64 - 1

def encodeSizeClass (cls : SizeClass) : Nat :=
  cls.fl.val * secondLevelCount + cls.sl.val

theorem encodeSizeClass_div (cls : SizeClass) :
    encodeSizeClass cls / secondLevelCount = cls.fl.val := by
  have hsl := cls.sl.isLt
  simp only [encodeSizeClass, secondLevelCount] at hsl ⊢
  omega

theorem encodeSizeClass_mod (cls : SizeClass) :
    encodeSizeClass cls % secondLevelCount = cls.sl.val := by
  have hsl := cls.sl.isLt
  simp only [encodeSizeClass, secondLevelCount] at hsl ⊢
  omega

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

theorem classifySizeBin_complete {size : Nat}
    (hsize : 0 < size) (hmax : size < 2 ^ firstLevelCount) :
    classifySizeBin size = some (encodeSizeClass (sizeClass size hsize hmax)) := by
  simp [classifySizeBin, hsize, hmax]

theorem classifySizeBin_ne_none {size : Nat}
    (hsize : 0 < size) (hmax : size < 2 ^ firstLevelCount) :
    classifySizeBin size ≠ none := by
  rw [classifySizeBin_complete hsize hmax]
  simp

theorem classifySizeBin_refines_block {block : Block} {encoded : Nat}
    (hclass : classifySizeBin block.bytes = some encoded) :
    ∃ cls, Bins.classifyBlock? block = some cls ∧
      encoded = encodeSizeClass cls := by
  obtain ⟨hsize, hmax, hencoded, _⟩ := classifySizeBin_result hclass
  let cls := sizeClass block.bytes hsize hmax
  refine ⟨cls, ?_, hencoded⟩
  simp [Bins.classifyBlock?, cls, hsize, hmax]

theorem classifySizeBin_of_classifyBlock {block : Block} {cls : SizeClass}
    (hclass : Bins.classifyBlock? block = some cls) :
    classifySizeBin block.bytes = some (encodeSizeClass cls) := by
  unfold Bins.classifyBlock? at hclass
  split at hclass <;> try contradiction
  next hsize =>
    split at hclass <;> try contradiction
    next hmax =>
      simp only [Option.some.injEq] at hclass
      subst cls
      exact classifySizeBin_complete hsize hmax

/-- The executable mapping-up classifier used to start allocation lookup. -/
def classifyRequestBin (request : Nat) : Option Nat :=
  if hrequest : 0 < request then
    if hmax : requestKey request < 2 ^ firstLevelCount then
      some (encodeSizeClass (searchSizeClass request hrequest hmax))
    else none
  else none

theorem classifyRequestBin_result {request encoded : Nat}
    (hclass : classifyRequestBin request = some encoded) :
    ∃ (hrequest : 0 < request)
        (hmax : requestKey request < 2 ^ firstLevelCount),
      encoded = encodeSizeClass (searchSizeClass request hrequest hmax) ∧
      encoded < 2048 := by
  unfold classifyRequestBin at hclass
  split at hclass <;> try contradiction
  next hrequest =>
    split at hclass <;> try contradiction
    next hmax =>
      simp only [Option.some.injEq] at hclass
      subst encoded
      refine ⟨hrequest, hmax, rfl, ?_⟩
      have hfl := (searchSizeClass request hrequest hmax).fl.isLt
      have hsl := (searchSizeClass request hrequest hmax).sl.isLt
      simp only [encodeSizeClass, firstLevelCount, secondLevelCount] at hfl hsl ⊢
      omega

/-- Mathematical value of Rust's `u64::leading_zeros` on a nonzero word.
The explicit out-of-range branch makes this a total model on `Nat`. -/
def leadingZeros64 (value : Nat) : Nat :=
  if value = 0 then 64
  else if value < 2 ^ 64 then 63 - value.log2
  else 0

theorem leadingZeros64_eq {value : Nat} (hpositive : 0 < value)
    (hmax : value < 2 ^ 64) :
    leadingZeros64 value = 63 - value.log2 := by
  simp [leadingZeros64, Nat.ne_of_gt hpositive, hmax]

/-- Independent, word-operation-shaped semantics of `tlsf_classify_size`.
Unlike `classifySizeBin`, this follows the source's `leading_zeros`, shifts,
subtractions, quotient, and final encoded-index checks. -/
def classifySizeBinLowered (size : Nat) : Option Nat :=
  if size > usizeMax then none
  else if size = 0 then none
  else if size ≤ 256 then
    some ((size - 1) >>> 3)
  else
    let leading := leadingZeros64 size
    if leading > 63 then none
    else
      let fl := 63 - leading
      if fl < 5 then none
      else
        let base := 1 <<< fl
        if base > size then none
        else
          let shift := fl - 5
          let step := 1 <<< shift
          let delta := size - base
          let sl := delta / step
          if sl ≥ 32 then none
          else
            let encodedBase := fl * 32
            let encoded := encodedBase + sl
            if encoded > usizeMax then none else some encoded

theorem classifySizeBinLowered_eq (size : Nat) :
    classifySizeBinLowered size = classifySizeBin size := by
  by_cases hzero : size = 0
  · simp [classifySizeBinLowered, classifySizeBin, hzero, usizeMax]
  have hpositive : 0 < size := Nat.pos_of_ne_zero hzero
  by_cases hmax : size < 2 ^ 64
  · have hlogMax : size.log2 < 64 :=
      (Nat.log2_lt (Nat.ne_of_gt hpositive)).2 hmax
    have hword : ¬size > usizeMax := by
      simp only [usizeMax]
      omega
    have hfl : 63 - (63 - size.log2) = size.log2 := by omega
    have hleading := leadingZeros64_eq hpositive hmax
    by_cases hlinear : size ≤ 256
    · have hshift : (size - 1) >>> 3 = (size - 1) / 8 := by
        simp [Nat.shiftRight_eq_div_pow]
      simp [classifySizeBinLowered, classifySizeBin, hword, hzero, hlinear,
        hshift, sizeClass, linearCutoff, alignment, encodeSizeClass,
        secondLevelCount, firstLevelCount]
      exact ⟨hpositive, by simpa using hmax⟩
    · have hhigh : linearCutoff < size := by
        simp only [linearCutoff, alignment, secondLevelCount]
        omega
      have hlog : 5 ≤ size.log2 := high_log_at_least_five size hhigh
      have hbase : 2 ^ size.log2 ≤ size :=
        Nat.log2_self_le (Nat.ne_of_gt hpositive)
      have hquotient := high_sizeClass_quotient_lt size hpositive hlog
      have hencoded : size.log2 * 32 +
          (size - 2 ^ size.log2) / 2 ^ (size.log2 - 5) ≤ usizeMax := by
        simp only [usizeMax]
        have : size.log2 ≤ 63 := by omega
        have hq : (size - 2 ^ size.log2) / 2 ^ (size.log2 - 5) < 32 := by
          simpa [secondLevelCount] using hquotient
        omega
      simp only [classifySizeBinLowered, hword, ↓reduceIte, hzero, hlinear,
        leadingZeros64_eq hpositive hmax]
      simp only [show ¬63 < 63 - size.log2 by omega, ↓reduceIte, hfl,
        Nat.not_lt_of_ge hlog, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.not_lt_of_ge hbase, Nat.not_le.mpr (by simpa using hquotient),
        hencoded]
      simp [classifySizeBin, hpositive, hmax, sizeClass,
        Nat.not_le_of_gt hhigh, encodeSizeClass, secondLevelCount,
        firstLevelCount, high_sizeClass_no_wrap size hpositive hlog]
      exact ⟨by simpa [secondLevelCount] using hquotient, hencoded,
        (high_sizeClass_no_wrap size hpositive hlog).symm⟩
  · have hout : ¬size < 2 ^ firstLevelCount := by
      simpa [firstLevelCount] using hmax
    have hword : size > usizeMax := by
      simp only [usizeMax]
      omega
    simp [classifySizeBinLowered, classifySizeBin, hword, hpositive, hout]

/-- Source-shaped computation of the upper endpoint used for mapping an
allocation request upward. The two final comparisons model the source's
checked additions in the 64-bit `usize` domain. -/
def highRequestKeyLowered (request : Nat) : Option Nat :=
  let leading := leadingZeros64 request
  if leading > 63 then none
  else
    let fl := 63 - leading
    if fl < 5 then none
    else
      let base := 1 <<< fl
      if base > request then none
      else
        let shift := fl - 5
        let step := 1 <<< shift
        let delta := request - base
        let sl := delta / step
        if sl ≥ 32 then none
        else
          let lowerDelta := sl * step
          let lower := base + lowerDelta
          if lower > usizeMax then none
          else
            let key := lower + step
            if key > usizeMax then none else some key

theorem highRequestKeyLowered_eq (request : Nat)
    (hpositive : 0 < request) (hhigh : linearCutoff < request)
    (hmax : request < 2 ^ 64) :
    highRequestKeyLowered request =
      if requestKey request > usizeMax then none else some (requestKey request) := by
  have hlogMax : request.log2 < 64 :=
    (Nat.log2_lt (Nat.ne_of_gt hpositive)).2 hmax
  have hfl : 63 - (63 - request.log2) = request.log2 := by omega
  have hlog : 5 ≤ request.log2 := high_log_at_least_five request hhigh
  have hbase : 2 ^ request.log2 ≤ request :=
    Nat.log2_self_le (Nat.ne_of_gt hpositive)
  have hsl : (request - 2 ^ request.log2) /
      2 ^ (request.log2 - 5) < 32 := by
    simpa [secondLevelCount] using
      high_sizeClass_quotient_lt request hpositive hlog
  have hlower : 2 ^ request.log2 +
      ((request - 2 ^ request.log2) / 2 ^ (request.log2 - 5)) *
        2 ^ (request.log2 - 5) = highBinLower request := by
    rfl
  have hkey : highBinLower request + 2 ^ (request.log2 - 5) =
      requestKey request := by
    simp [requestKey, Nat.not_le_of_gt hhigh, highBinUpper, highBinStep]
  have hlowerLe : highBinLower request ≤ request :=
    (high_sizeClass_covers request hpositive).1
  have hword : request ≤ usizeMax := by
    simp only [usizeMax]
    omega
  have hlowerWord : ¬highBinLower request > usizeMax := by omega
  simp only [highRequestKeyLowered, leadingZeros64_eq hpositive hmax,
    show ¬63 < 63 - request.log2 by omega, ↓reduceIte, hfl,
    Nat.not_lt_of_ge hlog, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.not_lt_of_ge hbase, Nat.not_le.mpr hsl]
  rw [hlower, if_neg hlowerWord, hkey]

/-- Independent executable semantics of `tlsf_classify_request`. The high
branch calls the separately lowered mapping-down classifier, matching the
actual Luffs call graph. -/
def classifyRequestBinLowered (request : Nat) : Option Nat :=
  if request > usizeMax then none
  else if request = 0 then none
  else if request ≤ 256 then classifySizeBinLowered request
  else do
    let key ← highRequestKeyLowered request
    classifySizeBinLowered key

theorem classifyRequestBinLowered_eq (request : Nat) :
    classifyRequestBinLowered request = classifyRequestBin request := by
  by_cases hwordOut : request > usizeMax
  · have hpositive : 0 < request := by omega
    have hkeyOut : ¬requestKey request < 2 ^ firstLevelCount := by
      have hle := request_le_key request hpositive
      simp only [usizeMax, firstLevelCount] at hwordOut ⊢
      omega
    simp [classifyRequestBinLowered, hwordOut, classifyRequestBin,
      hpositive, hkeyOut]
  by_cases hzero : request = 0
  · simp [classifyRequestBinLowered, hwordOut, hzero, classifyRequestBin]
  have hpositive : 0 < request := Nat.pos_of_ne_zero hzero
  have hmax : request < 2 ^ 64 := by
    simp only [usizeMax] at hwordOut
    omega
  by_cases hlinear : request ≤ 256
  · have hlinearCutoff : request ≤ linearCutoff := by
      simpa [linearCutoff, alignment, secondLevelCount] using hlinear
    have hkeyMax : requestKey request < 2 ^ firstLevelCount := by
      simp [requestKey, hlinearCutoff, linearBinUpper, linearBinNumber,
        alignment, firstLevelCount]
      omega
    have hkeyMax64 : requestKey request < 2 ^ 64 := by
      simpa [firstLevelCount] using hkeyMax
    rw [classifyRequestBinLowered]
    simp only [hwordOut, ↓reduceIte, hzero, hlinear]
    rw [classifySizeBinLowered_eq]
    simp [classifyRequestBin, classifySizeBin, hpositive, hmax, hkeyMax,
      hkeyMax64,
      searchSizeClass, hlinearCutoff, firstLevelCount]
  · have hhigh : linearCutoff < request := by
      simp only [linearCutoff, alignment, secondLevelCount]
      omega
    rw [classifyRequestBinLowered]
    simp only [hwordOut, ↓reduceIte, hzero, hlinear]
    rw [highRequestKeyLowered_eq request hpositive hhigh hmax]
    by_cases hkeyWord : requestKey request > usizeMax
    · have hkeyOut : ¬requestKey request < 2 ^ firstLevelCount := by
        simp only [usizeMax, firstLevelCount] at hkeyWord ⊢
        omega
      simp [hkeyWord, classifyRequestBin, hpositive, hkeyOut]
    · have hkeyMax : requestKey request < 2 ^ firstLevelCount := by
        simp only [usizeMax, firstLevelCount] at hkeyWord ⊢
        omega
      simp only [hkeyWord, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
      rw [classifySizeBinLowered_eq]
      simp [classifyRequestBin, classifySizeBin, hpositive, hkeyMax,
        searchSizeClass, requestSizeClass, Nat.not_le_of_gt hhigh,
        requestKey_positive]

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

/-- Exact metadata-operation count for `insert`: failed guards consume their
tested probes; success performs three guards, one head read, three mandatory
writes, and at most one old-head backlink write. -/
def insertSteps (state : Metadata) (bin block : Nat) : Nat :=
  if bin ≥ state.heads.length then 1
  else if block ≥ state.next.length then 2
  else if block ≥ state.previous.length then 3
  else
    let oldHead := state.heads[bin]?.getD 0
    if oldHead < state.previous.length then 8 else 7

theorem insertSteps_le (state : Metadata) (bin block : Nat) :
    insertSteps state bin block ≤ 8 := by
  simp only [insertSteps]
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

def insertProfile (state : Metadata) (bin block : Nat) : Option Metadata × Nat :=
  (insert state bin block, insertSteps state bin block)

theorem insertProfile_result (state : Metadata) (bin block : Nat) :
    (insertProfile state bin block).1 = insert state bin block ∧
      (insertProfile state bin block).2 ≤ 8 :=
  ⟨rfl, insertSteps_le state bin block⟩

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

/-- Exact metadata-operation count for `remove`: after its three guards and
two link reads, it performs three link-position tests, two mandatory detach
writes, and up to three conditional repair writes. -/
def removeSteps (state : Metadata) (bin block : Nat) : Nat :=
  if bin ≥ state.heads.length then 1
  else if block ≥ state.next.length then 2
  else if block ≥ state.previous.length then 3
  else
    let successor := state.next[block]?.getD state.next.length
    let predecessor := state.previous[block]?.getD state.next.length
    10 + (if predecessor ≥ state.next.length then 1 else 0) +
      (if predecessor < state.next.length then 1 else 0) +
      (if successor < state.previous.length then 1 else 0)

theorem removeSteps_le (state : Metadata) (bin block : Nat) :
    removeSteps state bin block ≤ 13 := by
  simp only [removeSteps]
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> split <;> split <;> omega

def removeProfile (state : Metadata) (bin block : Nat) : Option Metadata × Nat :=
  (remove state bin block, removeSteps state bin block)

theorem removeProfile_result (state : Metadata) (bin block : Nat) :
    (removeProfile state bin block).1 = remove state bin block ∧
      (removeProfile state bin block).2 ≤ 13 :=
  ⟨rfl, removeSteps_le state bin block⟩

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

/-- Once its three guards pass, intrusive removal has no remaining failure
edge. In particular, every conditional link repair is a checked write and the
two detach writes use the already-validated block index. -/
theorem removeArrays_ne_none_of_bounds
    {heads next previous : List Nat} {bin block : Nat}
    (hbin : bin < heads.length) (hnext : block < next.length)
    (hprevious : block < previous.length) :
    removeArrays heads next previous bin block ≠ none := by
  simp [removeArrays, remove, Nat.not_le.mpr hbin, Nat.not_le.mpr hnext,
    Nat.not_le.mpr hprevious]

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

/-- Number of loop iterations taken by `findNonzeroWords`. This is an exact
cost model for the only recursive loop in the lowered flat-bitmap lookup. -/
def findNonzeroWordsSteps : List (BitVec 64) → Nat
  | [] => 0
  | word :: rest =>
      if word = (0 : BitVec 64) then 1 + findNonzeroWordsSteps rest else 1

theorem findNonzeroWordsSteps_le (words : List (BitVec 64)) :
    findNonzeroWordsSteps words ≤ words.length := by
  induction words with
  | nil => exact Nat.le_refl 0
  | cons word rest ih =>
      simp only [findNonzeroWordsSteps, List.length_cons]
      split <;> omega

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

/-- Exact number of bitmap words inspected by `findNonemptyBinLowered`. -/
def findNonemptyBinLoweredSteps (words : List (BitVec 64)) (start : Nat) : Nat :=
  let wordIndex := start / 64
  let bit := start % 64
  match words.drop wordIndex with
  | [] => 0
  | word :: rest =>
      let masked := word &&& maskFrom bit
      if masked ≠ 0 then 1 else 1 + findNonzeroWordsSteps rest

theorem findNonemptyBinLoweredSteps_le (words : List (BitVec 64)) (start : Nat) :
    findNonemptyBinLoweredSteps words start ≤ words.length := by
  simp only [findNonemptyBinLoweredSteps]
  cases hdrop : words.drop (start / 64) with
  | nil => simp [hdrop]
  | cons word rest =>
      have hlength : rest.length + 1 ≤ words.length := by
        have hdropLength := congrArg List.length hdrop
        simp only [List.length_drop, List.length_cons] at hdropLength
        omega
      dsimp only
      split
      · omega
      · have hsteps := findNonzeroWordsSteps_le rest
        omega

theorem findNonemptyBinLoweredSteps_fixed (words : List (BitVec 64))
    (start : Nat) (hwords : words.length ≤ 4) :
    findNonemptyBinLoweredSteps words start ≤ 4 := by
  exact Nat.le_trans (findNonemptyBinLoweredSteps_le words start) hwords

def findNonemptyBinLoweredProfile (words : List (BitVec 64)) (start : Nat) :
    Option Nat × Nat :=
  (findNonemptyBinLowered words start, findNonemptyBinLoweredSteps words start)

theorem findNonemptyBinLoweredProfile_fixed (words : List (BitVec 64))
    (start : Nat) (hwords : words.length ≤ 4) :
    (findNonemptyBinLoweredProfile words start).1 =
        findNonemptyBinLowered words start ∧
      (findNonemptyBinLoweredProfile words start).2 ≤ 4 :=
  ⟨rfl, findNonemptyBinLoweredSteps_fixed words start hwords⟩

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

/-- Exact count of conditional metadata probes in the lowered two-level class
lookup. Unlike the flat fallback above, this path is branch-bounded and does
not traverse a list. -/
def findNonemptyClassLoweredSteps (second : List (BitVec 32)) (first : BitVec 64)
    (startFl startSl : Nat) : Nat :=
  if startFl ≥ second.length then 1 else
  if startSl ≥ 32 then 2 else
  let secondBitmap := second[startFl]?.getD 0
  let secondMasked := secondBitmap &&& maskFrom32 startSl
  if secondMasked ≠ 0 then 3 else
  let nextFl := startFl + 1
  if nextFl ≥ 64 then 4 else
  let firstMasked := first &&& maskFrom nextFl
  if firstMasked = 0 then 5 else
  let foundFl := firstMasked.ctz.toNat
  if foundFl ≥ second.length then 6 else
  let foundSecond := second[foundFl]?.getD 0
  if foundSecond = 0 then 7 else 7

theorem findNonemptyClassLoweredSteps_le (second : List (BitVec 32))
    (first : BitVec 64) (startFl startSl : Nat) :
    findNonemptyClassLoweredSteps second first startFl startSl ≤ 7 := by
  simp only [findNonemptyClassLoweredSteps]
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

def findNonemptyClassLoweredProfile (second : List (BitVec 32))
    (first : BitVec 64) (startFl startSl : Nat) : Option Nat × Nat :=
  (findNonemptyClassLowered second first startFl startSl,
    findNonemptyClassLoweredSteps second first startFl startSl)

theorem findNonemptyClassLoweredProfile_bounded (second : List (BitVec 32))
    (first : BitVec 64) (startFl startSl : Nat) :
    (findNonemptyClassLoweredProfile second first startFl startSl).1 =
        findNonemptyClassLowered second first startFl startSl ∧
      (findNonemptyClassLoweredProfile second first startFl startSl).2 ≤ 7 :=
  ⟨rfl, findNonemptyClassLoweredSteps_le second first startFl startSl⟩

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

/-- Once its public source guards and the intrusive-splice preflight hold,
class removal cannot fail after it begins mutating metadata. -/
theorem removeClassArrays_ne_none_of_preflight
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    (hbin : bin < heads.length) (hfl : bin / 32 < second.length)
    (hnext : block < next.length) (hprevious : block < previous.length) :
    removeClassArrays second first heads next previous bin block ≠ none := by
  have hremove := removeArrays_ne_none_of_bounds hbin hnext hprevious
  simp only [removeClassArrays, Nat.not_le.mpr hbin, if_false,
    Nat.not_le.mpr hfl, Nat.not_le.mpr hnext, Nat.not_le.mpr hprevious]
  cases hremoveEq : removeArrays heads next previous bin block with
  | none => exact (hremove hremoveEq).elim
  | some removed => simp

theorem removeClassArrays_preserves_lengths
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    {result : RemoveClassResult}
    (hremove : removeClassArrays second first heads next previous bin block =
      some result) :
    result.second.length = second.length ∧ result.heads.length = heads.length ∧
      result.next.length = next.length ∧
      result.previous.length = previous.length := by
  have hresult := removeClassArrays_result hremove
  have hmetadata := removeArrays_result hresult.2.2.2.2.1
  have hlens := remove_preserves_lengths hmetadata
  constructor
  · split at hresult
    · rw [hresult.2.1, clearClassBit_length]
    · rw [hresult.2.1]
  · exact hlens

/-- Bounds preflighted by public allocation make remainder insertion total.
No property of the old head is required: insertion conditionally repairs its
back-link only when that sentinel-or-offset is representable. -/
theorem insertClassArrays_ne_none_of_preflight
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {bin block : Nat}
    (hbin : bin < heads.length) (hfl : bin / 32 < second.length)
    (hnext : block < next.length) (hprevious : block < previous.length) :
    insertClassArrays second first heads next previous bin block ≠ none := by
  simp [insertClassArrays, insert, Nat.not_le.mpr hbin,
    Nat.not_le.mpr hfl, Nat.not_le.mpr hnext, Nat.not_le.mpr hprevious]

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

/-- Candidate removal is transactional at its call boundary: after lookup and
the four index guards, its only nested fallible operation is `removeArrays`,
which is total from exactly those validated indices. -/
theorem takeCandidateClassArrays_ne_none_of_preflight
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {startFl startSl bin block : Nat}
    (hfind : findNonemptyClassLowered second first startFl startSl = some bin)
    (hbin : bin < heads.length) (hfl : bin / 32 < second.length)
    (hblock : block = heads[bin]?.getD next.length)
    (hnext : block < next.length) (hprevious : block < previous.length) :
    takeCandidateClassArrays second first heads next previous startFl startSl ≠
      none := by
  subst block
  simp [takeCandidateClassArrays, hfind, Nat.not_le.mpr hbin,
    Nat.not_le.mpr hfl, Nat.not_le.mpr hnext,
    Nat.not_le.mpr hprevious, removeArrays, remove]
  split <;> simp

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

theorem represented_class_indices_bounded
    {second : List (BitVec 32)} {state : Bins.State}
    {heads next previous : List Nat}
    (hsecond : RepresentsSecondBitmap second state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (cls : SizeClass) :
    encodeSizeClass cls < heads.length ∧
      encodeSizeClass cls / secondLevelCount < second.length := by
  constructor
  · simpa [encodeSizeClass] using (hbins cls).1
  · rw [encodeSizeClass_div, hsecond.1]
    exact cls.fl.isLt

theorem represented_free_block_link_bounds
    {pool : Luffs.Memory.Region} {physical : List Block} {state : Bins.State}
    {heads next previous : List Nat} {block : Block}
    (hvalid : Alloc.Valid pool { physical, bins := state })
    (hbins : RepresentsBins { heads, next, previous } state)
    (hmem : block ∈ physical) (hfree : block.free = true) :
    block.offset < next.length ∧ block.offset < previous.length := by
  obtain ⟨cls, cached, hcached, hsame⟩ :=
    hvalid.2.2.2 block hmem hfree
  have hoffsetMem : block.offset ∈ (state.chains cls).map Block.offset := by
    rw [hsame.1]
    exact List.mem_map_of_mem Block.offset hcached
  exact linked_member_bounds (hbins cls).2.2.2.1 hoffsetMem

/-- A free physical block in a completely represented allocator satisfies all
classification and intrusive-address preflights required before coalescing. -/
theorem represented_free_block_preflight
    {pool : Luffs.Memory.Region} {physical : List Block} {state : Bins.State}
    {second : List (BitVec 32)} {heads next previous : List Nat}
    {block : Block}
    (hvalid : Alloc.Valid pool { physical, bins := state })
    (hsecond : RepresentsSecondBitmap second state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hmem : block ∈ physical) (hfree : block.free = true) :
  ∃ cls,
      classifySizeBin block.bytes = some (encodeSizeClass cls) ∧
      encodeSizeClass cls < heads.length ∧
      encodeSizeClass cls / secondLevelCount < second.length ∧
      block.offset < next.length ∧ block.offset < previous.length := by
  obtain ⟨_, cached, hcached, hsame⟩ :=
    hvalid.2.2.2 block hmem hfree
  obtain ⟨hsize, hmax, _⟩ := member_belongs hvalid.2.1 hcached
  have hblockSize : 0 < block.bytes := by
    simpa [hsame.2.1] using hsize
  have hblockMax : block.bytes < 2 ^ firstLevelCount := by
    simpa [hsame.2.1] using hmax
  let cls := sizeClass block.bytes hblockSize hblockMax
  have hclass : classifySizeBin block.bytes = some (encodeSizeClass cls) :=
    classifySizeBin_complete hblockSize hblockMax
  have hindices := represented_class_indices_bounded hsecond hbins cls
  have hlinks := represented_free_block_link_bounds hvalid hbins hmem hfree
  exact ⟨cls, hclass, hindices.1, hindices.2, hlinks.1, hlinks.2⟩

theorem represented_coalesced_block_preflight
    {pool : Luffs.Memory.Region} {physical : List Block} {state : Bins.State}
    {second : List (BitVec 32)} {heads next previous : List Nat}
    {left right : Block}
    (hvalid : Alloc.Valid pool { physical, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hsecond : RepresentsSecondBitmap second state)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hleftMem : left ∈ physical) (hrightMem : right ∈ physical)
    (hcan : canCoalesce left right) :
    ∃ cls,
      classifySizeBin (left.bytes + right.bytes) =
          some (encodeSizeClass cls) ∧
      encodeSizeClass cls < heads.length ∧
      encodeSizeClass cls / secondLevelCount < second.length := by
  have hpositive : 0 < left.bytes + right.bytes := by
    have hleftPositive := (hvalid.1.2.2.2 left hleftMem).1
    omega
  have hrightEnd := (hvalid.1.2.2.2 right hrightMem).2.1
  have hmax : left.bytes + right.bytes < 2 ^ firstLevelCount := by
    rw [hcan.2.2] at hrightEnd
    omega
  let cls := sizeClass (left.bytes + right.bytes) hpositive hmax
  have hclass := classifySizeBin_complete hpositive hmax
  have hindices := represented_class_indices_bounded hsecond hbins cls
  exact ⟨cls, hclass, hindices.1, hindices.2⟩

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

theorem replaceChain_preserves_offsets_disjoint
    {state : Bins.State} {target : SizeClass} {replacement : List Block}
    (hdisjoint : BinsOffsetsDisjoint state)
    (hsubset : ∀ offset, offset ∈ replacement.map Block.offset →
      offset ∈ (state.chains target).map Block.offset) :
    BinsOffsetsDisjoint (state.replaceChain target replacement) := by
  intro left right hne offset hleft hright
  by_cases hleftTarget : left = target
  · subst left
    have hrightTarget : right ≠ target := fun h => hne h.symm
    apply hdisjoint hne offset
    · apply hsubset offset
      simpa [Bins.State.replaceChain, Bins.State.fromChains,
        Bins.Chains.replace] using hleft
    · simpa [Bins.replaceChain_other state replacement hrightTarget] using hright
  · by_cases hrightTarget : right = target
    · subst right
      apply hdisjoint hne offset
      · simpa [Bins.replaceChain_other state replacement hleftTarget] using hleft
      · apply hsubset offset
        simpa [Bins.State.replaceChain, Bins.State.fromChains,
          Bins.Chains.replace] using hright
    · apply hdisjoint hne offset
      · simpa [Bins.replaceChain_other state replacement hleftTarget] using hleft
      · simpa [Bins.replaceChain_other state replacement hrightTarget] using hright

theorem takeCandidate_preserves_offsets_disjoint
    {state next : Bins.State} {start : SizeClass} {removed : Block}
    (hdisjoint : BinsOffsetsDisjoint state)
    (htake : state.takeCandidate start = some (removed, next)) :
    BinsOffsetsDisjoint next := by
  obtain ⟨cls, rest, _, hremove, rfl⟩ := takeCandidate_result htake
  apply replaceChain_preserves_offsets_disjoint hdisjoint
  have hoffsets := FreeList.removeFront_removes_head hremove
  intro offset hmem
  rw [hoffsets.2] at hmem
  exact List.mem_of_mem_tail hmem

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

theorem takeCandidateClassArrays_preserves_metadata_lengths
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {startFl startSl : Nat}
    {result : ClassCandidateResult}
    (htake : takeCandidateClassArrays second first heads next previous
      startFl startSl = some result) :
    result.heads.length = heads.length ∧ result.next.length = next.length ∧
      result.previous.length = previous.length := by
  have hresult := takeCandidateClassArrays_result htake
  have hremove := removeArrays_result hresult.2.2.2.2.2.2.1
  exact remove_preserves_lengths hremove

theorem takeCandidateClassArrays_preserves_second_length
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {startFl startSl : Nat}
    {result : ClassCandidateResult}
    (htake : takeCandidateClassArrays second first heads next previous
      startFl startSl = some result) :
    result.second.length = second.length := by
  have hresult := takeCandidateClassArrays_result htake
  by_cases hexhausted : next[result.block]?.getD next.length ≥ next.length
  · have heq := hresult.2.2.2.2.2.2.2
    simp only [hexhausted, if_true] at heq
    rw [heq.1, clearClassBit_length]
  · have heq := hresult.2.2.2.2.2.2.2
    simp only [hexhausted, if_false] at heq
    exact congrArg List.length heq.1

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

theorem removeOffset_absent_everywhere
    {state : Bins.State} {cls : SizeClass} {block : Nat}
    {removed : Block} {replacement : List Block}
    (hvalid : Bins.Valid state) (hdisjoint : BinsOffsetsDisjoint state)
    (hremove : FreeList.removeOffset (state.chains cls) block =
      some (removed, replacement)) :
    ∀ query, block ∉
      ((state.replaceChain cls replacement).chains query).map Block.offset := by
  have horigin := FreeList.removeOffset_removed_origin (hvalid.1 cls) hremove
  obtain ⟨old, holdMem, holdOffset, _⟩ := horigin
  intro query
  by_cases hquery : query = cls
  · subst query
    simpa [Bins.State.replaceChain, Bins.State.fromChains,
      Bins.Chains.replace] using
      (FreeList.removeOffset_absent (hvalid.1 cls) hremove)
  · intro hmem
    have hqueryMem : block ∈ (state.chains query).map Block.offset := by
      simpa [Bins.replaceChain_other state replacement hquery] using hmem
    have hselectedMem : block ∈ (state.chains cls).map Block.offset := by
      rw [← holdOffset]
      exact List.mem_map_of_mem holdMem
    exact hdisjoint (Ne.symm hquery) block hselectedMem hqueryMem

theorem removeOffset_preserves_global_absence
    {state : Bins.State} {cls : SizeClass} {removedOffset absent : Nat}
    {removed : Block} {replacement : List Block}
    (habsent : ∀ query, absent ∉
      (state.chains query).map Block.offset)
    (hremove : FreeList.removeOffset (state.chains cls) removedOffset =
      some (removed, replacement)) :
    ∀ query, absent ∉
      ((state.replaceChain cls replacement).chains query).map Block.offset := by
  have hoffsets := FreeList.removeOffset_offsets hremove
  intro query
  by_cases hquery : query = cls
  · subst query
    intro hmem
    have hreplacement : absent ∈ replacement.map Block.offset := by
      simpa [Bins.State.replaceChain, Bins.State.fromChains,
        Bins.Chains.replace] using hmem
    rw [hoffsets] at hreplacement
    exact habsent cls (List.mem_of_mem_erase hreplacement)
  · simpa [Bins.replaceChain_other state replacement hquery] using
      habsent query

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

/-- Concrete mutable metadata touched by `tlsf_mark_free`. Retaining it in a
failure result prevents an `Option` model from erasing an intermediate write. -/
structure MarkFreeMachineState where
  isFree : List (Fin 256)
  prevFree : List (Fin 256)
deriving DecidableEq, Repr

inductive MarkFreeOutcome where
  | success (state : MarkFreeMachineState)
  | failure (state : MarkFreeMachineState)
deriving DecidableEq, Repr

/-- Stateful, source-ordered semantics of `tlsf_mark_free`. Every rejection is
before the two writes; after the writes there is no fallible operation. -/
def markFreeArraysOutcome (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256))
    (block returnedOffset returnedBytes : Nat) : MarkFreeOutcome :=
  let input : MarkFreeMachineState := ⟨isFree, prevFree⟩
  if block ≥ offsets.length then .failure input
  else if block ≥ sizes.length then .failure input
  else if block ≥ isFree.length then .failure input
  else if block ≥ prevFree.length then .failure input
  else if isFree[block]? != some 0 then .failure input
  else if offsets[block]? != some returnedOffset then .failure input
  else if sizes[block]? != some returnedBytes then .failure input
  else
    let nextIsFree := isFree.set block 1
    let successor := block + 1
    let nextPrevFree := if successor < prevFree.length then
      prevFree.set successor 1 else prevFree
    .success ⟨nextIsFree, nextPrevFree⟩

theorem markFreeArraysOutcome_failure_eq_input
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {block returnedOffset returnedBytes : Nat} {failed : MarkFreeMachineState}
    (hfailure : markFreeArraysOutcome offsets sizes isFree prevFree block
      returnedOffset returnedBytes = .failure failed) :
    failed = ⟨isFree, prevFree⟩ := by
  unfold markFreeArraysOutcome at hfailure
  split at hfailure <;> simp_all

theorem markFreeArraysOutcome_failure_preserves_frame
    {PROP : Type} [Iris.BI PROP]
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {block returnedOffset returnedBytes : Nat} {failed : MarkFreeMachineState}
    (frame : PROP)
    (hfailure : markFreeArraysOutcome offsets sizes isFree prevFree block
      returnedOffset returnedBytes = .failure failed) :
    failed = ⟨isFree, prevFree⟩ ∧ (frame ∗ (emp : PROP) ⊣⊢ frame) := by
  exact ⟨markFreeArraysOutcome_failure_eq_input hfailure, sep_emp⟩

theorem markFreeArrays_ne_none_of_preflight
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {block returnedOffset returnedBytes : Nat}
    (hoffsets : block < offsets.length) (hsizes : block < sizes.length)
    (hisFree : block < isFree.length) (hprevFree : block < prevFree.length)
    (hallocated : isFree[block]? = some 0)
    (hoffset : offsets[block]? = some returnedOffset)
    (hbytes : sizes[block]? = some returnedBytes) :
    markFreeArrays offsets sizes isFree prevFree block returnedOffset
      returnedBytes ≠ none := by
  simp [markFreeArrays, Nat.not_le.mpr hoffsets, Nat.not_le.mpr hsizes,
    Nat.not_le.mpr hisFree, Nat.not_le.mpr hprevFree, hallocated, hoffset,
    hbytes]

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

theorem representsPhysicalArrays_get_size
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {blocks : List Block} {block : Block}
    (hrep : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some block) : sizes[i]? = some block.bytes := by
  have hi : i < count := by
    rw [hrep.1]
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hsizes := congrArg (fun values : List Nat => values[i]?)
    hrep.2.2.2.2.2.2.1
  rw [List.getElem?_take_of_lt hi] at hsizes
  simpa [blockSizes, hget] using hsizes

theorem representsPhysicalArrays_get_offset
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {blocks : List Block} {block : Block}
    (hrep : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some block) : offsets[i]? = some block.offset := by
  have hi : i < count := by
    rw [hrep.1]
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hoffsets := congrArg (fun values : List Nat => values[i]?)
    hrep.2.2.2.2.2.1
  rw [List.getElem?_take_of_lt hi] at hoffsets
  simpa [blockOffsets, hget] using hoffsets

theorem representsPhysicalArrays_get_free
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {blocks : List Block} {block : Block}
    (hrep : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some block) :
    isFree[i]? = some (if block.free then 1 else 0) := by
  have hi : i < count := by
    rw [hrep.1]
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hfree := congrArg (fun values : List (Fin 256) => values[i]?)
    hrep.2.2.2.2.2.2.2.1
  rw [List.getElem?_take_of_lt hi] at hfree
  simpa [freeFlags, hget] using hfree

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

theorem compactActive_prefix_append_pair {α : Type} [Inhabited α]
    (pre : List α) (left right : α) (rest spare : List α) :
    (compactActive ((pre ++ left :: right :: rest) ++ spare)
      (pre ++ left :: right :: rest).length (pre.length + 1)).take
        ((pre ++ left :: right :: rest).length - 1) =
      pre ++ left :: rest := by
  let active := pre ++ left :: right :: rest
  have htake : (active ++ spare).take (pre.length + 1) = pre ++ [left] := by
    rw [show active ++ spare = pre ++ left :: right :: (rest ++ spare) by
      simp [active]]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have hdrop : (active ++ spare).drop (pre.length + 1 + 1) = rest ++ spare := by
    rw [show active ++ spare = pre ++ left :: right :: (rest ++ spare) by
      simp [active]]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
    have htwo : pre.length + 1 + 1 - pre.length = 2 := by omega
    rw [htwo]
    rfl
  have hremaining : active.length - (pre.length + 1) - 1 = rest.length := by
    simp [active]
    omega
  rw [compactActive, htake, hdrop, hremaining]
  have hrestTake : (rest ++ spare).take rest.length = rest := by
    simp [List.take_append]
  rw [hrestTake]
  simp only [List.append_assoc]
  rw [List.take_append, List.take_of_length_le (by simp)]
  simp [active]

theorem compactActive_prefix_append_pair_length {α : Type} [Inhabited α]
    (pre : List α) (left right : α) (rest spare : List α) :
    (compactActive ((pre ++ left :: right :: rest) ++ spare)
      (pre ++ left :: right :: rest).length (pre.length + 1)).length =
      ((pre ++ left :: right :: rest) ++ spare).length := by
  simp [compactActive]
  omega

theorem compactActive_of_represented_prefix {α : Type} [Inhabited α]
    {values : List α} (pre : List α) (left right : α)
    (rest : List α) {count : Nat}
    (hcount : count = (pre ++ left :: right :: rest).length)
    (hprefix : values.take count = pre ++ left :: right :: rest) :
    (compactActive values count (pre.length + 1)).take (count - 1) =
      pre ++ left :: rest := by
  have hdecompose : values =
      (pre ++ left :: right :: rest) ++ values.drop count := by
    calc
      values = values.take count ++ values.drop count :=
        (List.take_append_drop count values).symm
      _ = (pre ++ left :: right :: rest) ++ values.drop count := by
        rw [hprefix]
  subst count
  rw [hdecompose]
  exact compactActive_prefix_append_pair pre left right rest _

theorem compactActive_of_represented_prefix_length {α : Type} [Inhabited α]
    {values : List α} (pre : List α) (left right : α)
    (rest : List α) {count : Nat}
    (hcount : count = (pre ++ left :: right :: rest).length)
    (hprefix : values.take count = pre ++ left :: right :: rest) :
    (compactActive values count (pre.length + 1)).length = values.length := by
  have hdecompose : values =
      (pre ++ left :: right :: rest) ++ values.drop count := by
    calc
      values = values.take count ++ values.drop count :=
        (List.take_append_drop count values).symm
      _ = (pre ++ left :: right :: rest) ++ values.drop count := by
        rw [hprefix]
  subst count
  rw [hdecompose]
  exact compactActive_prefix_append_pair_length pre left right rest _

theorem set_represented_prefix {α : Type}
    {values : List α} (pre : List α) (left right updated : α)
    (rest : List α) {count : Nat}
    (hcount : count = (pre ++ left :: right :: rest).length)
    (hprefix : values.take count = pre ++ left :: right :: rest) :
    (values.set pre.length updated).take count =
      pre ++ updated :: right :: rest := by
  have hdecompose : values =
      (pre ++ left :: right :: rest) ++ values.drop count := by
    calc
      values = values.take count ++ values.drop count :=
        (List.take_append_drop count values).symm
      _ = (pre ++ left :: right :: rest) ++ values.drop count := by
        rw [hprefix]
  subst count
  rw [hdecompose]
  simp [List.set_append]
  rw [List.take_append, List.take_of_length_le (by omega)]
  simp

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

/-- Insert one active value into a fixed-capacity array, shifting the active
suffix right and leaving the array length unchanged. -/
def expandActive {α : Type} [Inhabited α] (values : List α)
    (count inserted : Nat) (value : α) : List α :=
  values.take inserted ++ value ::
    (values.drop inserted).take (count - inserted) ++ values.drop (count + 1)

theorem expandActive_length {α : Type} [Inhabited α]
    (values : List α) (count inserted : Nat) (value : α)
    (hinserted : inserted ≤ count) (hcapacity : count < values.length) :
    (expandActive values count inserted value).length = values.length := by
  simp only [expandActive, List.length_append, List.length_cons,
    List.length_take, List.length_drop]
  omega

theorem expandActive_of_represented_prefix {α : Type} [Inhabited α]
    {values : List α} (pre : List α) (current value : α) (rest : List α)
    {count : Nat} (hcount : count = (pre ++ current :: rest).length)
    (hcapacity : count < values.length)
    (hprefix : values.take count = pre ++ current :: rest) :
    (expandActive values count (pre.length + 1) value).take (count + 1) =
      pre ++ current :: value :: rest := by
  have hdecompose : values =
      (pre ++ current :: rest) ++ values.drop count := by
    calc
      values = values.take count ++ values.drop count :=
        (List.take_append_drop count values).symm
      _ = (pre ++ current :: rest) ++ values.drop count := by rw [hprefix]
  have hspare : values.drop count ≠ [] := by
    intro hnil
    have := List.drop_eq_nil_iff.mp hnil
    omega
  obtain ⟨spare, spareRest, hspareEq⟩ := List.exists_cons_of_ne_nil hspare
  subst count
  rw [hdecompose, hspareEq]
  have htake :
      ((pre ++ current :: rest) ++ spare :: spareRest).take (pre.length + 1) =
        pre ++ [current] := by
    rw [show (pre ++ current :: rest) ++ spare :: spareRest =
      pre ++ current :: (rest ++ spare :: spareRest) by simp]
    rw [List.take_append]
    have hpre : pre.take (pre.length + 1) = pre :=
      List.take_of_length_le (by omega)
    rw [hpre]
    simp
  have hdrop :
      ((pre ++ current :: rest) ++ spare :: spareRest).drop (pre.length + 1) =
        rest ++ spare :: spareRest := by
    rw [show (pre ++ current :: rest) ++ spare :: spareRest =
      pre ++ current :: (rest ++ spare :: spareRest) by simp]
    simp [List.drop_append]
  have hend :
      ((pre ++ current :: rest) ++ spare :: spareRest).drop
          ((pre ++ current :: rest).length + 1) = spareRest := by
    rw [show (pre ++ current :: rest) ++ spare :: spareRest =
      ((pre ++ current :: rest) ++ [spare]) ++ spareRest by simp]
    rw [show (pre ++ current :: rest).length + 1 =
      ((pre ++ current :: rest) ++ [spare]).length by simp; omega]
    exact List.drop_append_length
  rw [expandActive, htake, hdrop, hend]
  have hremaining : (pre ++ current :: rest).length - (pre.length + 1) =
      rest.length := by simp; omega
  rw [hremaining]
  have hrestTake : (rest ++ spare :: spareRest).take rest.length = rest := by
    simp [List.take_append]
  rw [hrestTake]
  rw [show (pre ++ [current]) ++ value :: rest ++ spareRest =
    (pre ++ current :: value :: rest) ++ spareRest by simp]
  have hnewLength : (pre ++ current :: rest).length + 1 =
      (pre ++ current :: value :: rest).length := by simp; omega
  rw [hnewLength, List.take_append,
    List.take_of_length_le (Nat.le_refl _)]
  simp

theorem set_represented_prefix_single {α : Type}
    {values : List α} (pre : List α) (current updated : α) (rest : List α)
    {count : Nat} (hcount : count = (pre ++ current :: rest).length)
    (hprefix : values.take count = pre ++ current :: rest) :
    (values.set pre.length updated).take count =
      pre ++ updated :: rest := by
  have hdecompose : values =
      (pre ++ current :: rest) ++ values.drop count := by
    calc
      values = values.take count ++ values.drop count :=
        (List.take_append_drop count values).symm
      _ = (pre ++ current :: rest) ++ values.drop count := by rw [hprefix]
  subst count
  rw [hdecompose]
  rw [List.set_append]
  simp [List.take_append, List.take_of_length_le]

theorem exists_append_of_getElem?
    {α : Type} {values : List α} {i : Nat} {current : α}
    (hget : values[i]? = some current) :
    ∃ pre rest, values = pre ++ current :: rest ∧ pre.length = i := by
  induction values generalizing i with
  | nil => simp at hget
  | cons head tail ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst head
          exact ⟨[], tail, by simp⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          obtain ⟨pre, rest, htail, hlen⟩ := ih hget
          exact ⟨head :: pre, rest, by simp [htail], by simp [hlen]⟩

theorem boundaryTagsFrom_get_successor {blocks : List Block} {i : Nat}
    {previousFree : Bool}
    {left right : Block} (htags : boundaryTagsFrom previousFree blocks)
    (hleft : blocks[i]? = some left) (hright : blocks[i + 1]? = some right) :
    right.prevFree = left.free := by
  induction blocks generalizing i previousFree with
  | nil => simp at hleft
  | cons head tail ih =>
      simp only [boundaryTagsFrom] at htags
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
          subst head
          cases tail with
          | nil => simp at hright
          | cons next rest =>
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                Option.some.injEq] at hright
              subst next
              exact htags.2.1
      | succ j =>
          simp only [List.getElem?_cons_succ] at hleft
          have hright' : tail[j + 1]? = some right := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hright
          exact ih htags.2 hleft hright'

theorem boundaryTags_get_successor {blocks : List Block} {i : Nat}
    {left right : Block} (htags : boundaryTags blocks)
    (hleft : blocks[i]? = some left) (hright : blocks[i + 1]? = some right) :
    right.prevFree = left.free :=
  boundaryTagsFrom_get_successor htags hleft hright

theorem splitAt_append (pre : List Block) (selected : Block)
    (rest : List Block) (request : Nat) :
    splitAt (pre ++ selected :: rest) pre.length request =
      pre ++ (splitBlock selected request).1 ::
        (splitBlock selected request).2 :: rest := by
  induction pre with
  | nil => rfl
  | cons head tail ih => simp [splitAt, ih]

theorem markAllocatedAt_append (pre : List Block) (selected : Block)
    (rest : List Block) :
    markAllocatedAt (pre ++ selected :: rest) pre.length =
      pre ++ markAllocated selected ::
        match rest with
        | [] => []
        | next :: tail => { next with prevFree := false } :: tail := by
  induction pre with
  | nil => cases rest <;> rfl
  | cons head tail ih => simp [markAllocatedAt, ih]

structure AllocatePhysicalResult where
  offsets : List Nat
  sizes : List Nat
  isFree : List (Fin 256)
  prevFree : List (Fin 256)
  count : Nat
  allocatedOffset : Nat
  allocatedBytes : Nat
  remainderOffset : Option Nat
  remainderBytes : Option Nat
deriving DecidableEq, Repr

def allocateSplitPrevFree (prevFree : List (Fin 256))
    (count block : Nat) : List (Fin 256) :=
  let successor := block + 1
  let prevFree := expandActive prevFree count successor 0
  if successor + 1 < count + 1 then prevFree.set (successor + 1) 1
  else prevFree

def allocateWholePrevFree (prevFree : List (Fin 256))
    (count block : Nat) : List (Fin 256) :=
  if block + 1 < count then prevFree.set (block + 1) 0 else prevFree

theorem allocateSplitPrevFree_length (prevFree : List (Fin 256))
    (count block : Nat) (hblock : block < count)
    (hcapacity : count < prevFree.length) :
    (allocateSplitPrevFree prevFree count block).length = prevFree.length := by
  unfold allocateSplitPrevFree
  dsimp only
  have hlength := expandActive_length prevFree count (block + 1) 0
    (by omega) hcapacity
  split <;> simp [hlength]

theorem allocateWholePrevFree_length (prevFree : List (Fin 256))
    (count block : Nat) :
    (allocateWholePrevFree prevFree count block).length = prevFree.length := by
  unfold allocateWholePrevFree
  split <;> simp

theorem allocateSplitPrevFree_prefix
    {prevFree : List (Fin 256)} (pre : List (Fin 256))
    (selected : Fin 256) (rest : List (Fin 256)) {count : Nat}
    (hcount : count = (pre ++ selected :: rest).length)
    (hcapacity : count < prevFree.length)
    (hprefix : prevFree.take count = pre ++ selected :: rest)
    (hrest : ∀ head tail, rest = head :: tail → head = 1) :
    (allocateSplitPrevFree prevFree count pre.length).take (count + 1) =
      pre ++ selected :: 0 :: rest := by
  have hexpand := expandActive_of_represented_prefix pre selected (0 : Fin 256)
    rest hcount hcapacity hprefix
  cases rest with
  | nil =>
      simp [allocateSplitPrevFree, hcount] at hexpand ⊢
      exact hexpand
  | cons head tail =>
      have hhead : head = 1 := hrest head tail rfl
      subst head
      have hset := set_represented_prefix_single
        (pre ++ [selected, (0 : Fin 256)]) (1 : Fin 256) 1 tail
        (count := count + 1) (by simp [hcount]; omega)
        (by simpa using hexpand)
      simpa [allocateSplitPrevFree, hcount] using hset

theorem allocateWholePrevFree_prefix
    {prevFree : List (Fin 256)} (pre : List (Fin 256))
    (selected : Fin 256) (rest : List (Fin 256)) {count : Nat}
    (hcount : count = (pre ++ selected :: rest).length)
    (hprefix : prevFree.take count = pre ++ selected :: rest) :
    (allocateWholePrevFree prevFree count pre.length).take count =
      pre ++ selected :: match rest with
        | [] => []
        | _ :: tail => 0 :: tail := by
  cases rest with
  | nil => simpa [allocateWholePrevFree, hcount] using hprefix
  | cons head tail =>
      have hset := set_represented_prefix_single (pre ++ [selected]) head
        (0 : Fin 256) tail (by simpa using hcount) (by simpa using hprefix)
      simpa [allocateWholePrevFree, hcount] using hset

/-- Exact physical-header mutation for an already selected free block. The
caller has detached the block from its bin and preflighted remainder links. -/
def allocatePhysicalArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count block request : Nat) :
    Option AllocatePhysicalResult := do
  if request % alignment ≠ 0 ∨ count = 0 ∨
      count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length ∨ block ≥ count then none
  let selectedOffset ← offsets[block]?
  let selectedSize ← sizes[block]?
  if isFree[block]? = some 0 ∨ selectedSize < request ∨ request = 0 then none
  let remainderSize := selectedSize - request
  if remainderSize ≥ minimumBlockBytes then
    if count ≥ offsets.length ∨ count ≥ sizes.length ∨
        count ≥ isFree.length ∨ count ≥ prevFree.length then none
    let successor := block + 1
    let remainderOffset := selectedOffset + request
    let offsets := expandActive offsets count successor remainderOffset
    let sizes := expandActive (sizes.set block request) count successor remainderSize
    let isFree := expandActive (isFree.set block 0) count successor 1
    let prevFree := allocateSplitPrevFree prevFree count block
    some ⟨offsets, sizes, isFree, prevFree, count + 1,
      selectedOffset, request, some remainderOffset, some remainderSize⟩
  else
    let isFree := isFree.set block 0
    let prevFree := allocateWholePrevFree prevFree count block
    some ⟨offsets, sizes, isFree, prevFree, count,
      selectedOffset, selectedSize, none, none⟩

theorem allocatePhysicalArrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count block request : Nat} {result : AllocatePhysicalResult}
    (hsuccess : allocatePhysicalArrays offsets sizes isFree prevFree count
      block request = some result) :
    alignment ∣ request ∧ count ≤ offsets.length ∧
      count ≤ sizes.length ∧ count ≤ isFree.length ∧
      count ≤ prevFree.length ∧ block < count ∧ 0 < request ∧
      ∃ selectedOffset selectedSize,
        offsets[block]? = some selectedOffset ∧
        sizes[block]? = some selectedSize ∧ isFree[block]? ≠ some 0 ∧
        request ≤ selectedSize ∧ result.allocatedOffset = selectedOffset ∧
        ((minimumBlockBytes ≤ selectedSize - request ∧
            count < offsets.length ∧ count < sizes.length ∧
            count < isFree.length ∧ count < prevFree.length ∧
            result.count = count + 1 ∧ result.allocatedBytes = request ∧
            result.remainderOffset = some (selectedOffset + request) ∧
            result.remainderBytes = some (selectedSize - request) ∧
            result.offsets = expandActive offsets count (block + 1)
              (selectedOffset + request) ∧
            result.sizes = expandActive (sizes.set block request) count
              (block + 1) (selectedSize - request) ∧
            result.isFree = expandActive (isFree.set block 0) count
              (block + 1) 1 ∧
            result.prevFree = allocateSplitPrevFree prevFree count block) ∨
          (selectedSize - request < minimumBlockBytes ∧ result.count = count ∧
            result.allocatedBytes = selectedSize ∧
            result.remainderOffset = none ∧ result.remainderBytes = none ∧
            result.offsets = offsets ∧ result.sizes = sizes ∧
            result.isFree = isFree.set block 0 ∧
            result.prevFree = allocateWholePrevFree prevFree count block)) := by
  let bad := request % alignment ≠ 0 ∨ count = 0 ∨
    count > offsets.length ∨ count > sizes.length ∨
    count > isFree.length ∨ count > prevFree.length ∨ block ≥ count
  by_cases hbad : bad
  · simp [allocatePhysicalArrays, bad, hbad] at hsuccess
  have haligned : alignment ∣ request := by
    simp only [bad] at hbad
    apply Nat.dvd_of_mod_eq_zero
    apply Classical.byContradiction
    intro hmod
    exact hbad (Or.inl hmod)
  have hb : count ≤ offsets.length ∧ count ≤ sizes.length ∧
      count ≤ isFree.length ∧ count ≤ prevFree.length ∧ block < count := by
    simp only [bad] at hbad
    omega
  cases hoffset : offsets[block]? with
  | none => simp [allocatePhysicalArrays, bad, hbad, hoffset] at hsuccess
  | some selectedOffset =>
    cases hsize : sizes[block]? with
    | none =>
        simp [allocatePhysicalArrays, bad, hbad, hoffset, hsize] at hsuccess
    | some selectedSize =>
      have hsuitable : isFree[block]? ≠ some 0 ∧ request ≤ selectedSize ∧
          0 < request := by
        have haccept : ¬(isFree[block]? = some 0 ∨
            selectedSize < request ∨ request = 0) := by
          intro hreject
          simp [allocatePhysicalArrays, bad, hbad, hoffset, hsize,
            hreject] at hsuccess
        refine ⟨?_, Nat.le_of_not_gt ?_, Nat.pos_of_ne_zero ?_⟩
        · exact fun hzero => haccept (Or.inl hzero)
        · exact fun hsmall => haccept (Or.inr (Or.inl hsmall))
        · exact fun hzero => haccept (Or.inr (Or.inr hzero))
      by_cases hsplit : minimumBlockBytes ≤ selectedSize - request
      · have hcapacity : count < offsets.length ∧ count < sizes.length ∧
            count < isFree.length ∧ count < prevFree.length := by
          have haccept : ¬(count ≥ offsets.length ∨ count ≥ sizes.length ∨
              count ≥ isFree.length ∨ count ≥ prevFree.length) := by
            intro hreject
            simp [allocatePhysicalArrays, bad, hbad, hoffset, hsize,
              hsuitable, hsplit, hreject] at hsuccess
          omega
        simp [allocatePhysicalArrays, bad, hbad, hoffset, hsize, hsuitable,
          hsplit, hcapacity, Option.pure_def, Option.bind_eq_bind] at hsuccess
        rcases hsuccess with ⟨_, hresult⟩
        subst result
        exact ⟨haligned, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2,
          hsuitable.2.2, selectedOffset, selectedSize, rfl, rfl,
          hsuitable.1, hsuitable.2.1, rfl,
          Or.inl ⟨hsplit, hcapacity.1, hcapacity.2.1, hcapacity.2.2.1,
            hcapacity.2.2.2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      · have hwhole : selectedSize - request < minimumBlockBytes := by omega
        simp [allocatePhysicalArrays, bad, hbad, hoffset, hsize, hsuitable,
          hsplit, Option.pure_def, Option.bind_eq_bind] at hsuccess
        rcases hsuccess with ⟨_, hresult⟩
        subst result
        exact ⟨haligned, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2,
          hsuitable.2.2, selectedOffset, selectedSize, rfl, rfl,
          hsuitable.1, hsuitable.2.1, rfl,
          Or.inr ⟨hwhole, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The public allocator's preflight facts make the physical mutation
infallible. This is the first post-removal call, so this theorem is required
for transactional failure rather than merely for successful refinement. -/
theorem allocatePhysicalArrays_ne_none_of_preflight
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count block request selectedOffset selectedSize : Nat}
    (haligned : request % alignment = 0) (hcount : 0 < count)
    (hoffsets : count ≤ offsets.length) (hsizes : count ≤ sizes.length)
    (hfreeLength : count ≤ isFree.length)
    (hprevLength : count ≤ prevFree.length) (hblock : block < count)
    (hoffset : offsets[block]? = some selectedOffset)
    (hsize : sizes[block]? = some selectedSize)
    (hfree : isFree[block]? ≠ some 0) (hrequest : 0 < request)
    (hsuitable : request ≤ selectedSize)
    (hcapacity : minimumBlockBytes ≤ selectedSize - request →
      count < offsets.length ∧ count < sizes.length ∧
        count < isFree.length ∧ count < prevFree.length) :
    allocatePhysicalArrays offsets sizes isFree prevFree count block request ≠
      none := by
  intro hnone
  have hguard : ¬(request % alignment ≠ 0 ∨ count = 0 ∨
      count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length ∨ block ≥ count) := by
    omega
  have haccept : ¬(isFree[block]? = some 0 ∨ selectedSize < request ∨
      request = 0) := by
    intro hreject
    rcases hreject with hzero | hsmall | hzero
    · exact hfree hzero
    · omega
    · omega
  by_cases hsplit : minimumBlockBytes ≤ selectedSize - request
  · have hcap := hcapacity hsplit
    simp [allocatePhysicalArrays, hguard, hoffset, hsize, haccept, hsplit,
      hcap] at hnone
  · simp [allocatePhysicalArrays, hguard, hoffset, hsize, haccept, hsplit]
      at hnone

set_option maxHeartbeats 600000 in
theorem allocatePhysicalArrays_refines
    {blocks : List Block} {block request : Nat} {selected : Block}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {result : AllocatePhysicalResult}
    (hrep : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[block]? = some selected)
    (htags : boundaryTags blocks)
    (hsuccess : allocatePhysicalArrays offsets sizes isFree prevFree count
      block request = some result) :
    ∃ allocated next,
      allocateChosenAt blocks block request = some (allocated, next) ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
        result.prevFree result.count next ∧
      result.allocatedOffset = allocated.offset ∧
      result.allocatedBytes = allocated.bytes := by
  obtain ⟨haligned, _, _, _, _, _, hrequest, selectedOffset, selectedSize,
      hoffset, hsize, hfreeFlag, hfits, hresultOffset,
      hcase⟩ := allocatePhysicalArrays_result hsuccess
  have hoffsetExpected := representsPhysicalArrays_get_offset hrep hget
  rw [hoffset] at hoffsetExpected
  simp only [Option.some.injEq] at hoffsetExpected
  have hoffsetEq : selectedOffset = selected.offset := hoffsetExpected
  have hsizeExpected := representsPhysicalArrays_get_size hrep hget
  rw [hsize] at hsizeExpected
  simp only [Option.some.injEq] at hsizeExpected
  have hsizeEq : selectedSize = selected.bytes := hsizeExpected
  rw [hoffsetEq] at hresultOffset hcase
  rw [hsizeEq] at hfits hcase
  have hfreeExpected := representsPhysicalArrays_get_free hrep hget
  have hselectedFree : selected.free = true := by
    cases hselected : selected.free with
    | false =>
        simp [hselected] at hfreeExpected
        exact False.elim (hfreeFlag hfreeExpected)
    | true => rfl
  obtain ⟨pre, rest, hblocks, hpreLength⟩ := exists_append_of_getElem? hget
  have hcount : count = (pre ++ selected :: rest).length := by
    rw [hrep.1, hblocks]
  have hoffsetsPrefix : offsets.take count =
      blockOffsets pre ++ selected.offset :: blockOffsets rest := by
    simpa [blockOffsets, hblocks] using hrep.2.2.2.2.2.1
  have hsizesPrefix : sizes.take count =
      blockSizes pre ++ selected.bytes :: blockSizes rest := by
    simpa [blockSizes, hblocks] using hrep.2.2.2.2.2.2.1
  have hfreePrefix : isFree.take count =
      freeFlags pre ++ 1 :: freeFlags rest := by
    simpa [freeFlags, hblocks, hselectedFree] using hrep.2.2.2.2.2.2.2.1
  have hprevPrefix : prevFree.take count =
      prevFreeFlags pre ++ (if selected.prevFree then 1 else 0) ::
        prevFreeFlags rest := by
    simpa [prevFreeFlags, hblocks] using hrep.2.2.2.2.2.2.2.2
  rcases hcase with hsplit | hwhole
  · rcases hsplit with ⟨hsplit, hcapOffsets, hcapSizes, hcapFree,
      hcapPrev, hresultCount, hresultBytes, hresultRemainderOffset,
      hresultRemainderBytes, hresultOffsets, hresultSizes,
      hresultFree, hresultPrev⟩
    have hcan : canSplit selected request := by
      refine ⟨hrequest, ?_⟩
      simp only [minimumBlockBytes, alignment] at hsplit ⊢
      exact (Nat.le_sub_iff_add_le' hfits).mp hsplit
    have habstract : allocateChosenAt blocks block request =
        some ((splitBlock selected request).1, splitAt blocks block request) := by
      simp [allocateChosenAt, hget, hselectedFree, hfits, haligned, hcan]
    have hoffsetsNext := expandActive_of_represented_prefix
      (blockOffsets pre) selected.offset (selected.offset + request)
      (blockOffsets rest) (by simpa [blockOffsets] using hcount)
      hcapOffsets hoffsetsPrefix
    have hsizesSet := set_represented_prefix_single
      (blockSizes pre) selected.bytes request (blockSizes rest)
      (by simpa [blockSizes] using hcount) hsizesPrefix
    have hsizesNext := expandActive_of_represented_prefix
      (blockSizes pre) request (selected.bytes - request) (blockSizes rest)
      (by simpa [blockSizes] using hcount) (by simpa using hcapSizes) hsizesSet
    have hfreeSet := set_represented_prefix_single
      (freeFlags pre) (1 : Fin 256) 0 (freeFlags rest)
      (by simpa [freeFlags] using hcount) hfreePrefix
    have hfreeNext := expandActive_of_represented_prefix
      (freeFlags pre) (0 : Fin 256) 1 (freeFlags rest)
      (by simpa [freeFlags] using hcount) (by simpa using hcapFree) hfreeSet
    have hrestPrev : ∀ head tail,
        prevFreeFlags rest = head :: tail → head = 1 := by
      intro head tail hshape
      cases rest with
      | nil => simp [prevFreeFlags] at hshape
      | cons next more =>
          have hnextGet : blocks[block + 1]? = some next := by
            rw [hblocks, ← hpreLength]
            simp
          have htag := boundaryTags_get_successor htags hget hnextGet
          simp [prevFreeFlags, hselectedFree] at htag hshape
          simpa [← hshape] using htag
    have hprevNext := allocateSplitPrevFree_prefix
      (prevFreeFlags pre) (if selected.prevFree then 1 else 0)
      (prevFreeFlags rest) (by simpa [prevFreeFlags] using hcount)
      hcapPrev hprevPrefix hrestPrev
    have hphysical : RepresentsPhysicalArrays result.offsets result.sizes
        result.isFree result.prevFree result.count
        (splitAt blocks block request) := by
      rw [hresultCount, hresultOffsets, hresultSizes, hresultFree,
        hresultPrev, hblocks, ← hpreLength, splitAt_append]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons]
        simp only [List.length_append, List.length_cons] at hcount
        omega
      · rw [expandActive_length offsets count (pre.length + 1)
          (selected.offset + request) (by omega) hcapOffsets]
        omega
      · rw [expandActive_length (sizes.set pre.length request) count
          (pre.length + 1)
          (selected.bytes - request) (by omega) (by simpa using hcapSizes)]
        simp
        omega
      · rw [expandActive_length (isFree.set pre.length 0) count
          (pre.length + 1) 1
          (by omega) (by simpa using hcapFree)]
        simp
        omega
      · rw [allocateSplitPrevFree_length prevFree count pre.length
          (by omega) hcapPrev]
        omega
      · simpa [blockOffsets, splitBlock, hpreLength] using hoffsetsNext
      · simpa [blockSizes, splitBlock, hpreLength] using hsizesNext
      · simpa [freeFlags, splitBlock, hpreLength] using hfreeNext
      · simpa [prevFreeFlags, splitBlock, hpreLength] using hprevNext
    exact ⟨(splitBlock selected request).1, splitAt blocks block request,
      habstract, hphysical, by simpa [splitBlock] using hresultOffset,
      by simpa [splitBlock] using hresultBytes⟩
  · rcases hwhole with ⟨hwhole, hresultCount, hresultBytes,
      hresultRemainderOffset, hresultRemainderBytes, hresultOffsets,
      hresultSizes, hresultFree, hresultPrev⟩
    have hcannot : ¬canSplit selected request := by
      intro hcan
      have hroom := hcan.2
      simp only [minimumBlockBytes] at hroom hwhole
      have : 16 ≤ selected.bytes - request :=
        (Nat.le_sub_iff_add_le' hfits).2 hroom
      omega
    have habstract : allocateChosenAt blocks block request =
        some (markAllocated selected, markAllocatedAt blocks block) := by
      simp [allocateChosenAt, hget, hselectedFree, hfits, haligned, hcannot]
    have hfreeNext := set_represented_prefix_single
      (freeFlags pre) (1 : Fin 256) 0 (freeFlags rest)
      (by simpa [freeFlags] using hcount) hfreePrefix
    have hprevNext := allocateWholePrevFree_prefix
      (prevFreeFlags pre) (if selected.prevFree then 1 else 0)
      (prevFreeFlags rest) (by simpa [prevFreeFlags] using hcount) hprevPrefix
    have hphysical : RepresentsPhysicalArrays result.offsets result.sizes
        result.isFree result.prevFree result.count
        (markAllocatedAt blocks block) := by
      cases rest with
      | nil =>
          rw [hresultCount, hresultOffsets, hresultSizes, hresultFree,
            hresultPrev, hblocks, ← hpreLength, markAllocatedAt_append]
          refine ⟨by simpa using hcount, hrep.2.1, hrep.2.2.1,
            by simpa using hrep.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
          · rw [allocateWholePrevFree_length]
            exact hrep.2.2.2.2.1
          · simpa [blockOffsets, markAllocated] using hoffsetsPrefix
          · simpa [blockSizes, markAllocated] using hsizesPrefix
          · simpa [freeFlags, markAllocated] using hfreeNext
          · simpa [prevFreeFlags, markAllocated] using hprevNext
      | cons next more =>
          rw [hresultCount, hresultOffsets, hresultSizes, hresultFree,
            hresultPrev, hblocks, ← hpreLength, markAllocatedAt_append]
          refine ⟨by simpa using hcount, hrep.2.1, hrep.2.2.1,
            by simpa using hrep.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
          · rw [allocateWholePrevFree_length]
            exact hrep.2.2.2.2.1
          · simpa [blockOffsets, markAllocated] using hoffsetsPrefix
          · simpa [blockSizes, markAllocated] using hsizesPrefix
          · simpa [freeFlags, markAllocated] using hfreeNext
          · simpa [prevFreeFlags, markAllocated] using hprevNext
    exact ⟨markAllocated selected, markAllocatedAt blocks block,
      habstract, hphysical, by simpa [markAllocated] using hresultOffset,
      by simpa [markAllocated] using hresultBytes⟩

/-- The bounded linear scan used by the concrete allocator to translate a
free-list byte offset back to its physical-header array index. -/
def findOffsetIndex : List Nat → Nat → Nat → Option Nat
  | _, 0, _ => none
  | [], _ + 1, _ => none
  | offset :: rest, count + 1, target =>
      if offset = target then some 0
      else (findOffsetIndex rest count target).map Nat.succ

theorem findOffsetIndex_sound {offsets : List Nat} {count target i : Nat}
    (hfind : findOffsetIndex offsets count target = some i) :
    i < count ∧ offsets[i]? = some target := by
  induction offsets generalizing count i with
  | nil =>
      cases count <;> simp [findOffsetIndex] at hfind
  | cons offset rest ih =>
      cases count with
      | zero => simp [findOffsetIndex] at hfind
      | succ count =>
          by_cases heq : offset = target
          · simp [findOffsetIndex, heq] at hfind
            subst i
            exact ⟨by omega, by simp [heq]⟩
          · simp only [findOffsetIndex, heq, if_false] at hfind
            rw [Option.map_eq_some_iff] at hfind
            obtain ⟨j, hrest, rfl⟩ := hfind
            have hj := ih hrest
            exact ⟨by omega, by simpa using hj.2⟩

theorem findOffsetIndex_take (offsets : List Nat) (count target : Nat) :
    findOffsetIndex offsets count target =
      findOffsetIndex (offsets.take count) count target := by
  induction offsets generalizing count with
  | nil => cases count <;> rfl
  | cons offset rest ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [findOffsetIndex, List.take_succ_cons]
          split
          · rfl
          · rw [ih]

theorem findOffsetIndex_blockOffsets_eq_findPhysicalIndex
    (blocks : List Block) (target : Block)
    (hoffset : ∀ b ∈ blocks,
      b.offset = target.offset ↔ SamePhysical b target) :
    findOffsetIndex (blockOffsets blocks) blocks.length target.offset =
      findPhysicalIndex blocks target := by
  induction blocks with
  | nil => simp [findOffsetIndex, blockOffsets, findPhysicalIndex]
  | cons head rest ih =>
      have hhead := hoffset head (by simp)
      have htail : ∀ b ∈ rest,
          b.offset = target.offset ↔ SamePhysical b target := by
        intro b hb
        exact hoffset b (by simp [hb])
      simp only [blockOffsets, List.map_cons, List.length_cons,
        findOffsetIndex, findPhysicalIndex]
      by_cases h : head.offset = target.offset
      · simp [h, hhead.mp h]
      · have hsame : ¬SamePhysical head target :=
          fun hsame => h (hhead.mpr hsame)
        rw [if_neg h, if_neg hsame]
        exact congrArg (Option.map Nat.succ) (ih htail)

theorem findOffsetIndex_refines_findPhysicalIndex
    {pool : Luffs.Memory.Region} {blocks : List Block} {target actual : Block}
    (hwell : wellFormed pool blocks) (hactual : actual ∈ blocks)
    (hsame : SamePhysical actual target) :
    findOffsetIndex (blockOffsets blocks) blocks.length target.offset =
      findPhysicalIndex blocks target := by
  apply findOffsetIndex_blockOffsets_eq_findPhysicalIndex
  intro b hb
  constructor
  · intro hoffset
    have hsameBlock : b = actual := wellFormed_same_offset hwell hb hactual
      (hoffset.trans hsame.1.symm)
    subst b
    exact hsame
  · exact fun h => h.1

theorem findOffsetIndex_refines_findPhysicalIndex_represented
    {pool : Luffs.Memory.Region} {blocks : List Block} {target actual : Block}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    (hrep : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hwell : wellFormed pool blocks) (hactual : actual ∈ blocks)
    (hsame : SamePhysical actual target) :
    findOffsetIndex offsets count target.offset = findPhysicalIndex blocks target := by
  rw [findOffsetIndex_take, hrep.2.2.2.2.2.1, hrep.1]
  exact findOffsetIndex_refines_findPhysicalIndex hwell hactual hsame

structure AllocateArraysResult where
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
  allocatedOffset : Nat
  allocatedBytes : Nat
deriving DecidableEq, Repr

/-- The concrete metadata visible at an allocation call boundary. Unlike the
`Option` reference transformer below, this state is retained on failure so a
transactionality theorem can distinguish preflight rejection from a failure
after free-list or physical metadata has already been mutated. -/
structure AllocateMachineState where
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

inductive AllocateOutcome where
  | failure (state : AllocateMachineState)
  | success (result : AllocateArraysResult)
deriving DecidableEq, Repr

def allocateInputState (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) : AllocateMachineState :=
  ⟨offsets, sizes, isFree, prevFree, count, second, first, heads, next,
    previous⟩

def allocateStateAfterRemove (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (removed : ClassCandidateResult) : AllocateMachineState :=
  ⟨offsets, sizes, isFree, prevFree, count, removed.second, removed.first,
    removed.heads, removed.next, removed.previous⟩

def allocateStateAfterPhysical (physical : AllocatePhysicalResult)
    (removed : ClassCandidateResult) : AllocateMachineState :=
  ⟨physical.offsets, physical.sizes, physical.isFree, physical.prevFree,
    physical.count, removed.second, removed.first, removed.heads, removed.next,
    removed.previous⟩

/-- The mutation phase after public allocation has completed all preflight
checks. Keeping this phase separate makes its three possible call failures
explicit and permits a compositional transactionality proof. -/
def commitAllocateOutcome (input : AllocateMachineState)
    (offsets sizes : List Nat) (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (startBin block request : Nat)
    (split : Prop) [Decidable split] (remainderBin remainderOffset : Nat) :
    AllocateOutcome :=
  match takeCandidateClassArrays second first heads next previous
      (startBin / secondLevelCount) (startBin % secondLevelCount) with
  | none => .failure input
  | some removed =>
    match allocatePhysicalArrays offsets sizes isFree prevFree count block
        request with
    | none => .failure (allocateStateAfterRemove offsets sizes isFree prevFree
        count removed)
    | some physical =>
      if split then
        match insertClassArrays removed.second removed.first removed.heads
            removed.next removed.previous remainderBin remainderOffset with
        | none => .failure (allocateStateAfterPhysical physical removed)
        | some inserted => .success
            ⟨physical.offsets, physical.sizes, physical.isFree,
              physical.prevFree, physical.count, inserted.second,
              inserted.first, inserted.heads, inserted.next,
              inserted.previous, physical.allocatedOffset,
              physical.allocatedBytes⟩
      else .success
        ⟨physical.offsets, physical.sizes, physical.isFree,
          physical.prevFree, physical.count, removed.second, removed.first,
          removed.heads, removed.next, removed.previous,
          physical.allocatedOffset, physical.allocatedBytes⟩

theorem commitAllocateOutcome_failure_eq_input
    {input : AllocateMachineState}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {startBin block request : Nat}
    {split : Prop} [Decidable split] {remainderBin remainderOffset : Nat}
    {failed : AllocateMachineState}
    (htake : takeCandidateClassArrays second first heads next previous
      (startBin / secondLevelCount) (startBin % secondLevelCount) ≠ none)
    (hphysical : allocatePhysicalArrays offsets sizes isFree prevFree count
      block request ≠ none)
    (hinsert : ∀ removed,
      takeCandidateClassArrays second first heads next previous
          (startBin / secondLevelCount) (startBin % secondLevelCount) =
        some removed → split →
      insertClassArrays removed.second removed.first removed.heads removed.next
        removed.previous remainderBin remainderOffset ≠ none)
    (hfailure : commitAllocateOutcome input offsets sizes isFree prevFree count
      second first heads next previous startBin block request split remainderBin
      remainderOffset = .failure failed) :
    failed = input := by
  unfold commitAllocateOutcome at hfailure
  cases htakeEq : takeCandidateClassArrays second first heads next previous
      (startBin / secondLevelCount) (startBin % secondLevelCount) with
  | none => exact (htake htakeEq).elim
  | some removed =>
    simp only [htakeEq] at hfailure
    cases hphysicalEq : allocatePhysicalArrays offsets sizes isFree prevFree
        count block request with
    | none => exact (hphysical hphysicalEq).elim
    | some physical =>
      simp only [hphysicalEq] at hfailure
      by_cases hsplit : split
      · simp only [hsplit, if_true] at hfailure
        cases hinsertEq : insertClassArrays removed.second removed.first
            removed.heads removed.next removed.previous remainderBin
            remainderOffset with
        | none => exact (hinsert removed htakeEq hsplit hinsertEq).elim
        | some inserted => simp [hinsertEq] at hfailure
      · simp [hsplit] at hfailure

def finishAllocateArrays (removed : ClassCandidateResult)
    (physical : AllocatePhysicalResult) (split : Prop) [Decidable split]
    (remainderBin remainderOffset : Nat) : Option AllocateArraysResult := do
  if split then
    let inserted ← insertClassArrays removed.second removed.first
      removed.heads removed.next removed.previous remainderBin remainderOffset
    some ⟨physical.offsets, physical.sizes, physical.isFree,
      physical.prevFree, physical.count, inserted.second, inserted.first,
      inserted.heads, inserted.next, inserted.previous,
      physical.allocatedOffset, physical.allocatedBytes⟩
  else
    some ⟨physical.offsets, physical.sizes, physical.isFree,
      physical.prevFree, physical.count, removed.second, removed.first,
      removed.heads, removed.next, removed.previous,
      physical.allocatedOffset, physical.allocatedBytes⟩

theorem finishAllocateArrays_physical
    {removed : ClassCandidateResult} {physical : AllocatePhysicalResult}
    {split : Prop} [Decidable split] {remainderBin remainderOffset : Nat}
    {result : AllocateArraysResult}
    (hfinish : finishAllocateArrays removed physical split remainderBin
      remainderOffset = some result) :
    result.offsets = physical.offsets ∧ result.sizes = physical.sizes ∧
      result.isFree = physical.isFree ∧
      result.prevFree = physical.prevFree ∧ result.count = physical.count ∧
      result.allocatedOffset = physical.allocatedOffset ∧
      result.allocatedBytes = physical.allocatedBytes := by
  unfold finishAllocateArrays at hfinish
  by_cases hsplit : split
  · simp only [hsplit, if_true] at hfinish
    cases hinsert : insertClassArrays removed.second removed.first removed.heads
        removed.next removed.previous remainderBin remainderOffset with
    | none => simp [hinsert] at hfinish
    | some inserted =>
      simp [hinsert] at hfinish
      subst result
      simp
  · simp [hsplit] at hfinish
    subst result
    simp

theorem finishAllocateArrays_result
    {removed : ClassCandidateResult} {physical : AllocatePhysicalResult}
    {split : Prop} [Decidable split] {remainderBin remainderOffset : Nat}
    {result : AllocateArraysResult}
    (hfinish : finishAllocateArrays removed physical split remainderBin
      remainderOffset = some result) :
    (split ∧ ∃ inserted,
      insertClassArrays removed.second removed.first removed.heads removed.next
        removed.previous remainderBin remainderOffset = some inserted ∧
      result.second = inserted.second ∧ result.first = inserted.first ∧
      result.heads = inserted.heads ∧ result.next = inserted.next ∧
      result.previous = inserted.previous) ∨
    (¬split ∧ result.second = removed.second ∧
      result.first = removed.first ∧ result.heads = removed.heads ∧
      result.next = removed.next ∧ result.previous = removed.previous) := by
  unfold finishAllocateArrays at hfinish
  by_cases hsplit : split
  · simp only [hsplit, if_true] at hfinish
    cases hinsert : insertClassArrays removed.second removed.first removed.heads
        removed.next removed.previous remainderBin remainderOffset with
    | none => simp [hinsert] at hfinish
    | some inserted =>
      simp [hinsert] at hfinish
      subst result
      exact Or.inl ⟨hsplit, inserted, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [hsplit] at hfinish
    subst result
    exact Or.inr ⟨hsplit, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact pure state transformer for the public `tlsf_allocate` lowering.
Every check before `removeClassArrays` is a preflight check, so `none` leaves
all caller-owned arrays unchanged. -/
def allocateArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (request : Nat) :
    Option AllocateArraysResult := do
  if request = 0 ∨ request % alignment ≠ 0 then none
  let startBin ← classifyRequestBin request
  let foundBin ← findNonemptyClassLowered second first
    (startBin / secondLevelCount) (startBin % secondLevelCount)
  if foundBin ≥ heads.length then none
  let selectedOffset ← heads[foundBin]?
  if selectedOffset ≥ next.length ∨ selectedOffset ≥ previous.length ∨
      count = 0 ∨ count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length then none
  let block ← findOffsetIndex offsets count selectedOffset
  let selectedSize ← sizes[block]?
  if isFree[block]? = some 0 ∨ selectedSize < request then none
  let remainderSize := selectedSize - request
  let split := minimumBlockBytes ≤ remainderSize
  let remainderOffset := selectedOffset + request
  if split ∧ (count ≥ offsets.length ∨ count ≥ sizes.length ∨
      count ≥ isFree.length ∨ count ≥ prevFree.length) then none
  if split ∧ (remainderOffset ≥ 2 ^ 64 ∨ remainderOffset ≥ next.length ∨
      remainderOffset ≥ previous.length) then none
  let remainderBin ← if split then classifySizeBin remainderSize else some 0
  if split ∧ (remainderBin ≥ heads.length ∨
      remainderBin / secondLevelCount ≥ second.length) then none
  let removed ← takeCandidateClassArrays second first heads next previous
    (startBin / secondLevelCount) (startBin % secondLevelCount)
  let physical ← allocatePhysicalArrays offsets sizes isFree prevFree count
    block request
  finishAllocateArrays removed physical split remainderBin remainderOffset

/-- Stateful execution model for the public allocation call. Preflight
failures return the input state. Failures of a call after candidate removal
retain the already-mutated metadata, exactly exposing the obligations needed
to justify the source comment that allocation failure is transactional. -/
def allocateArraysOutcome (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (request : Nat) : AllocateOutcome :=
  let input := allocateInputState offsets sizes isFree prevFree count second
    first heads next previous
  if request = 0 ∨ request % alignment ≠ 0 then .failure input
  else match classifyRequestBin request with
  | none => .failure input
  | some startBin =>
    match findNonemptyClassLowered second first
        (startBin / secondLevelCount) (startBin % secondLevelCount) with
    | none => .failure input
    | some foundBin =>
      if foundBin ≥ heads.length then .failure input
      else match heads[foundBin]? with
      | none => .failure input
      | some selectedOffset =>
        if selectedOffset ≥ next.length ∨ selectedOffset ≥ previous.length ∨
            count = 0 ∨ count > offsets.length ∨ count > sizes.length ∨
            count > isFree.length ∨ count > prevFree.length then .failure input
        else match findOffsetIndex offsets count selectedOffset with
        | none => .failure input
        | some block =>
          match sizes[block]? with
          | none => .failure input
          | some selectedSize =>
            if isFree[block]? = some 0 ∨ selectedSize < request then
              .failure input
            else
              let remainderSize := selectedSize - request
              let split := minimumBlockBytes ≤ remainderSize
              let remainderOffset := selectedOffset + request
              if split ∧ (count ≥ offsets.length ∨ count ≥ sizes.length ∨
                  count ≥ isFree.length ∨ count ≥ prevFree.length) then
                .failure input
              else if split ∧ (remainderOffset ≥ 2 ^ 64 ∨
                  remainderOffset ≥ next.length ∨
                  remainderOffset ≥ previous.length) then .failure input
              else match if split then classifySizeBin remainderSize else some 0 with
              | none => .failure input
              | some remainderBin =>
                if split ∧ (remainderBin ≥ heads.length ∨
                    remainderBin / secondLevelCount ≥ second.length) then
                  .failure input
                else commitAllocateOutcome input offsets sizes isFree prevFree
                  count second first heads next previous startBin block request
                  split remainderBin remainderOffset

set_option maxHeartbeats 1000000 in
/-- Public allocation is transactional: every failure returns the exact input
metadata. This is an operational statement about ordered mutations, not a
consequence of erasing state behind `Option`. -/
theorem allocateArraysOutcome_failure_eq_input
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {request : Nat}
    {failed : AllocateMachineState}
    (hfailure : allocateArraysOutcome offsets sizes isFree prevFree count
      second first heads next previous request = .failure failed) :
    failed = allocateInputState offsets sizes isFree prevFree count second
      first heads next previous := by
  let input := allocateInputState offsets sizes isFree prevFree count second
    first heads next previous
  by_cases hguard : request = 0 ∨ request % alignment ≠ 0
  · simpa [allocateArraysOutcome, input, hguard] using hfailure.symm
  cases hstart : classifyRequestBin request with
  | none =>
      simpa [allocateArraysOutcome, input, hguard, hstart] using hfailure.symm
  | some startBin =>
    cases hfind : findNonemptyClassLowered second first
        (startBin / secondLevelCount) (startBin % secondLevelCount) with
    | none =>
        simpa [allocateArraysOutcome, input, hguard, hstart, hfind] using
          hfailure.symm
    | some foundBin =>
      by_cases hfound : foundBin ≥ heads.length
      · simpa [allocateArraysOutcome, input, hguard, hstart, hfind, hfound] using
          hfailure.symm
      cases hhead : heads[foundBin]? with
      | none =>
          simpa [allocateArraysOutcome, input, hguard, hstart, hfind, hfound,
            hhead] using hfailure.symm
      | some selectedOffset =>
        let bad := selectedOffset ≥ next.length ∨
          selectedOffset ≥ previous.length ∨ count = 0 ∨
          count > offsets.length ∨ count > sizes.length ∨
          count > isFree.length ∨ count > prevFree.length
        by_cases hbad : bad
        · simpa [allocateArraysOutcome, input, hguard, hstart, hfind, hfound,
            hhead, bad, hbad] using hfailure.symm
        cases hblock : findOffsetIndex offsets count selectedOffset with
        | none =>
            simpa [allocateArraysOutcome, input, hguard, hstart, hfind, hfound,
              hhead, bad, hbad, hblock] using hfailure.symm
        | some block =>
          cases hsize : sizes[block]? with
          | none =>
              simpa [allocateArraysOutcome, input, hguard, hstart, hfind,
                hfound, hhead, bad, hbad, hblock, hsize] using hfailure.symm
          | some selectedSize =>
            by_cases hsuitable : isFree[block]? = some 0 ∨
                selectedSize < request
            · simpa [allocateArraysOutcome, input, hguard, hstart, hfind,
                hfound, hhead, bad, hbad, hblock, hsize, hsuitable] using
                  hfailure.symm
            let split := minimumBlockBytes ≤ selectedSize - request
            let remainderOffset := selectedOffset + request
            let capacityBad := split ∧ (count ≥ offsets.length ∨
              count ≥ sizes.length ∨ count ≥ isFree.length ∨
              count ≥ prevFree.length)
            by_cases hcapacityBad : capacityBad
            · simpa [allocateArraysOutcome, input, hguard, hstart, hfind,
                hfound, hhead, bad, hbad, hblock, hsize, hsuitable, split,
                remainderOffset, capacityBad, hcapacityBad] using hfailure.symm
            let overflow := split ∧ (remainderOffset ≥ 2 ^ 64 ∨
              remainderOffset ≥ next.length ∨
              remainderOffset ≥ previous.length)
            by_cases hoverflow : overflow
            · simpa [allocateArraysOutcome, input, hguard, hstart, hfind,
                hfound, hhead, bad, hbad, hblock, hsize, hsuitable, split,
                remainderOffset, capacityBad, hcapacityBad, overflow,
                hoverflow] using hfailure.symm
            cases hrembin : if split then classifySizeBin
                (selectedSize - request) else some 0 with
            | none =>
                simpa [allocateArraysOutcome, input, hguard, hstart, hfind,
                  hfound, hhead, bad, hbad, hblock, hsize, hsuitable, split,
                  remainderOffset, capacityBad, hcapacityBad, overflow,
                  hoverflow, hrembin] using hfailure.symm
            | some remainderBin =>
              let remainderBad := split ∧ (remainderBin ≥ heads.length ∨
                remainderBin / secondLevelCount ≥ second.length)
              by_cases hrembad : remainderBad
              · have hsplit : split := hrembad.1
                have hcapacity : ¬(count ≥ offsets.length ∨
                    count ≥ sizes.length ∨ count ≥ isFree.length ∨
                    count ≥ prevFree.length) := by
                  intro hfull
                  exact hcapacityBad ⟨hsplit, hfull⟩
                have hnoOverflow : ¬(remainderOffset ≥ 2 ^ 64 ∨
                    remainderOffset ≥ next.length ∨
                    remainderOffset ≥ previous.length) := by
                  intro hout
                  exact hoverflow ⟨hsplit, hout⟩
                have hclass : classifySizeBin (selectedSize - request) =
                    some remainderBin := by
                  simpa [hsplit] using hrembin
                have hremBounds := hrembad.2
                simpa [allocateArraysOutcome, input, hguard, hstart, hfind,
                  hfound, hhead, bad, hbad, hblock, hsize, hsuitable, split,
                  remainderOffset, capacityBad, hcapacityBad, overflow,
                  hoverflow, hrembin, remainderBad, hrembad, hsplit,
                  hcapacity, hnoOverflow, hclass, hremBounds] using
                    hfailure.symm
              have hfindSound := findNonemptyClassLowered_sound hfind
              have hfoundFl : foundBin / secondLevelCount < second.length := by
                simp only [secondLevelCount]
                omega
              have hselectedNext : selectedOffset < next.length := by
                simp only [bad] at hbad
                omega
              have hselectedPrevious : selectedOffset < previous.length := by
                simp only [bad] at hbad
                omega
              have htake : takeCandidateClassArrays second first heads next
                  previous (startBin / secondLevelCount)
                    (startBin % secondLevelCount) ≠ none :=
                takeCandidateClassArrays_ne_none_of_preflight hfind
                  (Nat.lt_of_not_ge hfound) hfoundFl (by simp [hhead])
                  hselectedNext hselectedPrevious
              have hscan := findOffsetIndex_sound hblock
              have hphysical : allocatePhysicalArrays offsets sizes isFree
                  prevFree count block request ≠ none := by
                apply allocatePhysicalArrays_ne_none_of_preflight
                · apply Classical.byContradiction
                  intro hmod
                  exact hguard (Or.inr hmod)
                · simp only [bad] at hbad; omega
                · simp only [bad] at hbad; omega
                · simp only [bad] at hbad; omega
                · simp only [bad] at hbad; omega
                · simp only [bad] at hbad; omega
                · exact hscan.1
                · exact hscan.2
                · exact hsize
                · exact fun hzero => hsuitable (Or.inl hzero)
                · exact Nat.pos_of_ne_zero (fun hzero => hguard (Or.inl hzero))
                · exact Nat.le_of_not_gt (fun hsmall => hsuitable (Or.inr hsmall))
                · intro hsplit
                  have hcapacity : ¬(count ≥ offsets.length ∨
                      count ≥ sizes.length ∨ count ≥ isFree.length ∨
                      count ≥ prevFree.length) := by
                    intro hfull
                    apply hcapacityBad
                    exact ⟨by simpa [split] using hsplit, hfull⟩
                  omega
              apply commitAllocateOutcome_failure_eq_input (split := split)
                htake hphysical
              · intro removed htakeEq hsplit
                have hlens :=
                  takeCandidateClassArrays_preserves_metadata_lengths htakeEq
                have hsecondLen :=
                  takeCandidateClassArrays_preserves_second_length htakeEq
                apply insertClassArrays_ne_none_of_preflight
                · have hbound : remainderBin < heads.length := by
                    apply Nat.lt_of_not_ge
                    intro hout
                    apply hrembad
                    exact ⟨hsplit, Or.inl hout⟩
                  rw [hlens.1]
                  exact hbound
                · have hbound :
                      remainderBin / secondLevelCount < second.length := by
                    apply Nat.lt_of_not_ge
                    intro hout
                    apply hrembad
                    exact ⟨hsplit, Or.inr hout⟩
                  rw [hsecondLen]
                  exact hbound
                · have hbound : remainderOffset < next.length := by
                    apply Nat.lt_of_not_ge
                    intro hout
                    apply hoverflow
                    exact ⟨hsplit, Or.inr (Or.inl hout)⟩
                  rw [hlens.2.1]
                  exact hbound
                · have hbound : remainderOffset < previous.length := by
                    apply Nat.lt_of_not_ge
                    intro hout
                    apply hoverflow
                    exact ⟨hsplit, Or.inr (Or.inr hout)⟩
                  rw [hlens.2.2]
                  exact hbound
              · simpa [allocateArraysOutcome, input, hguard, hstart, hfind,
                  hfound, hhead, bad, hbad, hblock, hsize, hsuitable, split,
                  remainderOffset, capacityBad, hcapacityBad, overflow,
                  hoverflow, hrembin, remainderBad, hrembad] using hfailure

/-- Separation-logic corollary of transactional allocation failure. The frame
may be the allocator's complete `OwnsFree` assertion together with arbitrary
disjoint caller resources. -/
theorem allocateArraysOutcome_failure_preserves_frame
    {PROP : Type} [Iris.BI PROP]
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {request : Nat}
    {failed : AllocateMachineState} (frame : PROP)
    (hfailure : allocateArraysOutcome offsets sizes isFree prevFree count
      second first heads next previous request = .failure failed) :
    failed = allocateInputState offsets sizes isFree prevFree count second
        first heads next previous ∧
      (frame ∗ (emp : PROP) ⊣⊢ frame) := by
  exact ⟨allocateArraysOutcome_failure_eq_input hfailure, sep_emp⟩

theorem allocateArrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {request : Nat}
    {result : AllocateArraysResult}
    (hsuccess : allocateArrays offsets sizes isFree prevFree count second first
      heads next previous request = some result) :
    ∃ startBin foundBin selectedOffset block selectedSize remainderBin
        removed physical,
      classifyRequestBin request = some startBin ∧
      findNonemptyClassLowered second first
        (startBin / secondLevelCount) (startBin % secondLevelCount) =
          some foundBin ∧
      heads[foundBin]? = some selectedOffset ∧
      findOffsetIndex offsets count selectedOffset = some block ∧
      sizes[block]? = some selectedSize ∧
      (if minimumBlockBytes ≤ selectedSize - request then
          classifySizeBin (selectedSize - request) else some 0) =
        some remainderBin ∧
      takeCandidateClassArrays second first heads next previous
        (startBin / secondLevelCount) (startBin % secondLevelCount) =
          some removed ∧
      allocatePhysicalArrays offsets sizes isFree prevFree count block request =
        some physical ∧
      finishAllocateArrays removed physical
        (minimumBlockBytes ≤ selectedSize - request) remainderBin
          (selectedOffset + request) = some result := by
  by_cases hguard : request = 0 ∨ request % alignment ≠ 0
  · simp [allocateArrays, hguard] at hsuccess
  cases hstart : classifyRequestBin request with
  | none => simp [allocateArrays, hguard, hstart] at hsuccess
  | some startBin =>
    cases hfind : findNonemptyClassLowered second first
        (startBin / secondLevelCount) (startBin % secondLevelCount) with
    | none => simp [allocateArrays, hguard, hstart, hfind] at hsuccess
    | some foundBin =>
      by_cases hfound : foundBin ≥ heads.length
      · simp [allocateArrays, hguard, hstart, hfind, hfound] at hsuccess
      cases hhead : heads[foundBin]? with
      | none => simp [allocateArrays, hguard, hstart, hfind, hfound, hhead] at hsuccess
      | some selectedOffset =>
        let bad := selectedOffset ≥ next.length ∨
          selectedOffset ≥ previous.length ∨ count = 0 ∨
          count > offsets.length ∨ count > sizes.length ∨
          count > isFree.length ∨ count > prevFree.length
        by_cases hbad : bad
        · simp [allocateArrays, hguard, hstart, hfind, hfound, hhead,
            bad, hbad] at hsuccess
        cases hblock : findOffsetIndex offsets count selectedOffset with
        | none =>
            simp [allocateArrays, hguard, hstart, hfind, hfound, hhead,
              bad, hbad, hblock] at hsuccess
        | some block =>
          cases hsize : sizes[block]? with
          | none =>
              simp [allocateArrays, hguard, hstart, hfind, hfound, hhead,
                bad, hbad, hblock, hsize] at hsuccess
          | some selectedSize =>
            by_cases hsuitable : isFree[block]? = some 0 ∨ selectedSize < request
            · simp [allocateArrays, hguard, hstart, hfind, hfound, hhead,
                bad, hbad, hblock, hsize, hsuitable] at hsuccess
            let split := minimumBlockBytes ≤ selectedSize - request
            let remainderOffset := selectedOffset + request
            let overflow := split ∧ (remainderOffset ≥ 2 ^ 64 ∨
              remainderOffset ≥ next.length ∨
              remainderOffset ≥ previous.length)
            by_cases hoverflow : overflow
            · simp [allocateArrays, hguard, hstart, hfind, hfound, hhead,
                bad, hbad, hblock, hsize, hsuitable, split, remainderOffset,
                overflow, hoverflow] at hsuccess
            simp [allocateArrays, hguard, hstart, hfind,
              hfound, hhead, bad, hbad, hblock, hsize, hsuitable, split,
              remainderOffset, overflow, hoverflow] at hsuccess
            by_cases hsplit : minimumBlockBytes ≤ selectedSize - request
            · simp only [hsplit, if_true] at hsuccess
              cases hrembin : classifySizeBin (selectedSize - request) with
              | none => simp [hrembin] at hsuccess
              | some remainderBin =>
                simp only [hrembin, Option.bind_some] at hsuccess
                by_cases hrembound : remainderBin ≥ heads.length
                · simp [hrembound] at hsuccess
                by_cases hremfl : remainderBin / secondLevelCount ≥ second.length
                · simp [hrembound, hremfl] at hsuccess
                simp only [hrembound, hremfl, or_self, if_false] at hsuccess
                cases htake : takeCandidateClassArrays second first heads next
                    previous (startBin / secondLevelCount)
                      (startBin % secondLevelCount) with
                | none => simp [htake] at hsuccess
                | some removed =>
                  simp only [htake, Option.bind_some] at hsuccess
                  cases hphysical : allocatePhysicalArrays offsets sizes isFree
                      prevFree count block request with
                  | none => simp [hphysical] at hsuccess
                  | some physical =>
                    simp only [hphysical, Option.bind_some] at hsuccess
                    refine ⟨startBin, foundBin, selectedOffset, block,
                      selectedSize, remainderBin, removed, physical, rfl,
                      hfind, hhead, hblock, hsize, by simpa [hsplit] using hrembin,
                      htake, hphysical, ?_⟩
                    have hfinal :
                        (count < offsets.length ∧ count < sizes.length ∧
                          count < isFree.length ∧ count < prevFree.length) ∧
                        finishAllocateArrays removed physical True remainderBin
                          (selectedOffset + request) = some result := by
                      simpa [hsplit] using hsuccess
                    simpa [hsplit] using hfinal.2
            · simp only [hsplit, if_false, Option.bind_some] at hsuccess
              let remainderBin := 0
              have hrembound : ¬(split ∧ remainderBin ≥ heads.length) := by
                simp [split, hsplit]
              cases htake : takeCandidateClassArrays second first heads next
                  previous (startBin / secondLevelCount)
                    (startBin % secondLevelCount) with
              | none => simp [htake] at hsuccess
              | some removed =>
                simp only [htake, Option.bind_some] at hsuccess
                cases hphysical : allocatePhysicalArrays offsets sizes isFree
                    prevFree count block request with
                | none => simp [hphysical] at hsuccess
                | some physical =>
                  simp only [hphysical, Option.bind_some] at hsuccess
                  refine ⟨startBin, foundBin, selectedOffset, block,
                    selectedSize, remainderBin, removed, physical, rfl,
                    hfind, hhead, hblock, hsize, by simp [hsplit, remainderBin],
                    htake, hphysical, ?_⟩
                  simpa [remainderBin, hsplit] using hsuccess

theorem allocateArrays_count_le_offsets
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {request : Nat}
    {result : AllocateArraysResult}
    (hsuccess : allocateArrays offsets sizes isFree prevFree count second first
      heads next previous request = some result) :
    result.count ≤ offsets.length := by
  obtain ⟨_, _, _, _, _, _, _, physical, _, _, _, _, _, _, _, hphysical,
      hfinish⟩ := allocateArrays_result hsuccess
  have hfinishPhysical := finishAllocateArrays_physical hfinish
  have hcountEq : result.count = physical.count :=
    hfinishPhysical.2.2.2.2.1
  obtain ⟨_, hcountBound, _, _, _, _, _, _, _, _, _, _, _, hcases⟩ :=
    allocatePhysicalArrays_result hphysical
  rcases hcases with
    ⟨_, hcapacity, _, _, _, hphysicalCount, _⟩ |
    ⟨_, hphysicalCount, _⟩ <;> omega

set_option maxHeartbeats 1000000 in
/-- A successful concrete public allocation witnesses the corresponding
abstract TLSF allocation and therefore transfers exactly the returned Iris
byte capability to the caller. This theorem deliberately states the ownership
law before the separate post-state metadata representation theorem. -/
theorem allocateArrays_ownsFree
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)} {count : Nat}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {request : Nat}
    {result : AllocateArraysResult}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hphysicalInput : RepresentsPhysicalArrays offsets sizes isFree prevFree
      count blocks)
    (hsuccess : allocateArrays offsets sizes isFree prevFree count second first
      heads next previous request = some result) :
    ∃ (hrequest : 0 < request)
        (hkeyMax : requestKey request < 2 ^ firstLevelCount)
        (abstractResult : Alloc.Result),
      Alloc.allocate { physical := blocks, bins := state } request hrequest
          hkeyMax = some abstractResult ∧
      result.allocatedOffset = abstractResult.allocated.offset ∧
      result.allocatedBytes = abstractResult.allocated.bytes ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
        result.prevFree result.count abstractResult.state.physical ∧
      Bins.Valid abstractResult.state.bins ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
        abstractResult.state.bins ∧
      BinsOffsetsDisjoint abstractResult.state.bins ∧
      RepresentsSecondBitmap result.second abstractResult.state.bins ∧
      FirstBitmapRep result.first result.second ∧
      (Luffs.Allocator.TLSF.Ownership.OwnsFree (PROP := PROP) pool blocks ⊣⊢
        Luffs.Memory.OwnsBytes (abstractResult.allocated.region pool) ∗
          Luffs.Allocator.TLSF.Ownership.OwnsFree pool
            abstractResult.state.physical) := by
  obtain ⟨startBin, foundBin, selectedOffset, block, selectedSize,
      remainderBin, removedArrays, physicalArrays, hclass, hfindClass,
      hhead, hscan, hsize, hrembin, htake, hphysical, hfinish⟩ :=
    allocateArrays_result hsuccess
  obtain ⟨hrequest, hkeyMax, hstartBin, _⟩ :=
    classifyRequestBin_result hclass
  let start := searchSizeClass request hrequest hkeyMax
  have htake' : takeCandidateClassArrays second first heads next previous
      start.fl.val start.sl.val = some removedArrays := by
    simpa [start, hstartBin, encodeSizeClass_div, encodeSizeClass_mod] using htake
  obtain ⟨removedClass, removed, rest, habstractTake, hremovedOffset,
      hremovedBins, hremovedSecond, hremovedFirst⟩ :=
    takeCandidateClassArrays_refines_takeCandidate start hsecond hfirst
      hvalid.2.1 hbins hdisjoint htake'
  have htakeResult := takeCandidateClassArrays_result htake
  have hbinEq : removedArrays.bin = foundBin := by
    rw [hfindClass] at htakeResult
    exact Option.some.inj htakeResult.1.symm
  have harrayBlock : removedArrays.block = selectedOffset := by
    rw [htakeResult.2.2.2.1, hbinEq, hhead]
    simp
  have hselectedRemoved : selectedOffset = removed.offset := by
    rw [← harrayBlock, hremovedOffset]
  obtain ⟨actual, hactual, hactualRemoved, _, _, _, _⟩ :=
    takeCandidate_suitable hvalid request hrequest hkeyMax habstractTake
  have hscanRemoved : findOffsetIndex offsets count removed.offset =
      some block := by
    simpa [hselectedRemoved] using hscan
  have hscanEq := findOffsetIndex_refines_findPhysicalIndex_represented
    hphysicalInput hvalid.1 hactual hactualRemoved
  rw [hscanEq] at hscanRemoved
  obtain ⟨selected, hselected, hselectedRemovedPhysical⟩ :=
    findPhysicalIndex_sound hscanRemoved
  obtain ⟨allocated, nextPhysical, hchosen, hnextPhysical,
      hphysicalOffset, hphysicalBytes⟩ :=
    allocatePhysicalArrays_refines hphysicalInput hselected
      hvalid.1.2.2.1 hphysical
  let nextBins := state.replaceChain removedClass rest
  let prepared : Alloc.Prepared := {
    detached := removed
    physicalIndex := block
    bins := nextBins }
  have hprepare : Alloc.prepare { physical := blocks, bins := state } request
      hrequest hkeyMax = some prepared := by
    simp [Alloc.prepare, start, habstractTake, hscanRemoved, prepared, nextBins]
  let core : Alloc.CoreResult := {
    allocated := allocated
    physical := nextPhysical
    bins := nextBins
    freeRemainder := allocationRemainder blocks block request }
  have hcore : Alloc.allocateCore { physical := blocks, bins := state } request
      hrequest hkeyMax = some core := by
    simp [Alloc.allocateCore, hprepare, hchosen, core, prepared]
  have haligned : alignment ∣ request :=
    (allocatePhysicalArrays_result hphysical).1
  obtain ⟨abstractNext, habstractFinish⟩ :=
    Alloc.finishCore_complete hvalid haligned hcore
  let abstractResult : Alloc.Result := {
    allocated := allocated
    state := abstractNext }
  have habstract : Alloc.allocate { physical := blocks, bins := state } request
      hrequest hkeyMax = some abstractResult := by
    simp [Alloc.allocate, hcore, habstractFinish, abstractResult, core]
  have hresultPhysical := finishAllocateArrays_physical hfinish
  have hresultOffset : result.allocatedOffset = allocated.offset := by
    rw [hresultPhysical.2.2.2.2.2.1, hphysicalOffset]
  have hresultBytes : result.allocatedBytes = allocated.bytes := by
    rw [hresultPhysical.2.2.2.2.2.2, hphysicalBytes]
  have hselectedSize : selectedSize = selected.bytes := by
    have hexpected := representsPhysicalArrays_get_size
      hphysicalInput hselected
    rw [hsize] at hexpected
    exact Option.some.inj hexpected
  obtain ⟨_, hfits, _, _⟩ :=
    allocateChosenAt_success_cases hselected hchosen
  have hsplitIff : minimumBlockBytes ≤ selectedSize - request ↔
      canSplit selected request := by
    rw [hselectedSize]
    constructor
    · intro hroom
      exact ⟨hrequest, (Nat.le_sub_iff_add_le' hfits).1 hroom⟩
    · intro hcan
      exact (Nat.le_sub_iff_add_le' hfits).2 hcan.2
  have hresultPhysicalRep : RepresentsPhysicalArrays result.offsets
      result.sizes result.isFree result.prevFree result.count nextPhysical := by
    rw [hresultPhysical.1, hresultPhysical.2.1,
      hresultPhysical.2.2.1, hresultPhysical.2.2.2.1,
      hresultPhysical.2.2.2.2.1]
    exact hnextPhysical
  have hnextBinsValid : Bins.Valid nextBins := by
    exact Bins.takeCandidate_valid hvalid.2.1 habstractTake
  have hnextDisjoint : BinsOffsetsDisjoint nextBins := by
    exact takeCandidate_preserves_offsets_disjoint hdisjoint habstractTake
  have hfinishInfo := finishAllocateArrays_result hfinish
  have hpost :
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count abstractResult.state.physical ∧
      Bins.Valid abstractResult.state.bins ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
          abstractResult.state.bins ∧
      BinsOffsetsDisjoint abstractResult.state.bins ∧
      RepresentsSecondBitmap result.second abstractResult.state.bins ∧
      FirstBitmapRep result.first result.second := by
    by_cases hsplit : minimumBlockBytes ≤ selectedSize - request
    · have hcan : canSplit selected request := hsplitIff.mp hsplit
      let remainder := (splitBlock selected request).2
      have hremDef : allocationRemainder blocks block request = some remainder := by
        simp [allocationRemainder, hselected, hcan, remainder]
      have hcoreRem : core.freeRemainder = some remainder := by
        simp [core, hremDef]
      have hsplitSelected : minimumBlockBytes ≤ selected.bytes - request := by
        simpa [hselectedSize] using hsplit
      have hclassBin : classifySizeBin remainder.bytes = some remainderBin := by
        simpa [hselectedSize, hsplitSelected, remainder, splitBlock] using hrembin
      obtain ⟨remainderClass, hclassAbstract, hbin⟩ :=
        classifySizeBin_refines_block (block := remainder) hclassBin
      have habstractNext : abstractNext = {
          physical := nextPhysical
          bins := nextBins.insert remainderClass remainder } := by
        have hfinishExpected : Alloc.finishCore core = some {
            physical := nextPhysical
            bins := nextBins.insert remainderClass remainder } := by
          simp [Alloc.finishCore, core, hremDef, hclassAbstract]
        rw [habstractFinish] at hfinishExpected
        exact Option.some.inj hfinishExpected
      rcases hfinishInfo with hsplitInfo | hwholeInfo
      · obtain ⟨_, inserted, hinsert, hresultSecond, hresultFirst,
            hresultHeads, hresultNext, hresultPrevious⟩ := hsplitInfo
        have hfresh : ∀ query, remainder.offset ∉
            (nextBins.chains query).map Block.offset := by
          intro query
          exact Alloc.allocateCore_remainder_fresh hvalid hcore hcoreRem
        have hbelongs : Bins.Belongs remainderClass remainder :=
          Bins.classifyBlock?_result hclassAbstract
        have hremainderOffset : selectedOffset + request = remainder.offset := by
          rw [hselectedRemoved, ← hselectedRemovedPhysical.1]
          simp [remainder, splitBlock]
        have hinsertRefines := insertClassArrays_refines_insert hnextBinsValid
          hremovedSecond hremovedFirst hremovedBins hnextDisjoint hfresh
          hbelongs hremainderOffset hbin hinsert
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [abstractResult, habstractNext] using hresultPhysicalRep
        · simpa only [abstractResult, habstractNext] using hinsertRefines.1
        · simpa only [abstractResult, habstractNext, hresultHeads,
              hresultNext, hresultPrevious] using hinsertRefines.2.1
        · change BinsOffsetsDisjoint abstractResult.state.bins
          rw [show abstractResult.state.bins =
            nextBins.insert remainderClass remainder by
              simp [abstractResult, habstractNext]]
          exact insert_preserves_offsets_disjoint
            (cls := remainderClass) (inserted := remainder)
            hnextDisjoint hfresh
        · simpa only [abstractResult, habstractNext, hresultSecond] using
            hinsertRefines.2.2.1
        · rw [hresultFirst, hresultSecond]
          exact hinsertRefines.2.2.2
      · exact (hwholeInfo.1 hsplit).elim
    · have hcannot : ¬canSplit selected request :=
        fun hcan => hsplit (hsplitIff.mpr hcan)
      have habstractNext : abstractNext = {
          physical := nextPhysical
          bins := nextBins } := by
        have hfinishExpected : Alloc.finishCore core = some {
            physical := nextPhysical
            bins := nextBins } := by
          simp [Alloc.finishCore, core, allocationRemainder, hselected, hcannot]
        rw [habstractFinish] at hfinishExpected
        exact Option.some.inj hfinishExpected
      rcases hfinishInfo with hsplitInfo | hwholeInfo
      · exact (hsplit hsplitInfo.1).elim
      · obtain ⟨_, hresultSecond, hresultFirst, hresultHeads,
            hresultNext, hresultPrevious⟩ := hwholeInfo
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [abstractResult, habstractNext] using hresultPhysicalRep
        · simpa only [abstractResult, habstractNext] using hnextBinsValid
        · simpa only [abstractResult, habstractNext, hresultHeads,
              hresultNext, hresultPrevious] using hremovedBins
        · change BinsOffsetsDisjoint abstractResult.state.bins
          rw [show abstractResult.state.bins = nextBins by
            simp [abstractResult, habstractNext]]
          exact hnextDisjoint
        · simpa only [abstractResult, habstractNext, hresultSecond] using
            hremovedSecond
        · rw [hresultFirst, hresultSecond]
          exact hremovedFirst
  refine ⟨hrequest, hkeyMax, abstractResult, habstract, ?_, ?_, hpost.1,
    hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2.1,
    hpost.2.2.2.2.2, ?_⟩
  · simpa [abstractResult] using hresultOffset
  · simpa [abstractResult] using hresultBytes
  · exact Luffs.Allocator.TLSF.Ownership.allocate_ownsFree pool hvalid habstract

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

/-- The checked physical compaction has no post-preflight failure edge. -/
theorem coalescePhysicalArrays_ne_none_of_preflight
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count left leftOffset leftSize rightOffset rightSize : Nat}
    (hoffsetsCount : count ≤ offsets.length)
    (hsizesCount : count ≤ sizes.length)
    (hfreeCount : count ≤ isFree.length)
    (hprevCount : count ≤ prevFree.length)
    (hright : left + 1 < count)
    (hleftFree : isFree[left]? ≠ some 0)
    (hrightFree : isFree[left + 1]? ≠ some 0)
    (hleftOffset : offsets[left]? = some leftOffset)
    (hleftSize : sizes[left]? = some leftSize)
    (hrightOffset : offsets[left + 1]? = some rightOffset)
    (hrightSize : sizes[left + 1]? = some rightSize)
    (hadjacent : leftOffset + leftSize = rightOffset) :
    coalescePhysicalArrays offsets sizes isFree prevFree count left ≠ none := by
  simp [coalescePhysicalArrays, hoffsetsCount, hsizesCount, hfreeCount,
    hprevCount, Nat.not_le.mpr hright, hleftFree, hrightFree, hleftOffset,
    hleftSize, hrightOffset, hrightSize, hadjacent]

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

/-- Active-prefix form of physical coalescing. Unlike the canonical theorem,
this permits arbitrary spare capacity after `count`, which is required for a
second coalescing step after the first header compaction. -/
theorem coalescePhysicalArrays_refines_represented_append
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} (pre : List Block) (left right : Block) (rest : List Block)
    (hrep : RepresentsPhysicalArrays offsets sizes isFree prevFree count
      (pre ++ left :: right :: rest))
    (hcan : canCoalesce left right) {result : CoalescePhysicalResult}
    (hsuccess : coalescePhysicalArrays offsets sizes isFree prevFree count
      pre.length = some result) :
    RepresentsPhysicalArrays result.offsets result.sizes result.isFree
      result.prevFree result.count
      (coalesceAt (pre ++ left :: right :: rest) pre.length) := by
  rcases hcan with ⟨hleftFree, hrightFree, hadjacent⟩
  have hleftGet : (pre ++ left :: right :: rest)[pre.length]? = some left := by
    simp
  have hrightGet : (pre ++ left :: right :: rest)[pre.length + 1]? =
      some right := by simp
  have hleftOffset := representsPhysicalArrays_get_offset hrep hleftGet
  have hrightOffset := representsPhysicalArrays_get_offset hrep hrightGet
  have hleftSize := representsPhysicalArrays_get_size hrep hleftGet
  have hrightSize := representsPhysicalArrays_get_size hrep hrightGet
  have hleftFlag := representsPhysicalArrays_get_free hrep hleftGet
  have hrightFlag := representsPhysicalArrays_get_free hrep hrightGet
  have hbounds : count ≤ offsets.length ∧ count ≤ sizes.length ∧
      count ≤ isFree.length ∧ count ≤ prevFree.length :=
    ⟨hrep.2.1, hrep.2.2.1, hrep.2.2.2.1, hrep.2.2.2.2.1⟩
  have hrightBound : pre.length + 1 < count := by
    rw [hrep.1]
    simp
  unfold coalescePhysicalArrays at hsuccess
  simp only [hbounds, if_true, Nat.not_le.mpr hrightBound, if_false,
    hleftFlag, hrightFlag, hleftFree, hrightFree, hleftOffset, hleftSize,
    hrightOffset, hrightSize, Option.getD_some] at hsuccess
  simp only [hadjacent, ne_eq, not_true_eq_false, if_false,
    Option.some.injEq] at hsuccess
  simp at hsuccess
  subst result
  have hcount : count = (pre ++ left :: right :: rest).length := hrep.1
  have hoffsets := compactActive_of_represented_prefix
    (pre.map Block.offset) left.offset right.offset (rest.map Block.offset)
    (by simpa [blockOffsets] using hcount)
    (by simpa [blockOffsets] using hrep.2.2.2.2.2.1)
  have hsizesSet := set_represented_prefix
    (pre.map Block.bytes) left.bytes right.bytes (left.bytes + right.bytes)
    (rest.map Block.bytes) (by simpa [blockSizes] using hcount)
    (by simpa [blockSizes] using hrep.2.2.2.2.2.2.1)
  have hsizes := compactActive_of_represented_prefix
    (pre.map Block.bytes) (left.bytes + right.bytes) right.bytes
    (rest.map Block.bytes) (by simpa [blockSizes] using hcount) hsizesSet
  have hfree := compactActive_of_represented_prefix
    (pre.map fun block => if block.free then (1 : Fin 256) else 0)
    (1 : Fin 256) (1 : Fin 256)
    (rest.map fun block => if block.free then (1 : Fin 256) else 0)
    (by simpa [freeFlags] using hcount)
    (by simpa [freeFlags, hleftFree, hrightFree] using
      hrep.2.2.2.2.2.2.2.1)
  have hprev := compactActive_of_represented_prefix
    (pre.map fun block => if block.prevFree then (1 : Fin 256) else 0)
    (if left.prevFree then (1 : Fin 256) else 0)
    (if right.prevFree then (1 : Fin 256) else 0)
    (rest.map fun block => if block.prevFree then (1 : Fin 256) else 0)
    (by simpa [prevFreeFlags] using hcount)
    (by simpa [prevFreeFlags] using hrep.2.2.2.2.2.2.2.2)
  have hnewCount : count - 1 =
      (pre ++ coalesceBlocks left right :: rest).length := by
    rw [hcount]
    simp
  have hoffsetsBound : count - 1 ≤
      (compactActive offsets count (pre.length + 1)).length := by
    have hlen := compactActive_of_represented_prefix_length
      (pre.map Block.offset) left.offset right.offset (rest.map Block.offset)
      (by simpa [blockOffsets] using hcount)
      (by simpa [blockOffsets] using hrep.2.2.2.2.2.1)
    simp only [List.length_map] at hlen
    rw [hlen]
    omega
  have hsizesBound : count - 1 ≤
      (compactActive (sizes.set pre.length (left.bytes + right.bytes)) count
        (pre.length + 1)).length := by
    have hlen := compactActive_of_represented_prefix_length
      (pre.map Block.bytes) (left.bytes + right.bytes) right.bytes
      (rest.map Block.bytes) (by simpa [blockSizes] using hcount) hsizesSet
    simp only [List.length_map, List.length_set] at hlen
    rw [hlen]
    omega
  have hfreeBound : count - 1 ≤
      (compactActive isFree count (pre.length + 1)).length := by
    have hlen := compactActive_of_represented_prefix_length
      (pre.map fun block => if block.free then (1 : Fin 256) else 0)
      (1 : Fin 256) (1 : Fin 256)
      (rest.map fun block => if block.free then (1 : Fin 256) else 0)
      (by simpa [freeFlags] using hcount)
      (by simpa [freeFlags, hleftFree, hrightFree] using
        hrep.2.2.2.2.2.2.2.1)
    simp only [List.length_map] at hlen
    rw [hlen]
    omega
  have hprevBound : count - 1 ≤
      (compactActive prevFree count (pre.length + 1)).length := by
    have hlen := compactActive_of_represented_prefix_length
      (pre.map fun block => if block.prevFree then (1 : Fin 256) else 0)
      (if left.prevFree then (1 : Fin 256) else 0)
      (if right.prevFree then (1 : Fin 256) else 0)
      (rest.map fun block => if block.prevFree then (1 : Fin 256) else 0)
      (by simpa [prevFreeFlags] using hcount)
      (by simpa [prevFreeFlags] using hrep.2.2.2.2.2.2.2.2)
    simp only [List.length_map] at hlen
    rw [hlen]
    omega
  rw [coalesceAt_append_pair]
  refine ⟨hnewCount, hoffsetsBound, hsizesBound, hfreeBound, hprevBound,
    ?_, ?_, ?_, ?_⟩
  · simpa [blockOffsets, coalesceBlocks] using hoffsets
  · simpa [blockSizes, coalesceBlocks] using hsizes
  · simpa [freeFlags, coalesceBlocks] using hfree
  · simpa [prevFreeFlags, coalesceBlocks] using hprev

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

inductive CoalesceClassOutcome where
  | success (state : CoalesceClassResult)
  | failure (state : CoalesceClassResult)
deriving DecidableEq, Repr

def coalesceStateAfterRemove (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (count : Nat)
    (removed : RemoveClassResult) : CoalesceClassResult :=
  ⟨offsets, sizes, isFree, prevFree, count, removed.second, removed.first,
    removed.heads, removed.next, removed.previous⟩

def coalesceStateAfterPhysical (physical : CoalescePhysicalResult)
    (removed : RemoveClassResult) : CoalesceClassResult :=
  ⟨physical.offsets, physical.sizes, physical.isFree, physical.prevFree,
    physical.count, removed.second, removed.first, removed.heads, removed.next,
    removed.previous⟩

/-- Source-ordered mutation phase of `tlsf_coalesce_class`, after all size,
class, arithmetic, and bounds checks have completed. Unlike the older `Option`
transformer, each impossible failure retains its concrete intermediate state. -/
def commitCoalesceClassOutcome (input : CoalesceClassResult)
    (offsets sizes : List Nat) (isFree prevFree : List (Fin 256))
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (count left leftOffset rightOffset
      leftBin rightBin mergedBin : Nat) : CoalesceClassOutcome :=
  match removeClassArrays second first heads next previous leftBin leftOffset with
  | none => .failure input
  | some withoutLeft =>
    match removeClassArrays withoutLeft.second withoutLeft.first
        withoutLeft.heads withoutLeft.next withoutLeft.previous rightBin
        rightOffset with
    | none => .failure
        (coalesceStateAfterRemove offsets sizes isFree prevFree count withoutLeft)
    | some withoutRight =>
      match coalescePhysicalArrays offsets sizes isFree prevFree count left with
      | none => .failure
          (coalesceStateAfterRemove offsets sizes isFree prevFree count withoutRight)
      | some physical =>
        match insertClassArrays withoutRight.second withoutRight.first
            withoutRight.heads withoutRight.next withoutRight.previous mergedBin
            leftOffset with
        | none => .failure (coalesceStateAfterPhysical physical withoutRight)
        | some inserted => .success
            ⟨physical.offsets, physical.sizes, physical.isFree,
              physical.prevFree, physical.count, inserted.second, inserted.first,
              inserted.heads, inserted.next, inserted.previous⟩

/-- The remove/remove/compact/insert commit has no failure edge once each
source preflight has established totality of its corresponding component. -/
theorem commitCoalesceClassOutcome_ne_failure
    {input failed : CoalesceClassResult}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count left leftOffset rightOffset leftBin rightBin mergedBin : Nat}
    (hleft : removeClassArrays second first heads next previous leftBin
      leftOffset ≠ none)
    (hright : ∀ withoutLeft,
      removeClassArrays second first heads next previous leftBin leftOffset =
          some withoutLeft →
      removeClassArrays withoutLeft.second withoutLeft.first withoutLeft.heads
        withoutLeft.next withoutLeft.previous rightBin rightOffset ≠ none)
    (hphysical : coalescePhysicalArrays offsets sizes isFree prevFree count left ≠
      none)
    (hinsert : ∀ withoutLeft withoutRight,
      removeClassArrays second first heads next previous leftBin leftOffset =
          some withoutLeft →
      removeClassArrays withoutLeft.second withoutLeft.first withoutLeft.heads
          withoutLeft.next withoutLeft.previous rightBin rightOffset =
        some withoutRight →
      insertClassArrays withoutRight.second withoutRight.first withoutRight.heads
        withoutRight.next withoutRight.previous mergedBin leftOffset ≠ none) :
    commitCoalesceClassOutcome input offsets sizes isFree prevFree second first
      heads next previous count left leftOffset rightOffset leftBin rightBin
        mergedBin ≠ .failure failed := by
  unfold commitCoalesceClassOutcome
  cases hleftEq : removeClassArrays second first heads next previous leftBin
      leftOffset with
  | none => exact (hleft hleftEq).elim
  | some withoutLeft =>
    simp only [hleftEq]
    cases hrightEq : removeClassArrays withoutLeft.second withoutLeft.first
        withoutLeft.heads withoutLeft.next withoutLeft.previous rightBin
        rightOffset with
    | none => exact (hright withoutLeft hleftEq hrightEq).elim
    | some withoutRight =>
      simp only [hrightEq]
      cases hphysicalEq : coalescePhysicalArrays offsets sizes isFree prevFree
          count left with
      | none => exact (hphysical hphysicalEq).elim
      | some physical =>
        simp only [hphysicalEq]
        cases hinsertEq : insertClassArrays withoutRight.second
            withoutRight.first withoutRight.heads withoutRight.next
            withoutRight.previous mergedBin leftOffset with
        | none => exact (hinsert withoutLeft withoutRight hleftEq hrightEq
            hinsertEq).elim
        | some inserted => simp

/-- The actual bounds hoisted by `tlsf_coalesce_class` discharge every
component-totality premise, including bounds after both intrusive removals. -/
theorem commitCoalesceClassOutcome_ne_failure_of_preflight
    {input failed : CoalesceClassResult}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count left leftOffset rightOffset leftBin rightBin mergedBin : Nat}
    (hleftBin : leftBin < heads.length)
    (hrightBin : rightBin < heads.length)
    (hmergedBin : mergedBin < heads.length)
    (hleftFl : leftBin / 32 < second.length)
    (hrightFl : rightBin / 32 < second.length)
    (hmergedFl : mergedBin / 32 < second.length)
    (hleftNext : leftOffset < next.length)
    (hleftPrevious : leftOffset < previous.length)
    (hrightNext : rightOffset < next.length)
    (hrightPrevious : rightOffset < previous.length)
    (hphysical : coalescePhysicalArrays offsets sizes isFree prevFree count left ≠
      none) :
    commitCoalesceClassOutcome input offsets sizes isFree prevFree second first
      heads next previous count left leftOffset rightOffset leftBin rightBin
        mergedBin ≠ .failure failed := by
  have hleft := removeClassArrays_ne_none_of_preflight hleftBin hleftFl
    hleftNext hleftPrevious
  apply commitCoalesceClassOutcome_ne_failure hleft
  · intro withoutLeft hleftEq
    have hlens := removeClassArrays_preserves_lengths hleftEq
    apply removeClassArrays_ne_none_of_preflight
    · simpa [hlens.2.1] using hrightBin
    · simpa [hlens.1] using hrightFl
    · simpa [hlens.2.2.1] using hrightNext
    · simpa [hlens.2.2.2] using hrightPrevious
  · exact hphysical
  · intro withoutLeft withoutRight hleftEq hrightEq
    have hleftLens := removeClassArrays_preserves_lengths hleftEq
    have hrightLens := removeClassArrays_preserves_lengths hrightEq
    apply insertClassArrays_ne_none_of_preflight
    · rw [hrightLens.2.1, hleftLens.2.1]
      exact hmergedBin
    · rw [hrightLens.1, hleftLens.1]
      exact hmergedFl
    · rw [hrightLens.2.2.1, hleftLens.2.2.1]
      exact hleftNext
    · rw [hrightLens.2.2.2, hleftLens.2.2.2]
      exact hleftPrevious

/-- A successful stateful commit is exactly the older array transformer once
the precomputed source values are identified with its lookups. -/
theorem commitCoalesceClassOutcome_success_refines_arrays
    {input result : CoalesceClassResult}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count left leftOffset rightOffset leftSize rightSize
      leftBin rightBin mergedBin : Nat}
    (hleftOffset : offsets[left]? = some leftOffset)
    (hrightOffset : offsets[left + 1]? = some rightOffset)
    (hleftSize : sizes[left]? = some leftSize)
    (hrightSize : sizes[left + 1]? = some rightSize)
    (hleftClass : classifySizeBin leftSize = some leftBin)
    (hrightClass : classifySizeBin rightSize = some rightBin)
    (hmergedClass : classifySizeBin (leftSize + rightSize) = some mergedBin)
    (hcommit : commitCoalesceClassOutcome input offsets sizes isFree prevFree
      second first heads next previous count left leftOffset rightOffset leftBin
        rightBin mergedBin = .success result) :
    coalesceClassArrays offsets sizes isFree prevFree second first heads next
      previous count left = some result := by
  unfold commitCoalesceClassOutcome at hcommit
  cases hremoveLeft : removeClassArrays second first heads next previous leftBin
      leftOffset with
  | none => simp [hremoveLeft] at hcommit
  | some withoutLeft =>
    cases hremoveRight : removeClassArrays withoutLeft.second withoutLeft.first
        withoutLeft.heads withoutLeft.next withoutLeft.previous rightBin
        rightOffset with
    | none => simp [hremoveLeft, hremoveRight] at hcommit
    | some withoutRight =>
      cases hphysical : coalescePhysicalArrays offsets sizes isFree prevFree count
          left with
      | none => simp [hremoveLeft, hremoveRight, hphysical] at hcommit
      | some physical =>
        cases hinsert : insertClassArrays withoutRight.second withoutRight.first
            withoutRight.heads withoutRight.next withoutRight.previous mergedBin
            leftOffset with
        | none =>
            simp [hremoveLeft, hremoveRight, hphysical, hinsert] at hcommit
        | some inserted =>
          simp [hremoveLeft, hremoveRight, hphysical, hinsert] at hcommit
          subst result
          have hphysicalInfo := coalescePhysicalArrays_result hphysical
          obtain ⟨_, _, _, _, physicalLeftOffset, physicalLeftSize,
              physicalRightSize, hphysicalLeftOffset, hphysicalLeftSize,
              hphysicalRightOffset, hphysicalRightSize⟩ := hphysicalInfo
          have hphysicalLeftOffsetEq : physicalLeftOffset = leftOffset := by
            rw [hleftOffset] at hphysicalLeftOffset
            exact Option.some.inj hphysicalLeftOffset
          have hphysicalLeftSizeEq : physicalLeftSize = leftSize := by
            rw [hleftSize] at hphysicalLeftSize
            exact Option.some.inj hphysicalLeftSize
          have hphysicalRightSizeEq : physicalRightSize = rightSize := by
            rw [hrightSize] at hphysicalRightSize
            exact Option.some.inj hphysicalRightSize
          subst physicalLeftOffset
          subst physicalLeftSize
          subst physicalRightSize
          have hmergedSize : physical.sizes[left]? =
              some (leftSize + rightSize) := by
            unfold coalescePhysicalArrays at hphysical
            split at hphysical <;> try contradiction
            next =>
              dsimp only at hphysical
              split at hphysical <;> try contradiction
              next =>
                split at hphysical <;> try contradiction
                next =>
                  split at hphysical <;> try contradiction
                  next =>
                    simp only [hleftOffset, hleftSize, hrightOffset, hrightSize,
                      Option.getD_some] at hphysical
                    split at hphysical <;> try contradiction
                    next =>
                      simp only [Option.some.injEq] at hphysical
                      subst physical
                      have hleftBound : left < sizes.length :=
                        (List.getElem?_eq_some_iff.mp hleftSize).1
                      simp [compactActive, List.getElem?_append,
                        List.getElem?_set, hleftBound]
          simp [coalesceClassArrays, hleftOffset, hrightOffset, hleftSize,
            hrightSize, hleftClass, hrightClass, hremoveLeft, hremoveRight,
            hphysical, hmergedSize, hmergedClass, hinsert]

structure InitializeArraysResult where
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

/-- Exact pure state transformer for `tlsf_initialize`. All fixed-capacity
metadata is reset before the single mmap-backed free block is inserted. -/
def initializeArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (_first : BitVec 64) (heads next previous : List Nat)
    (poolBytes : Nat) : Option InitializeArraysResult := do
  if offsets.length = 0 ∨ sizes.length ≠ offsets.length ∨
      isFree.length ≠ offsets.length ∨ prevFree.length ≠ offsets.length ∨
      next.length ≠ offsets.length ∨ previous.length ≠ offsets.length then none
  else if poolBytes > next.length then none
  else
    let bin ← classifySizeBin poolBytes
    let sentinel := next.length
    let clearedOffsets := List.replicate offsets.length 0
    let clearedSizes := (List.replicate sizes.length 0).set 0 poolBytes
    let clearedFree := (List.replicate isFree.length (0 : Fin 256)).set 0 1
    let clearedPrevFree := List.replicate prevFree.length (0 : Fin 256)
    let clearedSecond := List.replicate second.length (0 : BitVec 32)
    let clearedHeads := List.replicate heads.length sentinel
    let clearedNext := List.replicate next.length sentinel
    let clearedPrevious := List.replicate previous.length sentinel
    let inserted ← insertClassArrays clearedSecond 0 clearedHeads clearedNext
      clearedPrevious bin 0
    pure {
      offsets := clearedOffsets
      sizes := clearedSizes
      isFree := clearedFree
      prevFree := clearedPrevFree
      count := 1
      second := inserted.second
      first := inserted.first
      heads := inserted.heads
      next := inserted.next
      previous := inserted.previous }

def emptyBins : Bins.State :=
  Bins.State.fromChains fun _ => []

def initialBlock (poolBytes : Nat) : Block := {
  offset := 0
  bytes := poolBytes
  free := true
  prevFree := false
  prevFreeLink := none
  nextFreeLink := none }

theorem emptyBins_valid : Bins.Valid emptyBins := by
  apply Bins.fromChains_valid
  constructor
  · intro cls
    exact ⟨by simp [FreeList.linkedFrom], by simp⟩
  · simp [Bins.Belongs]

theorem emptyBins_offsets_disjoint : BinsOffsetsDisjoint emptyBins := by
  simp [BinsOffsetsDisjoint, emptyBins, Bins.State.fromChains]

theorem clearedSecond_represents_emptyBins :
    RepresentsSecondBitmap (List.replicate firstLevelCount (0 : BitVec 32))
      emptyBins := by
  constructor
  · simp
  · intro cls
    have hword : (List.replicate firstLevelCount (0 : BitVec 32))[cls.fl.val]? =
        some 0 := List.getElem?_replicate_of_lt cls.fl.isLt
    have hbit := classBits_get hword cls.sl.isLt
    simpa [secondLevelCount, emptyBins, Bins.State.fromChains] using hbit

theorem clearedFirst_represents_clearedSecond :
    FirstBitmapRep 0
      (List.replicate firstLevelCount (0 : BitVec 32)) := by
  simp [FirstBitmapRep, firstLevelCount, wordBits, secondNonzeroBits]

theorem clearedMetadata_represents_emptyBins (headsLength linkLength : Nat)
    (hheadsLength : 2048 ≤ headsLength) :
    RepresentsBins {
      heads := List.replicate headsLength linkLength
      next := List.replicate linkLength linkLength
      previous := List.replicate linkLength linkLength } emptyBins := by
  intro cls
  have hbin : cls.fl.val * secondLevelCount + cls.sl.val < 2048 := by
    have := cls.fl.isLt
    have := cls.sl.isLt
    simp only [firstLevelCount, secondLevelCount] at *
    omega
  change RepresentsBin {
    heads := List.replicate headsLength linkLength
    next := List.replicate linkLength linkLength
    previous := List.replicate linkLength linkLength }
    (cls.fl.val * secondLevelCount + cls.sl.val) []
  have hbin' : cls.fl.val * secondLevelCount + cls.sl.val < headsLength :=
    Nat.lt_of_lt_of_le hbin hheadsLength
  refine ⟨by simpa only [List.length_replicate] using hbin',
    by simp only [List.length_replicate], ?_, trivial,
    List.nodup_nil⟩
  rw [List.getElem?_replicate_of_lt hbin']
  simp only [Option.getD_some, List.head?_nil, Option.getD_none,
    List.length_replicate]

theorem initializeArrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {poolBytes : Nat}
    {result : InitializeArraysResult}
    (hsuccess : initializeArrays offsets sizes isFree prevFree second first
      heads next previous poolBytes = some result) :
    ∃ bin inserted,
      classifySizeBin poolBytes = some bin ∧
      insertClassArrays (List.replicate second.length (0 : BitVec 32)) 0
          (List.replicate heads.length next.length)
          (List.replicate next.length next.length)
          (List.replicate previous.length next.length) bin 0 = some inserted ∧
      result.offsets = List.replicate offsets.length 0 ∧
      result.sizes = (List.replicate sizes.length 0).set 0 poolBytes ∧
      result.isFree = (List.replicate isFree.length (0 : Fin 256)).set 0 1 ∧
      result.prevFree = List.replicate prevFree.length (0 : Fin 256) ∧
      result.count = 1 ∧ result.second = inserted.second ∧
      result.first = inserted.first ∧ result.heads = inserted.heads ∧
      result.next = inserted.next ∧ result.previous = inserted.previous := by
  unfold initializeArrays at hsuccess
  split at hsuccess
  next => contradiction
  next =>
    split at hsuccess
    next => contradiction
    next =>
      cases hclass : classifySizeBin poolBytes with
      | none => simp [hclass] at hsuccess
      | some bin =>
          rw [hclass] at hsuccess
          simp only [Option.bind_eq_bind, Option.bind_some] at hsuccess
          cases hinsert : insertClassArrays
              (List.replicate second.length (0 : BitVec 32)) 0
              (List.replicate heads.length next.length)
              (List.replicate next.length next.length)
              (List.replicate previous.length next.length) bin 0 with
          | none => rw [hinsert] at hsuccess; contradiction
          | some inserted =>
              rw [hinsert] at hsuccess
              simp only [Option.bind_some, Option.pure_def,
                Option.some.injEq] at hsuccess
              subst result
              exact ⟨bin, inserted, rfl, hinsert, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem initializeArrays_poolBytes_le
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {poolBytes : Nat}
    {result : InitializeArraysResult}
    (hsuccess : initializeArrays offsets sizes isFree prevFree second first
      heads next previous poolBytes = some result) :
    poolBytes ≤ next.length := by
  by_cases hle : poolBytes ≤ next.length
  · exact hle
  · have htooLarge : poolBytes > next.length := by omega
    simp [initializeArrays, htooLarge] at hsuccess

theorem initializedPhysical_represents (capacity poolBytes : Nat)
    (hcapacity : 0 < capacity) :
    RepresentsPhysicalArrays
      (List.replicate capacity 0)
      ((List.replicate capacity 0).set 0 poolBytes)
      ((List.replicate capacity (0 : Fin 256)).set 0 1)
      (List.replicate capacity (0 : Fin 256)) 1
      [initialBlock poolBytes] := by
  cases capacity with
  | zero => omega
  | succ capacity =>
      simp [List.replicate_succ, RepresentsPhysicalArrays, blockOffsets,
        blockSizes, freeFlags, prevFreeFlags, initialBlock]

set_option maxHeartbeats 600000 in
/-- Successful fixed-capacity initialization constructs the valid abstract
allocator containing exactly the mmap-backed pool as one free block. -/
theorem initializeArrays_refines
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {poolBytes : Nat}
    {result : InitializeArraysResult}
    (hoffsets : offsets.length = 4096) (hsizes : sizes.length = 4096)
    (hisFree : isFree.length = 4096) (hprevFree : prevFree.length = 4096)
    (hsecondLength : second.length = firstLevelCount)
    (hheads : heads.length = 2048) (hnext : next.length = 4096)
    (hprevious : previous.length = 4096)
    (hpositive : 0 < poolBytes)
    (hmax : poolBytes < 2 ^ firstLevelCount)
    (hsuccess : initializeArrays offsets sizes isFree prevFree second first
      heads next previous poolBytes = some result) :
    ∃ cls,
      Bins.classifyBlock? (initialBlock poolBytes) = some cls ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count [initialBlock poolBytes] ∧
      Bins.Valid (emptyBins.insert cls (initialBlock poolBytes)) ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
          (emptyBins.insert cls (initialBlock poolBytes)) ∧
      BinsOffsetsDisjoint (emptyBins.insert cls (initialBlock poolBytes)) ∧
      RepresentsSecondBitmap result.second
          (emptyBins.insert cls (initialBlock poolBytes)) ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨bin, inserted, hclass, hinsert, hresultOffsets, hresultSizes,
      hresultFree, hresultPrevFree, hresultCount, hresultSecond,
      hresultFirst, hresultHeads, hresultNext, hresultPrevious⟩ :=
    initializeArrays_result hsuccess
  obtain ⟨cls, habstractClass, hencoded⟩ :=
    classifySizeBin_refines_block (block := initialBlock poolBytes) (by
      simpa [initialBlock] using hclass)
  have hinsert' : insertClassArrays
      (List.replicate firstLevelCount (0 : BitVec 32)) 0
      (List.replicate 2048 4096) (List.replicate 4096 4096)
      (List.replicate 4096 4096) bin 0 = some inserted := by
    rw [hsecondLength, hheads, hnext, hprevious] at hinsert
    exact hinsert
  have hfresh : ∀ query,
      (initialBlock poolBytes).offset ∉
        (emptyBins.chains query).map Block.offset := by
    simp [emptyBins, Bins.State.fromChains]
  have hrefine := insertClassArrays_refines_insert
    (inserted := initialBlock poolBytes) emptyBins_valid
    clearedSecond_represents_emptyBins
    clearedFirst_represents_clearedSecond
    (clearedMetadata_represents_emptyBins 2048 4096 (Nat.le_refl _))
    emptyBins_offsets_disjoint hfresh
    (Bins.classifyBlock?_result habstractClass) (by simp [initialBlock])
    hencoded hinsert'
  have hphysical : RepresentsPhysicalArrays result.offsets result.sizes
      result.isFree result.prevFree result.count [initialBlock poolBytes] := by
    rw [hresultOffsets, hresultSizes, hresultFree, hresultPrevFree,
      hresultCount, hoffsets, hsizes, hisFree, hprevFree]
    exact initializedPhysical_represents 4096 poolBytes (by omega)
  rw [hresultSecond, hresultFirst, hresultHeads, hresultNext, hresultPrevious]
  exact ⟨cls, habstractClass, hphysical, hrefine.1, hrefine.2.1,
    insert_preserves_offsets_disjoint emptyBins_offsets_disjoint hfresh,
    hrefine.2.2.1, hrefine.2.2.2⟩

theorem initialAllocator_valid (pool : Luffs.Memory.Region)
    (hpositive : 0 < pool.bytes) (haligned : alignment ∣ pool.bytes)
    {cls : SizeClass}
    (hclass : Bins.classifyBlock? (initialBlock pool.bytes) = some cls) :
    Alloc.Valid pool {
      physical := [initialBlock pool.bytes]
      bins := emptyBins.insert cls (initialBlock pool.bytes) } := by
  have hbelongs := Bins.classifyBlock?_result hclass
  have hfresh : (initialBlock pool.bytes).offset ∉
      (emptyBins.chains cls).map Block.offset := by
    simp [emptyBins, Bins.State.fromChains]
  have hbinsValid := Bins.insert_valid emptyBins_valid cls
    (initialBlock pool.bytes) hbelongs hfresh
  have hwell : wellFormed pool [initialBlock pool.bytes] := by
    have haligned8 : 8 ∣ pool.bytes := by
      simpa [alignment] using haligned
    simp [wellFormed, ordered, partitions, contiguousFrom, covers,
      boundaryTags, boundaryTagsFrom, initialBlock, Block.aligned,
      alignment, hpositive, haligned8]
  have hagreement : Bins.PhysicalAgreement [initialBlock pool.bytes]
      (emptyBins.insert cls (initialBlock pool.bytes)) := by
    constructor
    · intro query cached hmem
      by_cases hquery : query = cls
      · subst query
        have horigin := Bins.insert_member_origin emptyBins_valid
          (inserted := initialBlock pool.bytes) (by simp [initialBlock]) hmem
        rcases horigin with hnew | hold
        · exact ⟨initialBlock pool.bytes, by simp, hnew⟩
        · rcases hold with ⟨old, hold, _⟩
          simp [emptyBins, Bins.State.fromChains] at hold
      · have hold : cached ∈ emptyBins.chains query := by
          simp only [Bins.State.insert] at hmem
          rw [Bins.replaceChain_other emptyBins
            (FreeList.insertFront (initialBlock pool.bytes)
              (emptyBins.chains cls)) hquery] at hmem
          exact hmem
        simp [emptyBins, Bins.State.fromChains] at hold
    · intro actual hmem hfree
      simp only [List.mem_singleton] at hmem
      subst actual
      obtain ⟨cached, hcached, hsame⟩ :=
        Bins.inserted_has_representation (state := emptyBins) (cls := cls)
          (inserted := initialBlock pool.bytes) (by simp [initialBlock])
      exact ⟨cls, cached, hcached, hsame⟩
  exact ⟨hwell, hbinsValid, hagreement⟩

theorem initializeArrays_constructs_valid_pool
    {pool : Luffs.Memory.Region}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : InitializeArraysResult}
    (hoffsets : offsets.length = 4096) (hsizes : sizes.length = 4096)
    (hisFree : isFree.length = 4096) (hprevFree : prevFree.length = 4096)
    (hsecondLength : second.length = firstLevelCount)
    (hheads : heads.length = 2048) (hnext : next.length = 4096)
    (hprevious : previous.length = 4096)
    (hpositive : 0 < pool.bytes) (haligned : alignment ∣ pool.bytes)
    (hmax : pool.bytes < 2 ^ firstLevelCount)
    (hsuccess : initializeArrays offsets sizes isFree prevFree second first
      heads next previous pool.bytes = some result) :
    ∃ cls,
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count [initialBlock pool.bytes] ∧
      Alloc.Valid pool {
        physical := [initialBlock pool.bytes]
        bins := emptyBins.insert cls (initialBlock pool.bytes) } ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
          (emptyBins.insert cls (initialBlock pool.bytes)) ∧
      BinsOffsetsDisjoint (emptyBins.insert cls (initialBlock pool.bytes)) ∧
      RepresentsSecondBitmap result.second
          (emptyBins.insert cls (initialBlock pool.bytes)) ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨cls, hclass, hphysical, _, hbins, hdisjoint, hsecond, hfirst⟩ :=
    initializeArrays_refines hoffsets hsizes hisFree hprevFree hsecondLength
      hheads hnext hprevious hpositive hmax hsuccess
  exact ⟨cls, hphysical, initialAllocator_valid pool hpositive haligned hclass,
    hbins, hdisjoint, hsecond, hfirst⟩

theorem initialAllocator_ownsMappedPool
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    (pool : Luffs.Memory.Region) :
    Luffs.Allocator.TLSF.Ownership.OwnsFree (PROP := PROP) pool
        [initialBlock pool.bytes] ⊣⊢
      Luffs.Memory.OwnsBytes pool := by
  simp only [Luffs.Allocator.TLSF.Ownership.OwnsFree, initialBlock,
    Block.region, List.foldr_cons, List.foldr_nil]
  change Luffs.Memory.OwnsBytes (PROP := PROP) pool ∗ iprop(emp) ⊣⊢
    Luffs.Memory.OwnsBytes pool
  exact Iris.BI.sep_emp

/-- A successful trusted mmap transfers its complete byte capability directly
into the initial TLSF free-pool assertion; no allocator implementation is
trusted in this handoff. -/
theorem mmap_success_ownsInitialAllocator
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    [Luffs.Memory.MMapSpec PROP]
    (bytes : Nat) (hbytes : 0 < bytes) (pool : Luffs.Memory.Region) :
    Luffs.Memory.MMapSpec.mmapPost (PROP := PROP) bytes (some pool) ⊢
      ⌜pool.bytes = bytes ∧
        pool.base % Luffs.Memory.MMapSpec.pageSize (PROP := PROP) = 0⌝ ∗
      Luffs.Allocator.TLSF.Ownership.OwnsFree (PROP := PROP) pool
        [initialBlock pool.bytes] := by
  exact (Luffs.Memory.MMapSpec.success (PROP := PROP) bytes hbytes pool).trans
    (Iris.BI.sep_mono_right
      (initialAllocator_ownsMappedPool (PROP := PROP) pool).mpr)

/-- End-to-end trusted-boundary handoff. A successful mmap and successful
concrete Luffs metadata initialization jointly establish the full represented
TLSF invariant and transfer the mapped bytes into `OwnsFree`. -/
theorem mmap_success_initializeArrays
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    [Luffs.Memory.MMapSpec PROP]
    {pool : Luffs.Memory.Region} {bytes : Nat}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : InitializeArraysResult}
    (hoffsets : offsets.length = 4096) (hsizes : sizes.length = 4096)
    (hisFree : isFree.length = 4096) (hprevFree : prevFree.length = 4096)
    (hsecondLength : second.length = firstLevelCount)
    (hheads : heads.length = 2048) (hnext : next.length = 4096)
    (hprevious : previous.length = 4096)
    (hpositive : 0 < bytes) (haligned : alignment ∣ bytes)
    (hmax : bytes < 2 ^ firstLevelCount)
    (hsuccess : initializeArrays offsets sizes isFree prevFree second first
      heads next previous pool.bytes = some result) :
    Luffs.Memory.MMapSpec.mmapPost (PROP := PROP) bytes (some pool) ⊢
      ⌜∃ cls,
        RepresentsPhysicalArrays result.offsets result.sizes result.isFree
            result.prevFree result.count [initialBlock pool.bytes] ∧
        Alloc.Valid pool {
          physical := [initialBlock pool.bytes]
          bins := emptyBins.insert cls (initialBlock pool.bytes) } ∧
        RepresentsBins (Metadata.mk result.heads result.next result.previous)
            (emptyBins.insert cls (initialBlock pool.bytes)) ∧
        BinsOffsetsDisjoint (emptyBins.insert cls (initialBlock pool.bytes)) ∧
        RepresentsSecondBitmap result.second
            (emptyBins.insert cls (initialBlock pool.bytes)) ∧
        FirstBitmapRep result.first result.second⌝ ∗
      Luffs.Allocator.TLSF.Ownership.OwnsFree (PROP := PROP) pool
        [initialBlock pool.bytes] := by
  iintro Hmapped
  ihave Hsuccess :
      (⌜pool.bytes = bytes ∧
        pool.base % Luffs.Memory.MMapSpec.pageSize (PROP := PROP) = 0⌝ ∗
      Luffs.Memory.OwnsBytes pool) $$ [Hmapped]
  · iapply Luffs.Memory.MMapSpec.success bytes hpositive pool
    iassumption
  icases Hsuccess with ⟨Hfacts, Hpool⟩
  ipure Hfacts
  have hpoolBytes : pool.bytes = bytes := Hfacts.1
  have hpoolPositive : 0 < pool.bytes := by omega
  have hpoolAligned : alignment ∣ pool.bytes := by simpa [hpoolBytes] using haligned
  have hpoolMax : pool.bytes < 2 ^ firstLevelCount := by omega
  obtain ⟨cls, hphysical, hvalid, hbins, hdisjoint, hsecond, hfirst⟩ :=
    initializeArrays_constructs_valid_pool hoffsets hsizes hisFree hprevFree
      hsecondLength hheads hnext hprevious hpoolPositive hpoolAligned hpoolMax
      hsuccess
  isplitl []
  · ipureintro
    exact ⟨cls, hphysical, hvalid, hbins, hdisjoint, hsecond, hfirst⟩
  · iapply (initialAllocator_ownsMappedPool (PROP := PROP) pool).mpr $$ Hpool


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

def allocatorArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count : Nat) : CoalesceClassResult := {
  offsets, sizes, isFree, prevFree, count, second, first, heads, next, previous }

/-- Exact pure semantics of `tlsf_coalesce_if_possible`. Ineligible or absent
neighbors are successful identity transitions. -/
def coalesceIfPossibleArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count left : Nat) : Option CoalesceClassResult :=
  if count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length then none
  else if left = usizeMax then
    some (allocatorArrays offsets sizes isFree prevFree second first heads next
      previous count)
  else
    let right := left + 1
    if right ≥ count then
      some (allocatorArrays offsets sizes isFree prevFree second first heads next
        previous count)
    else if isFree[left]? = some 0 then
      some (allocatorArrays offsets sizes isFree prevFree second first heads next
        previous count)
    else if isFree[right]? = some 0 then
      some (allocatorArrays offsets sizes isFree prevFree second first heads next
        previous count)
    else match offsets[left]?, sizes[left]?, offsets[right]? with
      | some leftOffset, some leftSize, some rightOffset =>
          if leftOffset + leftSize ≠ rightOffset then
            some (allocatorArrays offsets sizes isFree prevFree second first
              heads next previous count)
          else coalesceClassArrays offsets sizes isFree prevFree second first
            heads next previous count left
      | _, _, _ => none

/-- Stateful source semantics of conditional coalescing. Missing or ineligible
neighbors are successful identity transitions. All genuine rejection precedes
the stateful coalescing commit. -/
def coalesceIfPossibleArraysOutcome (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count left : Nat) : CoalesceClassOutcome :=
  let input := allocatorArrays offsets sizes isFree prevFree second first heads
    next previous count
  if count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length then .failure input
  else if left = usizeMax then .success input
  else
    let right := left + 1
    if right ≥ count then .success input
    else if isFree[left]? = some 0 then .success input
    else if isFree[right]? = some 0 then .success input
    else match offsets[left]?, sizes[left]?, offsets[right]?, sizes[right]? with
    | some leftOffset, some leftSize, some rightOffset, some rightSize =>
      if leftOffset + leftSize ≠ rightOffset then .success input
      else match classifySizeBin leftSize, classifySizeBin rightSize,
          classifySizeBin (leftSize + rightSize) with
      | some leftBin, some rightBin, some mergedBin =>
        if leftBin ≥ heads.length ∨ rightBin ≥ heads.length ∨
            mergedBin ≥ heads.length ∨
            leftBin / secondLevelCount ≥ second.length ∨
            rightBin / secondLevelCount ≥ second.length ∨
            mergedBin / secondLevelCount ≥ second.length ∨
            leftOffset ≥ next.length ∨ leftOffset ≥ previous.length ∨
            rightOffset ≥ next.length ∨ rightOffset ≥ previous.length then
          .failure input
        else commitCoalesceClassOutcome input offsets sizes isFree prevFree
          second first heads next previous count left leftOffset rightOffset
          leftBin rightBin mergedBin
      | _, _, _ => .failure input
    | _, _, _, _ => .failure input

set_option maxHeartbeats 1000000 in
/-- Conditional coalescing is transactional: every failure carries the exact
complete metadata state supplied by its caller. -/
theorem coalesceIfPossibleArraysOutcome_failure_eq_input
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {count left : Nat}
    {failed : CoalesceClassResult}
    (hfailure : coalesceIfPossibleArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count left = .failure failed) :
    failed = allocatorArrays offsets sizes isFree prevFree second first heads next
      previous count := by
  let input := allocatorArrays offsets sizes isFree prevFree second first heads
    next previous count
  let capacityBad := count > offsets.length ∨ count > sizes.length ∨
    count > isFree.length ∨ count > prevFree.length
  by_cases hcapacity : capacityBad
  · simpa [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity] using
      hfailure.symm
  by_cases hmax : left = usizeMax
  · simp [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
      hmax] at hfailure
  let right := left + 1
  by_cases hright : right ≥ count
  · simp [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
      hmax, right, hright] at hfailure
  by_cases hleftFree : isFree[left]? = some 0
  · simp [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
      hmax, right, hright, hleftFree] at hfailure
  by_cases hrightFree : isFree[right]? = some 0
  · simp [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
      hmax, right, hright, hleftFree, hrightFree] at hfailure
  cases hleftOffset : offsets[left]? with
  | none =>
      simpa [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
        hmax, right, hright, hleftFree, hrightFree, hleftOffset] using
        hfailure.symm
  | some leftOffset =>
    cases hleftSize : sizes[left]? with
    | none =>
        simpa [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
          hmax, right, hright, hleftFree, hrightFree, hleftOffset, hleftSize]
          using hfailure.symm
    | some leftSize =>
      cases hrightOffset : offsets[right]? with
      | none =>
          simpa [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
            hmax, right, hright, hleftFree, hrightFree, hleftOffset, hleftSize,
            hrightOffset] using hfailure.symm
      | some rightOffset =>
        cases hrightSize : sizes[right]? with
        | none =>
            simpa [coalesceIfPossibleArraysOutcome, input, capacityBad, hcapacity,
              hmax, right, hright, hleftFree, hrightFree, hleftOffset,
              hleftSize, hrightOffset, hrightSize] using hfailure.symm
        | some rightSize =>
          by_cases hadjacent : leftOffset + leftSize ≠ rightOffset
          · simp [coalesceIfPossibleArraysOutcome, input, capacityBad,
              hcapacity, hmax, right, hright, hleftFree, hrightFree,
              hleftOffset, hleftSize, hrightOffset, hrightSize, hadjacent] at
              hfailure
          cases hleftBin : classifySizeBin leftSize with
          | none =>
              simpa [coalesceIfPossibleArraysOutcome, input, capacityBad,
                hcapacity, hmax, right, hright, hleftFree, hrightFree,
                hleftOffset, hleftSize, hrightOffset, hrightSize, hadjacent,
                hleftBin] using hfailure.symm
          | some leftBin =>
            cases hrightBin : classifySizeBin rightSize with
            | none =>
                simpa [coalesceIfPossibleArraysOutcome, input, capacityBad,
                  hcapacity, hmax, right, hright, hleftFree, hrightFree,
                  hleftOffset, hleftSize, hrightOffset, hrightSize, hadjacent,
                  hleftBin, hrightBin] using hfailure.symm
            | some rightBin =>
              cases hmergedBin : classifySizeBin (leftSize + rightSize) with
              | none =>
                  simpa [coalesceIfPossibleArraysOutcome, input, capacityBad,
                    hcapacity, hmax, right, hright, hleftFree, hrightFree,
                    hleftOffset, hleftSize, hrightOffset, hrightSize, hadjacent,
                    hleftBin, hrightBin, hmergedBin] using hfailure.symm
              | some mergedBin =>
                let metadataBad := leftBin ≥ heads.length ∨
                  rightBin ≥ heads.length ∨ mergedBin ≥ heads.length ∨
                  leftBin / secondLevelCount ≥ second.length ∨
                  rightBin / secondLevelCount ≥ second.length ∨
                  mergedBin / secondLevelCount ≥ second.length ∨
                  leftOffset ≥ next.length ∨ leftOffset ≥ previous.length ∨
                  rightOffset ≥ next.length ∨ rightOffset ≥ previous.length
                by_cases hmetadata : metadataBad
                · simpa [coalesceIfPossibleArraysOutcome, input, capacityBad,
                    hcapacity, hmax, right, hright, hleftFree, hrightFree,
                    hleftOffset, hleftSize, hrightOffset, hrightSize, hadjacent,
                    hleftBin, hrightBin, hmergedBin, metadataBad, hmetadata]
                    using hfailure.symm
                have hphysical : coalescePhysicalArrays offsets sizes isFree
                    prevFree count left ≠ none := by
                  apply coalescePhysicalArrays_ne_none_of_preflight
                  all_goals simp only [capacityBad] at hcapacity
                  · omega
                  · omega
                  · omega
                  · omega
                  · simpa [right] using Nat.lt_of_not_ge hright
                  · exact hleftFree
                  · simpa [right] using hrightFree
                  · exact hleftOffset
                  · exact hleftSize
                  · simpa [right] using hrightOffset
                  · simpa [right] using hrightSize
                  · exact Classical.byContradiction (fun h => hadjacent h)
                have himpossible :=
                  commitCoalesceClassOutcome_ne_failure_of_preflight
                    (input := input) (failed := failed)
                    (Nat.lt_of_not_ge (fun h => hmetadata (Or.inl h)))
                    (Nat.lt_of_not_ge (fun h => hmetadata (Or.inr (Or.inl h))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inl h)))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inr (Or.inl h))))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inl h)))))))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inl h))))))))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inl h)))))))))))
                    (Nat.lt_of_not_ge (fun h => hmetadata
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr h))))))))))) hphysical
                apply himpossible
                simpa [coalesceIfPossibleArraysOutcome, input, capacityBad,
                  hcapacity, hmax, right, hright, hleftFree, hrightFree,
                  hleftOffset, hleftSize, hrightOffset, hrightSize, hadjacent,
                  hleftBin, hrightBin, hmergedBin, metadataBad, hmetadata] using
                  hfailure

theorem coalesceIfPossibleArraysOutcome_failure_preserves_frame
    {PROP : Type} [Iris.BI PROP]
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {count left : Nat}
    {failed : CoalesceClassResult} (frame : PROP)
    (hfailure : coalesceIfPossibleArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count left = .failure failed) :
    failed = allocatorArrays offsets sizes isFree prevFree second first heads next
        previous count ∧ (frame ∗ (emp : PROP) ⊣⊢ frame) := by
  exact ⟨coalesceIfPossibleArraysOutcome_failure_eq_input hfailure, sep_emp⟩

/-- A successful state-retaining conditional coalescing execution is exactly
the `Option` array transformer used by the established abstract refinement. -/
theorem coalesceIfPossibleArraysOutcome_success_refines_option
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {count left : Nat}
    {result : CoalesceClassResult}
    (hsuccess : coalesceIfPossibleArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count left = .success result) :
    coalesceIfPossibleArrays offsets sizes isFree prevFree second first heads next
      previous count left = some result := by
  let input := allocatorArrays offsets sizes isFree prevFree second first heads
    next previous count
  unfold coalesceIfPossibleArraysOutcome at hsuccess
  split at hsuccess <;> try contradiction
  next hcapacity =>
    split at hsuccess
    next hmax =>
      simp only [CoalesceClassOutcome.success.injEq] at hsuccess
      subst result
      simp [coalesceIfPossibleArrays, input, hcapacity, hmax]
    next hmax =>
      dsimp only at hsuccess
      split at hsuccess
      next hright =>
        simp only [CoalesceClassOutcome.success.injEq] at hsuccess
        subst result
        simp [coalesceIfPossibleArrays, input, hcapacity, hmax, hright]
      next hright =>
        split at hsuccess
        next hleftFree =>
          simp only [CoalesceClassOutcome.success.injEq] at hsuccess
          subst result
          simp [coalesceIfPossibleArrays, input, hcapacity, hmax, hright,
            hleftFree]
        next hleftFree =>
          split at hsuccess
          next hrightFree =>
            simp only [CoalesceClassOutcome.success.injEq] at hsuccess
            subst result
            simp [coalesceIfPossibleArrays, input, hcapacity, hmax, hright,
              hleftFree, hrightFree]
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
                      simp [hleftOffset, hleftSize, hrightOffset, hrightSize] at
                        hsuccess
                  | some rightSize =>
                    split at hsuccess
                    next hadjacent =>
                      simp only [CoalesceClassOutcome.success.injEq] at hsuccess
                      subst result
                      simp [coalesceIfPossibleArrays, input, hcapacity, hmax,
                        hright, hleftFree, hrightFree, hleftOffset, hleftSize,
                        hrightOffset, hadjacent]
                    next hadjacent =>
                      cases hleftClass : classifySizeBin leftSize with
                      | none => simp [hleftClass] at hsuccess
                      | some leftBin =>
                        cases hrightClass : classifySizeBin rightSize with
                        | none => simp [hleftClass, hrightClass] at hsuccess
                        | some rightBin =>
                          cases hmergedClass : classifySizeBin
                              (leftSize + rightSize) with
                          | none =>
                              simp [hleftClass, hrightClass, hmergedClass] at
                                hsuccess
                          | some mergedBin =>
                            split at hsuccess <;> try contradiction
                            next hmetadata =>
                              have hclassSuccess :=
                                commitCoalesceClassOutcome_success_refines_arrays
                                  hleftOffset hrightOffset hleftSize hrightSize
                                  hleftClass hrightClass hmergedClass hsuccess
                              simp [coalesceIfPossibleArrays, input, hcapacity,
                                hmax, hright, hleftFree, hrightFree, hleftOffset,
                                hleftSize, hrightOffset, hadjacent, hclassSuccess]

set_option maxHeartbeats 1000000 in
/-- A conditionally coalescing call on a completely represented valid
allocator cannot fail. Ineligible pairs return the identity state; eligible
pairs satisfy every concrete preflight and enter the proved-total commit. -/
theorem coalesceIfPossibleArraysOutcome_ne_failure_of_valid
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {count left : Nat}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hsecond : RepresentsSecondBitmap second state)
    (hbins : RepresentsBins { heads, next, previous } state) :
    ∀ failed, coalesceIfPossibleArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count left ≠ .failure failed := by
  intro failed
  let input := allocatorArrays offsets sizes isFree prevFree second first heads
    next previous count
  have hcapacity : ¬(count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length) := by
    omega
  by_cases hmax : left = usizeMax
  · simp [coalesceIfPossibleArraysOutcome, input, hcapacity, hmax]
  let right := left + 1
  by_cases hrightBound : right ≥ count
  · simp [coalesceIfPossibleArraysOutcome, input, hcapacity, hmax, right,
      hrightBound]
  by_cases hleftFreeFlag : isFree[left]? = some 0
  · simp [coalesceIfPossibleArraysOutcome, input, hcapacity, hmax, right,
      hrightBound, hleftFreeFlag]
  by_cases hrightFreeFlag : isFree[right]? = some 0
  · simp [coalesceIfPossibleArraysOutcome, input, hcapacity, hmax, right,
      hrightBound, hleftFreeFlag, hrightFreeFlag]
  have hleftBound : left < blocks.length := by
    rw [← hphysical.1]
    omega
  have hrightBlocksBound : right < blocks.length := by
    rw [← hphysical.1]
    omega
  let leftBlock := blocks[left]
  let rightBlock := blocks[right]
  have hleftGet : blocks[left]? = some leftBlock :=
    List.getElem?_eq_some_iff.mpr ⟨hleftBound, rfl⟩
  have hrightGet : blocks[right]? = some rightBlock :=
    List.getElem?_eq_some_iff.mpr ⟨hrightBlocksBound, rfl⟩
  have hleftOffset := representsPhysicalArrays_get_offset hphysical hleftGet
  have hleftSize := representsPhysicalArrays_get_size hphysical hleftGet
  have hrightOffset := representsPhysicalArrays_get_offset hphysical hrightGet
  have hrightSize := representsPhysicalArrays_get_size hphysical hrightGet
  have hleftFlag := representsPhysicalArrays_get_free hphysical hleftGet
  have hrightFlag := representsPhysicalArrays_get_free hphysical hrightGet
  have hleftFree : leftBlock.free = true := by
    by_cases hfree : leftBlock.free
    · exact hfree
    · simp [hfree] at hleftFlag
      exact (hleftFreeFlag hleftFlag).elim
  have hrightFree : rightBlock.free = true := by
    by_cases hfree : rightBlock.free
    · exact hfree
    · simp [hfree] at hrightFlag
      exact (hrightFreeFlag hrightFlag).elim
  by_cases hadjacent : leftBlock.offset + leftBlock.bytes ≠ rightBlock.offset
  · simp [coalesceIfPossibleArraysOutcome, input, hcapacity, hmax, right,
      hrightBound, hleftFreeFlag, hrightFreeFlag, hleftOffset, hleftSize,
      hrightOffset, hrightSize, hadjacent]
  have hcan : canCoalesce leftBlock rightBlock :=
    ⟨hleftFree, hrightFree, Classical.byContradiction (fun h => hadjacent h)⟩
  have hleftMem : leftBlock ∈ blocks :=
    List.mem_iff_getElem?.2 ⟨left, hleftGet⟩
  have hrightMem : rightBlock ∈ blocks :=
    List.mem_iff_getElem?.2 ⟨right, hrightGet⟩
  obtain ⟨leftClass, hleftClass, hleftBin, hleftFl, hleftNext,
      hleftPrevious⟩ := represented_free_block_preflight hvalid hsecond hbins
        hleftMem hleftFree
  obtain ⟨rightClass, hrightClass, hrightBin, hrightFl, hrightNext,
      hrightPrevious⟩ := represented_free_block_preflight hvalid hsecond hbins
        hrightMem hrightFree
  obtain ⟨mergedClass, hmergedClass, hmergedBin, hmergedFl⟩ :=
    represented_coalesced_block_preflight hvalid hpoolMax hsecond hbins
      hleftMem hrightMem hcan
  have hphysicalTotal : coalescePhysicalArrays offsets sizes isFree prevFree
      count left ≠ none := by
    apply coalescePhysicalArrays_ne_none_of_preflight
    · exact hphysical.2.1
    · exact hphysical.2.2.1
    · exact hphysical.2.2.2.1
    · exact hphysical.2.2.2.2.1
    · simpa [right] using Nat.lt_of_not_ge hrightBound
    · exact hleftFreeFlag
    · simpa [right] using hrightFreeFlag
    · exact hleftOffset
    · exact hleftSize
    · simpa [right] using hrightOffset
    · simpa [right] using hrightSize
    · simpa only using Classical.byContradiction (fun h => hadjacent h)
  have hcommit := commitCoalesceClassOutcome_ne_failure_of_preflight
    (input := input) (failed := failed) hleftBin hrightBin hmergedBin hleftFl
      hrightFl hmergedFl hleftNext hleftPrevious hrightNext hrightPrevious
      hphysicalTotal
  apply hcommit
  simpa [coalesceIfPossibleArraysOutcome, input, hcapacity, hmax, right,
    hrightBound, hleftFreeFlag, hrightFreeFlag, hleftOffset, hleftSize,
    hrightOffset, hrightSize, hadjacent, hleftClass, hrightClass,
    hmergedClass, hleftBin, hrightBin, hmergedBin, hleftFl, hrightFl,
    hmergedFl, hleftNext, hleftPrevious, hrightNext, hrightPrevious]

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

set_option maxHeartbeats 400000 in
/-- The complete concrete coalescing transaction refines the corresponding
abstract allocator transition, including physical headers and all bin caches. -/
theorem coalesceClassArrays_refines_allocator_append
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat}
    (pre : List Block) (leftBlock rightBlock : Block) (rest : List Block)
    (hcan : canCoalesce leftBlock rightBlock)
    {state abstractNext : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hvalid : Bins.Valid state)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hphysicalInput : RepresentsPhysicalArrays offsets sizes isFree prevFree
      count (pre ++ leftBlock :: rightBlock :: rest))
    (hpair : Dealloc.coalescePair
      { physical := pre ++ leftBlock :: rightBlock :: rest, bins := state }
      pre.length = some
        { physical := coalesceAt (pre ++ leftBlock :: rightBlock :: rest)
            pre.length,
          bins := abstractNext })
    (hsuccess : coalesceClassArrays
      offsets sizes isFree prevFree second first heads next previous count
      pre.length = some result) :
    RepresentsPhysicalArrays result.offsets result.sizes result.isFree
        result.prevFree result.count
        (coalesceAt (pre ++ leftBlock :: rightBlock :: rest) pre.length) ∧
      Bins.Valid abstractNext ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
        abstractNext ∧
      BinsOffsetsDisjoint abstractNext ∧
      RepresentsSecondBitmap result.second abstractNext ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨left, right, leftClass, rightClass, removedLeft, afterLeft,
      removedRight, afterRight, mergedClass, hleft, hright, _,
      hleftClass, hrightClass, hremoveLeftAbstract, hremoveRightAbstract,
      hmergedClass, _, hfinalBins⟩ := Dealloc.coalescePair_result hpair
  have hleftEq : left = leftBlock := by
    have : (pre ++ leftBlock :: rightBlock :: rest)[pre.length]? =
        some leftBlock := by simp
    exact Option.some.inj (hleft.symm.trans this)
  have hrightEq : right = rightBlock := by
    have : (pre ++ leftBlock :: rightBlock :: rest)[pre.length + 1]? =
        some rightBlock := by simp
    exact Option.some.inj (hright.symm.trans this)
  subst left
  subst right
  obtain ⟨leftOffset, rightOffset, leftSize, rightSize, leftBin, rightBin,
      withoutLeft, withoutRight, physical, mergedSize, mergedBin, inserted,
      hleftOffset, hrightOffset, hleftSize, hrightSize, hleftBin,
      hrightBin, hremoveLeft, hremoveRight, hphysicalStep, hmergedSize,
      hmergedBin, hinsert, hoffsets, hsizes, hisFree, hprevFree, hcount,
      hsecondResult, hfirstResult, hheads, hnext, hprevious⟩ :=
    coalesceClassArrays_result hsuccess
  have hphysical := coalescePhysicalArrays_refines_represented_append pre
    leftBlock rightBlock rest hphysicalInput hcan hphysicalStep
  have hleftOffsetEq : leftOffset = leftBlock.offset := by
    have hget : (pre ++ leftBlock :: rightBlock :: rest)[pre.length]? =
        some leftBlock := by simp
    exact Option.some.inj (hleftOffset.symm.trans
      (representsPhysicalArrays_get_offset hphysicalInput hget))
  have hrightOffsetEq : rightOffset = rightBlock.offset := by
    have hget : (pre ++ leftBlock :: rightBlock :: rest)[pre.length + 1]? =
        some rightBlock := by simp
    exact Option.some.inj (hrightOffset.symm.trans
      (representsPhysicalArrays_get_offset hphysicalInput hget))
  have hleftSizeEq : leftSize = leftBlock.bytes := by
    have hget : (pre ++ leftBlock :: rightBlock :: rest)[pre.length]? =
        some leftBlock := by simp
    exact Option.some.inj (hleftSize.symm.trans
      (representsPhysicalArrays_get_size hphysicalInput hget))
  have hrightSizeEq : rightSize = rightBlock.bytes := by
    have hget : (pre ++ leftBlock :: rightBlock :: rest)[pre.length + 1]? =
        some rightBlock := by simp
    exact Option.some.inj (hrightSize.symm.trans
      (representsPhysicalArrays_get_size hphysicalInput hget))
  subst leftOffset
  subst rightOffset
  subst leftSize
  subst rightSize
  obtain ⟨leftRuntimeClass, hleftRuntimeClass, hleftEncoded⟩ :=
    classifySizeBin_refines_block hleftBin
  have hleftClassEq : leftRuntimeClass = leftClass :=
    Option.some.inj (hleftRuntimeClass.symm.trans hleftClass)
  subst leftRuntimeClass
  obtain ⟨rightRuntimeClass, hrightRuntimeClass, hrightEncoded⟩ :=
    classifySizeBin_refines_block hrightBin
  have hrightClassEq : rightRuntimeClass = rightClass :=
    Option.some.inj (hrightRuntimeClass.symm.trans hrightClass)
  subst rightRuntimeClass
  have hphysicalArrays := coalescePhysicalArrays_refines_represented_append pre
    leftBlock rightBlock rest hphysicalInput hcan hphysicalStep
  have hmergedGet :
      (coalesceAt (pre ++ leftBlock :: rightBlock :: rest) pre.length)[pre.length]? =
        some (coalesceBlocks leftBlock rightBlock) := by
    rw [coalesceAt_append_pair]
    simp
  have hmergedConcrete := representsPhysicalArrays_get_size hphysicalArrays
    hmergedGet
  have hmergedSizeEq : mergedSize = (coalesceBlocks leftBlock rightBlock).bytes :=
    Option.some.inj (hmergedSize.symm.trans hmergedConcrete)
  subst mergedSize
  obtain ⟨mergedRuntimeClass, hmergedRuntimeClass, hmergedEncoded⟩ :=
    classifySizeBin_refines_block hmergedBin
  have hmergedClassEq : mergedRuntimeClass = mergedClass :=
    Option.some.inj (hmergedRuntimeClass.symm.trans hmergedClass)
  subst mergedRuntimeClass
  obtain ⟨leftReplacement, hleftRemoveList, hafterLeft⟩ :=
    Bins.removeOffset_success hremoveLeftAbstract
  subst afterLeft
  obtain ⟨rightReplacement, hrightRemoveList, hafterRight⟩ :=
    Bins.removeOffset_success hremoveRightAbstract
  subst afterRight
  have hleftAbsent := removeOffset_absent_everywhere hvalid hdisjoint
    hleftRemoveList
  have hleftStillAbsent := removeOffset_preserves_global_absence hleftAbsent
    hrightRemoveList
  have hmergedFresh : ∀ query,
      (coalesceBlocks leftBlock rightBlock).offset ∉
        (((state.replaceChain leftClass leftReplacement).replaceChain
          rightClass rightReplacement).chains query).map Block.offset := by
    simpa [coalesceBlocks] using hleftStillAbsent
  have hbelongs : Bins.Belongs mergedClass
      (coalesceBlocks leftBlock rightBlock) :=
    Bins.classifyBlock?_result hmergedClass
  have hsteps := removeRemoveInsert_refines
    (merged := coalesceBlocks leftBlock rightBlock)
    hvalid hsecond hfirst hbins
    hdisjoint hleftEncoded hrightEncoded hmergedEncoded rfl
    hremoveLeftAbstract hremoveRightAbstract hbelongs hmergedFresh
    hremoveLeft hremoveRight hinsert
  have hfinalBins' : abstractNext =
      ((state.replaceChain leftClass leftReplacement).replaceChain
        rightClass rightReplacement).insert mergedClass
          (coalesceBlocks leftBlock rightBlock) := by
    simpa using hfinalBins
  dsimp only at hsteps
  rw [← hfinalBins'] at hsteps
  simpa [hoffsets, hsizes, hisFree, hprevFree, hcount, hsecondResult,
    hfirstResult, hheads, hnext, hprevious] using
    And.intro hphysical hsteps

set_option maxHeartbeats 500000 in
/-- A successful conditional concrete coalescing call refines the abstract
identity-or-coalesce transition. The backing arrays may contain inactive spare
capacity, so this theorem composes across consecutive coalescing calls. -/
theorem coalesceIfPossibleArrays_refines_allocator_append
    {pool : Luffs.Memory.Region}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat}
    (pre : List Block) (leftBlock rightBlock : Block) (rest : List Block)
    {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hallocValid : Alloc.Valid pool
      { physical := pre ++ leftBlock :: rightBlock :: rest, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hphysicalInput : RepresentsPhysicalArrays offsets sizes isFree prevFree
      count (pre ++ leftBlock :: rightBlock :: rest))
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hsuccess : coalesceIfPossibleArrays offsets sizes isFree prevFree second
      first heads next previous count pre.length = some result) :
    ∃ abstractNext,
      Dealloc.coalesceIfPossible
          { physical := pre ++ leftBlock :: rightBlock :: rest, bins := state }
          pre.length = some abstractNext ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count abstractNext.physical ∧
      Bins.Valid abstractNext.bins ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
          abstractNext.bins ∧
      BinsOffsetsDisjoint abstractNext.bins ∧
      RepresentsSecondBitmap result.second abstractNext.bins ∧
      FirstBitmapRep result.first result.second := by
  have hbounds : ¬(count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length) := by
    have := hphysicalInput.2.1
    have := hphysicalInput.2.2.1
    have := hphysicalInput.2.2.2.1
    have := hphysicalInput.2.2.2.2.1
    omega
  have hleftNotMax : pre.length ≠ usizeMax := by
    have := hphysicalInput.1
    simp only [List.length_append, List.length_cons] at this
    omega
  have hrightBound : ¬pre.length + 1 ≥ count := by
    rw [hphysicalInput.1]
    simp
  have hleftGet : (pre ++ leftBlock :: rightBlock :: rest)[pre.length]? =
      some leftBlock := by simp
  have hrightGet :
      (pre ++ leftBlock :: rightBlock :: rest)[pre.length + 1]? =
        some rightBlock := by simp
  have hleftFlag := representsPhysicalArrays_get_free hphysicalInput hleftGet
  have hrightFlag := representsPhysicalArrays_get_free hphysicalInput hrightGet
  have hleftOffset := representsPhysicalArrays_get_offset hphysicalInput hleftGet
  have hrightOffset := representsPhysicalArrays_get_offset hphysicalInput hrightGet
  have hleftSize := representsPhysicalArrays_get_size hphysicalInput hleftGet
  by_cases hcan : canCoalesce leftBlock rightBlock
  · rcases hcan with ⟨hleftFree, hrightFree, hadjacent⟩
    have hclassSuccess : coalesceClassArrays offsets sizes isFree prevFree
        second first heads next previous count pre.length = some result := by
      unfold coalesceIfPossibleArrays at hsuccess
      simp only [hbounds, if_false, hleftNotMax, hrightBound,
        hleftFlag, hrightFlag, hleftFree, hrightFree, hleftOffset, hleftSize,
        hrightOffset, hadjacent, ne_eq, not_true_eq_false] at hsuccess
      exact hsuccess
    obtain ⟨abstractNext, hpair⟩ := Dealloc.coalescePair_complete hallocValid
      hpoolMax hleftGet hrightGet ⟨hleftFree, hrightFree, hadjacent⟩
    have hconditional : Dealloc.coalesceIfPossible
        { physical := pre ++ leftBlock :: rightBlock :: rest, bins := state }
        pre.length = some abstractNext := by
      simp [Dealloc.coalesceIfPossible, hleftGet, hrightGet, hleftFree,
        hrightFree, hadjacent, hpair, canCoalesce]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hphysicalNext, _⟩ := Dealloc.coalescePair_result hpair
    cases abstractNext with
    | mk abstractPhysical abstractBins =>
        change abstractPhysical = coalesceAt
          (pre ++ leftBlock :: rightBlock :: rest) pre.length at hphysicalNext
        subst abstractPhysical
        have hrefine := coalesceClassArrays_refines_allocator_append pre
          leftBlock rightBlock rest ⟨hleftFree, hrightFree, hadjacent⟩
          (hvalid := hallocValid.2.1) hsecond hfirst hbins hdisjoint
          hphysicalInput hpair hclassSuccess
        let final : Alloc.State := {
          physical := coalesceAt
            (pre ++ leftBlock :: rightBlock :: rest) pre.length
          bins := abstractBins }
        exact ⟨final, by simpa [final] using hconditional, by
          simpa [final] using hrefine⟩
  · have hresult : result = allocatorArrays offsets sizes isFree prevFree
        second first heads next previous count := by
      unfold coalesceIfPossibleArrays at hsuccess
      rw [if_neg hbounds, if_neg hleftNotMax, if_neg hrightBound]
        at hsuccess
      rw [hleftFlag, hrightFlag, hleftOffset, hleftSize, hrightOffset]
        at hsuccess
      cases hleftFree : leftBlock.free
      · simpa [hleftFree] using hsuccess.symm
      · cases hrightFree : rightBlock.free
        · simpa [hleftFree, hrightFree] using hsuccess.symm
        · have hadjacent : leftBlock.offset + leftBlock.bytes ≠
              rightBlock.offset := by
            intro heq
            apply hcan
            exact ⟨hleftFree, hrightFree, heq.symm⟩
          simpa [hleftFree, hrightFree, hadjacent] using hsuccess.symm
    subst result
    let original : Alloc.State :=
      { physical := pre ++ leftBlock :: rightBlock :: rest, bins := state }
    have hconditional : Dealloc.coalesceIfPossible original pre.length =
        some original := by
      simp [Dealloc.coalesceIfPossible, original, hcan]
    refine ⟨original, hconditional, ?_⟩
    change RepresentsPhysicalArrays offsets sizes isFree prevFree count
        (pre ++ leftBlock :: rightBlock :: rest) ∧
      Bins.Valid state ∧ RepresentsBins (Metadata.mk heads next previous) state ∧
      BinsOffsetsDisjoint state ∧ RepresentsSecondBitmap second state ∧
      FirstBitmapRep first second
    exact ⟨hphysicalInput, hallocValid.2.1, hbins, hdisjoint, hsecond, hfirst⟩

theorem exists_append_pair_of_getElem?
    {α : Type} {values : List α} {i : Nat} {left right : α}
    (hleft : values[i]? = some left)
    (hright : values[i + 1]? = some right) :
    ∃ pre rest, values = pre ++ left :: right :: rest ∧ pre.length = i := by
  induction values generalizing i with
  | nil => simp at hleft
  | cons head tail ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
          subst head
          cases tail with
          | nil => simp at hright
          | cons next rest =>
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                Option.some.injEq] at hright
              subst next
              exact ⟨[], rest, by simp⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hleft
          have hright' : tail[j + 1]? = some right := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hright
          obtain ⟨pre, rest, htail, hlen⟩ := ih hleft hright'
          exact ⟨head :: pre, rest, by simp [htail], by simp [hlen]⟩

set_option maxHeartbeats 600000 in
/-- Arbitrary-index form of conditional coalescing refinement. Missing
neighbors are proved to be identity transitions; an existing adjacent pair is
delegated to `coalesceIfPossibleArrays_refines_allocator_append`. -/
theorem coalesceIfPossibleArrays_refines_allocator
    {pool : Luffs.Memory.Region} {blocks : List Block}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hphysicalInput : RepresentsPhysicalArrays offsets sizes isFree prevFree
      count blocks)
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hsuccess : coalesceIfPossibleArrays offsets sizes isFree prevFree second
      first heads next previous count i = some result) :
    ∃ abstractNext,
      Dealloc.coalesceIfPossible { physical := blocks, bins := state } i =
          some abstractNext ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count abstractNext.physical ∧
      Bins.Valid abstractNext.bins ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
          abstractNext.bins ∧
      BinsOffsetsDisjoint abstractNext.bins ∧
      RepresentsSecondBitmap result.second abstractNext.bins ∧
      FirstBitmapRep result.first result.second := by
  have hbounds : ¬(count > offsets.length ∨ count > sizes.length ∨
      count > isFree.length ∨ count > prevFree.length) := by
    have := hphysicalInput.2.1
    have := hphysicalInput.2.2.1
    have := hphysicalInput.2.2.2.1
    have := hphysicalInput.2.2.2.2.1
    omega
  cases hleft : blocks[i]? with
  | none =>
      have hi : count ≤ i := by
        rw [hphysicalInput.1]
        exact List.getElem?_eq_none_iff.mp hleft
      have hresult : result = allocatorArrays offsets sizes isFree prevFree
          second first heads next previous count := by
        unfold coalesceIfPossibleArrays at hsuccess
        rw [if_neg hbounds] at hsuccess
        by_cases hmax : i = usizeMax
        · simpa [hmax] using hsuccess.symm
        · have hright : i + 1 ≥ count := by omega
          simpa [hmax, hright] using hsuccess.symm
      subst result
      let original : Alloc.State := { physical := blocks, bins := state }
      have habstract : Dealloc.coalesceIfPossible original i = some original := by
        simp [Dealloc.coalesceIfPossible, original, hleft]
      refine ⟨original, habstract, ?_⟩
      change RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks ∧
        Bins.Valid state ∧ RepresentsBins (Metadata.mk heads next previous) state ∧
        BinsOffsetsDisjoint state ∧ RepresentsSecondBitmap second state ∧
        FirstBitmapRep first second
      exact ⟨hphysicalInput, hallocValid.2.1, hbins, hdisjoint, hsecond, hfirst⟩
  | some leftBlock =>
      cases hright : blocks[i + 1]? with
      | none =>
          have hrightBound : i + 1 ≥ count := by
            rw [hphysicalInput.1]
            exact List.getElem?_eq_none_iff.mp hright
          have hresult : result = allocatorArrays offsets sizes isFree prevFree
              second first heads next previous count := by
            unfold coalesceIfPossibleArrays at hsuccess
            rw [if_neg hbounds] at hsuccess
            by_cases hmax : i = usizeMax
            · simpa [hmax] using hsuccess.symm
            · simpa [hmax, hrightBound] using hsuccess.symm
          subst result
          let original : Alloc.State := { physical := blocks, bins := state }
          have habstract : Dealloc.coalesceIfPossible original i =
              some original := by
            simp [Dealloc.coalesceIfPossible, original, hleft, hright]
          refine ⟨original, habstract, ?_⟩
          change RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks ∧
            Bins.Valid state ∧
            RepresentsBins (Metadata.mk heads next previous) state ∧
            BinsOffsetsDisjoint state ∧ RepresentsSecondBitmap second state ∧
            FirstBitmapRep first second
          exact ⟨hphysicalInput, hallocValid.2.1, hbins, hdisjoint, hsecond, hfirst⟩
      | some rightBlock =>
          obtain ⟨pre, rest, hblocks, hlen⟩ :=
            exists_append_pair_of_getElem? hleft hright
          subst blocks
          subst i
          exact coalesceIfPossibleArrays_refines_allocator_append pre leftBlock
            rightBlock rest hallocValid hpoolMax hphysicalInput hcountMax
            hsecond hfirst hbins hdisjoint hsuccess

theorem coalesceIfPossibleArraysOutcome_refines_allocator
    {pool : Luffs.Memory.Region} {blocks : List Block}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hsuccess : coalesceIfPossibleArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count i = .success result) :
    ∃ abstractNext,
      Dealloc.coalesceIfPossible { physical := blocks, bins := state } i =
          some abstractNext ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count abstractNext.physical ∧
      Bins.Valid abstractNext.bins ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
          abstractNext.bins ∧
      BinsOffsetsDisjoint abstractNext.bins ∧
      RepresentsSecondBitmap result.second abstractNext.bins ∧
      FirstBitmapRep result.first result.second := by
  apply coalesceIfPossibleArrays_refines_allocator hallocValid hpoolMax hphysical
    hcountMax hsecond hfirst hbins hdisjoint
  exact coalesceIfPossibleArraysOutcome_success_refines_option hsuccess

theorem coalesceClassArrays_complete_refinement
    (pool : Luffs.Memory.Region) (pre : List Block)
    (leftBlock rightBlock : Block) (rest : List Block)
    (hcan : canCoalesce leftBlock rightBlock)
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    {state : Bins.State}
    (hallocValid : Alloc.Valid pool
      { physical := pre ++ leftBlock :: rightBlock :: rest, bins := state })
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hsuccess : coalesceClassArrays
      (blockOffsets (pre ++ leftBlock :: rightBlock :: rest))
      (blockSizes (pre ++ leftBlock :: rightBlock :: rest))
      (freeFlags (pre ++ leftBlock :: rightBlock :: rest))
      (prevFreeFlags (pre ++ leftBlock :: rightBlock :: rest))
      second first heads next previous
      (pre ++ leftBlock :: rightBlock :: rest).length pre.length = some result) :
    ∃ abstractNext,
      Dealloc.coalescePair
          { physical := pre ++ leftBlock :: rightBlock :: rest, bins := state }
          pre.length = some abstractNext ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count abstractNext.physical ∧
      Bins.Valid abstractNext.bins ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
        abstractNext.bins ∧
      BinsOffsetsDisjoint abstractNext.bins ∧
      RepresentsSecondBitmap result.second abstractNext.bins ∧
      FirstBitmapRep result.first result.second := by
  have hleft : (pre ++ leftBlock :: rightBlock :: rest)[pre.length]? =
      some leftBlock := by simp
  have hright : (pre ++ leftBlock :: rightBlock :: rest)[pre.length + 1]? =
      some rightBlock := by simp
  obtain ⟨abstractNext, hpair⟩ := Dealloc.coalescePair_complete hallocValid
    hpoolMax hleft hright hcan
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hphysicalNext, _⟩ := Dealloc.coalescePair_result hpair
  cases abstractNext with
  | mk abstractPhysical abstractBins =>
      change abstractPhysical = coalesceAt
        (pre ++ leftBlock :: rightBlock :: rest) pre.length at hphysicalNext
      subst abstractPhysical
      have hrefine := coalesceClassArrays_refines_allocator_append pre leftBlock
        rightBlock rest hcan (hvalid := hallocValid.2.1) hsecond hfirst hbins
        hdisjoint (canonical_representsPhysicalArrays _) hpair hsuccess
      let final : Alloc.State := {
        physical := coalesceAt (pre ++ leftBlock :: rightBlock :: rest) pre.length
        bins := abstractBins }
      refine ⟨final, ?_, ?_⟩
      · simpa [final] using hpair
      · simpa [final] using hrefine

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

structure DeallocateMachineState where
  isFree : List (Fin 256)
  prevFree : List (Fin 256)
  second : List (BitVec 32)
  first : BitVec 64
  heads : List Nat
  next : List Nat
  previous : List Nat
deriving DecidableEq, Repr

inductive DeallocateUncoalescedOutcome where
  | success (state : DeallocateMachineState)
  | failure (state : DeallocateMachineState)
deriving DecidableEq, Repr

def deallocateInputState (isFree prevFree : List (Fin 256))
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) : DeallocateMachineState :=
  ⟨isFree, prevFree, second, first, heads, next, previous⟩

def deallocateStateAfterMark (marked : List (Fin 256) × List (Fin 256))
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) : DeallocateMachineState :=
  ⟨marked.1, marked.2, second, first, heads, next, previous⟩

/-- Mutation phase of uncoalesced deallocation after all source preflights.
Its explicit failure states expose whether a supposedly impossible failure
would occur before or after physical flag mutation. -/
def commitDeallocateUncoalescedOutcome (input : DeallocateMachineState)
    (offsets sizes : List Nat) (isFree prevFree : List (Fin 256))
    (second : List (BitVec 32)) (first : BitVec 64)
    (heads next previous : List Nat) (block returnedOffset returnedBytes bin : Nat) :
    DeallocateUncoalescedOutcome :=
  match markFreeArrays offsets sizes isFree prevFree block returnedOffset
      returnedBytes with
  | none => .failure input
  | some marked =>
    match insertClassArrays second first heads next previous bin returnedOffset with
    | none => .failure
        (deallocateStateAfterMark marked second first heads next previous)
    | some inserted => .success
        ⟨marked.1, marked.2, inserted.second, inserted.first, inserted.heads,
          inserted.next, inserted.previous⟩

/-- Once the source preflight facts establish totality of both component
operations, the uncoalesced mutation phase has no failure edge at all. -/
theorem commitDeallocateUncoalescedOutcome_ne_failure
    {input failed : DeallocateMachineState}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {block returnedOffset returnedBytes bin : Nat}
    (hmark : markFreeArrays offsets sizes isFree prevFree block returnedOffset
      returnedBytes ≠ none)
    (hinsert : insertClassArrays second first heads next previous bin
      returnedOffset ≠ none) :
    commitDeallocateUncoalescedOutcome input offsets sizes isFree prevFree
      second first heads next previous block returnedOffset returnedBytes bin ≠
        .failure failed := by
  unfold commitDeallocateUncoalescedOutcome
  cases hmarkEq : markFreeArrays offsets sizes isFree prevFree block
      returnedOffset returnedBytes with
  | none => exact (hmark hmarkEq).elim
  | some marked =>
    simp only [hmarkEq]
    cases hinsertEq : insertClassArrays second first heads next previous bin
        returnedOffset with
    | none => exact (hinsert hinsertEq).elim
    | some inserted => simp

/-- Stateful semantics of the complete uncoalesced source transaction. The
guards are the checks hoisted by `tlsf_deallocate_uncoalesced` before its first
write. -/
def deallocateUncoalescedArraysOutcome (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count block returnedOffset returnedBytes : Nat) :
    DeallocateUncoalescedOutcome :=
  let input := deallocateInputState isFree prevFree second first heads next previous
  let bad := count > offsets.length ∨ count > sizes.length ∨
    count > isFree.length ∨ count > prevFree.length ∨ block ≥ count ∨
    block ≥ offsets.length ∨ block ≥ sizes.length ∨
    block ≥ isFree.length ∨ block ≥ prevFree.length ∨
    isFree[block]? != some 0 ∨ offsets[block]? != some returnedOffset ∨
    sizes[block]? != some returnedBytes
  if bad then .failure input
  else match classifySizeBin returnedBytes with
  | none => .failure input
  | some bin =>
    if bin ≥ heads.length ∨ bin / secondLevelCount ≥ second.length ∨
        returnedOffset ≥ next.length ∨ returnedOffset ≥ previous.length then
      .failure input
    else commitDeallocateUncoalescedOutcome input offsets sizes isFree prevFree
      second first heads next previous block returnedOffset returnedBytes bin

/-- Public uncoalesced deallocation is transactional: failure returns the
exact complete mutable metadata state supplied by the caller. -/
theorem deallocateUncoalescedArraysOutcome_failure_eq_input
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count block returnedOffset returnedBytes : Nat}
    {failed : DeallocateMachineState}
    (hfailure : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count block returnedOffset returnedBytes =
        .failure failed) :
    failed = deallocateInputState isFree prevFree second first heads next previous := by
  let input := deallocateInputState isFree prevFree second first heads next previous
  let bad := count > offsets.length ∨ count > sizes.length ∨
    count > isFree.length ∨ count > prevFree.length ∨ block ≥ count ∨
    block ≥ offsets.length ∨ block ≥ sizes.length ∨
    block ≥ isFree.length ∨ block ≥ prevFree.length ∨
    isFree[block]? != some 0 ∨ offsets[block]? != some returnedOffset ∨
    sizes[block]? != some returnedBytes
  by_cases hbad : bad
  · simpa [deallocateUncoalescedArraysOutcome, input, bad, hbad] using
      hfailure.symm
  cases hclass : classifySizeBin returnedBytes with
  | none =>
      simpa [deallocateUncoalescedArraysOutcome, input, bad, hbad, hclass] using
        hfailure.symm
  | some bin =>
    let insertionBad := bin ≥ heads.length ∨
      bin / secondLevelCount ≥ second.length ∨
      returnedOffset ≥ next.length ∨ returnedOffset ≥ previous.length
    by_cases hinsertionBad : insertionBad
    · simpa [deallocateUncoalescedArraysOutcome, input, bad, hbad, hclass,
        insertionBad, hinsertionBad] using hfailure.symm
    have hmark : markFreeArrays offsets sizes isFree prevFree block
        returnedOffset returnedBytes ≠ none := by
      apply markFreeArrays_ne_none_of_preflight
      all_goals simp only [bad] at hbad
      · omega
      · omega
      · omega
      · omega
      · apply Classical.byContradiction; intro h; exact hbad (by aesop)
      · apply Classical.byContradiction; intro h; exact hbad (by aesop)
      · apply Classical.byContradiction; intro h; exact hbad (by aesop)
    have hinsert : insertClassArrays second first heads next previous bin
        returnedOffset ≠ none := by
      apply insertClassArrays_ne_none_of_preflight
      all_goals simp only [insertionBad] at hinsertionBad
      all_goals omega
    exact (commitDeallocateUncoalescedOutcome_ne_failure hmark hinsert (by
      simpa [deallocateUncoalescedArraysOutcome, input, bad, hbad, hclass,
        insertionBad, hinsertionBad] using hfailure)).elim

theorem deallocateUncoalescedArraysOutcome_failure_preserves_frame
    {PROP : Type} [Iris.BI PROP]
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count block returnedOffset returnedBytes : Nat}
    {failed : DeallocateMachineState} (frame : PROP)
    (hfailure : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count block returnedOffset returnedBytes =
        .failure failed) :
    failed = deallocateInputState isFree prevFree second first heads next previous ∧
      (frame ∗ (emp : PROP) ⊣⊢ frame) := by
  exact ⟨deallocateUncoalescedArraysOutcome_failure_eq_input hfailure, sep_emp⟩

/-- A successful state-retaining uncoalesced execution exposes the exact two
component calls used by the older refinement transformer. This is the bridge
needed to reuse its physical/bin invariant and Iris ownership proofs. -/
theorem deallocateUncoalescedArraysOutcome_success_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count block returnedOffset returnedBytes : Nat}
    {state : DeallocateMachineState}
    (hsuccess : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count block returnedOffset returnedBytes =
        .success state) :
    ∃ marked bin inserted,
      markFreeArrays offsets sizes isFree prevFree block returnedOffset
          returnedBytes = some marked ∧
      classifySizeBin returnedBytes = some bin ∧
      insertClassArrays second first heads next previous bin returnedOffset =
          some inserted ∧
      state = ⟨marked.1, marked.2, inserted.second, inserted.first,
        inserted.heads, inserted.next, inserted.previous⟩ := by
  unfold deallocateUncoalescedArraysOutcome at hsuccess
  split at hsuccess <;> try contradiction
  next =>
    split at hsuccess <;> try contradiction
    next bin hclass =>
      split at hsuccess <;> try contradiction
      next =>
        unfold commitDeallocateUncoalescedOutcome at hsuccess
        cases hmark : markFreeArrays offsets sizes isFree prevFree block
            returnedOffset returnedBytes with
        | none => simp [hmark] at hsuccess
        | some marked =>
          cases hinsert : insertClassArrays second first heads next previous bin
              returnedOffset with
          | none => simp [hmark, hinsert] at hsuccess
          | some inserted =>
            simp [hmark, hinsert] at hsuccess
            subst state
            exact ⟨marked, bin, inserted, hmark, hclass, hinsert, rfl⟩

/-- Successful stateful execution is also a successful execution of the exact
`Option` transformer consumed by the existing allocator refinement theorems. -/
theorem deallocateUncoalescedArraysOutcome_success_refines_option
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count block returnedOffset returnedBytes : Nat}
    {state : DeallocateMachineState}
    (hsuccess : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count block returnedOffset returnedBytes =
        .success state) :
    ∃ result,
      deallocateUncoalescedArrays offsets sizes isFree prevFree second first heads
          next previous count block returnedOffset returnedBytes = some result ∧
      result.isFree = state.isFree ∧ result.prevFree = state.prevFree ∧
      result.insertion.second = state.second ∧
      result.insertion.first = state.first ∧
      result.insertion.heads = state.heads ∧
      result.insertion.next = state.next ∧
      result.insertion.previous = state.previous := by
  obtain ⟨marked, bin, inserted, hmark, hclass, hinsert, rfl⟩ :=
    deallocateUncoalescedArraysOutcome_success_result hsuccess
  have hbounds : count ≤ offsets.length ∧ count ≤ sizes.length ∧
      count ≤ isFree.length ∧ count ≤ prevFree.length ∧ block < count := by
    unfold deallocateUncoalescedArraysOutcome at hsuccess
    split at hsuccess
    · contradiction
    · rename_i hbad
      simp only at hbad
      omega
  let result : DeallocateUncoalescedResult :=
    ⟨marked.1, marked.2, inserted⟩
  refine ⟨result, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [deallocateUncoalescedArrays, hbounds, hmark, hclass, hinsert, result]

/-- Exact pure semantics of the public Luffs deallocator. -/
def deallocateArrays (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count block returnedOffset returnedBytes : Nat) :
    Option CoalesceClassResult := do
  let marked ← deallocateUncoalescedArrays offsets sizes isFree prevFree second
    first heads next previous count block returnedOffset returnedBytes
  let afterRight ← coalesceIfPossibleArrays offsets sizes marked.isFree
    marked.prevFree marked.insertion.second marked.insertion.first
    marked.insertion.heads marked.insertion.next marked.insertion.previous
    count block
  if block = 0 then return afterRight
  let afterLeft ← coalesceIfPossibleArrays afterRight.offsets afterRight.sizes
    afterRight.isFree afterRight.prevFree afterRight.second afterRight.first
    afterRight.heads afterRight.next afterRight.previous afterRight.count
    (block - 1)
  return afterLeft

inductive DeallocateOutcome where
  | success (state : CoalesceClassResult)
  | failure (state : CoalesceClassResult)
deriving DecidableEq, Repr

def deallocateStateFromUncoalesced (offsets sizes : List Nat) (count : Nat)
    (state : DeallocateMachineState) : CoalesceClassResult :=
  ⟨offsets, sizes, state.isFree, state.prevFree, count, state.second,
    state.first, state.heads, state.next, state.previous⟩

/-- Stateful semantics of the public sequential deallocator. Unlike the
`Option` refinement model, failures retain the exact state at each call
boundary, making a late failure observably distinct from an early rejection. -/
def deallocateArraysOutcome (offsets sizes : List Nat)
    (isFree prevFree : List (Fin 256)) (second : List (BitVec 32))
    (first : BitVec 64) (heads next previous : List Nat)
    (count block returnedOffset returnedBytes : Nat) : DeallocateOutcome :=
  match deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree second
      first heads next previous count block returnedOffset returnedBytes with
  | .failure failed => .failure
      (deallocateStateFromUncoalesced offsets sizes count failed)
  | .success marked =>
    match coalesceIfPossibleArraysOutcome offsets sizes marked.isFree
        marked.prevFree marked.second marked.first marked.heads marked.next
        marked.previous count block with
    | .failure failed => .failure failed
    | .success afterRight =>
      if block = 0 then .success afterRight
      else match coalesceIfPossibleArraysOutcome afterRight.offsets
          afterRight.sizes afterRight.isFree afterRight.prevFree afterRight.second
          afterRight.first afterRight.heads afterRight.next afterRight.previous
          afterRight.count (block - 1) with
      | .failure failed => .failure failed
      | .success afterLeft => .success afterLeft

/-- Compositional public transactionality theorem. The two totality premises
are deliberately stated at the actual intermediate states; later the complete
allocator invariant discharges them for both optional coalescing calls. -/
theorem deallocateArraysOutcome_failure_eq_input_of_coalesces_total
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count block returnedOffset returnedBytes : Nat}
    {failed : CoalesceClassResult}
    (hright : ∀ marked,
      deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree second
          first heads next previous count block returnedOffset returnedBytes =
        .success marked →
      ∀ failedRight, coalesceIfPossibleArraysOutcome offsets sizes
        marked.isFree marked.prevFree marked.second marked.first marked.heads
        marked.next marked.previous count block ≠ .failure failedRight)
    (hleft : ∀ marked afterRight,
      deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree second
          first heads next previous count block returnedOffset returnedBytes =
        .success marked →
      coalesceIfPossibleArraysOutcome offsets sizes marked.isFree marked.prevFree
          marked.second marked.first marked.heads marked.next marked.previous
          count block = .success afterRight → block ≠ 0 →
      ∀ failedLeft, coalesceIfPossibleArraysOutcome afterRight.offsets
        afterRight.sizes afterRight.isFree afterRight.prevFree afterRight.second
        afterRight.first afterRight.heads afterRight.next afterRight.previous
        afterRight.count (block - 1) ≠ .failure failedLeft)
    (hfailure : deallocateArraysOutcome offsets sizes isFree prevFree second first
      heads next previous count block returnedOffset returnedBytes =
        .failure failed) :
    failed = allocatorArrays offsets sizes isFree prevFree second first heads next
      previous count := by
  unfold deallocateArraysOutcome at hfailure
  cases hunco : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count block returnedOffset returnedBytes with
  | failure rejected =>
      simp only [hunco, DeallocateOutcome.failure.injEq] at hfailure
      subst failed
      have hrejected :=
        deallocateUncoalescedArraysOutcome_failure_eq_input hunco
      subst rejected
      rfl
  | success marked =>
    simp only [hunco] at hfailure
    cases hrightOutcome : coalesceIfPossibleArraysOutcome offsets sizes
        marked.isFree marked.prevFree marked.second marked.first marked.heads
        marked.next marked.previous count block with
    | failure failedRight => exact (hright marked hunco failedRight
        hrightOutcome).elim
    | success afterRight =>
      simp only [hrightOutcome] at hfailure
      by_cases hblock : block = 0
      · simp [hblock] at hfailure
      · simp only [hblock, if_false] at hfailure
        cases hleftOutcome : coalesceIfPossibleArraysOutcome afterRight.offsets
            afterRight.sizes afterRight.isFree afterRight.prevFree
            afterRight.second afterRight.first afterRight.heads afterRight.next
            afterRight.previous afterRight.count (block - 1) with
        | failure failedLeft => exact (hleft marked afterRight hunco hrightOutcome
            hblock failedLeft hleftOutcome).elim
        | success afterLeft => simp [hleftOutcome] at hfailure

theorem deallocateArraysOutcome_failure_preserves_frame_of_coalesces_total
    {PROP : Type} [Iris.BI PROP]
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count block returnedOffset returnedBytes : Nat}
    {failed : CoalesceClassResult} (frame : PROP)
    (hright : ∀ marked,
      deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree second
          first heads next previous count block returnedOffset returnedBytes =
        .success marked →
      ∀ failedRight, coalesceIfPossibleArraysOutcome offsets sizes
        marked.isFree marked.prevFree marked.second marked.first marked.heads
        marked.next marked.previous count block ≠ .failure failedRight)
    (hleft : ∀ marked afterRight,
      deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree second
          first heads next previous count block returnedOffset returnedBytes =
        .success marked →
      coalesceIfPossibleArraysOutcome offsets sizes marked.isFree marked.prevFree
          marked.second marked.first marked.heads marked.next marked.previous
          count block = .success afterRight → block ≠ 0 →
      ∀ failedLeft, coalesceIfPossibleArraysOutcome afterRight.offsets
        afterRight.sizes afterRight.isFree afterRight.prevFree afterRight.second
        afterRight.first afterRight.heads afterRight.next afterRight.previous
        afterRight.count (block - 1) ≠ .failure failedLeft)
    (hfailure : deallocateArraysOutcome offsets sizes isFree prevFree second first
      heads next previous count block returnedOffset returnedBytes =
        .failure failed) :
    failed = allocatorArrays offsets sizes isFree prevFree second first heads next
        previous count ∧ (frame ∗ (emp : PROP) ⊣⊢ frame) := by
  exact ⟨deallocateArraysOutcome_failure_eq_input_of_coalesces_total hright
    hleft hfailure, sep_emp⟩

theorem coalesceIfPossibleArrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {count left : Nat}
    {result : CoalesceClassResult}
    (hsuccess : coalesceIfPossibleArrays offsets sizes isFree prevFree second
      first heads next previous count left = some result) :
    result = allocatorArrays offsets sizes isFree prevFree second first heads
        next previous count ∨
      coalesceClassArrays offsets sizes isFree prevFree second first heads next
        previous count left = some result := by
  unfold coalesceIfPossibleArrays at hsuccess
  split at hsuccess <;> try contradiction
  next =>
    split at hsuccess
    next => exact Or.inl (Option.some.inj hsuccess).symm
    next =>
      dsimp only at hsuccess
      split at hsuccess
      next => exact Or.inl (Option.some.inj hsuccess).symm
      next =>
        split at hsuccess
        next => exact Or.inl (Option.some.inj hsuccess).symm
        next =>
          split at hsuccess
          next => exact Or.inl (Option.some.inj hsuccess).symm
          next =>
            split at hsuccess <;> try contradiction
            next leftOffset leftSize rightOffset =>
              split at hsuccess
              next => exact Or.inl (Option.some.inj hsuccess).symm
              next => exact Or.inr hsuccess

theorem deallocateArrays_result
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat}
    {count block returnedOffset returnedBytes : Nat}
    {result : CoalesceClassResult}
    (hsuccess : deallocateArrays offsets sizes isFree prevFree second first heads
      next previous count block returnedOffset returnedBytes = some result) :
    ∃ marked afterRight,
      deallocateUncoalescedArrays offsets sizes isFree prevFree second first heads
          next previous count block returnedOffset returnedBytes = some marked ∧
      coalesceIfPossibleArrays offsets sizes marked.isFree marked.prevFree
          marked.insertion.second marked.insertion.first marked.insertion.heads
          marked.insertion.next marked.insertion.previous count block =
        some afterRight ∧
      ((block = 0 ∧ result = afterRight) ∨
        (block ≠ 0 ∧ coalesceIfPossibleArrays afterRight.offsets
          afterRight.sizes afterRight.isFree afterRight.prevFree
          afterRight.second afterRight.first afterRight.heads afterRight.next
          afterRight.previous afterRight.count (block - 1) = some result)) := by
  unfold deallocateArrays at hsuccess
  cases hmarked : deallocateUncoalescedArrays offsets sizes isFree prevFree
      second first heads next previous count block returnedOffset returnedBytes with
  | none => simp [hmarked] at hsuccess
  | some marked =>
      cases hright : coalesceIfPossibleArrays offsets sizes marked.isFree
          marked.prevFree marked.insertion.second marked.insertion.first
          marked.insertion.heads marked.insertion.next marked.insertion.previous
          count block with
      | none => simp [hmarked, hright] at hsuccess
      | some afterRight =>
          rw [hmarked] at hsuccess
          simp [hright] at hsuccess
          by_cases hblock : block = 0
          · have hresult : afterRight = result := by
              simpa [hblock] using hsuccess
            exact ⟨marked, afterRight, rfl, hright,
              Or.inl ⟨hblock, hresult.symm⟩⟩
          · have hlast : coalesceIfPossibleArrays afterRight.offsets
                afterRight.sizes afterRight.isFree afterRight.prevFree
                afterRight.second afterRight.first afterRight.heads
                afterRight.next afterRight.previous afterRight.count
                (block - 1) = some result := by
              simpa [hblock] using hsuccess
            exact ⟨marked, afterRight, rfl, hright, Or.inr ⟨hblock, hlast⟩⟩

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

theorem markFreeAt_length (blocks : List Block) (i : Nat) :
    (markFreeAt blocks i).length = blocks.length := by
  induction blocks generalizing i with
  | nil => simp [markFreeAt]
  | cons head tail ih =>
      cases i <;> cases tail <;> simp [markFreeAt, ih]

theorem blockOffsets_markFreeAt (blocks : List Block) (i : Nat) :
    blockOffsets (markFreeAt blocks i) = blockOffsets blocks := by
  induction blocks generalizing i with
  | nil => simp [markFreeAt, blockOffsets]
  | cons head tail ih =>
      cases i <;> cases tail <;> simp [markFreeAt, blockOffsets]
      exact ih _

theorem blockSizes_markFreeAt (blocks : List Block) (i : Nat) :
    blockSizes (markFreeAt blocks i) = blockSizes blocks := by
  induction blocks generalizing i with
  | nil => simp [markFreeAt, blockSizes]
  | cons head tail ih =>
      cases i <;> cases tail <;> simp [markFreeAt, blockSizes]
      exact ih _

theorem marked_representsPhysicalArrays (blocks : List Block) (i : Nat) :
    RepresentsPhysicalArrays (blockOffsets blocks) (blockSizes blocks)
      (freeFlags (markFreeAt blocks i)) (prevFreeFlags (markFreeAt blocks i))
      blocks.length (markFreeAt blocks i) := by
  refine ⟨(markFreeAt_length blocks i).symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blockOffsets]
  · simp [blockSizes]
  · simp [freeFlags, markFreeAt_length]
  · simp [prevFreeFlags, markFreeAt_length]
  · rw [blockOffsets_markFreeAt]
    exact (canonical_representsPhysicalArrays blocks).2.2.2.2.2.1
  · rw [blockSizes_markFreeAt]
    exact (canonical_representsPhysicalArrays blocks).2.2.2.2.2.2.1
  · simpa [markFreeAt_length] using
      (canonical_representsPhysicalArrays (markFreeAt blocks i)).2.2.2.2.2.2.2.1
  · simpa [markFreeAt_length] using
      (canonical_representsPhysicalArrays (markFreeAt blocks i)).2.2.2.2.2.2.2.2

theorem take_set_of_lt {α : Type} (values : List α) (value : α)
    {count i : Nat} (hi : i < count) :
    (values.set i value).take count = (values.take count).set i value := by
  induction values generalizing count i with
  | nil => simp
  | cons head tail ih =>
      cases count with
      | zero => omega
      | succ count =>
          cases i with
          | zero => simp
          | succ i =>
              simp only [List.set, List.take_succ_cons]
              rw [ih (by omega)]

theorem take_set_of_ge {α : Type} (values : List α) (value : α)
    {count i : Nat} (hi : count ≤ i) :
    (values.set i value).take count = values.take count := by
  induction values generalizing count i with
  | nil => simp
  | cons head tail ih =>
      cases count with
      | zero => simp
      | succ count =>
          cases i with
          | zero => omega
          | succ i =>
              simp only [List.set, List.take_succ_cons, List.cons.injEq, true_and]
              exact ih (by omega)

/-- `markFreeArrays` respects the active-prefix representation used by the
fixed-capacity runtime arrays. A successor boundary-tag write into spare
capacity is intentionally framed out by `take count`. -/
theorem markFreeArrays_refines_represented
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {blocks : List Block} {selected : Block}
    {nextIsFree nextPrevFree : List (Fin 256)}
    (hrep : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hmark : markFreeArrays offsets sizes isFree prevFree i selected.offset
      selected.bytes = some (nextIsFree, nextPrevFree)) :
    RepresentsPhysicalArrays offsets sizes nextIsFree nextPrevFree count
      (markFreeAt blocks i) := by
  obtain ⟨hiOffsets, hiSizes, hiFree, hiPrev, _, _, _, hnextFree,
      hnextPrev⟩ := markFreeArrays_result hmark
  have hiBlocks : i < blocks.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have hiCount : i < count := by simpa [hrep.1] using hiBlocks
  have hcanonical := markFreeArrays_refines_markFreeAt hget hallocated
  obtain ⟨_, _, _, _, _, _, _, hcanonicalFree, hcanonicalPrev⟩ :=
    markFreeArrays_result hcanonical
  refine ⟨by simpa [markFreeAt_length] using hrep.1, hrep.2.1,
    hrep.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hnextFree] using hrep.2.2.2.1
  · rw [hnextPrev]
    split <;> simpa using hrep.2.2.2.2.1
  · simpa [blockOffsets_markFreeAt] using hrep.2.2.2.2.2.1
  · simpa [blockSizes_markFreeAt] using hrep.2.2.2.2.2.2.1
  · rw [hnextFree, take_set_of_lt isFree 1 hiCount,
      hrep.2.2.2.2.2.2.2.1]
    exact hcanonicalFree.symm
  · rw [hnextPrev]
    by_cases hsuccessor : i + 1 < count
    · have hsuccessorArray : i + 1 < prevFree.length :=
        Nat.lt_of_lt_of_le hsuccessor hrep.2.2.2.2.1
      rw [if_pos hsuccessorArray, take_set_of_lt prevFree 1 hsuccessor,
        hrep.2.2.2.2.2.2.2.2]
      rw [if_pos (by simpa [prevFreeFlags, hrep.1] using hsuccessor)] at hcanonicalPrev
      exact hcanonicalPrev.symm
    · have houtside : count ≤ i + 1 := Nat.le_of_not_gt hsuccessor
      have hcanonicalOutside : ¬i + 1 < (prevFreeFlags blocks).length := by
        simpa [prevFreeFlags, hrep.1] using hsuccessor
      rw [if_neg hcanonicalOutside] at hcanonicalPrev
      by_cases hsuccessorArray : i + 1 < prevFree.length
      · rw [if_pos hsuccessorArray, take_set_of_ge prevFree 1 houtside]
        exact hrep.2.2.2.2.2.2.2.2.trans hcanonicalPrev.symm
      · rw [if_neg hsuccessorArray]
        exact hrep.2.2.2.2.2.2.2.2.trans hcanonicalPrev.symm

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
      BinsOffsetsDisjoint (state.insert cls (Dealloc.freedBlock selected)) ∧
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
          exact ⟨cls, habstract, rfl, rfl, hrefine.1, hrefine.2.1,
            insert_preserves_offsets_disjoint hdisjoint
              (by simpa [Dealloc.freedBlock] using hfresh),
            hrefine.2.2.1, hrefine.2.2.2⟩

/-- Active-prefix form of `deallocateUncoalescedArrays_refines`, suitable for
composing deallocation immediately after allocation in fixed-capacity arrays. -/
theorem deallocateUncoalescedArrays_refines_represented
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {blocks : List Block} {i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : DeallocateUncoalescedResult}
    {state : Bins.State}
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hvalid : Bins.Valid state)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hsuccess : deallocateUncoalescedArrays offsets sizes isFree prevFree
      second first heads next previous count i selected.offset selected.bytes =
        some result) :
    ∃ cls,
      classifyBlock? (Dealloc.freedBlock selected) = some cls ∧
      RepresentsPhysicalArrays offsets sizes result.isFree result.prevFree count
        (markFreeAt blocks i) ∧
      Bins.Valid (state.insert cls (Dealloc.freedBlock selected)) ∧
      RepresentsBins
        { heads := result.insertion.heads,
          next := result.insertion.next,
          previous := result.insertion.previous }
        (state.insert cls (Dealloc.freedBlock selected)) ∧
      BinsOffsetsDisjoint (state.insert cls (Dealloc.freedBlock selected)) ∧
      RepresentsSecondBitmap result.insertion.second
        (state.insert cls (Dealloc.freedBlock selected)) ∧
      FirstBitmapRep result.insertion.first result.insertion.second := by
  unfold deallocateUncoalescedArrays at hsuccess
  have hi : i < count := by
    rw [hphysical.1]
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hpre : count ≤ offsets.length ∧ count ≤ sizes.length ∧
      count ≤ isFree.length ∧ count ≤ prevFree.length ∧ i < count :=
    ⟨hphysical.2.1, hphysical.2.2.1, hphysical.2.2.2.1,
      hphysical.2.2.2.2.1, hi⟩
  rw [if_pos hpre] at hsuccess
  cases hmark : markFreeArrays offsets sizes isFree prevFree i
      selected.offset selected.bytes with
  | none => simp [hmark] at hsuccess
  | some marked =>
      cases marked with
      | mk nextIsFree nextPrevFree =>
        cases hclass : classifySizeBin selected.bytes with
        | none => simp [hmark, hclass] at hsuccess
        | some bin =>
          cases hinsert : insertClassArrays second first heads next previous
              bin selected.offset with
          | none => simp [hmark, hclass, hinsert] at hsuccess
          | some insertion =>
            simp [hmark, hclass, hinsert] at hsuccess
            subst result
            obtain ⟨hsize, hmax, hbin, _⟩ := classifySizeBin_result hclass
            let cls := sizeClass selected.bytes hsize hmax
            have habstract : classifyBlock? (Dealloc.freedBlock selected) =
                some cls := by
              simp [classifyBlock?, Dealloc.freedBlock, cls, hsize, hmax]
            have hbelongs : Bins.Belongs cls (Dealloc.freedBlock selected) :=
              classifyBlock?_result habstract
            have hrefine := insertClassArrays_refines_insert
              (inserted := Dealloc.freedBlock selected) hvalid hsecond hfirst
              hbins hdisjoint (by simpa [Dealloc.freedBlock] using hfresh)
              hbelongs (by simp [Dealloc.freedBlock]) hbin hinsert
            have hmarked := markFreeArrays_refines_represented hphysical hget
              hallocated hmark
            exact ⟨cls, habstract, hmarked, hrefine.1, hrefine.2.1,
              insert_preserves_offsets_disjoint hdisjoint
                (by simpa [Dealloc.freedBlock] using hfresh),
              hrefine.2.2.1, hrefine.2.2.2⟩

theorem deallocateUncoalescedArraysOutcome_refines_represented
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count : Nat} {blocks : List Block} {i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {concrete : DeallocateMachineState}
    {state : Bins.State}
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hvalid : Bins.Valid state)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hsuccess : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count i selected.offset selected.bytes =
        .success concrete) :
    ∃ cls,
      classifyBlock? (Dealloc.freedBlock selected) = some cls ∧
      RepresentsPhysicalArrays offsets sizes concrete.isFree concrete.prevFree count
        (markFreeAt blocks i) ∧
      Bins.Valid (state.insert cls (Dealloc.freedBlock selected)) ∧
      RepresentsBins
        { heads := concrete.heads, next := concrete.next,
          previous := concrete.previous }
        (state.insert cls (Dealloc.freedBlock selected)) ∧
      BinsOffsetsDisjoint (state.insert cls (Dealloc.freedBlock selected)) ∧
      RepresentsSecondBitmap concrete.second
        (state.insert cls (Dealloc.freedBlock selected)) ∧
      FirstBitmapRep concrete.first concrete.second := by
  obtain ⟨result, hoption, hfreeEq, hprevEq, hsecondEq, hfirstEq,
      hheadsEq, hnextEq, hpreviousEq⟩ :=
    deallocateUncoalescedArraysOutcome_success_refines_option hsuccess
  obtain ⟨cls, hclass, hphysicalNext, hvalidNext, hbinsNext, hdisjointNext,
      hsecondNext, hfirstNext⟩ :=
    deallocateUncoalescedArrays_refines_represented hphysical hget hallocated
      hvalid hsecond hfirst hbins hdisjoint hfresh hoption
  refine ⟨cls, hclass, ?_, hvalidNext, ?_, hdisjointNext, ?_, ?_⟩
  · simpa [hfreeEq, hprevEq] using hphysicalNext
  · simpa [hheadsEq, hnextEq, hpreviousEq] using hbinsNext
  · simpa [hsecondEq] using hsecondNext
  · simpa [hfirstEq, hsecondEq] using hfirstNext

theorem deallocateUncoalescedArraysOutcome_constructs_valid
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {concrete : DeallocateMachineState}
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hsuccess : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count i selected.offset selected.bytes =
        .success concrete) :
    ∃ cls markedAbstract,
      markedAbstract = {
        physical := markFreeAt blocks i
        bins := state.insert cls (Dealloc.freedBlock selected) } ∧
      Dealloc.deallocateUncoalesced pool { physical := blocks, bins := state } i
          (selected.region pool) = some markedAbstract ∧
      Alloc.Valid pool markedAbstract ∧
      RepresentsPhysicalArrays offsets sizes concrete.isFree concrete.prevFree count
        markedAbstract.physical ∧
      RepresentsBins { heads := concrete.heads, next := concrete.next,
          previous := concrete.previous } markedAbstract.bins ∧
      BinsOffsetsDisjoint markedAbstract.bins ∧
      RepresentsSecondBitmap concrete.second markedAbstract.bins ∧
      FirstBitmapRep concrete.first concrete.second := by
  obtain ⟨cls, hclass, hphysicalNext, hbinsValid, hbinsNext, hdisjointNext,
      hsecondNext, hfirstNext⟩ :=
    deallocateUncoalescedArraysOutcome_refines_represented hphysical hget
      hallocated hallocValid.2.1 hsecond hfirst hbins hdisjoint hfresh hsuccess
  let markedAbstract : Alloc.State := {
    physical := markFreeAt blocks i
    bins := state.insert cls (Dealloc.freedBlock selected) }
  have habstract : Dealloc.deallocateUncoalesced pool
      { physical := blocks, bins := state } i (selected.region pool) =
      some markedAbstract := by
    simp [Dealloc.deallocateUncoalesced, deallocateAt, hget, hallocated, hclass,
      markedAbstract]
  have hvalidNext : Alloc.Valid pool markedAbstract :=
    Dealloc.deallocateUncoalesced_preserves_valid hallocValid habstract
  exact ⟨cls, markedAbstract, rfl, habstract, hvalidNext, hphysicalNext,
    hbinsNext, hdisjointNext, hsecondNext, hfirstNext⟩

theorem deallocateArraysOutcome_right_coalesce_total
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {marked : DeallocateMachineState}
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hmarked : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count i selected.offset selected.bytes =
        .success marked) :
    ∀ failed, coalesceIfPossibleArraysOutcome offsets sizes marked.isFree
      marked.prevFree marked.second marked.first marked.heads marked.next
      marked.previous count i ≠ .failure failed := by
  obtain ⟨_, markedAbstract, _, _, hmarkedValid, hmarkedPhysical,
      hmarkedBins, _, hmarkedSecond, _⟩ :=
    deallocateUncoalescedArraysOutcome_constructs_valid hphysical hget hallocated
      hallocValid hsecond hfirst hbins hdisjoint hfresh hmarked
  exact coalesceIfPossibleArraysOutcome_ne_failure_of_valid hmarkedValid hpoolMax
    hmarkedPhysical hmarkedSecond hmarkedBins

theorem deallocateArraysOutcome_left_coalesce_total
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {marked : DeallocateMachineState}
    {afterRight : CoalesceClassResult}
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hmarked : deallocateUncoalescedArraysOutcome offsets sizes isFree prevFree
      second first heads next previous count i selected.offset selected.bytes =
        .success marked)
    (hright : coalesceIfPossibleArraysOutcome offsets sizes marked.isFree
      marked.prevFree marked.second marked.first marked.heads marked.next
      marked.previous count i = .success afterRight) :
    ∀ failed, coalesceIfPossibleArraysOutcome afterRight.offsets afterRight.sizes
      afterRight.isFree afterRight.prevFree afterRight.second afterRight.first
      afterRight.heads afterRight.next afterRight.previous afterRight.count
      (i - 1) ≠ .failure failed := by
  obtain ⟨_, markedAbstract, _, _, hmarkedValid, hmarkedPhysical,
      hmarkedBins, hmarkedDisjoint, hmarkedSecond, hmarkedFirst⟩ :=
    deallocateUncoalescedArraysOutcome_constructs_valid hphysical hget hallocated
      hallocValid hsecond hfirst hbins hdisjoint hfresh hmarked
  obtain ⟨abstractAfterRight, hrightAbstract, hrightPhysical,
      _, hrightBins, hrightDisjoint, hrightSecond, _⟩ :=
    coalesceIfPossibleArraysOutcome_refines_allocator hmarkedValid hpoolMax
      hmarkedPhysical hcountMax hmarkedSecond hmarkedFirst hmarkedBins
      hmarkedDisjoint hright
  have hrightValid : Alloc.Valid pool abstractAfterRight :=
    Dealloc.coalesceIfPossible_preserves_valid hmarkedValid hrightAbstract
  exact coalesceIfPossibleArraysOutcome_ne_failure_of_valid hrightValid hpoolMax
    hrightPhysical hrightSecond hrightBins

/-- Public deallocation is transactional for every completely represented
valid allocator: a rejected return carries the exact complete input metadata. -/
theorem deallocateArraysOutcome_failure_eq_input
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {failed : CoalesceClassResult}
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hfailure : deallocateArraysOutcome offsets sizes isFree prevFree second first
      heads next previous count i selected.offset selected.bytes =
        .failure failed) :
    failed = allocatorArrays offsets sizes isFree prevFree second first heads next
      previous count := by
  apply deallocateArraysOutcome_failure_eq_input_of_coalesces_total
  · intro marked hmarked
    exact deallocateArraysOutcome_right_coalesce_total hphysical hget hallocated
      hallocValid hpoolMax hsecond hfirst hbins hdisjoint hfresh hmarked
  · intro marked afterRight hmarked hright _
    exact deallocateArraysOutcome_left_coalesce_total hphysical hget hallocated
      hallocValid hpoolMax hcountMax hsecond hfirst hbins hdisjoint hfresh
      hmarked hright
  · exact hfailure

theorem deallocateArraysOutcome_failure_preserves_frame
    {PROP : Type} [Iris.BI PROP]
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat} {selected : Block}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {failed : CoalesceClassResult}
    (frame : PROP)
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hfailure : deallocateArraysOutcome offsets sizes isFree prevFree second first
      heads next previous count i selected.offset selected.bytes =
        .failure failed) :
    failed = allocatorArrays offsets sizes isFree prevFree second first heads next
        previous count ∧ (frame ∗ (emp : PROP) ⊣⊢ frame) := by
  exact ⟨deallocateArraysOutcome_failure_eq_input hphysical hget hallocated
    hallocValid hpoolMax hcountMax hsecond hfirst hbins hdisjoint hfresh hfailure,
    sep_emp⟩

set_option maxHeartbeats 1000000 in
/-- End-to-end pure refinement of the public Luffs deallocator. This composes
the verified flag/bin insertion with right coalescing and, for nonzero block
indices, left coalescing over the compacted active prefix. -/
theorem deallocateArrays_refines
    {pool : Luffs.Memory.Region} {blocks : List Block}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat}
    {selected : Block} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hsuccess : deallocateArrays offsets sizes isFree prevFree second first
      heads next previous count i selected.offset selected.bytes = some result) :
    ∃ abstractNext,
      Dealloc.deallocate pool { physical := blocks, bins := state } i
          (selected.region pool) = some abstractNext ∧
      RepresentsPhysicalArrays result.offsets result.sizes result.isFree
          result.prevFree result.count abstractNext.physical ∧
      Bins.Valid abstractNext.bins ∧
      RepresentsBins (Metadata.mk result.heads result.next result.previous)
          abstractNext.bins ∧
      BinsOffsetsDisjoint abstractNext.bins ∧
      RepresentsSecondBitmap result.second abstractNext.bins ∧
      FirstBitmapRep result.first result.second := by
  obtain ⟨marked, afterRight, hmarked, hright, hlast⟩ :=
    deallocateArrays_result hsuccess
  obtain ⟨cls, hclass, hmarkedPhysical, hmarkedBinsValid,
      hmarkedBins, hmarkedDisjoint, hmarkedSecond, hmarkedFirst⟩ :=
    deallocateUncoalescedArrays_refines_represented hphysical hget hallocated
      hallocValid.2.1
      hsecond hfirst hbins hdisjoint hfresh hmarked
  let markedAbstract : Alloc.State := {
    physical := markFreeAt blocks i
    bins := state.insert cls (Dealloc.freedBlock selected) }
  have hmarkedAbstract : Dealloc.deallocateUncoalesced pool
      { physical := blocks, bins := state } i (selected.region pool) =
      some markedAbstract := by
    simp [Dealloc.deallocateUncoalesced, deallocateAt, hget,
      hallocated, hclass, markedAbstract]
  have hmarkedValid : Alloc.Valid pool markedAbstract :=
    Dealloc.deallocateUncoalesced_preserves_valid hallocValid hmarkedAbstract
  obtain ⟨abstractAfterRight, hrightAbstract, hrightPhysical,
      hrightBinsValid, hrightBins, hrightDisjoint, hrightSecond,
      hrightFirst⟩ :=
    coalesceIfPossibleArrays_refines_allocator hmarkedValid hpoolMax
      hmarkedPhysical hcountMax hmarkedSecond hmarkedFirst hmarkedBins
      hmarkedDisjoint hright
  have hrightValid : Alloc.Valid pool abstractAfterRight :=
    Dealloc.coalesceIfPossible_preserves_valid hmarkedValid hrightAbstract
  rcases hlast with ⟨hzero, hresult⟩ | ⟨hnonzero, hleft⟩
  · subst result
    have hdeallocate : Dealloc.deallocate pool
        { physical := blocks, bins := state } i (selected.region pool) =
        some abstractAfterRight := by
      unfold Dealloc.deallocate
      apply Option.bind_eq_some_iff.mpr
      refine ⟨markedAbstract, hmarkedAbstract, ?_⟩
      apply Option.bind_eq_some_iff.mpr
      refine ⟨abstractAfterRight, hrightAbstract, ?_⟩
      simp [hzero]
    exact ⟨abstractAfterRight, hdeallocate, hrightPhysical,
      hrightBinsValid, hrightBins, hrightDisjoint, hrightSecond, hrightFirst⟩
  · have hrightCountMax : afterRight.count ≤ usizeMax := by
      have hlength := Dealloc.coalesceIfPossible_physical_length_le
        hrightAbstract
      have hmarkedLength := markFreeAt_length blocks i
      dsimp only [markedAbstract] at hlength
      calc
        afterRight.count = abstractAfterRight.physical.length := hrightPhysical.1
        _ ≤ (markFreeAt blocks i).length := hlength
        _ = blocks.length := hmarkedLength
        _ = count := hphysical.1.symm
        _ ≤ usizeMax := hcountMax
    obtain ⟨abstractAfterLeft, hleftAbstract, hleftPhysical,
        hleftBinsValid, hleftBins, hleftDisjoint, hleftSecond, hleftFirst⟩ :=
      coalesceIfPossibleArrays_refines_allocator hrightValid hpoolMax
        hrightPhysical hrightCountMax hrightSecond hrightFirst hrightBins
        hrightDisjoint hleft
    have hdeallocate : Dealloc.deallocate pool
        { physical := blocks, bins := state } i (selected.region pool) =
        some abstractAfterLeft := by
      unfold Dealloc.deallocate
      apply Option.bind_eq_some_iff.mpr
      refine ⟨markedAbstract, hmarkedAbstract, ?_⟩
      apply Option.bind_eq_some_iff.mpr
      refine ⟨abstractAfterRight, hrightAbstract, ?_⟩
      simpa [hnonzero, Nat.pred_eq_sub_one] using hleftAbstract
    exact ⟨abstractAfterLeft, hdeallocate, hleftPhysical, hleftBinsValid,
      hleftBins, hleftDisjoint, hleftSecond, hleftFirst⟩

theorem allocatedBlock_offset_fresh
    {pool : Luffs.Memory.Region} {blocks : List Block} {state : Bins.State}
    (hvalid : Alloc.Valid pool { physical := blocks, bins := state })
    {i : Nat} {selected : Block} (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false) :
    ∀ query, selected.offset ∉ (state.chains query).map Block.offset := by
  intro query hoffset
  obtain ⟨cached, hcached, hcachedOffset⟩ := List.mem_map.mp hoffset
  obtain ⟨actual, hactual, hsame⟩ := hvalid.2.2.1 query cached hcached
  have hselectedMem : selected ∈ blocks :=
    List.mem_iff_getElem?.2 ⟨i, hget⟩
  have hoffsetEq : actual.offset = selected.offset := by
    rw [hsame.1, hcachedOffset]
  have heq : actual = selected :=
    wellFormed_same_offset hvalid.1 hactual hselectedMem hoffsetEq
  have hcachedFree := Bins.member_free hvalid.2.1 hcached
  have hactualFree := Bins.samePhysical_free hsame |>.trans hcachedFree
  rw [heq, hallocated] at hactualFree
  contradiction

/-- Iris ownership corollary for the complete concrete public deallocator.
The returned client capability is consumed exactly once; both optional
coalescing stages merely regroup the allocator's owned free bytes. -/
theorem deallocateArrays_ownsFree
    {PROP : Type} [Iris.BI PROP] [Luffs.Memory.ByteRegionLogic PROP]
    {pool : Luffs.Memory.Region} {blocks : List Block}
    {offsets sizes : List Nat} {isFree prevFree : List (Fin 256)}
    {count i : Nat}
    {selected : Block} {state : Bins.State}
    {second : List (BitVec 32)} {first : BitVec 64}
    {heads next previous : List Nat} {result : CoalesceClassResult}
    (hget : blocks[i]? = some selected)
    (hallocated : selected.free = false)
    (hphysical : RepresentsPhysicalArrays offsets sizes isFree prevFree count blocks)
    (hallocValid : Alloc.Valid pool { physical := blocks, bins := state })
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hcountMax : count ≤ usizeMax)
    (hsecond : RepresentsSecondBitmap second state)
    (hfirst : FirstBitmapRep first second)
    (hbins : RepresentsBins { heads, next, previous } state)
    (hdisjoint : BinsOffsetsDisjoint state)
    (hfresh : ∀ query, selected.offset ∉
      (state.chains query).map Block.offset)
    (hsuccess : deallocateArrays offsets sizes isFree prevFree second first
      heads next previous count i selected.offset selected.bytes = some result) :
    ∃ abstractNext,
      Dealloc.deallocate pool { physical := blocks, bins := state } i
          (selected.region pool) = some abstractNext ∧
      (Luffs.Memory.OwnsBytes (PROP := PROP) (selected.region pool) ∗
          Luffs.Allocator.TLSF.Ownership.OwnsFree pool blocks ⊣⊢
        Luffs.Allocator.TLSF.Ownership.OwnsFree pool abstractNext.physical) := by
  obtain ⟨abstractNext, habstract, _⟩ := deallocateArrays_refines hget
    hallocated hphysical hallocValid hpoolMax hcountMax hsecond hfirst hbins
    hdisjoint hfresh hsuccess
  exact ⟨abstractNext, habstract, Dealloc.deallocate_ownsFree habstract⟩

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
