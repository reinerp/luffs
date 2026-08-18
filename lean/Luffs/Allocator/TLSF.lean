import Luffs.Memory.Iris

set_option autoImplicit false

namespace Luffs.Allocator.TLSF

open Luffs.Memory
open Iris Iris.BI

/-- Minimum block alignment. Metadata flags occupy the low alignment bits. -/
def alignment : Nat := 16

def firstLevelCount : Nat := 64
def secondLevelCount : Nat := 32
def linearCutoff : Nat := alignment * secondLevelCount
def minimumBlockBytes : Nat := 16

structure SizeClass where
  fl : Fin firstLevelCount
  sl : Fin secondLevelCount
deriving DecidableEq, Repr

/-- Two-level size mapping. Requests through 512 bytes use 32 linear 16-byte
classes. Larger requests use logarithmic first-level classes and 32 subdivisions. -/
def sizeClass (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) : SizeClass :=
  if hlinear : size ≤ linearCutoff then
    {
      fl := ⟨0, by decide⟩
      sl := ⟨(size - 1) / alignment, by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < alignment)]
        simp only [linearCutoff, alignment, secondLevelCount] at hlinear ⊢
        omega⟩
    }
  else
    let log := size.log2
    let base := 2 ^ log
    let step := 2 ^ (log - 5)
    {
      fl := ⟨log, (Nat.log2_lt (Nat.ne_of_gt hsize)).2 hmax⟩
      sl := ⟨((size - base) / step) % secondLevelCount,
        Nat.mod_lt _ (by decide : 0 < secondLevelCount)⟩
    }

theorem high_sizeClass_fl (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) (hhigh : linearCutoff < size) :
    (sizeClass size hsize hmax).fl.val = size.log2 := by
  simp [sizeClass, Nat.not_le_of_gt hhigh]

theorem sizeClass_fl_zero_linear (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount)
    (hfl : (sizeClass size hsize hmax).fl.val = 0) :
    size ≤ linearCutoff := by
  apply Nat.le_of_not_gt
  intro hhigh
  have hlog : 8 ≤ size.log2 := by
    rw [Nat.le_log2 (Nat.ne_of_gt hsize)]
    simp only [linearCutoff, alignment, secondLevelCount] at hhigh
    change 256 ≤ size
    omega
  rw [high_sizeClass_fl size hsize hmax hhigh] at hfl
  omega

theorem sizeClass_indices_in_bounds (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) :
    (sizeClass size hsize hmax).fl.val < firstLevelCount ∧
      (sizeClass size hsize hmax).sl.val < secondLevelCount := by
  exact ⟨(sizeClass size hsize hmax).fl.isLt,
    (sizeClass size hsize hmax).sl.isLt⟩

def linearBinNumber (size : Nat) : Nat := (size - 1) / alignment
def linearBinLower (size : Nat) : Nat := linearBinNumber size * alignment + 1
def linearBinUpper (size : Nat) : Nat := (linearBinNumber size + 1) * alignment

/-- Rust-shaped arithmetic rounding used by the Luffs implementation after its
checked `size + 15`. Unlike a bit mask, this expression has a direct generic
integer semantics in both generated Lean and Rust. -/
def roundUp16 (size : Nat) : Nat := (size + 15) / 16 * 16

theorem roundUp16_eq_linearBinUpper (size : Nat) (hsize : 0 < size) :
    roundUp16 size = linearBinUpper size := by
  simp [roundUp16, linearBinUpper, linearBinNumber, alignment]
  omega

theorem linear_sizeClass_values (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) (hlinear : size ≤ linearCutoff) :
    (sizeClass size hsize hmax).fl.val = 0 ∧
      (sizeClass size hsize hmax).sl.val = linearBinNumber size := by
  simp [sizeClass, hlinear, linearBinNumber]

/-- A request in the linear range belongs to the selected 16-byte bin. The
upper endpoint is inclusive because allocation rounds upward to that boundary. -/
theorem linear_sizeClass_covers (size : Nat) (hsize : 0 < size) :
    linearBinLower size ≤ size ∧ size ≤ linearBinUpper size := by
  have hlo := Nat.div_mul_le_self (size - 1) alignment
  have hhi := Nat.lt_div_mul_add (a := size - 1) (by decide : 0 < alignment)
  have hdecomp : size - 1 + 1 = size := by omega
  simp only [linearBinLower, linearBinUpper, linearBinNumber]
  constructor
  · omega
  · rw [Nat.add_mul]
    omega

private theorem sub_div_lt_of_lt_add_mul {size base step bins : Nat}
    (hstep : 0 < step) (hbase : base ≤ size)
    (hupper : size < base + bins * step) :
    (size - base) / step < bins := by
  rw [Nat.div_lt_iff_lt_mul hstep]
  omega

/-- Above the linear-size range, the second-level quotient is genuinely below
32. Consequently the executable `% 32` in `sizeClass` never wraps. -/
theorem high_sizeClass_quotient_lt (size : Nat) (hsize : 0 < size)
    (hlog : 5 ≤ size.log2) :
    (size - 2 ^ size.log2) / 2 ^ (size.log2 - 5) < secondLevelCount := by
  have hbase : 2 ^ size.log2 ≤ size :=
    Nat.log2_self_le (Nat.ne_of_gt hsize)
  have hupper0 : size < 2 ^ (size.log2 + 1) := Nat.lt_log2_self
  have hpow : 2 ^ size.log2 = secondLevelCount * 2 ^ (size.log2 - 5) := by
    rw [show secondLevelCount = 2 ^ 5 by decide, Nat.mul_comm,
      Nat.pow_sub_mul_pow 2 hlog]
  apply sub_div_lt_of_lt_add_mul (Nat.pow_pos (by decide)) hbase
  rw [← hpow]
  simpa [Nat.pow_add, Nat.mul_two] using hupper0

theorem high_sizeClass_no_wrap (size : Nat) (hsize : 0 < size)
    (hlog : 5 ≤ size.log2) :
    ((size - 2 ^ size.log2) / 2 ^ (size.log2 - 5)) % secondLevelCount =
      (size - 2 ^ size.log2) / 2 ^ (size.log2 - 5) := by
  exact Nat.mod_eq_of_lt (high_sizeClass_quotient_lt size hsize hlog)

def highBinStep (size : Nat) : Nat := 2 ^ (size.log2 - 5)

def highBinNumber (size : Nat) : Nat :=
  (size - 2 ^ size.log2) / highBinStep size

def highBinLower (size : Nat) : Nat :=
  2 ^ size.log2 + highBinNumber size * highBinStep size

def highBinUpper (size : Nat) : Nat := highBinLower size + highBinStep size

/-- The computed high-range TLSF bin contains the requested size. -/
theorem high_sizeClass_covers (size : Nat) (hsize : 0 < size) :
    highBinLower size ≤ size ∧ size < highBinUpper size := by
  have hbase : 2 ^ size.log2 ≤ size :=
    Nat.log2_self_le (Nat.ne_of_gt hsize)
  have hstep : 0 < highBinStep size := Nat.pow_pos (by decide)
  have hlo := Nat.div_mul_le_self (size - 2 ^ size.log2) (highBinStep size)
  have hhi := Nat.lt_div_mul_add (a := size - 2 ^ size.log2) hstep
  have hdecomp : 2 ^ size.log2 + (size - 2 ^ size.log2) = size :=
    Nat.add_sub_of_le hbase
  simp only [highBinUpper, highBinLower, highBinNumber, highBinStep] at hlo hhi ⊢
  constructor <;> omega

/-- TLSF uses mapping-down when inserting a free block, but mapping-up for an
allocation request. Linear bins end at an alignment boundary. High bins are
half-open, so their upper boundary classifies into the next bin (including the
carry into the next first level). -/
def requestKey (size : Nat) : Nat :=
  if size ≤ linearCutoff then linearBinUpper size else highBinUpper size

theorem request_le_key (size : Nat) (hsize : 0 < size) :
    size ≤ requestKey size := by
  by_cases hlinear : size ≤ linearCutoff
  · simp only [requestKey, hlinear, ↓reduceIte]
    exact (linear_sizeClass_covers size hsize).2
  · simp only [requestKey, hlinear, ↓reduceIte]
    exact Nat.le_of_lt (high_sizeClass_covers size hsize).2

theorem requestKey_positive (size : Nat) (hsize : 0 < size) :
    0 < requestKey size :=
  Nat.lt_of_lt_of_le hsize (request_le_key size hsize)

/-- Executable request classifier. The explicit maximum premise records the
top-bin overflow check that callers must discharge before bitmap lookup. -/
def requestSizeClass (size : Nat) (hsize : 0 < size)
    (hkeymax : requestKey size < 2 ^ firstLevelCount) : SizeClass :=
  sizeClass (requestKey size) (requestKey_positive size hsize) hkeymax

/-- Starting class used by allocation lookup. Linear classes already round
aligned blocks upward; logarithmic classes require the explicit mapping-up key. -/
def searchSizeClass (size : Nat) (hsize : 0 < size)
    (hkeymax : requestKey size < 2 ^ firstLevelCount) : SizeClass :=
  if _hlinear : size ≤ linearCutoff then
    sizeClass size hsize
      (Nat.lt_of_le_of_lt (request_le_key size hsize) hkeymax)
  else requestSizeClass size hsize hkeymax

theorem searchSizeClass_linear (size : Nat) (hsize : 0 < size)
    (hkeymax : requestKey size < 2 ^ firstLevelCount)
    (hlinear : size ≤ linearCutoff) :
    searchSizeClass size hsize hkeymax =
      sizeClass size hsize
        (Nat.lt_of_le_of_lt (request_le_key size hsize) hkeymax) := by
  simp [searchSizeClass, hlinear]

theorem searchSizeClass_high (size : Nat) (hsize : 0 < size)
    (hkeymax : requestKey size < 2 ^ firstLevelCount)
    (hhigh : linearCutoff < size) :
    searchSizeClass size hsize hkeymax = requestSizeClass size hsize hkeymax := by
  simp [searchSizeClass, Nat.not_le_of_gt hhigh]

theorem requestSizeClass_indices_in_bounds (size : Nat) (hsize : 0 < size)
    (hkeymax : requestKey size < 2 ^ firstLevelCount) :
    (requestSizeClass size hsize hkeymax).fl.val < firstLevelCount ∧
      (requestSizeClass size hsize hkeymax).sl.val < secondLevelCount := by
  exact sizeClass_indices_in_bounds (requestKey size)
    (requestKey_positive size hsize) hkeymax

theorem linear_requestKey (size : Nat) (hlinear : size ≤ linearCutoff) :
    requestKey size = linearBinUpper size := by
  simp [requestKey, hlinear]

theorem high_requestKey (size : Nat) (hhigh : linearCutoff < size) :
    requestKey size = highBinUpper size := by
  simp [requestKey, Nat.not_le_of_gt hhigh]

/-- In the linear range, aligned free-block sizes are exactly the upper
endpoints of their 16-byte bins. Thus sharing a mapping-down class with an
arbitrary request is already sufficient for the block to fit that request. -/
theorem linear_same_class_suitable (request block : Nat)
    (hrequest : 0 < request) (hblock : 0 < block)
    (hrequestMax : request < 2 ^ firstLevelCount)
    (hblockMax : block < 2 ^ firstLevelCount)
    (hrequestLinear : request ≤ linearCutoff)
    (hblockLinear : block ≤ linearCutoff)
    (haligned : alignment ∣ block)
    (hclass : sizeClass request hrequest hrequestMax =
      sizeClass block hblock hblockMax) :
    request ≤ block := by
  have hrequestValues := linear_sizeClass_values request hrequest
    hrequestMax hrequestLinear
  have hblockValues := linear_sizeClass_values block hblock
    hblockMax hblockLinear
  have hbins : linearBinNumber request = linearBinNumber block := by
    rw [← hrequestValues.2, ← hblockValues.2, hclass]
  have hrequestUpper := (linear_sizeClass_covers request hrequest).2
  have hblockLower := (linear_sizeClass_covers block hblock).1
  have hblockUpper := (linear_sizeClass_covers block hblock).2
  obtain ⟨multiple, hmultiple⟩ := haligned
  simp [linearBinLower, linearBinUpper, hbins, alignment, Nat.add_mul]
    at hrequestUpper hblockLower
  simp [linearBinUpper, alignment, Nat.add_mul] at hblockUpper
  simp [alignment, Nat.mul_comm] at hmultiple
  omega

/-- Searching at or above a request's linear second-level index is suitable:
every aligned block in the selected linear bin is large enough. -/
theorem linear_later_class_suitable (request block : Nat)
    (hrequest : 0 < request) (hblock : 0 < block)
    (hrequestMax : request < 2 ^ firstLevelCount)
    (hblockMax : block < 2 ^ firstLevelCount)
    (hrequestLinear : request ≤ linearCutoff)
    (hblockLinear : block ≤ linearCutoff)
    (haligned : alignment ∣ block)
    (hsl : (sizeClass request hrequest hrequestMax).sl.val ≤
      (sizeClass block hblock hblockMax).sl.val) :
    request ≤ block := by
  have hrequestValues := linear_sizeClass_values request hrequest
    hrequestMax hrequestLinear
  have hblockValues := linear_sizeClass_values block hblock
    hblockMax hblockLinear
  have hbins : linearBinNumber request ≤ linearBinNumber block := by
    rw [← hrequestValues.2, ← hblockValues.2]
    exact hsl
  have hrequestUpper := (linear_sizeClass_covers request hrequest).2
  have hblockLower := (linear_sizeClass_covers block hblock).1
  have hblockUpper := (linear_sizeClass_covers block hblock).2
  obtain ⟨multiple, hmultiple⟩ := haligned
  simp [linearBinLower, linearBinUpper, alignment, Nat.add_mul]
    at hrequestUpper hblockLower hblockUpper
  simp [alignment, Nat.mul_comm] at hmultiple
  omega

theorem high_sizeClass_sl (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) (hhigh : linearCutoff < size)
    (hlog : 5 ≤ size.log2) :
    (sizeClass size hsize hmax).sl.val = highBinNumber size := by
  simp [sizeClass, Nat.not_le_of_gt hhigh, highBinNumber, highBinStep,
    high_sizeClass_no_wrap size hsize hlog]

theorem high_log_at_least_five (size : Nat) (hhigh : linearCutoff < size) :
    5 ≤ size.log2 := by
  have hsize : 0 < size := by
    simp only [linearCutoff, alignment, secondLevelCount] at hhigh
    omega
  rw [Nat.le_log2 (Nat.ne_of_gt hsize)]
  simp only [linearCutoff, alignment, secondLevelCount] at hhigh
  change 32 ≤ size
  omega

/-- Mapping-down classes are genuine intervals: two high-range sizes in the
same class have exactly the same lower boundary. -/
theorem high_same_class_lower_eq (left right : Nat)
    (hleft : 0 < left) (hright : 0 < right)
    (hleftMax : left < 2 ^ firstLevelCount)
    (hrightMax : right < 2 ^ firstLevelCount)
    (hleftHigh : linearCutoff < left)
    (hrightHigh : linearCutoff < right)
    (hclass : sizeClass left hleft hleftMax =
      sizeClass right hright hrightMax) :
    highBinLower left = highBinLower right := by
  have hlogs : left.log2 = right.log2 := by
    rw [← high_sizeClass_fl left hleft hleftMax hleftHigh,
      ← high_sizeClass_fl right hright hrightMax hrightHigh, hclass]
  have hleftLog := high_log_at_least_five left hleftHigh
  have hrightLog := high_log_at_least_five right hrightHigh
  have hbins : highBinNumber left = highBinNumber right := by
    rw [← high_sizeClass_sl left hleft hleftMax hleftHigh hleftLog,
      ← high_sizeClass_sl right hright hrightMax hrightHigh hrightLog, hclass]
  simp [highBinLower, highBinStep, hlogs, hbins]

/-- Once mapping-up produces an exact high-bin boundary, any free block in
that class is large enough. -/
theorem high_boundary_same_class_suitable (requestKey block : Nat)
    (hkey : 0 < requestKey) (hblock : 0 < block)
    (hkeyMax : requestKey < 2 ^ firstLevelCount)
    (hblockMax : block < 2 ^ firstLevelCount)
    (hkeyHigh : linearCutoff < requestKey)
    (hblockHigh : linearCutoff < block)
    (hboundary : highBinLower requestKey = requestKey)
    (hclass : sizeClass requestKey hkey hkeyMax =
      sizeClass block hblock hblockMax) :
    requestKey ≤ block := by
  have hlower := (high_sizeClass_covers block hblock).1
  have heq := high_same_class_lower_eq requestKey block hkey hblock hkeyMax
    hblockMax hkeyHigh hblockHigh hclass
  rw [hboundary] at heq
  rw [← heq] at hlower
  exact hlower

/-- The upper endpoint of a high-range containing bin is exactly the lower
endpoint of the mapping-up bin. This includes the `sl = 31` carry into the next
first level. -/
theorem high_upper_is_boundary (size : Nat) (hsize : 0 < size)
    (hhigh : linearCutoff < size) :
    highBinLower (highBinUpper size) = highBinUpper size := by
  let log := size.log2
  let step := highBinStep size
  let quotient := highBinNumber size
  have hlog : 5 ≤ log := high_log_at_least_five size hhigh
  have hstep : 0 < step := by
    exact Nat.pow_pos (by decide)
  have hquotient : quotient < secondLevelCount := by
    exact high_sizeClass_quotient_lt size hsize hlog
  have hbaseStep : 2 ^ log = secondLevelCount * step := by
    simp only [log, step, highBinStep]
    rw [show secondLevelCount = 2 ^ 5 by decide, Nat.mul_comm,
      Nat.pow_sub_mul_pow 2 hlog]
  have hupper : highBinUpper size = 2 ^ log + (quotient + 1) * step := by
    simp [highBinUpper, highBinLower, quotient, step, log, Nat.add_mul,
      Nat.add_assoc]
  by_cases hlast : quotient + 1 = secondLevelCount
  · have hkey : highBinUpper size = 2 ^ (log + 1) := by
      rw [hupper, hlast, ← hbaseStep]
      simp [Nat.pow_add, Nat.mul_two]
    simp [highBinLower, highBinNumber, highBinStep, hkey]
  · have hqnext : quotient + 1 < secondLevelCount := by omega
    have hkeyPositive : 0 < highBinUpper size :=
      Nat.lt_trans hsize (high_sizeClass_covers size hsize).2
    have hkeyLog : (highBinUpper size).log2 = log := by
      rw [Nat.log2_eq_iff (Nat.ne_of_gt hkeyPositive)]
      constructor
      · rw [hupper]
        exact Nat.le_add_right _ _
      · have hterm : (quotient + 1) * step < secondLevelCount * step :=
          Nat.mul_lt_mul_of_pos_right hqnext hstep
        rw [← hbaseStep] at hterm
        rw [hupper, Nat.pow_add, Nat.mul_two]
        omega
    simp only [highBinLower, highBinNumber, highBinStep]
    rw [show (highBinUpper size).log2 = log from hkeyLog]
    rw [hupper]
    change 2 ^ log +
      ((2 ^ log + (quotient + 1) * step - 2 ^ log) / step) * step =
        2 ^ log + (quotient + 1) * step
    simp [hstep]

theorem high_requestKey_is_boundary (size : Nat) (hsize : 0 < size)
    (hhigh : linearCutoff < size) :
    highBinLower (requestKey size) = requestKey size := by
  rw [high_requestKey size hhigh]
  exact high_upper_is_boundary size hsize hhigh

/-- A block in the exact mapping-up class of a high-range request is suitable.
Search into later classes is handled separately by class-order monotonicity. -/
theorem high_request_same_class_suitable (request block : Nat)
    (hrequest : 0 < request) (hblock : 0 < block)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount)
    (hblockMax : block < 2 ^ firstLevelCount)
    (hrequestHigh : linearCutoff < request)
    (hblockHigh : linearCutoff < block)
    (hclass : requestSizeClass request hrequest hkeyMax =
      sizeClass block hblock hblockMax) :
    request ≤ block := by
  have hkeyPositive := requestKey_positive request hrequest
  have hkeyHigh : linearCutoff < requestKey request :=
    Nat.lt_of_lt_of_le hrequestHigh (request_le_key request hrequest)
  have hkeyFits := high_boundary_same_class_suitable
    (requestKey request) block hkeyPositive hblock hkeyMax hblockMax
    hkeyHigh hblockHigh (high_requestKey_is_boundary request hrequest hrequestHigh)
    hclass
  exact Nat.le_trans (request_le_key request hrequest) hkeyFits

/-- Lexicographically later high-range classes are also suitable. This is the
cross-bin inequality needed after bitmap search skips an empty mapping-up bin. -/
theorem high_boundary_later_class_suitable (key block : Nat)
    (hkey : 0 < key) (hblock : 0 < block)
    (hkeyMax : key < 2 ^ firstLevelCount)
    (hblockMax : block < 2 ^ firstLevelCount)
    (hkeyHigh : linearCutoff < key)
    (hblockHigh : linearCutoff < block)
    (hboundary : highBinLower key = key)
    (horder :
      (sizeClass key hkey hkeyMax).fl.val <
        (sizeClass block hblock hblockMax).fl.val ∨
      ((sizeClass key hkey hkeyMax).fl.val =
          (sizeClass block hblock hblockMax).fl.val ∧
        (sizeClass key hkey hkeyMax).sl.val ≤
          (sizeClass block hblock hblockMax).sl.val)) :
    key ≤ block := by
  rcases horder with hfl | ⟨hfl, hsl⟩
  · have hlogs : key.log2 < block.log2 := by
      simpa [high_sizeClass_fl key hkey hkeyMax hkeyHigh,
        high_sizeClass_fl block hblock hblockMax hblockHigh] using hfl
    have hkeyUpper : key < 2 ^ (key.log2 + 1) := Nat.lt_log2_self
    have hpowers : 2 ^ (key.log2 + 1) ≤ 2 ^ block.log2 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hblockLower : 2 ^ block.log2 ≤ block :=
      Nat.log2_self_le (Nat.ne_of_gt hblock)
    exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le hkeyUpper hpowers))
      hblockLower
  · have hlogs : key.log2 = block.log2 := by
      simpa [high_sizeClass_fl key hkey hkeyMax hkeyHigh,
        high_sizeClass_fl block hblock hblockMax hblockHigh] using hfl
    have hkeyLog := high_log_at_least_five key hkeyHigh
    have hblockLog := high_log_at_least_five block hblockHigh
    have hbins : highBinNumber key ≤ highBinNumber block := by
      rw [← high_sizeClass_sl key hkey hkeyMax hkeyHigh hkeyLog,
        ← high_sizeClass_sl block hblock hblockMax hblockHigh hblockLog]
      exact hsl
    have hlower := (high_sizeClass_covers block hblock).1
    rw [← hboundary]
    simp only [highBinLower, highBinStep]
    rw [hlogs]
    simp only [highBinLower, highBinStep] at hlower
    apply Nat.le_trans _ hlower
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hbins) _

theorem high_request_later_class_suitable (request block : Nat)
    (hrequest : 0 < request) (hblock : 0 < block)
    (hkeyMax : requestKey request < 2 ^ firstLevelCount)
    (hblockMax : block < 2 ^ firstLevelCount)
    (hrequestHigh : linearCutoff < request)
    (hblockHigh : linearCutoff < block)
    (horder :
      (requestSizeClass request hrequest hkeyMax).fl.val <
        (sizeClass block hblock hblockMax).fl.val ∨
      ((requestSizeClass request hrequest hkeyMax).fl.val =
          (sizeClass block hblock hblockMax).fl.val ∧
        (requestSizeClass request hrequest hkeyMax).sl.val ≤
          (sizeClass block hblock hblockMax).sl.val)) :
    request ≤ block := by
  have hkey := requestKey_positive request hrequest
  have hkeyHigh : linearCutoff < requestKey request :=
    Nat.lt_of_lt_of_le hrequestHigh (request_le_key request hrequest)
  apply Nat.le_trans (request_le_key request hrequest)
  exact high_boundary_later_class_suitable (requestKey request) block hkey hblock
    hkeyMax hblockMax hkeyHigh hblockHigh
    (high_requestKey_is_boundary request hrequest hrequestHigh) horder

/-- A compact pure view used by the executable allocator and its Iris invariant. -/
structure Block where
  offset : Nat
  bytes : Nat
  free : Bool
  /-- Cached physical-predecessor state used for O(1) backward coalescing. -/
  prevFree : Bool
  /-- Intrusive links are block offsets within the same pool. -/
  prevFreeLink : Option Nat
  nextFreeLink : Option Nat
deriving DecidableEq, Repr

def splitBlock (b : Block) (wanted : Nat) : Block × Block :=
  ({ offset := b.offset, bytes := wanted, free := false,
     prevFree := b.prevFree, prevFreeLink := none, nextFreeLink := none },
   { offset := b.offset + wanted, bytes := b.bytes - wanted,
     free := true, prevFree := false,
     prevFreeLink := none, nextFreeLink := none })

/-- Replace the selected physical block by its two split pieces. An invalid
index is totalized to the unchanged tail; verified callers prove lookup first. -/
def splitAt : List Block -> Nat -> Nat -> List Block
  | [], _, _ => []
  | b :: rest, 0, wanted =>
      (splitBlock b wanted).1 :: (splitBlock b wanted).2 :: rest
  | b :: rest, i + 1, wanted => b :: splitAt rest i wanted

def canSplit (b : Block) (wanted : Nat) : Prop :=
  0 < wanted ∧ wanted + minimumBlockBytes ≤ b.bytes

instance (b : Block) (wanted : Nat) : Decidable (canSplit b wanted) := by
  unfold canSplit
  infer_instance

theorem canSplit_wanted_le {b : Block} {wanted : Nat} (h : canSplit b wanted) :
    wanted ≤ b.bytes := by
  rcases h with ⟨_, h⟩
  exact Nat.le_trans (Nat.le_add_right _ _) h

theorem splitBlock_nonempty {b : Block} {wanted : Nat} (h : canSplit b wanted) :
    0 < (splitBlock b wanted).1.bytes ∧ 0 < (splitBlock b wanted).2.bytes := by
  rcases h with ⟨hwanted, hroom⟩
  simp only [splitBlock]
  constructor
  · exact hwanted
  · simp only [minimumBlockBytes] at hroom
    omega

theorem splitBlock_allocation_state (b : Block) (wanted : Nat) :
    (splitBlock b wanted).1.free = false ∧
      (splitBlock b wanted).2.free = true := by
  exact ⟨rfl, rfl⟩

/-- Executable successful-split path of allocation. Exact-fit allocation is a
separate path because it produces no remainder block. -/
def allocateAt (blocks : List Block) (i wanted : Nat) : Option (Block × List Block) :=
  match blocks[i]? with
  | none => none
  | some b =>
      if b.free = true ∧ canSplit b wanted ∧ alignment ∣ wanted then
        some ((splitBlock b wanted).1, splitAt blocks i wanted)
      else none

def markAllocated (b : Block) : Block :=
  { offset := b.offset, bytes := b.bytes, free := false,
    prevFree := b.prevFree, prevFreeLink := none, nextFreeLink := none }

/-- Allocate a whole physical block and clear the successor's cached
predecessor-free bit. -/
def markAllocatedAt : List Block -> Nat -> List Block
  | [], _ => []
  | [b], 0 => [markAllocated b]
  | b :: next :: rest, 0 => markAllocated b :: { next with prevFree := false } :: rest
  | b :: rest, i + 1 => b :: markAllocatedAt rest i

/-- Full chosen-block transition. A splittable block returns exactly `wanted`
bytes and a free remainder. An exact or near fit consumes the whole block,
avoiding a remainder smaller than `minimumBlockBytes`. -/
def allocateChosenAt (blocks : List Block) (i wanted : Nat) :
    Option (Block × List Block) :=
  match blocks[i]? with
  | none => none
  | some b =>
      if b.free = true ∧ wanted ≤ b.bytes ∧ alignment ∣ wanted then
        if canSplit b wanted then
          some ((splitBlock b wanted).1, splitAt blocks i wanted)
        else some (markAllocated b, markAllocatedAt blocks i)
      else none

def allocationRemainder (blocks : List Block) (i wanted : Nat) : Option Block :=
  match blocks[i]? with
  | none => none
  | some b => if canSplit b wanted then some (splitBlock b wanted).2 else none

theorem allocationRemainder_result {blocks : List Block} {i wanted : Nat}
    {remainder : Block}
    (hresult : allocationRemainder blocks i wanted = some remainder) :
    ∃ b, blocks[i]? = some b ∧ canSplit b wanted ∧
      remainder = (splitBlock b wanted).2 := by
  unfold allocationRemainder at hresult
  cases hget : blocks[i]? with
  | none => simp [hget] at hresult
  | some b =>
      by_cases hsplit : canSplit b wanted
      · simp [hget, hsplit] at hresult
        exact ⟨b, rfl, hsplit, hresult.symm⟩
      · simp [hget, hsplit] at hresult

theorem allocateChosenAt_success_cases {blocks : List Block} {i wanted : Nat}
    {b allocated : Block} {next : List Block} (hget : blocks[i]? = some b)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    b.free = true ∧ wanted ≤ b.bytes ∧ alignment ∣ wanted ∧
      ((canSplit b wanted ∧ allocated = (splitBlock b wanted).1 ∧
          next = splitAt blocks i wanted) ∨
        (¬ canSplit b wanted ∧ allocated = markAllocated b ∧
          next = markAllocatedAt blocks i)) := by
  simp only [allocateChosenAt, hget] at hsuccess
  split at hsuccess
  next hpre =>
    split at hsuccess
    next hsplit =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsuccess
      exact ⟨hpre.1, hpre.2.1, hpre.2.2, Or.inl
        ⟨hsplit, hsuccess.1.symm, hsuccess.2.symm⟩⟩
    next hnosplit =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsuccess
      exact ⟨hpre.1, hpre.2.1, hpre.2.2, Or.inr
        ⟨hnosplit, hsuccess.1.symm, hsuccess.2.symm⟩⟩
  next => contradiction

theorem allocateChosenAt_exists {blocks : List Block} {i wanted : Nat} {b : Block}
    (hget : blocks[i]? = some b) (hfree : b.free = true)
    (hfits : wanted ≤ b.bytes) (haligned : alignment ∣ wanted) :
    ∃ allocated next,
      allocateChosenAt blocks i wanted = some (allocated, next) := by
  by_cases hsplit : canSplit b wanted
  · exact ⟨(splitBlock b wanted).1, splitAt blocks i wanted, by
      simp [allocateChosenAt, hget, hfree, hfits, haligned, hsplit]⟩
  · exact ⟨markAllocated b, markAllocatedAt blocks i, by
      simp [allocateChosenAt, hget, hfree, hfits, haligned, hsplit]⟩

theorem allocateAt_success_iff {blocks : List Block} {i wanted : Nat} {b : Block}
    (hget : blocks[i]? = some b) :
    allocateAt blocks i wanted =
        some ((splitBlock b wanted).1, splitAt blocks i wanted) ↔
      b.free = true ∧ canSplit b wanted ∧ alignment ∣ wanted := by
  simp [allocateAt, hget]

def Block.region (pool : Region) (b : Block) : Region :=
  { base := pool.base + b.offset, bytes := b.bytes }

def Block.aligned (b : Block) : Prop :=
  alignment ∣ b.offset ∧ alignment ∣ b.bytes

def ordered (blocks : List Block) : Prop :=
  ∀ i j (hi : i < blocks.length) (hj : j < blocks.length), i < j ->
    (blocks[i]'hi).offset + (blocks[i]'hi).bytes ≤ (blocks[j]'hj).offset

def covers (pool : Region) (blocks : List Block) : Prop :=
  (blocks.map (fun b => b.bytes)).sum = pool.bytes

/-- Blocks are physically adjacent starting at `cursor`; unlike `ordered`,
this rules out unowned gaps. -/
def contiguousFrom : Nat -> List Block -> Prop
  | _, [] => True
  | cursor, b :: rest =>
      b.offset = cursor ∧ contiguousFrom (cursor + b.bytes) rest

/-- The cached `prevFree` bit of each block agrees with its physical
predecessor. The first block has no predecessor and therefore starts false. -/
def boundaryTagsFrom : Bool -> List Block -> Prop
  | _, [] => True
  | previousFree, b :: rest =>
      b.prevFree = previousFree ∧ boundaryTagsFrom b.free rest

def boundaryTags (blocks : List Block) : Prop := boundaryTagsFrom false blocks

def partitions (pool : Region) (blocks : List Block) : Prop :=
  contiguousFrom 0 blocks ∧ covers pool blocks

def wellFormed (pool : Region) (blocks : List Block) : Prop :=
  ordered blocks ∧ partitions pool blocks ∧ boundaryTags blocks ∧
    ∀ b ∈ blocks, 0 < b.bytes ∧ b.offset + b.bytes ≤ pool.bytes ∧ b.aligned

theorem contiguousFrom_get_offset_ge {blocks : List Block} {cursor i : Nat}
    (hcontig : contiguousFrom cursor blocks) (hi : i < blocks.length) :
    cursor ≤ (blocks[i]'hi).offset := by
  induction blocks generalizing cursor i with
  | nil => simp at hi
  | cons head rest ih =>
      simp only [contiguousFrom] at hcontig
      cases i with
      | zero => simpa using Nat.le_of_eq hcontig.1.symm
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          have htail := ih hcontig.2 hi
          exact Nat.le_trans (by omega) htail

theorem contiguousFrom_ordered {blocks : List Block} {cursor : Nat}
    (hcontig : contiguousFrom cursor blocks) : ordered blocks := by
  intro i j hi hj hij
  induction blocks generalizing cursor i j with
  | nil => simp at hi
  | cons head rest ih =>
      simp only [contiguousFrom] at hcontig
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ k =>
              simp only [List.getElem_cons_zero, List.getElem_cons_succ]
              have hk : k < rest.length := by simpa using hj
              have hge := contiguousFrom_get_offset_ge hcontig.2 hk
              rw [hcontig.1]
              exact hge
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi hj hij
              simp only [List.getElem_cons_succ]
              exact ih (cursor := cursor + head.bytes) (i := i) (j := j)
                hcontig.2 hi hj hij

theorem contiguousFrom_member_end_le {blocks : List Block} {cursor : Nat}
    (hcontig : contiguousFrom cursor blocks) {b : Block} (hmem : b ∈ blocks) :
    b.offset + b.bytes ≤ cursor + (blocks.map Block.bytes).sum := by
  induction blocks generalizing cursor with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [contiguousFrom] at hcontig
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · rw [hcontig.1]
        simp
      · have hrest := ih hcontig.2 htail
        simp only [List.map_cons, List.sum_cons]
        omega

theorem wellFormed_of_partitions_boundary {pool : Region} {blocks : List Block}
    (hparts : partitions pool blocks) (htags : boundaryTags blocks)
    (hshape : ∀ b ∈ blocks, 0 < b.bytes ∧ b.aligned) :
    wellFormed pool blocks := by
  refine ⟨contiguousFrom_ordered hparts.1, hparts, htags, ?_⟩
  intro b hmem
  have hend := contiguousFrom_member_end_le hparts.1 hmem
  have hcover := hparts.2
  unfold covers at hcover
  rw [hcover] at hend
  have hend' : b.offset + b.bytes ≤ pool.bytes := by
    simpa only [Nat.zero_add] using hend
  exact ⟨(hshape b hmem).1, hend', (hshape b hmem).2⟩

theorem no_block_starts_inside {pool : Region} {blocks : List Block}
    (hwell : wellFormed pool blocks) {container other : Block}
    (hcontainer : container ∈ blocks) (hother : other ∈ blocks)
    (hlower : container.offset < other.offset)
    (hupper : other.offset < container.offset + container.bytes) : False := by
  obtain ⟨i, hi, hgetContainer⟩ := List.mem_iff_getElem.mp hcontainer
  obtain ⟨j, hj, hgetOther⟩ := List.mem_iff_getElem.mp hother
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have hord := hwell.1 i j hi hj hij
    rw [hgetContainer, hgetOther] at hord
    omega
  · subst j
    have heq : container = other := by
      rw [← hgetContainer, ← hgetOther]
    have hoffset := congrArg Block.offset heq
    omega
  · have hord := hwell.1 j i hj hi hij
    rw [hgetOther, hgetContainer] at hord
    have hotherPositive := (hwell.2.2.2 other hother).1
    omega

theorem wellFormed_same_offset {pool : Region} {blocks : List Block}
    (hwell : wellFormed pool blocks) {left right : Block}
    (hleft : left ∈ blocks) (hright : right ∈ blocks)
    (hoffset : left.offset = right.offset) : left = right := by
  obtain ⟨i, hi, hgetLeft⟩ := List.mem_iff_getElem.mp hleft
  obtain ⟨j, hj, hgetRight⟩ := List.mem_iff_getElem.mp hright
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have hord := hwell.1 i j hi hj hij
    rw [hgetLeft, hgetRight, ← hoffset] at hord
    have hpositive := (hwell.2.2.2 left hleft).1
    omega
  · subst j
    rw [← hgetLeft, ← hgetRight]
  · have hord := hwell.1 j i hj hi hij
    rw [hgetRight, hgetLeft, hoffset] at hord
    have hpositive := (hwell.2.2.2 right hright).1
    omega

theorem wellFormed_regions_disjoint {pool : Region} {blocks : List Block}
    (hwell : wellFormed pool blocks) {left right : Block}
    (hleft : left ∈ blocks) (hright : right ∈ blocks)
    (hne : left ≠ right) :
    (left.region pool).disjoint (right.region pool) := by
  obtain ⟨i, hi, hgetLeft⟩ := List.mem_iff_getElem.mp hleft
  obtain ⟨j, hj, hgetRight⟩ := List.mem_iff_getElem.mp hright
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have hord := hwell.1 i j hi hj hij
    rw [hgetLeft, hgetRight] at hord
    exact Or.inl (by
      simp only [Block.region, Region.endAddr]
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left hord pool.base)
  · subst j
    have : left = right := by rw [← hgetLeft, ← hgetRight]
    exact (hne this).elim
  · have hord := hwell.1 j i hj hi hij
    rw [hgetRight, hgetLeft] at hord
    exact Or.inr (by
      simp only [Block.region, Region.endAddr]
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left hord pool.base)

theorem block_inside {pool : Region} {blocks : List Block}
    (h : wellFormed pool blocks) {b : Block} (hb : b ∈ blocks) {i : Nat}
    (hi : i < b.bytes) : pool.contains (pool.base + b.offset + i) := by
  rcases h with ⟨_, _, _, hall⟩
  have hbound := (hall b hb).2.1
  simp only [Region.contains, Region.endAddr]
  constructor
  · exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  · have hin : b.offset + i < pool.bytes :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi b.offset) hbound
    simpa only [Nat.add_assoc] using Nat.add_lt_add_left hin pool.base

/-- Splitting preserves byte count, the first algebraic TLSF invariant. -/
theorem split_preserves_bytes (b : Block) (wanted : Nat) (h : wanted ≤ b.bytes) :
    wanted + (b.bytes - wanted) = b.bytes := by
  omega

theorem splitBlock_offsets (b : Block) (wanted : Nat) :
    (splitBlock b wanted).1.offset = b.offset ∧
      (splitBlock b wanted).2.offset = b.offset + wanted := by
  exact ⟨rfl, rfl⟩

theorem splitAt_contains_remainder {blocks : List Block} {i wanted : Nat}
    {b : Block} (hget : blocks[i]? = some b) :
    (splitBlock b wanted).2 ∈ splitAt blocks i wanted := by
  induction blocks generalizing i b with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst b
          simp [splitAt]
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp [splitAt, ih hget]

theorem splitAt_contains_allocated {blocks : List Block} {i wanted : Nat}
    {b : Block} (hget : blocks[i]? = some b) :
    (splitBlock b wanted).1 ∈ splitAt blocks i wanted := by
  induction blocks generalizing i b with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst b
          simp [splitAt]
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp [splitAt, ih hget]

theorem markAllocatedAt_contains {blocks : List Block} {i : Nat} {b : Block}
    (hget : blocks[i]? = some b) : markAllocated b ∈ markAllocatedAt blocks i := by
  induction blocks generalizing i b with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst b
          cases rest <;> simp [markAllocatedAt]
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp [markAllocatedAt, ih hget]

theorem splitBlock_preserves_end (b : Block) (wanted : Nat) (h : wanted ≤ b.bytes) :
    (splitBlock b wanted).2.offset + (splitBlock b wanted).2.bytes =
      b.offset + b.bytes := by
  simp only [splitBlock]
  omega

theorem contiguousFrom_split_head (cursor : Nat) (b : Block) (rest : List Block)
    (wanted : Nat)
    (hcontig : contiguousFrom cursor (b :: rest))
    (hwanted : wanted ≤ b.bytes) :
    contiguousFrom cursor
      ((splitBlock b wanted).1 :: (splitBlock b wanted).2 :: rest) := by
  simp only [contiguousFrom] at hcontig ⊢
  rcases hcontig with ⟨hoffset, hrest⟩
  constructor
  · exact hoffset
  constructor
  · simp only [splitBlock]
    omega
  · simp only [splitBlock]
    have heq : cursor + wanted + (b.bytes - wanted) = cursor + b.bytes := by
      omega
    rwa [heq]

theorem partitions_split_head (pool : Region) (b : Block) (rest : List Block)
    (wanted : Nat)
    (hparts : partitions pool (b :: rest)) (hwanted : wanted ≤ b.bytes) :
    partitions pool ((splitBlock b wanted).1 :: (splitBlock b wanted).2 :: rest) := by
  rcases hparts with ⟨hcontig, hcover⟩
  constructor
  · exact contiguousFrom_split_head 0 b rest wanted hcontig hwanted
  · unfold covers at hcover ⊢
    simp only [List.map_cons, List.sum_cons, splitBlock] at hcover ⊢
    omega

theorem contiguousFrom_splitAt {blocks : List Block} {i : Nat} {b : Block}
    (cursor wanted : Nat) (hget : blocks[i]? = some b)
    (hcontig : contiguousFrom cursor blocks) (hwanted : wanted ≤ b.bytes) :
    contiguousFrom cursor (splitAt blocks i wanted) := by
  induction blocks generalizing i b cursor with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          exact contiguousFrom_split_head cursor head rest wanted hcontig hwanted
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [contiguousFrom] at hcontig ⊢
          rcases hcontig with ⟨hoffset, hrest⟩
          exact ⟨hoffset, ih (cursor := cursor + head.bytes)
            (b := b) hget hrest hwanted⟩

theorem covers_splitAt {pool : Region} {blocks : List Block} {i : Nat} {b : Block}
    (wanted : Nat) (hget : blocks[i]? = some b) (hcover : covers pool blocks)
    (hwanted : wanted ≤ b.bytes) : covers pool (splitAt blocks i wanted) := by
  unfold covers at hcover ⊢
  induction blocks generalizing i b pool with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          simp only [splitAt, List.map_cons, List.sum_cons, splitBlock] at hcover ⊢
          omega
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [splitAt, List.map_cons, List.sum_cons] at hcover ⊢
          have htail : (rest.map (fun b => b.bytes)).sum =
              pool.bytes - head.bytes := by omega
          have ih' := ih (pool := { pool with bytes := pool.bytes - head.bytes })
            (b := b) hget htail hwanted
          change (splitAt rest j wanted |>.map (fun b => b.bytes)).sum =
            pool.bytes - head.bytes at ih'
          omega

theorem partitions_splitAt {pool : Region} {blocks : List Block} {i : Nat} {b : Block}
    (wanted : Nat) (hget : blocks[i]? = some b) (hparts : partitions pool blocks)
    (hwanted : wanted ≤ b.bytes) : partitions pool (splitAt blocks i wanted) := by
  exact ⟨contiguousFrom_splitAt 0 wanted hget hparts.1 hwanted,
    covers_splitAt wanted hget hparts.2 hwanted⟩

theorem boundaryTagsFrom_split_head (previousFree : Bool) (b : Block)
    (rest : List Block) (wanted : Nat) (hbfree : b.free = true)
    (htags : boundaryTagsFrom previousFree (b :: rest)) :
    boundaryTagsFrom previousFree
      ((splitBlock b wanted).1 :: (splitBlock b wanted).2 :: rest) := by
  simp only [boundaryTagsFrom] at htags ⊢
  rcases htags with ⟨hprev, hrest⟩
  simp only [splitBlock]
  exact ⟨hprev, trivial, by simpa only [hbfree] using hrest⟩

theorem boundaryTagsFrom_splitAt {blocks : List Block} {i : Nat} {b : Block}
    (previousFree : Bool) (wanted : Nat) (hget : blocks[i]? = some b)
    (hbfree : b.free = true) (htags : boundaryTagsFrom previousFree blocks) :
    boundaryTagsFrom previousFree (splitAt blocks i wanted) := by
  induction blocks generalizing i b previousFree with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          exact boundaryTagsFrom_split_head previousFree head rest wanted hbfree htags
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [boundaryTagsFrom, splitAt] at htags ⊢
          exact ⟨htags.1, ih head.free hget hbfree htags.2⟩

theorem boundaryTags_splitAt {blocks : List Block} {i : Nat} {b : Block}
    (wanted : Nat) (hget : blocks[i]? = some b) (hbfree : b.free = true)
    (htags : boundaryTags blocks) : boundaryTags (splitAt blocks i wanted) :=
  boundaryTagsFrom_splitAt false wanted hget hbfree htags

theorem contiguousFrom_markAllocatedAt (blocks : List Block) (cursor i : Nat)
    (h : contiguousFrom cursor blocks) :
    contiguousFrom cursor (markAllocatedAt blocks i) := by
  induction blocks generalizing cursor i with
  | nil => trivial
  | cons b rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simpa [contiguousFrom, markAllocatedAt, markAllocated] using h
          | cons next tail =>
              simpa [contiguousFrom, markAllocatedAt, markAllocated] using h
      | succ j =>
          simp only [contiguousFrom, markAllocatedAt] at h ⊢
          exact ⟨h.1, ih (cursor + b.bytes) j h.2⟩

theorem covers_markAllocatedAt (pool : Region) (blocks : List Block) (i : Nat)
    (h : covers pool blocks) : covers pool (markAllocatedAt blocks i) := by
  unfold covers at h ⊢
  induction blocks generalizing i pool with
  | nil => exact h
  | cons b rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simpa [markAllocatedAt, markAllocated] using h
          | cons next tail => simpa [markAllocatedAt, markAllocated] using h
      | succ j =>
          simp only [markAllocatedAt, List.map_cons, List.sum_cons] at h ⊢
          have htail : (rest.map (fun b => b.bytes)).sum = pool.bytes - b.bytes := by
            omega
          have ih' := ih (pool := { pool with bytes := pool.bytes - b.bytes }) j htail
          change (markAllocatedAt rest j |>.map (fun b => b.bytes)).sum =
            pool.bytes - b.bytes at ih'
          omega

theorem partitions_markAllocatedAt (pool : Region) (blocks : List Block) (i : Nat)
    (h : partitions pool blocks) : partitions pool (markAllocatedAt blocks i) :=
  ⟨contiguousFrom_markAllocatedAt blocks 0 i h.1,
    covers_markAllocatedAt pool blocks i h.2⟩

theorem boundaryTagsFrom_markAllocatedAt {blocks : List Block} {i : Nat}
    {b : Block} (previousFree : Bool) (hget : blocks[i]? = some b)
    (hfree : b.free = true) (htags : boundaryTagsFrom previousFree blocks) :
    boundaryTagsFrom previousFree (markAllocatedAt blocks i) := by
  induction blocks generalizing i b previousFree with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          cases rest with
          | nil =>
              simpa [boundaryTagsFrom, markAllocatedAt, markAllocated] using htags
          | cons next tail =>
              simp only [boundaryTagsFrom] at htags ⊢
              rcases htags with ⟨hhead, _hnext, htail⟩
              simp only [markAllocatedAt, markAllocated]
              exact ⟨hhead, rfl, htail⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [boundaryTagsFrom, markAllocatedAt] at htags ⊢
          exact ⟨htags.1, ih head.free hget hfree htags.2⟩

theorem boundaryTags_markAllocatedAt {blocks : List Block} {i : Nat} {b : Block}
    (hget : blocks[i]? = some b) (hfree : b.free = true)
    (htags : boundaryTags blocks) : boundaryTags (markAllocatedAt blocks i) :=
  boundaryTagsFrom_markAllocatedAt false hget hfree htags

def blocksShaped (blocks : List Block) : Prop :=
  ∀ b ∈ blocks, 0 < b.bytes ∧ b.aligned

theorem wellFormed_blocksShaped {pool : Region} {blocks : List Block}
    (hwell : wellFormed pool blocks) : blocksShaped blocks := by
  intro b hmem
  exact ⟨(hwell.2.2.2 b hmem).1, (hwell.2.2.2 b hmem).2.2⟩

theorem blocksShaped_markAllocatedAt {blocks : List Block} {i : Nat}
    (hshape : blocksShaped blocks) : blocksShaped (markAllocatedAt blocks i) := by
  induction blocks generalizing i with
  | nil =>
      intro b hmem
      simp [markAllocatedAt] at hmem
  | cons head rest ih =>
      have hhead := hshape head (by simp)
      have hrest : blocksShaped rest := by
        intro b hmem
        exact hshape b (by simp [hmem])
      cases i with
      | zero =>
          cases rest with
          | nil =>
              intro b hmem
              simp [markAllocatedAt] at hmem
              subst b
              simpa [markAllocated, Block.aligned] using hhead
          | cons next tail =>
              intro b hmem
              simp only [markAllocatedAt, List.mem_cons] at hmem
              rcases hmem with hallocated | htail
              · subst b
                simpa [markAllocated, Block.aligned] using hhead
              · rcases htail with hnext | htail
                · subst b
                  simpa [Block.aligned] using hrest next (by simp)
                · exact hrest b (by simp [htail])
      | succ j =>
          intro b hmem
          simp only [markAllocatedAt, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hhead
          · exact ih hrest b hmem

theorem blocksShaped_splitAt {blocks : List Block} {i wanted : Nat} {b : Block}
    (hget : blocks[i]? = some b) (hshape : blocksShaped blocks)
    (hcan : canSplit b wanted) (hwanted : alignment ∣ wanted) :
    blocksShaped (splitAt blocks i wanted) := by
  induction blocks generalizing i b with
  | nil => simp at hget
  | cons head rest ih =>
      have hhead := hshape head (by simp)
      have hrest : blocksShaped rest := by
        intro old hmem
        exact hshape old (by simp [hmem])
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst b
          have hnonempty := splitBlock_nonempty hcan
          have haligned : (splitBlock head wanted).1.aligned ∧
              (splitBlock head wanted).2.aligned := by
            rcases hhead.2 with ⟨hoffset, hbytes⟩
            simp only [Block.aligned, splitBlock]
            exact ⟨⟨hoffset, hwanted⟩,
              ⟨Nat.dvd_add hoffset hwanted, Nat.dvd_sub hbytes hwanted⟩⟩
          intro current hmem
          simp only [splitAt, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact ⟨hnonempty.1, haligned.1⟩
          · rcases hmem with rfl | hmem
            · exact ⟨hnonempty.2, haligned.2⟩
            · exact hrest current hmem
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          intro current hmem
          simp only [splitAt, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hhead
          · exact ih (b := b) hget hrest hcan current hmem

theorem allocateChosenAt_blocksShaped {blocks next : List Block}
    {i wanted : Nat} {b allocated : Block} (hget : blocks[i]? = some b)
    (hshape : blocksShaped blocks)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    blocksShaped next := by
  obtain ⟨_, _, hwanted, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hsuccess
  · rcases hsplit with ⟨hcan, _, rfl⟩
    exact blocksShaped_splitAt hget hshape hcan hwanted
  · rcases hwhole with ⟨_, _, rfl⟩
    exact blocksShaped_markAllocatedAt hshape

theorem allocateAt_preserves_partitions {pool : Region} {blocks : List Block}
    {i wanted : Nat} {b : Block} (hget : blocks[i]? = some b)
    (hparts : partitions pool blocks)
    (hsuccess : allocateAt blocks i wanted =
      some ((splitBlock b wanted).1, splitAt blocks i wanted)) :
    partitions pool (splitAt blocks i wanted) := by
  have hpre := (allocateAt_success_iff hget).1 hsuccess
  exact partitions_splitAt wanted hget hparts (canSplit_wanted_le hpre.2.1)

theorem allocateAt_preserves_boundaryTags {blocks : List Block}
    {i wanted : Nat} {b : Block} (hget : blocks[i]? = some b)
    (htags : boundaryTags blocks)
    (hsuccess : allocateAt blocks i wanted =
      some ((splitBlock b wanted).1, splitAt blocks i wanted)) :
    boundaryTags (splitAt blocks i wanted) := by
  have hpre := (allocateAt_success_iff hget).1 hsuccess
  exact boundaryTags_splitAt wanted hget hpre.1 htags

theorem allocateChosenAt_preserves_partitions {pool : Region}
    {blocks next : List Block} {i wanted : Nat} {b allocated : Block}
    (hget : blocks[i]? = some b) (hparts : partitions pool blocks)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    partitions pool next := by
  obtain ⟨_, _, _, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hsuccess
  · rcases hsplit with ⟨hcan, _, rfl⟩
    exact partitions_splitAt wanted hget hparts (canSplit_wanted_le hcan)
  · rcases hwhole with ⟨_, _, rfl⟩
    exact partitions_markAllocatedAt pool blocks i hparts

theorem allocateChosenAt_preserves_boundaryTags {blocks next : List Block}
    {i wanted : Nat} {b allocated : Block} (hget : blocks[i]? = some b)
    (htags : boundaryTags blocks)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    boundaryTags next := by
  obtain ⟨hfree, _, _, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hsuccess
  · rcases hsplit with ⟨_, _, rfl⟩
    exact boundaryTags_splitAt wanted hget hfree htags
  · rcases hwhole with ⟨_, _, rfl⟩
    exact boundaryTags_markAllocatedAt hget hfree htags

theorem allocateChosenAt_preserves_wellFormed {pool : Region}
    {blocks next : List Block} {i wanted : Nat} {b allocated : Block}
    (hget : blocks[i]? = some b) (hwell : wellFormed pool blocks)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    wellFormed pool next := by
  apply wellFormed_of_partitions_boundary
    (allocateChosenAt_preserves_partitions hget hwell.2.1 hsuccess)
    (allocateChosenAt_preserves_boundaryTags hget hwell.2.2.1 hsuccess)
  exact allocateChosenAt_blocksShaped hget (wellFormed_blocksShaped hwell) hsuccess

theorem splitBlock_aligned {b : Block} {wanted : Nat} (hb : b.aligned)
    (hwanted : alignment ∣ wanted) :
    (splitBlock b wanted).1.aligned ∧ (splitBlock b wanted).2.aligned := by
  rcases hb with ⟨hoffset, hbytes⟩
  simp only [Block.aligned, splitBlock]
  exact ⟨⟨hoffset, hwanted⟩,
    ⟨Nat.dvd_add hoffset hwanted, Nat.dvd_sub hbytes hwanted⟩⟩

theorem allocateAt_result {blocks : List Block} {i wanted : Nat} {b : Block}
    (hget : blocks[i]? = some b) (hb : b.aligned)
    (hsuccess : allocateAt blocks i wanted =
      some ((splitBlock b wanted).1, splitAt blocks i wanted)) :
    (splitBlock b wanted).1.bytes = wanted ∧
      (splitBlock b wanted).1.free = false ∧
      (splitBlock b wanted).1.aligned ∧
      0 < (splitBlock b wanted).1.bytes := by
  have hpre := (allocateAt_success_iff hget).1 hsuccess
  have haligned := (splitBlock_aligned hb hpre.2.2).1
  have hnonempty := (splitBlock_nonempty hpre.2.1).1
  exact ⟨rfl, rfl, haligned, hnonempty⟩

theorem markAllocated_aligned (b : Block) (haligned : b.aligned) :
    (markAllocated b).aligned := by
  simpa [markAllocated, Block.aligned] using haligned

theorem allocateChosenAt_result {blocks next : List Block} {i wanted : Nat}
    {b allocated : Block} (hget : blocks[i]? = some b) (hb : b.aligned)
    (hsuccess : allocateChosenAt blocks i wanted = some (allocated, next)) :
    allocated.free = false ∧ allocated.aligned ∧ wanted ≤ allocated.bytes ∧
      ((canSplit b wanted ∧ allocated.bytes = wanted) ∨
        (¬ canSplit b wanted ∧ allocated.bytes = b.bytes)) := by
  obtain ⟨_, hwanted, halignment, hsplit | hwhole⟩ :=
    allocateChosenAt_success_cases hget hsuccess
  · rcases hsplit with ⟨hcan, rfl, _⟩
    exact ⟨rfl, (splitBlock_aligned hb halignment).1,
      Nat.le_refl _, Or.inl ⟨hcan, rfl⟩⟩
  · rcases hwhole with ⟨hnosplit, rfl, _⟩
    exact ⟨rfl, markAllocated_aligned b hb,
      hwanted, Or.inr ⟨hnosplit, rfl⟩⟩

theorem splitBlock_regions_disjoint (pool : Region) (b : Block) (wanted : Nat) :
    ((splitBlock b wanted).1.region pool).disjoint
      ((splitBlock b wanted).2.region pool) := by
  simp [splitBlock, Block.region, Region.disjoint, Region.endAddr, Nat.add_assoc]

/-- The logical ownership transfer used by the executable TLSF split: no byte
is invented, duplicated, dropped, or left behind. -/
theorem ownsBytes_splitBlock {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) (b : Block) (wanted : Nat) (h : wanted ≤ b.bytes) :
    OwnsBytes (PROP := PROP) (b.region pool) ⊣⊢
      OwnsBytes ((splitBlock b wanted).1.region pool) ∗
      OwnsBytes ((splitBlock b wanted).2.region pool) := by
  unfold OwnsBytes Block.region splitBlock
  simpa only [Nat.add_assoc] using
    (ByteRegionLogic.split (PROP := PROP)
      (r := { base := pool.base + b.offset, bytes := b.bytes })
      (left := wanted) (right := b.bytes - wanted)
      (split_preserves_bytes b wanted h).symm)

/-- Coalescing adjacent blocks preserves byte count. -/
def coalesceBlocks (left right : Block) : Block :=
  { offset := left.offset, bytes := left.bytes + right.bytes, free := true,
    prevFree := left.prevFree, prevFreeLink := none, nextFreeLink := none }

def canCoalesce (left right : Block) : Prop :=
  left.free = true ∧ right.free = true ∧
    right.offset = left.offset + left.bytes

/-- Coalesce blocks at indices `i` and `i+1`. Verified callers establish both
lookups and adjacency; invalid indices leave the list unchanged. -/
def coalesceAt : List Block -> Nat -> List Block
  | left :: right :: rest, 0 => coalesceBlocks left right :: rest
  | head :: rest, i + 1 => head :: coalesceAt rest i
  | blocks, _ => blocks

theorem coalesce_preserves_bytes (left right : Block) :
    left.bytes + right.bytes = (coalesceBlocks left right).bytes := by
  rfl

theorem coalesceBlocks_aligned {left right : Block}
    (hleft : left.aligned) (hright : right.aligned) :
    (coalesceBlocks left right).aligned := by
  exact ⟨hleft.1, Nat.dvd_add hleft.2 hright.2⟩

theorem contiguousFrom_coalesce_head (cursor : Nat) (left right : Block)
    (rest : List Block)
    (hcontig : contiguousFrom cursor (left :: right :: rest)) :
    contiguousFrom cursor (coalesceBlocks left right :: rest) := by
  simp only [contiguousFrom] at hcontig ⊢
  rcases hcontig with ⟨hleft, hright, hrest⟩
  constructor
  · exact hleft
  · simp only [coalesceBlocks]
    simpa only [Nat.add_assoc] using hrest

theorem partitions_coalesce_head (pool : Region) (left right : Block)
    (rest : List Block) (hparts : partitions pool (left :: right :: rest)) :
    partitions pool (coalesceBlocks left right :: rest) := by
  rcases hparts with ⟨hcontig, hcover⟩
  constructor
  · exact contiguousFrom_coalesce_head 0 left right rest hcontig
  · unfold covers at hcover ⊢
    simp only [List.map_cons, List.sum_cons, coalesceBlocks] at hcover ⊢
    omega

theorem contiguousFrom_coalesceAt {blocks : List Block} {i : Nat}
    {left right : Block} (cursor : Nat)
    (hleft : blocks[i]? = some left) (hright : blocks[i + 1]? = some right)
    (hcontig : contiguousFrom cursor blocks) :
    contiguousFrom cursor (coalesceAt blocks i) := by
  induction blocks generalizing i left right cursor with
  | nil => simp at hleft
  | cons head rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simp at hright
          | cons next tail =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
              simp only [Nat.zero_add, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at hright
              subst hleft
              subst hright
              exact contiguousFrom_coalesce_head cursor head next tail hcontig
      | succ j =>
          simp only [List.getElem?_cons_succ] at hleft
          have hright' : rest[j + 1]? = some right := by
            change rest[j + 1]? = some right at hright
            exact hright
          simp only [coalesceAt, contiguousFrom] at hcontig ⊢
          exact ⟨hcontig.1, ih (cursor := cursor + head.bytes)
            hleft hright' hcontig.2⟩

theorem covers_coalesceAt {pool : Region} {blocks : List Block} {i : Nat}
    {left right : Block} (hleft : blocks[i]? = some left)
    (hright : blocks[i + 1]? = some right) (hcover : covers pool blocks) :
    covers pool (coalesceAt blocks i) := by
  unfold covers at hcover ⊢
  induction blocks generalizing i left right pool with
  | nil => simp at hleft
  | cons head rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simp at hright
          | cons next tail =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
              simp only [Nat.zero_add, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at hright
              subst hleft
              subst hright
              simp only [coalesceAt, List.map_cons, List.sum_cons, coalesceBlocks]
              simpa [Nat.add_assoc] using hcover
      | succ j =>
          simp only [List.getElem?_cons_succ] at hleft
          have hright' : rest[j + 1]? = some right := by
            change rest[j + 1]? = some right at hright
            exact hright
          simp only [coalesceAt, List.map_cons, List.sum_cons] at hcover ⊢
          have htail : (rest.map (fun b => b.bytes)).sum =
              pool.bytes - head.bytes := by omega
          have ih' := ih (pool := { pool with bytes := pool.bytes - head.bytes })
            hleft hright' htail
          change (coalesceAt rest j |>.map (fun b => b.bytes)).sum =
            pool.bytes - head.bytes at ih'
          omega

theorem partitions_coalesceAt {pool : Region} {blocks : List Block} {i : Nat}
    {left right : Block} (hleft : blocks[i]? = some left)
    (hright : blocks[i + 1]? = some right) (hparts : partitions pool blocks) :
    partitions pool (coalesceAt blocks i) :=
  ⟨contiguousFrom_coalesceAt 0 hleft hright hparts.1,
    covers_coalesceAt hleft hright hparts.2⟩

theorem boundaryTagsFrom_coalesce_head (previousFree : Bool)
    (left right : Block) (rest : List Block) (hcan : canCoalesce left right)
    (htags : boundaryTagsFrom previousFree (left :: right :: rest)) :
    boundaryTagsFrom previousFree (coalesceBlocks left right :: rest) := by
  rcases hcan with ⟨hleftFree, hrightFree, _⟩
  simp only [boundaryTagsFrom] at htags ⊢
  rcases htags with ⟨hleftPrev, _hrightPrev, hrest⟩
  simp only [coalesceBlocks]
  exact ⟨hleftPrev, by simpa only [hrightFree] using hrest⟩

theorem boundaryTagsFrom_coalesceAt {blocks : List Block} {i : Nat}
    {left right : Block} (previousFree : Bool)
    (hleft : blocks[i]? = some left) (hright : blocks[i + 1]? = some right)
    (hcan : canCoalesce left right)
    (htags : boundaryTagsFrom previousFree blocks) :
    boundaryTagsFrom previousFree (coalesceAt blocks i) := by
  induction blocks generalizing i left right previousFree with
  | nil => simp at hleft
  | cons head rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simp at hright
          | cons next tail =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
              simp only [Nat.zero_add, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at hright
              subst hleft
              subst hright
              exact boundaryTagsFrom_coalesce_head previousFree head next tail hcan htags
      | succ j =>
          simp only [List.getElem?_cons_succ] at hleft
          have hright' : rest[j + 1]? = some right := by
            change rest[j + 1]? = some right at hright
            exact hright
          simp only [boundaryTagsFrom, coalesceAt] at htags ⊢
          exact ⟨htags.1, ih head.free hleft hright' hcan htags.2⟩

theorem boundaryTags_coalesceAt {blocks : List Block} {i : Nat}
    {left right : Block} (hleft : blocks[i]? = some left)
    (hright : blocks[i + 1]? = some right) (hcan : canCoalesce left right)
    (htags : boundaryTags blocks) : boundaryTags (coalesceAt blocks i) :=
  boundaryTagsFrom_coalesceAt false hleft hright hcan htags

/-- Adjacent ownership fragments recombine into ownership of the merged block. -/
theorem ownsBytes_coalesceBlocks {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (pool : Region) (left right : Block)
    (hadjacent : right.offset = left.offset + left.bytes) :
    OwnsBytes (PROP := PROP) (left.region pool) ∗ OwnsBytes (right.region pool) ⊣⊢
      OwnsBytes ((coalesceBlocks left right).region pool) := by
  unfold OwnsBytes Block.region coalesceBlocks
  rw [hadjacent]
  simpa only [Nat.add_assoc] using
    (ByteRegionLogic.split (PROP := PROP)
      (r := { base := pool.base + left.offset, bytes := left.bytes + right.bytes })
      (left := left.bytes) (right := right.bytes) rfl).symm

/-- Change only allocation state; physical layout is untouched. -/
def markFreeAt : List Block -> Nat -> List Block
  | [], _ => []
  | [b], 0 =>
      [{ offset := b.offset, bytes := b.bytes, free := true,
         prevFree := b.prevFree, prevFreeLink := none, nextFreeLink := none }]
  | b :: next :: rest, 0 =>
      { offset := b.offset, bytes := b.bytes, free := true,
        prevFree := b.prevFree, prevFreeLink := none, nextFreeLink := none } ::
        { next with prevFree := true } :: rest
  | b :: rest, i + 1 => b :: markFreeAt rest i

def deallocateAt (pool : Region) (blocks : List Block) (i : Nat)
    (returned : Region) : Option (List Block) :=
  match blocks[i]? with
  | none => none
  | some b =>
      if b.free = false ∧ returned = b.region pool then
        some (markFreeAt blocks i)
      else none

theorem deallocateAt_success_iff {pool : Region} {blocks : List Block} {i : Nat}
    {b : Block} {returned : Region} (hget : blocks[i]? = some b) :
    deallocateAt pool blocks i returned = some (markFreeAt blocks i) ↔
      b.free = false ∧ returned = b.region pool := by
  simp [deallocateAt, hget]

theorem deallocateAt_rejects_double_free {pool : Region} {blocks : List Block}
    {i : Nat} {b : Block} {returned : Region} (hget : blocks[i]? = some b)
    (hfree : b.free = true) : deallocateAt pool blocks i returned = none := by
  simp [deallocateAt, hget, hfree]

theorem deallocateAt_rejects_wrong_region {pool : Region} {blocks : List Block}
    {i : Nat} {b : Block} {returned : Region} (hget : blocks[i]? = some b)
    (hregion : returned ≠ b.region pool) :
    deallocateAt pool blocks i returned = none := by
  simp [deallocateAt, hget, hregion]

theorem contiguousFrom_markFreeAt (blocks : List Block) (cursor i : Nat)
    (h : contiguousFrom cursor blocks) :
    contiguousFrom cursor (markFreeAt blocks i) := by
  induction blocks generalizing cursor i with
  | nil => trivial
  | cons b rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simpa [contiguousFrom, markFreeAt] using h
          | cons next tail => simpa [contiguousFrom, markFreeAt] using h
      | succ j =>
          simp only [contiguousFrom, markFreeAt] at h ⊢
          exact ⟨h.1, ih (cursor + b.bytes) j h.2⟩

theorem covers_markFreeAt (pool : Region) (blocks : List Block) (i : Nat)
    (h : covers pool blocks) : covers pool (markFreeAt blocks i) := by
  unfold covers at h ⊢
  induction blocks generalizing i pool with
  | nil => exact h
  | cons b rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simpa [markFreeAt] using h
          | cons next tail => simpa [markFreeAt] using h
      | succ j =>
          simp only [markFreeAt, List.map_cons, List.sum_cons] at h ⊢
          have htail : (rest.map (fun b => b.bytes)).sum = pool.bytes - b.bytes := by
            omega
          have ih' := ih (pool := { pool with bytes := pool.bytes - b.bytes }) j htail
          change (markFreeAt rest j |>.map (fun b => b.bytes)).sum =
            pool.bytes - b.bytes at ih'
          omega

theorem partitions_markFreeAt (pool : Region) (blocks : List Block) (i : Nat)
    (h : partitions pool blocks) : partitions pool (markFreeAt blocks i) :=
  ⟨contiguousFrom_markFreeAt blocks 0 i h.1, covers_markFreeAt pool blocks i h.2⟩

theorem boundaryTagsFrom_markFreeAt {blocks : List Block} {i : Nat} {b : Block}
    (previousFree : Bool) (hget : blocks[i]? = some b) (hallocated : b.free = false)
    (htags : boundaryTagsFrom previousFree blocks) :
    boundaryTagsFrom previousFree (markFreeAt blocks i) := by
  induction blocks generalizing i b previousFree with
  | nil => simp at hget
  | cons head rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          cases rest with
          | nil => simpa [boundaryTagsFrom, markFreeAt] using htags
          | cons next tail =>
              simp only [boundaryTagsFrom] at htags ⊢
              rcases htags with ⟨hhead, hnext, htail⟩
              simp only [markFreeAt]
              exact ⟨hhead, rfl, htail⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [boundaryTagsFrom, markFreeAt] at htags ⊢
          exact ⟨htags.1, ih head.free hget hallocated htags.2⟩

theorem boundaryTags_markFreeAt {blocks : List Block} {i : Nat} {b : Block}
    (hget : blocks[i]? = some b) (hallocated : b.free = false)
    (htags : boundaryTags blocks) : boundaryTags (markFreeAt blocks i) :=
  boundaryTagsFrom_markFreeAt false hget hallocated htags

theorem deallocateAt_preserves_partitions {pool : Region} {blocks : List Block}
    {i : Nat} {b : Block} {returned : Region} (hget : blocks[i]? = some b)
    (hparts : partitions pool blocks)
    (hsuccess : deallocateAt pool blocks i returned = some (markFreeAt blocks i)) :
    partitions pool (markFreeAt blocks i) := by
  have _hpre := (deallocateAt_success_iff hget).1 hsuccess
  exact partitions_markFreeAt pool blocks i hparts

theorem deallocateAt_preserves_boundaryTags {pool : Region} {blocks : List Block}
    {i : Nat} {b : Block} {returned : Region} (hget : blocks[i]? = some b)
    (htags : boundaryTags blocks)
    (hsuccess : deallocateAt pool blocks i returned = some (markFreeAt blocks i)) :
    boundaryTags (markFreeAt blocks i) := by
  have hpre := (deallocateAt_success_iff hget).1 hsuccess
  exact boundaryTags_markFreeAt hget hpre.1 htags

end Luffs.Allocator.TLSF
