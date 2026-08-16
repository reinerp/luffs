import Luffs.Memory.Iris

set_option autoImplicit false

namespace Luffs.Allocator.TLSF

open Luffs.Memory

/-- Minimum block alignment. Metadata flags occupy the low alignment bits. -/
def alignment : Nat := 8

def firstLevelCount : Nat := 64
def secondLevelCount : Nat := 32
def linearCutoff : Nat := alignment * secondLevelCount

structure SizeClass where
  fl : Fin firstLevelCount
  sl : Fin secondLevelCount
deriving DecidableEq, Repr

/-- Two-level size mapping. The modulo is executable totalization; the
subsequent suitability proof must show it never wraps for admissible sizes. -/
def sizeClass (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) : SizeClass :=
  let log := size.log2
  let base := 2 ^ log
  let step := if log < 5 then alignment else 2 ^ (log - 5)
  {
    fl := ⟨log, (Nat.log2_lt (Nat.ne_of_gt hsize)).2 hmax⟩
    sl := ⟨((size - base) / step) % secondLevelCount,
      Nat.mod_lt _ (by decide : 0 < secondLevelCount)⟩
  }

theorem sizeClass_fl (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) :
    (sizeClass size hsize hmax).fl.val = size.log2 := by
  rfl

theorem sizeClass_indices_in_bounds (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) :
    (sizeClass size hsize hmax).fl.val < firstLevelCount ∧
      (sizeClass size hsize hmax).sl.val < secondLevelCount := by
  exact ⟨(sizeClass size hsize hmax).fl.isLt,
    (sizeClass size hsize hmax).sl.isLt⟩

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

theorem high_sizeClass_sl (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) (hlog : 5 ≤ size.log2) :
    (sizeClass size hsize hmax).sl.val = highBinNumber size := by
  have hnlt : ¬size.log2 < 5 := Nat.not_lt_of_ge hlog
  simp [sizeClass, hnlt, highBinNumber, highBinStep,
    high_sizeClass_no_wrap size hsize hlog]

/-- A compact pure view used by the executable allocator and its Iris invariant. -/
structure Block where
  offset : Nat
  bytes : Nat
  free : Bool
deriving DecidableEq, Repr

def Block.region (pool : Region) (b : Block) : Region :=
  { base := pool.base + b.offset, bytes := b.bytes }

def ordered (blocks : List Block) : Prop :=
  ∀ i j (hi : i < blocks.length) (hj : j < blocks.length), i < j ->
    (blocks[i]'hi).offset + (blocks[i]'hi).bytes ≤ (blocks[j]'hj).offset

def covers (pool : Region) (blocks : List Block) : Prop :=
  (blocks.map (fun b => b.bytes)).sum = pool.bytes

def wellFormed (pool : Region) (blocks : List Block) : Prop :=
  ordered blocks ∧ covers pool blocks ∧
    ∀ b ∈ blocks, 0 < b.bytes ∧ b.offset + b.bytes ≤ pool.bytes

theorem block_inside {pool : Region} {blocks : List Block}
    (h : wellFormed pool blocks) {b : Block} (hb : b ∈ blocks) {i : Nat}
    (hi : i < b.bytes) : pool.contains (pool.base + b.offset + i) := by
  rcases h with ⟨_, _, hall⟩
  have hbound := (hall b hb).2
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

/-- Coalescing adjacent blocks preserves byte count. -/
theorem coalesce_preserves_bytes (left right : Block) :
    left.bytes + right.bytes = ({ left with bytes := left.bytes + right.bytes }).bytes := by
  rfl

end Luffs.Allocator.TLSF
