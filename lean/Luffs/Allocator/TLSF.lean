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
