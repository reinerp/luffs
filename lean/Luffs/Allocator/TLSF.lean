import Luffs.Memory.Iris

set_option autoImplicit false

namespace Luffs.Allocator.TLSF

open Luffs.Memory

/-- Minimum block alignment. Metadata flags occupy the low alignment bits. -/
def alignment : Nat := 8

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
