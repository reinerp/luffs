import Luffs.Memory.Iris

set_option autoImplicit false

namespace Luffs.Allocator.TLSF

open Luffs.Memory
open Iris Iris.BI

/-- Minimum block alignment. Metadata flags occupy the low alignment bits. -/
def alignment : Nat := 8

def firstLevelCount : Nat := 64
def secondLevelCount : Nat := 32
def linearCutoff : Nat := alignment * secondLevelCount
def minimumBlockBytes : Nat := 16

structure SizeClass where
  fl : Fin firstLevelCount
  sl : Fin secondLevelCount
deriving DecidableEq, Repr

/-- Two-level size mapping. Requests through 256 bytes use 32 linear 8-byte
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

theorem sizeClass_indices_in_bounds (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) :
    (sizeClass size hsize hmax).fl.val < firstLevelCount ∧
      (sizeClass size hsize hmax).sl.val < secondLevelCount := by
  exact ⟨(sizeClass size hsize hmax).fl.isLt,
    (sizeClass size hsize hmax).sl.isLt⟩

def linearBinNumber (size : Nat) : Nat := (size - 1) / alignment
def linearBinLower (size : Nat) : Nat := linearBinNumber size * alignment + 1
def linearBinUpper (size : Nat) : Nat := (linearBinNumber size + 1) * alignment

theorem linear_sizeClass_values (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) (hlinear : size ≤ linearCutoff) :
    (sizeClass size hsize hmax).fl.val = 0 ∧
      (sizeClass size hsize hmax).sl.val = linearBinNumber size := by
  simp [sizeClass, hlinear, linearBinNumber]

/-- A request in the linear range belongs to the selected 8-byte bin. The
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

theorem high_sizeClass_sl (size : Nat) (hsize : 0 < size)
    (hmax : size < 2 ^ firstLevelCount) (hhigh : linearCutoff < size)
    (hlog : 5 ≤ size.log2) :
    (sizeClass size hsize hmax).sl.val = highBinNumber size := by
  simp [sizeClass, Nat.not_le_of_gt hhigh, highBinNumber, highBinStep,
    high_sizeClass_no_wrap size hsize hlog]

/-- A compact pure view used by the executable allocator and its Iris invariant. -/
structure Block where
  offset : Nat
  bytes : Nat
  free : Bool
deriving DecidableEq, Repr

def splitBlock (b : Block) (wanted : Nat) : Block × Block :=
  ({ b with bytes := wanted, free := false },
   { offset := b.offset + wanted, bytes := b.bytes - wanted, free := true })

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

def partitions (pool : Region) (blocks : List Block) : Prop :=
  contiguousFrom 0 blocks ∧ covers pool blocks

def wellFormed (pool : Region) (blocks : List Block) : Prop :=
  ordered blocks ∧ partitions pool blocks ∧
    ∀ b ∈ blocks, 0 < b.bytes ∧ b.offset + b.bytes ≤ pool.bytes ∧ b.aligned

theorem block_inside {pool : Region} {blocks : List Block}
    (h : wellFormed pool blocks) {b : Block} (hb : b ∈ blocks) {i : Nat}
    (hi : i < b.bytes) : pool.contains (pool.base + b.offset + i) := by
  rcases h with ⟨_, _, hall⟩
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

theorem allocateAt_preserves_partitions {pool : Region} {blocks : List Block}
    {i wanted : Nat} {b : Block} (hget : blocks[i]? = some b)
    (hparts : partitions pool blocks)
    (hsuccess : allocateAt blocks i wanted =
      some ((splitBlock b wanted).1, splitAt blocks i wanted)) :
    partitions pool (splitAt blocks i wanted) := by
  have hpre := (allocateAt_success_iff hget).1 hsuccess
  exact partitions_splitAt wanted hget hparts (canSplit_wanted_le hpre.2.1)

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
theorem coalesce_preserves_bytes (left right : Block) :
    left.bytes + right.bytes = ({ left with bytes := left.bytes + right.bytes }).bytes := by
  rfl

end Luffs.Allocator.TLSF
