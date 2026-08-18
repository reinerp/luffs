import Iris

set_option autoImplicit false

namespace Luffs.Memory

/-- Byte addresses in the Luffs abstract machine. -/
abbrev Addr := Nat

/-- A byte in the Luffs abstract machine. -/
abbrev Byte := Fin 256

/-- A half-open byte range `[base, base + bytes)`. -/
structure Region where
  base : Addr
  bytes : Nat
deriving DecidableEq, Repr

def Region.endAddr (r : Region) : Addr := r.base + r.bytes

def Region.contains (r : Region) (p : Addr) : Prop :=
  r.base ≤ p ∧ p < r.endAddr

instance (r : Region) (p : Addr) : Decidable (r.contains p) := by
  unfold Region.contains Region.endAddr
  infer_instance

def Region.disjoint (a b : Region) : Prop :=
  a.endAddr ≤ b.base ∨ b.endAddr ≤ a.base

/-- The pure layout of a live allocation. Ownership is carried separately by Iris. -/
structure Allocation where
  region : Region
  align : Nat
  align_pos : 0 < align
  base_aligned : region.base % align = 0
  nonempty : 0 < region.bytes

theorem contains_offset (r : Region) (i : Nat) (hi : i < r.bytes) :
    r.contains (r.base + i) := by
  simp only [Region.contains, Region.endAddr]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩

theorem disjoint_symmetric {a b : Region} :
    a.disjoint b ↔ b.disjoint a := by
  simp only [Region.disjoint, or_comm]

/-- Disjointness is inherited by a subregion of the left-hand region. This is
the arithmetic bridge used when an allocation payload write is known to stay
inside a pool that is disjoint from allocator metadata. -/
theorem Region.subregion_disjoint_left {inner outer other : Region}
    (hbase : outer.base ≤ inner.base)
    (hend : inner.endAddr ≤ outer.endAddr)
    (hdisjoint : outer.disjoint other) : inner.disjoint other := by
  unfold Region.disjoint Region.endAddr at hdisjoint ⊢
  rcases hdisjoint with hbefore | hafter
  · exact Or.inl (Nat.le_trans hend hbefore)
  · exact Or.inr (Nat.le_trans hafter hbase)

theorem not_contains_of_disjoint {a b : Region} (h : a.disjoint b)
    {p : Addr} (hp : a.contains p) : ¬b.contains p := by
  simp only [Region.disjoint, Region.endAddr] at h
  simp only [Region.contains, Region.endAddr] at hp ⊢
  intro hbp
  rcases h with h | h
  · exact (Nat.not_lt_of_ge (Nat.le_trans h hbp.1)) hp.2
  · exact (Nat.not_lt_of_ge (Nat.le_trans h hp.1)) hbp.2

theorem common_address_of_not_disjoint {a b : Region}
    (ha : 0 < a.bytes) (hb : 0 < b.bytes) (h : ¬a.disjoint b) :
    ∃ p, a.contains p ∧ b.contains p := by
  simp only [Region.disjoint, Region.endAddr, not_or] at h
  have hrightA : b.base < a.base + a.bytes := Nat.lt_of_not_ge h.1
  have hrightB : a.base < b.base + b.bytes := Nat.lt_of_not_ge h.2
  by_cases hab : a.base ≤ b.base
  · refine ⟨b.base, ?_, ?_⟩
    · exact ⟨hab, hrightA⟩
    · exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right hb⟩
  · have hba : b.base < a.base := Nat.lt_of_not_ge hab
    refine ⟨a.base, ?_, ?_⟩
    · exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right ha⟩
    · exact ⟨Nat.le_of_lt hba, hrightB⟩

end Luffs.Memory
