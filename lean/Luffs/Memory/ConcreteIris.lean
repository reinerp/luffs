import Luffs.Memory.Iris
import Iris.BI.BigOp.BigSepList
import Iris.Instances.Lib.GhostMap

set_option autoImplicit false

namespace Luffs.Memory

open Iris Iris.BI Std

abbrev ByteMap := fun V => Std.ExtTreeMap Nat V compare

/-- Ghost state backing Luffs byte ownership. The authoritative half lives in
the machine-state interpretation; clients receive full fragments. -/
class ByteRegionGS (GF : BundledGFunctors) extends GhostMapG GF Nat Unit ByteMap where
  name : GName

attribute [instance] ByteRegionGS.toGhostMapG

def ghostOwnsBytesFrac {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (q : Qp) (r : Region) : IProp GF :=
  [∗list] _k ↦ address ∈ List.range' r.base r.bytes,
    G.name ↪◯MAP[address]{.own q} ()

/-- Full byte ownership is the exclusive capability used by mutable borrows. -/
def ghostOwnsBytes {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (r : Region) : IProp GF :=
  ghostOwnsBytesFrac (G := G) 1 r

/-- Read-only borrows carry a fraction of every byte in their region. -/
abbrev SharedBorrow {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (q : Qp) (r : Region) : IProp GF :=
  ghostOwnsBytesFrac (G := G) q r

/-- A mutable borrow carries the full, and therefore exclusive, fraction. -/
abbrev MutableBorrow {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (r : Region) : IProp GF :=
  ghostOwnsBytes (G := G) r

theorem ghostOwnsBytesFrac_split {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (q₁ q₂ : Qp) (r : Region) :
    ghostOwnsBytesFrac (G := G) (q₁ + q₂) r ⊣⊢
      ghostOwnsBytesFrac q₁ r ∗ ghostOwnsBytesFrac q₂ r := by
  unfold ghostOwnsBytesFrac
  induction List.range' r.base r.bytes with
  | nil => exact emp_sep.symm
  | cons address addresses ih =>
      exact BigSepL.bigSepL_cons.trans <|
        (sep_congr
          ((ghost_map_elem_fractional (GF := GF) G.name address ()).fractional q₁ q₂)
          ih).trans <|
        sep_sep_sep_comm.trans <|
        sep_congr
          (BigSepL.bigSepL_cons
            (Φ := fun _ address => G.name ↪◯MAP[address]{.own q₁} ())).symm
          (BigSepL.bigSepL_cons
            (Φ := fun _ address => G.name ↪◯MAP[address]{.own q₂} ())).symm

instance {GF : BundledGFunctors} [G : ByteRegionGS GF] (r : Region) :
    Fractional (fun q => ghostOwnsBytesFrac (G := G) q r) where
  fractional := fun q₁ q₂ => ghostOwnsBytesFrac_split q₁ q₂ r

/-- Starting a shared reborrow splits its parent's fraction in half. The
second half is the restoration capability retained by the parent lifetime. -/
theorem shared_reborrow {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (q : Qp) (r : Region) :
    SharedBorrow (G := G) q r ⊣⊢
      SharedBorrow q.half r ∗ SharedBorrow q.half r := by
  simpa only [Qp.half_add_half] using
    ghostOwnsBytesFrac_split (G := G) q.half q.half r

/-- A mutable borrow can be temporarily reborrowed read-only. Recombining the
two halves when the child lifetime ends restores the mutable borrow. -/
theorem mutable_reborrow_restore {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (r : Region) :
    MutableBorrow (G := G) r ⊣⊢
      SharedBorrow (Qp.half 1) r ∗ SharedBorrow (Qp.half 1) r := by
  unfold MutableBorrow ghostOwnsBytes
  simpa only [Qp.half_add_half] using
    ghostOwnsBytesFrac_split (G := G) (Qp.half 1) (Qp.half 1) r

/-- Authoritative byte-address map owned by the Luffs machine-state interpretation. -/
def byteHeapInterp {GF : BundledGFunctors} [G : ByteRegionGS GF]
    (allocated : ByteMap Unit) : IProp GF :=
  G.name ↪●MAP allocated

theorem ghostOwnsBytes_split {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {r : Region} {left right : Nat} (h : r.bytes = left + right) :
    ghostOwnsBytes (G := G) r ⊣⊢
      ghostOwnsBytes { base := r.base, bytes := left } ∗
      ghostOwnsBytes { base := r.base + left, bytes := right } := by
  unfold ghostOwnsBytes ghostOwnsBytesFrac
  rw [h, ← List.range'_append_1]
  exact BigSepL.bigSepL_append

theorem ghostOwnsBytes_exclusive {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {r : Region} (h : 0 < r.bytes) :
    ghostOwnsBytes (G := G) r ∗ ghostOwnsBytes r ⊢ False := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  unfold ghostOwnsBytes ghostOwnsBytesFrac
  rw [hn]
  simp only [List.range'_succ]
  iintro ⟨Hleft, Hright⟩
  icases BigSepL.bigSepL_cons.mp $$ Hleft with ⟨Hleft, _⟩
  icases BigSepL.bigSepL_cons.mp $$ Hright with ⟨Hright, _⟩
  ihave %hne := ghost_map_elem_ne G.name r.base r.base (.own 1) () () $$ Hleft Hright
  exact (hne rfl).elim

/-- Two full mutable byte-region capabilities cannot overlap at even one byte. -/
theorem ghostOwnsBytes_overlap_exclusive {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {a b : Region} {p : Addr} (ha : a.contains p) (hb : b.contains p) :
    ghostOwnsBytes (G := G) a ∗ ghostOwnsBytes b ⊢ False := by
  change a.base ≤ p ∧ p < a.base + a.bytes at ha
  change b.base ≤ p ∧ p < b.base + b.bytes at hb
  have hia : p - a.base < a.bytes := by
    exact (Nat.sub_lt_iff_lt_add' ha.1).2 ha.2
  have hib : p - b.base < b.bytes := by
    exact (Nat.sub_lt_iff_lt_add' hb.1).2 hb.2
  have hgeta : (List.range' a.base a.bytes)[p - a.base]? = some p := by
    simpa [Nat.add_sub_of_le ha.1] using
      (List.getElem?_range' (s := a.base) (step := 1) hia)
  have hgetb : (List.range' b.base b.bytes)[p - b.base]? = some p := by
    simpa [Nat.add_sub_of_le hb.1] using
      (List.getElem?_range' (s := b.base) (step := 1) hib)
  unfold ghostOwnsBytes ghostOwnsBytesFrac
  iintro ⟨Ha, Hb⟩
  icases (BigSepL.bigSepL_lookup_acc hgeta).mp $$ Ha with ⟨Ha, _⟩
  icases (BigSepL.bigSepL_lookup_acc hgetb).mp $$ Hb with ⟨Hb, _⟩
  ihave %hne := ghost_map_elem_ne G.name p p (.own 1) () () $$ Ha Hb
  exact (hne rfl).elim

/-- Owning two nonempty mutable regions simultaneously exposes the pure Rust
aliasing fact needed by clients: their address ranges are disjoint. -/
theorem ghostOwnsBytes_disjoint {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {a b : Region} (ha : 0 < a.bytes) (hb : 0 < b.bytes) :
    ghostOwnsBytes (G := G) a ∗ ghostOwnsBytes b ⊢ ⌜a.disjoint b⌝ := by
  iintro H
  by_cases hdisjoint : a.disjoint b
  · ipureintro
    exact hdisjoint
  · obtain ⟨p, hap, hbp⟩ := common_address_of_not_disjoint ha hb hdisjoint
    iexfalso
    iapply ghostOwnsBytes_overlap_exclusive hap hbp $$ H

/-- A live mutable borrow cannot overlap any shared borrow. This is the Iris
form of Rust's "there exists no other live reference" rule for `&mut`. -/
theorem mutable_shared_overlap_exclusive {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {a b : Region} {p : Addr} (q : Qp) (ha : a.contains p) (hb : b.contains p) :
    MutableBorrow (G := G) a ∗ SharedBorrow q b ⊢ False := by
  change a.base ≤ p ∧ p < a.base + a.bytes at ha
  change b.base ≤ p ∧ p < b.base + b.bytes at hb
  have hia : p - a.base < a.bytes :=
    (Nat.sub_lt_iff_lt_add' ha.1).2 ha.2
  have hib : p - b.base < b.bytes :=
    (Nat.sub_lt_iff_lt_add' hb.1).2 hb.2
  have hgeta : (List.range' a.base a.bytes)[p - a.base]? = some p := by
    simpa [Nat.add_sub_of_le ha.1] using
      (List.getElem?_range' (s := a.base) (step := 1) hia)
  have hgetb : (List.range' b.base b.bytes)[p - b.base]? = some p := by
    simpa [Nat.add_sub_of_le hb.1] using
      (List.getElem?_range' (s := b.base) (step := 1) hib)
  unfold MutableBorrow ghostOwnsBytes SharedBorrow ghostOwnsBytesFrac
  iintro ⟨Ha, Hb⟩
  icases (BigSepL.bigSepL_lookup_acc hgeta).mp $$ Ha with ⟨Ha, _⟩
  icases (BigSepL.bigSepL_lookup_acc hgetb).mp $$ Hb with ⟨Hb, _⟩
  ihave %hne := ghost_map_elem_ne G.name p p (.own q) () () $$ Ha Hb
  exact (hne rfl).elim

/-- Every address covered by a client fragment is present in the authoritative
machine heap. This is the agreement bridge used by load/store safety proofs. -/
theorem byteHeapInterp_lookup_frac {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {r : Region} {p : Addr} (q : Qp) (hp : r.contains p) :
    byteHeapInterp (G := G) allocated ∗ ghostOwnsBytesFrac q r ⊢
      ⌜Std.PartialMap.get? allocated p = some ()⌝ := by
  change r.base ≤ p ∧ p < r.base + r.bytes at hp
  have hi : p - r.base < r.bytes :=
    (Nat.sub_lt_iff_lt_add' hp.1).2 hp.2
  have hget : (List.range' r.base r.bytes)[p - r.base]? = some p := by
    simpa [Nat.add_sub_of_le hp.1] using
      (List.getElem?_range' (s := r.base) (step := 1) hi)
  unfold byteHeapInterp ghostOwnsBytesFrac
  iintro ⟨Hauth, Hregion⟩
  icases (BigSepL.bigSepL_lookup_acc hget).mp $$ Hregion with ⟨Hpoint, _⟩
  iapply ghost_map_lookup $$ Hauth Hpoint

theorem byteHeapInterp_lookup {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {r : Region} {p : Addr} (hp : r.contains p) :
    byteHeapInterp (G := G) allocated ∗ ghostOwnsBytes r ⊢
      ⌜Std.PartialMap.get? allocated p = some ()⌝ := by
  unfold ghostOwnsBytes
  exact byteHeapInterp_lookup_frac (G := G) 1 hp

instance {GF : BundledGFunctors} [G : ByteRegionGS GF] :
    ByteRegionLogic (IProp GF) where
  ownsBytes := ghostOwnsBytes (G := G)
  split := ghostOwnsBytes_split
  exclusive := ghostOwnsBytes_exclusive

end Luffs.Memory
