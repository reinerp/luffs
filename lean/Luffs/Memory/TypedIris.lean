import Luffs.Memory.Semantics
import Iris.BI.BigOp.BigSepList
import Iris.Instances.Lib.GhostMap

set_option autoImplicit false

namespace Luffs.Memory

open Iris Iris.BI Std

abbrev ContentsMapF := fun V => Std.ExtTreeMap Nat V compare
abbrev ContentsMap := ContentsMapF Byte

/-- Authoritative byte contents, separate from the allocation/liveness ghost
map. Keeping the resources separate lets `OwnsBytes` express uninitialized
storage while `PointsToBytes` records initialized contents. -/
class ByteContentsGS (GF : BundledGFunctors)
    extends GhostMapG GF Nat Byte ContentsMapF where
  name : GName

attribute [instance] ByteContentsGS.toGhostMapG

def PointsToBytes {GF : BundledGFunctors} [G : ByteContentsGS GF]
    (base : Addr) : List Byte -> IProp GF
  | [] => iprop(emp)
  | value :: rest => iprop(
      (G.name ↪◯MAP[base] value) ∗ PointsToBytes (G := G) (base + 1) rest)

def contentsInterp {GF : BundledGFunctors} [G : ByteContentsGS GF]
    (contents : ContentsMap) : IProp GF :=
  G.name ↪●MAP contents

/-- The authoritative initialized-byte map agrees with concrete machine
contents. Uninitialized but mapped bytes may be absent from `contents`. -/
def ContentsRep (contents : ContentsMap) (mem : Memory) : Prop :=
  ∀ p value, Std.PartialMap.get? contents p = some value → mem p = some value

def deleteBytes (contents : ContentsMap) (base : Addr) : List Byte -> ContentsMap
  | [] => contents
  | _ :: rest => deleteBytes (Std.PartialMap.delete contents base) (base + 1) rest

def insertBytes (contents : ContentsMap) (base : Addr) : List Byte -> ContentsMap
  | [] => contents
  | value :: rest =>
      insertBytes (Std.PartialMap.insert contents base value) (base + 1) rest

def CanInsertBytes (contents : ContentsMap) (base : Addr) : List Byte -> Prop
  | [] => True
  | value :: rest =>
      Std.PartialMap.get? contents base = none ∧
        CanInsertBytes (Std.PartialMap.insert contents base value) (base + 1) rest

def BytesInContents (contents : ContentsMap) (base : Addr)
    (values : List Byte) : Prop :=
  ∀ i value, values[i]? = some value →
    Std.PartialMap.get? contents (base + i) = some value

theorem pointsToBytes_append {GF : BundledGFunctors} [G : ByteContentsGS GF]
    (base : Addr) (left right : List Byte) :
    PointsToBytes (G := G) base (left ++ right) ⊣⊢
      PointsToBytes base left ∗ PointsToBytes (base + left.length) right := by
  induction left generalizing base with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.add_zero, PointsToBytes]
      exact emp_sep.symm
  | cons value rest ih =>
      simp only [List.cons_append, PointsToBytes, List.length_cons]
      refine (sep_congr_right (ih (base + 1))).trans ?_
      rw [Nat.add_assoc, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
      exact sep_assoc.symm

theorem pointsToBytes_lookup {GF : BundledGFunctors} [G : ByteContentsGS GF]
    {contents : ContentsMap} {base : Addr} {values : List Byte}
    {i : Nat} (hi : i < values.length) :
    contentsInterp (G := G) contents ∗ PointsToBytes base values ⊢
      ⌜Std.PartialMap.get? contents (base + i) = some values[i]⌝ := by
  induction values generalizing base i with
  | nil => simp at hi
  | cons value rest ih =>
      cases i with
      | zero =>
          simp only [PointsToBytes, contentsInterp, Nat.add_zero,
            List.getElem_cons_zero]
          iintro ⟨Hauth, Hvalues⟩
          icases Hvalues with ⟨Hvalue, _⟩
          iapply ghost_map_lookup $$ Hauth Hvalue
      | succ j =>
          have hj : j < rest.length := by simpa using hi
          simp only [PointsToBytes, contentsInterp, List.getElem_cons_succ]
          iintro ⟨Hauth, Hvalues⟩
          icases Hvalues with ⟨_, Hrest⟩
          have haddr : base + (j + 1) = (base + 1) + j := by
            simp [Nat.add_comm, Nat.add_left_comm]
          rw [haddr]
          icombine Hauth Hrest as H
          have hih := ih (base := base + 1) hj
          unfold contentsInterp at hih
          iapply hih $$ H

/-- Agreement for an entire initialized slice, while retaining both the
authoritative map and every linear fragment. The pure fact can therefore be
used to justify an operational read/copy without consuming ownership. -/
theorem pointsToBytes_agreement {GF : BundledGFunctors}
    [G : ByteContentsGS GF] (contents : ContentsMap) (base : Addr)
    (values : List Byte) :
    contentsInterp (G := G) contents ∗ PointsToBytes base values ⊢
      (contentsInterp contents ∗ PointsToBytes base values) ∗
        ⌜BytesInContents contents base values⌝ := by
  induction values generalizing base with
  | nil =>
      simp only [PointsToBytes, BytesInContents]
      iintro H
      isplitl [H]
      · iassumption
      · ipureintro
        intro i value hget
        simp at hget
  | cons head rest ih =>
      iintro H
      ihave ⟨H, %hhead⟩ := persistent_entails_left
        (pointsToBytes_lookup (G := G) (contents := contents)
          (base := base) (values := head :: rest) (i := 0) (by simp)) $$ H
      iunfold PointsToBytes in H
      icases H with ⟨Hauth, Hvalues⟩
      icases Hvalues with ⟨Hhead, Hrest⟩
      icombine Hauth Hrest as Htail
      ihave ⟨Htail, %htail⟩ := ih (base + 1) $$ Htail
      icases Htail with ⟨Hauth, Hrest⟩
      isplitl [Hauth Hhead Hrest]
      · iunfold PointsToBytes
        isplitl [Hauth]
        · iassumption
        · isplitl [Hhead]
          · iassumption
          · iassumption
      · ipureintro
        intro i value hget
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
            subst value
            simpa using hhead
        | succ j =>
            simp only [List.getElem?_cons_succ] at hget
            have hlookup := htail j value hget
            simpa [Nat.add_assoc, Nat.add_comm 1 j] using hlookup

theorem pointsToBytes_read_steps {GF : BundledGFunctors}
    [G : ByteContentsGS GF] {contents : ContentsMap} {mem : Memory}
    (hrep : ContentsRep contents mem) (base : Addr) (values : List Byte) :
    contentsInterp (G := G) contents ∗ PointsToBytes base values ⊢
      (contentsInterp contents ∗ PointsToBytes base values) ∗
        ⌜ReadSteps base values mem⌝ := by
  iintro H
  ihave ⟨H, %hagreement⟩ :=
    pointsToBytes_agreement contents base values $$ H
  isplitl [H]
  · iassumption
  · ipureintro
    apply readSteps_exists
    intro i value hget
    exact hrep (base + i) value (hagreement i value hget)

theorem pointsToBytes_load_exact {GF : BundledGFunctors}
    [G : ByteContentsGS GF] {contents : ContentsMap} {mem : Memory}
    (hrep : ContentsRep contents mem) {base : Addr} {values : List Byte}
    {i : Nat} (hi : i < values.length) :
    contentsInterp (G := G) contents ∗ PointsToBytes base values ⊢
      ⌜PrimStep (.load (base + i)) mem (.byte values[i]) mem⌝ := by
  iintro H
  ihave %hlookup := pointsToBytes_lookup (G := G) hi $$ H
  ipureintro
  exact .load (hrep (base + i) values[i] hlookup)

theorem pointsToBytes_delete {GF : BundledGFunctors} [G : ByteContentsGS GF]
    (contents : ContentsMap) (base : Addr) (values : List Byte) :
    contentsInterp (G := G) contents ∗ PointsToBytes base values ==∗
      contentsInterp (deleteBytes contents base values) := by
  induction values generalizing contents base with
  | nil =>
      simp only [PointsToBytes, deleteBytes, contentsInterp]
      iintro ⟨Hauth, _⟩
      imodintro
      iassumption
  | cons value rest ih =>
      simp only [PointsToBytes, deleteBytes, contentsInterp]
      iintro ⟨Hauth, Hvalues⟩
      icases Hvalues with ⟨Hvalue, Hrest⟩
      imod ghost_map_delete base value $$ Hauth Hvalue with Hauth
      icombine Hauth Hrest as H
      have hih := ih (Std.PartialMap.delete contents base) (base + 1)
      unfold contentsInterp at hih
      iapply hih $$ H

theorem pointsToBytes_insert {GF : BundledGFunctors} [G : ByteContentsGS GF]
    (contents : ContentsMap) (base : Addr) (values : List Byte)
    (hfresh : CanInsertBytes contents base values) :
    contentsInterp (G := G) contents ==∗
      contentsInterp (insertBytes contents base values) ∗
        PointsToBytes base values := by
  induction values generalizing contents base with
  | nil =>
      simp only [insertBytes, PointsToBytes, contentsInterp]
      iintro Hauth
      imodintro
      isplitl [Hauth]
      · iassumption
      · itrivial
  | cons value rest ih =>
      simp only [CanInsertBytes] at hfresh
      simp only [insertBytes, PointsToBytes, contentsInterp]
      iintro Hauth
      imod ghost_map_insert base value hfresh.1 $$ Hauth with ⟨Hauth, Hvalue⟩
      have hih := ih (Std.PartialMap.insert contents base value) (base + 1)
        hfresh.2
      unfold contentsInterp at hih
      imod hih $$ Hauth with ⟨Hauth, Hrest⟩
      imodintro
      isplitl [Hauth]
      · iassumption
      · isplitl [Hvalue]
        · iassumption
        · iassumption

end Luffs.Memory
