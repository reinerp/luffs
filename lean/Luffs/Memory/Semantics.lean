import Luffs.Memory.ConcreteIris

set_option autoImplicit false

namespace Luffs.Memory

open Iris Iris.BI

/-- Extensional machine memory. Unmapped addresses contain no byte. -/
abbrev Memory := Addr -> Option Byte

def Memory.mapped (mem : Memory) (p : Addr) : Prop := (mem p).isSome

def Memory.regionMapped (mem : Memory) (r : Region) : Prop :=
  ∀ p, r.contains p -> mem.mapped p

def Memory.regionUnmapped (mem : Memory) (r : Region) : Prop :=
  ∀ p, r.contains p -> mem p = none

def Memory.write (mem : Memory) (p : Addr) (v : Byte) : Memory :=
  fun q => if q = p then some v else mem q

def Memory.mapZeroed (mem : Memory) (r : Region) : Memory :=
  fun p => if r.contains p then some 0 else mem p

def Memory.unmap (mem : Memory) (r : Region) : Memory :=
  fun p => if r.contains p then none else mem p

inductive Prim where
  | offset (base delta addrMax : Nat)
  | load (p : Addr)
  | store (p : Addr) (value : Byte)
  | mmap (bytes align : Nat)
  | munmap (region : Region)
deriving DecidableEq, Repr

inductive Result where
  | addr (value : Addr)
  | byte (value : Byte)
  | region (value : Region)
  | unit
deriving DecidableEq, Repr

/-- Small-step semantics for the only trusted memory primitives. A missing
constructor is a stuck operation, so safety is stated as existence of a step. -/
inductive PrimStep : Prim -> Memory -> Result -> Memory -> Prop where
  | offset {mem base delta addrMax} (hbound : base + delta ≤ addrMax) :
      PrimStep (.offset base delta addrMax) mem (.addr (base + delta)) mem
  | load {mem p value} (h : mem p = some value) :
      PrimStep (.load p) mem (.byte value) mem
  | store {mem p old value} (h : mem p = some old) :
      PrimStep (.store p value) mem .unit (mem.write p value)
  | mmap {mem bytes align base}
      (hbytes : 0 < bytes) (halign : 0 < align) (hbase : base % align = 0)
      (hfresh : mem.regionUnmapped { base, bytes }) :
      PrimStep (.mmap bytes align) mem (.region { base, bytes })
        (mem.mapZeroed { base, bytes })
  | munmap {mem region} (hmapped : mem.regionMapped region) :
      PrimStep (.munmap region) mem .unit (mem.unmap region)

/-- The operational trace used by moves and reallocations: each source byte is
loaded and then stored before proceeding to the next byte. This is deliberately
not a bulk-memory axiom. -/
inductive CopySteps : Addr -> Addr -> List Byte -> Memory -> Memory -> Prop where
  | nil {src dst mem} : CopySteps src dst [] mem mem
  | cons {src dst value rest mem next}
      (hload : PrimStep (.load src) mem (.byte value) mem)
      (hstore : PrimStep (.store dst value) mem .unit (mem.write dst value))
      (htail : CopySteps (src + 1) (dst + 1) rest
        (mem.write dst value) next) :
      CopySteps src dst (value :: rest) mem next

/-- Sequential loads of a complete encoded value. -/
inductive ReadSteps : Addr -> List Byte -> Memory -> Prop where
  | nil {base mem} : ReadSteps base [] mem
  | cons {base value rest mem}
      (hload : PrimStep (.load base) mem (.byte value) mem)
      (htail : ReadSteps (base + 1) rest mem) :
      ReadSteps base (value :: rest) mem

/-- Sequential stores of a complete encoded value. -/
inductive WriteSteps : Addr -> List Byte -> Memory -> Memory -> Prop where
  | nil {base mem} : WriteSteps base [] mem mem
  | cons {base value rest mem next old}
      (hstore : PrimStep (.store base value) mem .unit (mem.write base value))
      (hold : mem base = some old)
      (htail : WriteSteps (base + 1) rest (mem.write base value) next) :
      WriteSteps base (value :: rest) mem next

theorem readSteps_exists (base : Addr) (values : List Byte) (mem : Memory)
    (hsrc : ∀ i value, values[i]? = some value →
      mem (base + i) = some value) :
    ReadSteps base values mem := by
  induction values generalizing base with
  | nil => exact .nil
  | cons value rest ih =>
      have hload : PrimStep (.load base) mem (.byte value) mem :=
        .load (by simpa using hsrc 0 value (by simp))
      have htail : ReadSteps (base + 1) rest mem := by
        apply ih
        intro i tailValue hget
        have h := hsrc (i + 1) tailValue (by simpa using hget)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using h
      exact ReadSteps.cons hload htail

theorem writeSteps_exists (base : Addr) (values : List Byte) (mem : Memory)
    (hmapped : ∀ i, i < values.length → mem.mapped (base + i)) :
    ∃ next, WriteSteps base values mem next := by
  induction values generalizing base mem with
  | nil => exact ⟨mem, .nil⟩
  | cons value rest ih =>
      obtain ⟨old, hold⟩ : ∃ old, mem base = some old := by
        have h := hmapped 0 (by simp)
        unfold Memory.mapped at h
        cases hmem : mem base with
        | none => simp [hmem] at h
        | some old => exact ⟨old, rfl⟩
      have htailMapped : ∀ i, i < rest.length →
          (mem.write base value).mapped (base + 1 + i) := by
        intro i hi
        have h := hmapped (i + 1)
          (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
        unfold Memory.mapped at h ⊢
        simp only [Memory.write]
        split
        · simp
        · rw [Nat.add_assoc, Nat.add_comm 1 i]
          exact h
      obtain ⟨next, htail⟩ := ih (base + 1) (mem.write base value) htailMapped
      exact ⟨next, .cons (.store hold) hold htail⟩


/-- A bytewise copy has an operational execution whenever every source byte
has the specified value, every destination byte is mapped, and the ranges do
not overlap. -/
theorem copySteps_exists (src dst : Addr) (values : List Byte) (mem : Memory)
    (hsrc : ∀ i value, values[i]? = some value →
      mem (src + i) = some value)
    (hdst : ∀ i, i < values.length → mem.mapped (dst + i))
    (hdisjoint : ∀ i, i < values.length → ∀ j, j < values.length →
      src + i ≠ dst + j) :
    ∃ next, CopySteps src dst values mem next := by
  induction values generalizing src dst mem with
  | nil => exact ⟨mem, .nil⟩
  | cons value rest ih =>
      have hload : PrimStep (.load src) mem (.byte value) mem := by
        exact .load (by simpa using hsrc 0 value (by simp))
      obtain ⟨old, hold⟩ : ∃ old, mem dst = some old := by
        have hmapped := hdst 0 (by simp)
        unfold Memory.mapped at hmapped
        cases h : mem dst with
        | none => simp [h] at hmapped
        | some old => exact ⟨old, rfl⟩
      have hstore : PrimStep (.store dst value) mem .unit
          (mem.write dst value) := .store hold
      have hsrcTail : ∀ i tailValue, rest[i]? = some tailValue →
          (mem.write dst value) (src + 1 + i) = some tailValue := by
        intro i tailValue hget
        have hi : i < rest.length := (getElem?_eq_some_iff.mp hget).1
        have hne : src + (i + 1) ≠ dst := by
          simpa using hdisjoint (i + 1)
            (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
            0 (by simp)
        rw [Nat.add_assoc, Nat.add_comm 1 i]
        simp only [Memory.write, if_neg hne]
        exact hsrc (i + 1) tailValue (by simpa using hget)
      have hdstTail : ∀ i, i < rest.length →
          (mem.write dst value).mapped (dst + 1 + i) := by
        intro i hi
        have hmapped := hdst (i + 1)
          (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
        unfold Memory.mapped at hmapped ⊢
        simp only [Memory.write]
        split
        · simp
        · rw [Nat.add_assoc, Nat.add_comm 1 i]
          exact hmapped
      have hdisjointTail : ∀ i, i < rest.length → ∀ j,
          j < rest.length → src + 1 + i ≠ dst + 1 + j := by
        intro i hi j hj
        have hne := hdisjoint (i + 1)
          (by simpa only [List.length_cons] using Nat.succ_lt_succ hi) (j + 1)
          (by simpa only [List.length_cons] using Nat.succ_lt_succ hj)
        intro heq
        apply hne
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
      obtain ⟨next, htail⟩ := ih (src + 1) (dst + 1)
        (mem.write dst value) hsrcTail hdstTail hdisjointTail
      exact ⟨next, .cons hload hstore htail⟩

def Prim.safe (op : Prim) (mem : Memory) : Prop :=
  ∃ result next, PrimStep op mem result next

theorem offset_safe_iff (mem : Memory) (base delta addrMax : Nat) :
    (Prim.offset base delta addrMax).safe mem ↔ base + delta ≤ addrMax := by
  constructor
  · rintro ⟨result, next, hstep⟩
    cases hstep with
    | offset hbound => exact hbound
  · intro h
    exact ⟨.addr (base + delta), mem, .offset h⟩

theorem load_safe_iff (mem : Memory) (p : Addr) :
    (Prim.load p).safe mem ↔ mem.mapped p := by
  constructor
  · rintro ⟨result, next, hstep⟩
    cases hstep with
    | load h => simp [Memory.mapped, h]
  · intro h
    unfold Memory.mapped at h
    cases hp : mem p with
    | none => simp [hp] at h
    | some value => exact ⟨.byte value, mem, .load hp⟩

theorem store_safe_iff (mem : Memory) (p : Addr) (value : Byte) :
    (Prim.store p value).safe mem ↔ mem.mapped p := by
  constructor
  · rintro ⟨result, next, hstep⟩
    cases hstep with
    | store h => simp [Memory.mapped, h]
  · intro h
    unfold Memory.mapped at h
    cases hp : mem p with
    | none => simp [hp] at h
    | some old => exact ⟨.unit, mem.write p value, .store hp⟩

theorem mapZeroed_mapped {mem : Memory} {r : Region} {p : Addr}
    (hp : r.contains p) : (mem.mapZeroed r) p = some 0 := by
  simp [Memory.mapZeroed, hp]

theorem mapZeroed_preserves_outside {mem : Memory} {r : Region} {p : Addr}
    (hp : ¬r.contains p) : (mem.mapZeroed r) p = mem p := by
  simp [Memory.mapZeroed, hp]

theorem unmap_none {mem : Memory} {r : Region} {p : Addr}
    (hp : r.contains p) : (mem.unmap r) p = none := by
  simp [Memory.unmap, hp]

theorem write_preserves_mapped {mem : Memory} {p q : Addr} {old value : Byte}
    (hp : mem p = some old) :
    (mem.write p value).mapped q ↔ mem.mapped q := by
  by_cases hqp : q = p
  · subst hqp
    simp [Memory.write, Memory.mapped, hp]
  · simp [Memory.write, Memory.mapped, hqp]

/-- Connects the executable memory state to the authoritative Iris allocation
map. Byte contents are modeled separately; this relation records liveness. -/
def MemoryRep (allocated : ByteMap Unit) (mem : Memory) : Prop :=
  ∀ p, Std.PartialMap.get? allocated p = some () ↔ mem.mapped p

/-- Adequacy for loads: authoritative agreement plus an owned region proves
that the operational semantics has a next step. -/
theorem owned_load_safe {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {r : Region} {p : Addr}
    (hrep : MemoryRep allocated mem) (hp : r.contains p) :
    byteHeapInterp (G := G) allocated ∗ ghostOwnsBytes r ⊢
      ⌜(Prim.load p).safe mem⌝ := by
  iintro H
  ihave %hlookup := byteHeapInterp_lookup (G := G) hp $$ H
  ipureintro
  exact (load_safe_iff mem p).2 ((hrep p).1 hlookup)

/-- Adequacy for stores follows from the same exclusive region capability. -/
theorem owned_store_safe {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {r : Region} {p : Addr}
    (hrep : MemoryRep allocated mem) (hp : r.contains p) (value : Byte) :
    byteHeapInterp (G := G) allocated ∗ ghostOwnsBytes r ⊢
      ⌜(Prim.store p value).safe mem⌝ := by
  iintro H
  ihave %hlookup := byteHeapInterp_lookup (G := G) hp $$ H
  ipureintro
  exact (store_safe_iff mem p value).2 ((hrep p).1 hlookup)

/-- Closed, finite memory-effect programs. The continuation makes subsequent
control flow depend on the exact result of the preceding primitive. -/
inductive Program where
  | done
  | call (op : Prim) (next : Result → Program)

/-- Complete execution of a closed primitive program. A missing `PrimStep`
constructor prevents this relation from being constructed, representing a
stuck memory access. -/
inductive Program.Exec : Program → Memory → Memory → Prop where
  | done {mem} : Exec .done mem mem
  | call {op next mem result after final}
      (hstep : PrimStep op mem result after)
      (htail : Exec (next result) after final) :
      Exec (.call op next) mem final

def Program.Safe (program : Program) (mem : Memory) : Prop :=
  ∃ final, Program.Exec program mem final

def Program.Spec (program : Program) (mem : Memory)
    (post : Memory → Prop) : Prop :=
  Program.Safe program mem ∧
    ∀ final, Program.Exec program mem final → post final

/-- The semantic weakest precondition embedded in Iris: execution exists, and
every possible complete execution establishes the postcondition. The first
conjunct is precisely the no-stuck obligation; the second is demonic over the
nondeterministic `mmap` base choice. -/
def Program.wp {GF : BundledGFunctors} (program : Program) (mem : Memory)
    (post : Memory → Prop) : IProp GF :=
  iprop(⌜Program.Spec program mem post⌝)

theorem Program.wp_done {GF : BundledGFunctors} (mem : Memory)
    (post : Memory → Prop) (hpost : post mem) :
    ⊢@{IProp GF} Program.wp .done mem post := by
  unfold Program.wp
  ipureintro
  exact ⟨⟨mem, .done⟩, fun final hexec => by cases hexec; exact hpost⟩

theorem Program.wp_call {GF : BundledGFunctors} {op : Prim}
    {next : Result → Program} {mem : Memory} {post : Memory → Prop}
    (hsafe : Prim.safe op mem)
    (hnext : ∀ result after, PrimStep op mem result after →
      Program.Safe (next result) after ∧
        ∀ final, Program.Exec (next result) after final → post final) :
    ⊢@{IProp GF} Program.wp (.call op next) mem post := by
  unfold Program.wp
  ipureintro
  obtain ⟨result, after, hstep⟩ := hsafe
  obtain ⟨⟨final, htail⟩, _⟩ := hnext result after hstep
  refine ⟨⟨final, .call hstep htail⟩, ?_⟩
  intro final hexec
  cases hexec with
  | call hstep' htail' => exact (hnext _ _ hstep').2 final htail'

/-- Iris adequacy for the Luffs primitive language. This is the closed-proof
boundary: semantic validity of a WP yields an actual complete execution. -/
theorem Program.wp_adequacy {GF : BundledGFunctors} {program : Program}
    {mem : Memory} {post : Memory → Prop}
    (hwp : ⊢@{IProp GF} Program.wp program mem post) :
    Program.Safe program mem ∧
      ∀ final, Program.Exec program mem final → post final := by
  apply pure_soundness (PROP := IProp GF)
  exact hwp

def Program.single (op : Prim) : Program := .call op (fun _ => .done)

theorem Program.single_safe_iff (op : Prim) (mem : Memory) :
    (Program.single op).Safe mem ↔ op.safe mem := by
  constructor
  · rintro ⟨final, hexec⟩
    cases hexec with
    | call hstep _ => exact ⟨_, _, hstep⟩
  · rintro ⟨result, after, hstep⟩
    exact ⟨after, .call hstep .done⟩

theorem Program.single_wp {GF : BundledGFunctors} {op : Prim} {mem : Memory}
    {post : Memory → Prop} (hsafe : op.safe mem)
    (hpost : ∀ result after, PrimStep op mem result after → post after) :
    ⊢@{IProp GF} Program.wp (Program.single op) mem post := by
  unfold Program.wp
  ipureintro
  refine ⟨(Program.single_safe_iff op mem).2 hsafe, ?_⟩
  intro final hexec
  cases hexec with
  | call hstep hdone =>
      cases hdone
      exact hpost _ _ hstep

theorem offset_wp {GF : BundledGFunctors} (mem : Memory)
    (base delta addrMax : Nat) (hbound : base + delta ≤ addrMax) :
    ⊢@{IProp GF} Program.wp (Program.single (.offset base delta addrMax)) mem
      (fun final => final = mem) := by
  apply Program.single_wp ((offset_safe_iff mem base delta addrMax).2 hbound)
  intro result after hstep
  cases hstep
  rfl

theorem mmap_wp {GF : BundledGFunctors} {mem : Memory} {bytes align base : Nat}
    (hbytes : 0 < bytes) (halign : 0 < align) (hbase : base % align = 0)
    (hfresh : mem.regionUnmapped { base, bytes }) :
    ⊢@{IProp GF} Program.wp (Program.single (.mmap bytes align)) mem
      (fun final => ∃ chosen, chosen % align = 0 ∧
        mem.regionUnmapped { base := chosen, bytes } ∧
        final = mem.mapZeroed { base := chosen, bytes }) := by
  apply Program.single_wp
    ⟨.region { base, bytes }, mem.mapZeroed { base, bytes },
      .mmap hbytes halign hbase hfresh⟩
  intro result after hstep
  cases hstep with
  | mmap _ _ hchosen hfreshChosen =>
      exact ⟨_, hchosen, hfreshChosen, rfl⟩

theorem munmap_wp {GF : BundledGFunctors} {mem : Memory} {region : Region}
    (hmapped : mem.regionMapped region) :
    ⊢@{IProp GF} Program.wp (Program.single (.munmap region)) mem
      (fun final => final = mem.unmap region) := by
  apply Program.single_wp ⟨.unit, mem.unmap region, .munmap hmapped⟩
  intro result after hstep
  cases hstep
  rfl

/-- Full WP rule for an owned load. The authoritative interpretation and
client fragment are retained as the premise; the conclusion is a closed
no-stuck program proof, suitable for `Program.wp_adequacy`. -/
theorem owned_load_wp {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {r : Region} {p : Addr}
    (hrep : MemoryRep allocated mem) (hp : r.contains p) :
    byteHeapInterp (G := G) allocated ∗ ghostOwnsBytes r ⊢
      Program.wp (Program.single (.load p)) mem (fun final => final = mem) := by
  iintro H
  ihave %hsafe := owned_load_safe (G := G) hrep hp $$ H
  unfold Program.wp
  ipureintro
  refine ⟨(Program.single_safe_iff (.load p) mem).2 hsafe, ?_⟩
  intro final hexec
  cases hexec with
  | call hstep hdone =>
      cases hstep
      cases hdone
      rfl

/-- Full WP rule for an owned store. -/
theorem owned_store_wp {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {r : Region} {p : Addr}
    (hrep : MemoryRep allocated mem) (hp : r.contains p) (value : Byte) :
    byteHeapInterp (G := G) allocated ∗ ghostOwnsBytes r ⊢
      Program.wp (Program.single (.store p value)) mem
        (fun final => final = mem.write p value) := by
  iintro H
  ihave %hsafe := owned_store_safe (G := G) hrep hp value $$ H
  unfold Program.wp
  ipureintro
  refine ⟨(Program.single_safe_iff (.store p value) mem).2 hsafe, ?_⟩
  intro final hexec
  cases hexec with
  | call hstep hdone =>
      cases hstep
      cases hdone
      rfl

end Luffs.Memory
