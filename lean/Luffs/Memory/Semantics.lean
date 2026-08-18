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

/-- Two memories have identical bytes throughout a region. This is the
semantic frame relation used to show allocator metadata programs cannot alter
container payloads. -/
def Memory.AgreesOn (r : Region) (left right : Memory) : Prop :=
  ∀ p, r.contains p → right p = left p

@[refl] theorem Memory.AgreesOn.refl (r : Region) (mem : Memory) :
    mem.AgreesOn r mem := by
  intro _ _
  rfl

theorem Memory.AgreesOn.trans {r : Region} {first middle last : Memory}
    (hfirst : first.AgreesOn r middle) (hlast : middle.AgreesOn r last) :
    first.AgreesOn r last := by
  intro p hp
  exact (hlast p hp).trans (hfirst p hp)

def Memory.write (mem : Memory) (p : Addr) (v : Byte) : Memory :=
  fun q => if q = p then some v else mem q

/-- Deterministic result of the byte stores emitted for one encoded scalar. -/
def Memory.writeBytes (mem : Memory) (base : Addr) : List Byte → Memory
  | [] => mem
  | value :: rest => (mem.write base value).writeBytes (base + 1) rest

theorem Memory.mapped_write {mem : Memory} {written p : Addr} {value : Byte}
    (hmapped : mem.mapped p) :
    (mem.write written value).mapped p := by
  simp only [Memory.mapped, Memory.write]
  split <;> simp_all [Memory.mapped]

theorem Memory.mapped_writeBytes {mem : Memory} {base : Addr}
    {values : List Byte} {p : Addr} (hmapped : mem.mapped p) :
    (mem.writeBytes base values).mapped p := by
  induction values generalizing mem base with
  | nil => exact hmapped
  | cons value rest ih =>
      exact ih (Memory.mapped_write hmapped)

theorem Memory.writeBytes_eq_of_outside {mem : Memory} {base q : Addr}
    {values : List Byte}
    (houtside : q < base ∨ base + values.length ≤ q) :
    mem.writeBytes base values q = mem q := by
  induction values generalizing mem base q with
  | nil => rfl
  | cons value rest ih =>
      simp only [Memory.writeBytes]
      rw [ih]
      · have hne : q ≠ base := by
          rcases houtside with hbefore | hafter
          · exact Nat.ne_of_lt hbefore
          · simp only [List.length_cons] at hafter
            have hpositive : 0 < rest.length + 1 := Nat.zero_lt_succ _
            have hlt : base < q :=
              Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hpositive) hafter
            exact Ne.symm (Nat.ne_of_lt hlt)
        simp [Memory.write, hne]
      · rcases houtside with hbefore | hafter
        · exact Or.inl (Nat.lt_trans hbefore (Nat.lt_succ_self base))
        · simp only [List.length_cons] at hafter
          exact Or.inr (by
            simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using hafter)

theorem Memory.writeBytes_get {mem : Memory} {base : Addr}
    {values : List Byte} {i : Nat} (hi : i < values.length) :
    mem.writeBytes base values (base + i) = some values[i] := by
  induction values generalizing mem base i with
  | nil => simp at hi
  | cons value rest ih =>
      cases i with
      | zero =>
          simp only [Memory.writeBytes, Nat.add_zero, List.getElem_cons_zero]
          rw [Memory.writeBytes_eq_of_outside (values := rest) (q := base)
            (Or.inl (by simp))]
          simp [Memory.write]
      | succ i =>
          have hitail : i < rest.length := by simpa using hi
          simp only [Memory.writeBytes, List.getElem_cons_succ]
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using
            (ih (mem := mem.write base value) (base := base + 1) hitail)

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

theorem MemoryRep.write {allocated : ByteMap Unit} {mem : Memory}
    {p : Addr} {old value : Byte} (hrep : MemoryRep allocated mem)
    (hold : mem p = some old) :
    MemoryRep allocated (mem.write p value) := by
  intro q
  rw [write_preserves_mapped hold]
  exact hrep q

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

/-- Fractional ownership suffices for reads. Unlike `owned_store_safe`, this
rule applies to arbitrarily nested shared reborrows. -/
theorem shared_load_safe {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {r : Region} {p : Addr}
    (q : Qp) (hrep : MemoryRep allocated mem) (hp : r.contains p) :
    byteHeapInterp (G := G) allocated ∗ SharedBorrow q r ⊢
      ⌜(Prim.load p).safe mem⌝ := by
  iintro H
  ihave %hlookup := byteHeapInterp_lookup_frac (G := G) q hp $$ H
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

/-- Sequential composition of closed effect programs. This is the control-flow
algebra used by generated Luffs code: reaching `done` in the first program
continues with the second program. -/
def Program.then : Program → Program → Program
  | .done, tail => tail
  | .call op next, tail => .call op (fun result => (next result).then tail)

/-- Syntactic effect property used when composing allocator and container
programs: the trace may read, store, or extend mappings, but never release one. -/
def Prim.DoesNotUnmap : Prim → Prop
  | .munmap _ => False
  | _ => True

def Program.DoesNotUnmap : Program → Prop
  | .done => True
  | .call op next => op.DoesNotUnmap ∧ ∀ result, (next result).DoesNotUnmap

@[simp] theorem Program.done_doesNotUnmap : Program.done.DoesNotUnmap := trivial

theorem Program.DoesNotUnmap.then {first tail : Program}
    (hfirst : first.DoesNotUnmap) (htail : tail.DoesNotUnmap) :
    (first.then tail).DoesNotUnmap := by
  induction first with
  | done => exact htail
  | call op next ih =>
      exact ⟨hfirst.1, fun result => ih result (hfirst.2 result)⟩

@[simp] theorem Program.doesNotUnmap_then_iff (first tail : Program) :
    (first.then tail).DoesNotUnmap ↔
      first.DoesNotUnmap ∧ tail.DoesNotUnmap := by
  constructor
  · intro h
    induction first with
    | done => exact ⟨trivial, h⟩
    | call op next ih =>
        have hnext : ∀ result, (next result).DoesNotUnmap ∧
            tail.DoesNotUnmap := fun result => ih result (h.2 result)
        exact ⟨⟨h.1, fun result => (hnext result).1⟩, (hnext .unit).2⟩
  · rintro ⟨hfirst, htail⟩
    exact hfirst.then htail

theorem PrimStep.mapped_preserved_of_doesNotUnmap
    {op : Prim} {before after : Memory} {result : Result}
    (hstep : PrimStep op before result after) (hop : op.DoesNotUnmap) :
    ∀ p, before.mapped p → after.mapped p := by
  intro p hp
  cases hstep with
  | offset => exact hp
  | load => exact hp
  | store => exact Memory.mapped_write hp
  | @mmap mem bytes align base hbytes halign hbase hfresh =>
      by_cases hin : ({ base := base, bytes := bytes } : Region).contains p
      · simp [Memory.mapZeroed, Memory.mapped, hin]
      · unfold Memory.mapped at hp ⊢
        rw [Memory.mapZeroed_preserves_outside hin]
        exact hp
  | munmap => contradiction

/-- Every execution of a no-unmap program monotonically preserves the mapped
domain, independently of the concrete reads and stores it performs. -/
theorem Program.DoesNotUnmap.exec_mapped_preserved {program : Program}
    (hprogram : program.DoesNotUnmap) {before after : Memory}
    (hexec : Program.Exec program before after) :
    ∀ p, before.mapped p → after.mapped p := by
  induction hexec with
  | done => exact fun _ hp => hp
  | @call op next mem result middle final hstep htail ih =>
      intro p hp
      exact ih (hprogram.2 result) p
        (hstep.mapped_preserved_of_doesNotUnmap hprogram.1 p hp)

theorem Program.exec_then {first tail : Program} {before middle after : Memory}
    (hfirst : Program.Exec first before middle)
    (htail : Program.Exec tail middle after) :
    Program.Exec (first.then tail) before after := by
  induction hfirst with
  | done => exact htail
  | call hstep _ ih => exact .call hstep (ih htail)

theorem Program.exec_then_iff (first tail : Program) (before after : Memory) :
    Program.Exec (first.then tail) before after ↔
      ∃ middle, Program.Exec first before middle ∧
        Program.Exec tail middle after := by
  constructor
  · intro hexec
    induction first generalizing before after with
    | done => exact ⟨before, .done, hexec⟩
    | call op next ih =>
        cases hexec with
        | call hstep hrest =>
            obtain ⟨middle, hnext, htail⟩ := ih _ _ _ hrest
            exact ⟨middle, .call hstep hnext, htail⟩
  · rintro ⟨middle, hfirst, htail⟩
    exact Program.exec_then hfirst htail

/-- A closed effect program frames a region when every one of its executions
leaves all bytes in that region unchanged. -/
def Program.PreservesRegion (program : Program) (region : Region) : Prop :=
  ∀ ⦃before after⦄, Program.Exec program before after →
    before.AgreesOn region after

@[simp] theorem Program.done_preservesRegion (region : Region) :
    Program.done.PreservesRegion region := by
  intro before after hexec
  cases hexec
  exact Memory.AgreesOn.refl region before

theorem Program.PreservesRegion.then {first tail : Program} {region : Region}
    (hfirst : first.PreservesRegion region)
    (htail : tail.PreservesRegion region) :
    (first.then tail).PreservesRegion region := by
  intro before after hexec
  obtain ⟨middle, hfirstExec, htailExec⟩ :=
    (Program.exec_then_iff first tail before after).1 hexec
  exact (hfirst hfirstExec).trans (htail htailExec)

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

theorem Program.wp_mono {GF : BundledGFunctors} {program : Program}
    {mem : Memory} {post stronger : Memory → Prop}
    (hwp : ⊢@{IProp GF} Program.wp program mem post)
    (hmono : ∀ final, post final → stronger final) :
    ⊢@{IProp GF} Program.wp program mem stronger := by
  have hspec : Program.Spec program mem post :=
    pure_soundness (PROP := IProp GF) hwp
  unfold Program.wp
  ipureintro
  exact ⟨hspec.1, fun final hexec => hmono final (hspec.2 final hexec)⟩

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

/-- Sequential WP composition. Generated control flow may prove the first
fragment against an intermediate memory predicate, then continue from every
memory satisfying that predicate. The resulting theorem is a closed no-stuck
proof for the concatenated program. -/
theorem Program.wp_then {GF : BundledGFunctors} {first tail : Program}
    {before : Memory} {middle post : Memory → Prop}
    (hfirst : ⊢@{IProp GF} Program.wp first before middle)
    (htail : ∀ mem, middle mem →
      ⊢@{IProp GF} Program.wp tail mem post) :
    ⊢@{IProp GF} Program.wp (first.then tail) before post := by
  have hfirstSpec : Program.Spec first before middle :=
    pure_soundness (PROP := IProp GF) hfirst
  unfold Program.wp
  ipureintro
  obtain ⟨middleMem, hmiddleExec⟩ := hfirstSpec.1
  have hmiddle : middle middleMem := hfirstSpec.2 middleMem hmiddleExec
  have htailSpec : Program.Spec tail middleMem post :=
    pure_soundness (PROP := IProp GF) (htail middleMem hmiddle)
  obtain ⟨final, hfinalExec⟩ := htailSpec.1
  refine ⟨⟨final, Program.exec_then hmiddleExec hfinalExec⟩, ?_⟩
  intro after hexec
  obtain ⟨split, hprefix, hsuffix⟩ :=
    (Program.exec_then_iff first tail before after).1 hexec
  have hsplit : middle split := hfirstSpec.2 split hprefix
  have hsplitTail : Program.Spec tail split post :=
    pure_soundness (PROP := IProp GF) (htail split hsplit)
  exact hsplitTail.2 after hsuffix

/-- Sequential composition specialized to metadata initialization: both
fragments preserve the mapped domain, so the combined program does too. -/
theorem Program.wp_then_preserves_mapped {GF : BundledGFunctors}
    {first tail : Program} {before : Memory}
    (hfirst : ⊢@{IProp GF} Program.wp first before
      (fun middle => ∀ p, before.mapped p → middle.mapped p))
    (htail : ∀ middle, (∀ p, before.mapped p → middle.mapped p) →
      ⊢@{IProp GF} Program.wp tail middle
        (fun final => ∀ p, middle.mapped p → final.mapped p)) :
    ⊢@{IProp GF} Program.wp (first.then tail) before
      (fun final => ∀ p, before.mapped p → final.mapped p) := by
  apply Program.wp_then hfirst
  intro middle hmiddle
  apply Program.wp_mono (htail middle hmiddle)
  intro final hfinal p hp
  exact hfinal p (hmiddle p hp)

/-- Pure CFG branch selection. Conditions are evaluated by the value semantics;
the effect semantics records which memory-effect subprogram is executed. -/
def Program.branch (condition : Bool) (thenProgram elseProgram : Program) :
    Program :=
  if condition then thenProgram else elseProgram

theorem Program.wp_branch {GF : BundledGFunctors} (condition : Bool)
    {thenProgram elseProgram : Program} {mem : Memory}
    {post : Memory → Prop}
    (hthen : condition = true →
      ⊢@{IProp GF} Program.wp thenProgram mem post)
    (helse : condition = false →
      ⊢@{IProp GF} Program.wp elseProgram mem post) :
    ⊢@{IProp GF} Program.wp
      (Program.branch condition thenProgram elseProgram) mem post := by
  cases condition with
  | false => simpa [Program.branch] using helse rfl
  | true => simpa [Program.branch] using hthen rfl

/-- A statically bounded `while cursor < bound; cursor += 1` effect program.
The body may depend on the exact loop index. -/
def Program.forRange (start : Nat) : Nat → (Nat → Program) → Program
  | 0, _ => .done
  | count + 1, body =>
      (body start).then (Program.forRange (start + 1) count body)

/-- Loop-invariant WP rule for generated bounded loops. The invariant is
indexed by the next cursor value, so array facts derived from the loop
condition can be supplied independently for every body instance. -/
theorem Program.wp_forRange {GF : BundledGFunctors} (body : Nat → Program)
    (invariant : Nat → Memory → Prop) (start count : Nat) (mem : Memory)
    (hinit : invariant start mem)
    (hbody : ∀ i current, invariant i current →
      ⊢@{IProp GF} Program.wp (body i) current (invariant (i + 1))) :
    ⊢@{IProp GF} Program.wp (Program.forRange start count body) mem
      (invariant (start + count)) := by
  induction count generalizing start mem with
  | zero =>
      simpa [Program.forRange] using
        (Program.wp_done (GF := GF) mem (invariant start) hinit)
  | succ count ih =>
      apply Program.wp_then (hbody start mem hinit)
      intro after hnext
      have htail := ih (start + 1) after hnext
      have hindex : start + 1 + count = start + (count + 1) := by omega
      simpa [Program.forRange, hindex] using htail

theorem Program.wp_forRange_bounded {GF : BundledGFunctors}
    (body : Nat → Program) (invariant : Nat → Memory → Prop)
    (start count : Nat) (mem : Memory)
    (hinit : invariant start mem)
    (hbody : ∀ i current, start ≤ i → i < start + count →
      invariant i current →
      ⊢@{IProp GF} Program.wp (body i) current (invariant (i + 1))) :
    ⊢@{IProp GF} Program.wp (Program.forRange start count body) mem
      (invariant (start + count)) := by
  induction count generalizing start mem with
  | zero =>
      simpa [Program.forRange] using
        (Program.wp_done (GF := GF) mem (invariant start) hinit)
  | succ count ih =>
      apply Program.wp_then (hbody start mem (by omega) (by omega) hinit)
      intro after hnext
      have htail := ih (start := start + 1) (mem := after) hnext (by
        intro i current hlo hi hinvariant
        apply hbody i current (by omega) (by omega) hinvariant)
      have hindex : start + 1 + count = start + (count + 1) := by omega
      simpa [hindex] using htail

/-- The effect of the Rust-shaped Vec relocation loop. The loaded byte is fed
directly to the corresponding store, exactly as in the source loop body. -/
def Program.copyLoopBody (src dst : Addr) (i : Nat) : Program :=
  .call (.load (src + i)) (fun result =>
    match result with
    | .byte value => .call (.store (dst + i) value) (fun _ => .done)
    | _ => .done)

def Program.copyLoop (src dst count : Nat) : Program :=
  Program.forRange 0 count (Program.copyLoopBody src dst)

def Program.copyLoopFrom (src dst : Addr) : Nat → Program
  | 0 => .done
  | count + 1 =>
      .call (.load src) (fun result =>
        match result with
        | .byte value =>
            .call (.store dst value) (fun _ =>
              copyLoopFrom (src + 1) (dst + 1) count)
        | _ => copyLoopFrom (src + 1) (dst + 1) count)

theorem Program.forRange_copyLoopBody (src dst start count : Nat) :
    Program.forRange start count (Program.copyLoopBody src dst) =
      Program.copyLoopFrom (src + start) (dst + start) count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [Program.forRange, Program.copyLoopBody, Program.then,
        Program.copyLoopFrom]
      congr 1
      funext result
      cases result <;> simp [ih, Nat.add_assoc, Program.then]

theorem Program.copyLoop_eq_copyLoopFrom (src dst count : Nat) :
    Program.copyLoop src dst count = Program.copyLoopFrom src dst count := by
  simpa [Program.copyLoop] using
    Program.forRange_copyLoopBody src dst 0 count

theorem CopySteps.copyLoopFrom_exec {src dst : Addr} {values : List Byte}
    {before after : Memory}
    (hsteps : CopySteps src dst values before after) :
    Program.Exec (Program.copyLoopFrom src dst values.length) before after := by
  induction hsteps with
  | nil => exact .done
  | cons hload hstore htail ih =>
      exact .call hload (.call hstore ih)

theorem CopySteps.copyLoopFrom_exec_unique {src dst : Addr}
    {values : List Byte} {before after final : Memory}
    (hsteps : CopySteps src dst values before after)
    (hexec : Program.Exec (Program.copyLoopFrom src dst values.length)
      before final) :
    final = after := by
  induction hsteps generalizing final with
  | nil => cases hexec; rfl
  | @cons src dst value rest mem next hload hstore htail ih =>
      cases hload with
      | load hexpected =>
          cases hexec with
          | call executedLoad restExec =>
              cases executedLoad with
              | @load _ _ actual hactual =>
                  have hvalue : actual = value := by
                    rw [hactual] at hexpected
                    exact Option.some.inj hexpected
                  subst actual
                  cases restExec with
                  | call executedStore tailExec =>
                      cases executedStore
                      exact ih tailExec

/-- Exact refinement of the generated bounded loop to the byte-copy trace used
by the Vec ownership transfer. -/
theorem CopySteps.copyLoop_wp_exact {GF : BundledGFunctors}
    {src dst : Addr} {values : List Byte} {before after : Memory}
    (hsteps : CopySteps src dst values before after) :
    ⊢@{IProp GF} Program.wp
      (Program.copyLoop src dst values.length) before
      (fun final => final = after) := by
  rw [Program.copyLoop_eq_copyLoopFrom]
  unfold Program.wp
  ipureintro
  exact ⟨⟨after, hsteps.copyLoopFrom_exec⟩,
    fun final hexec => hsteps.copyLoopFrom_exec_unique hexec⟩

/-- Whole-loop safety from the facts tracked by the CFG: every source and
destination byte is mapped. Stores preserve mappedness, including for
overlapping ranges, so this rule does not need a stronger non-alias premise. -/
theorem Program.copyLoop_wp {GF : BundledGFunctors}
    (src dst count : Nat) (mem : Memory)
    (hsrc : ∀ i, i < count → mem.mapped (src + i))
    (hdst : ∀ i, i < count → mem.mapped (dst + i)) :
    ⊢@{IProp GF} Program.wp (Program.copyLoop src dst count) mem
      (fun final =>
        (∀ i, i < count → final.mapped (src + i)) ∧
        (∀ i, i < count → final.mapped (dst + i))) := by
  let invariant : Nat → Memory → Prop := fun cursor current =>
    cursor ≤ count ∧
    (∀ i, i < count → current.mapped (src + i)) ∧
    (∀ i, i < count → current.mapped (dst + i))
  unfold Program.copyLoop
  have hloop := Program.wp_forRange_bounded (GF := GF)
    (Program.copyLoopBody src dst) invariant 0 count mem
    (by exact ⟨by omega, hsrc, hdst⟩) (by
    intro i current hlo hi hinvariant
    apply Program.wp_call
    · exact (load_safe_iff current (src + i)).2
        (hinvariant.2.1 i (by omega))
    · intro result after hload
      cases hload with
      | @load _ _ value hvalue =>
          have hstoreSafe :
              Prim.safe (.store (dst + i) value) current :=
            (store_safe_iff current (dst + i) value).2
              (hinvariant.2.2 i (by omega))
          apply pure_soundness (PROP := IProp GF)
          apply Program.wp_call hstoreSafe
          intro storeResult storeAfter hstore
          cases hstore with
          | store hold =>
              have hnext : invariant (i + 1)
                  (current.write (dst + i) value) := by
                refine ⟨by omega, ?_, ?_⟩
                · intro j hj
                  exact Memory.mapped_write (hinvariant.2.1 j hj)
                · intro j hj
                  exact Memory.mapped_write (hinvariant.2.2 j hj)
              exact pure_soundness (PROP := IProp GF)
                (Program.wp_done _ _ hnext))
  simpa [invariant] using hloop

/-- The effect program emitted for a contiguous checked byte read. Results of
individual loads are consumed by the value-level generated semantics; this
program records the memory effects and stuckness obligations. -/
def Program.readBytes (base : Addr) : Nat → Program
  | 0 => .done
  | count + 1 => .call (.load base) (fun _ => readBytes (base + 1) count)

theorem Program.readBytes_preservesRegion (base count : Nat) (region : Region) :
    (Program.readBytes base count).PreservesRegion region := by
  induction count generalizing base with
  | zero => simp [Program.readBytes]
  | succ count ih =>
      intro before after hexec
      cases hexec with
      | call hload htail =>
          cases hload
          exact ih (base := base + 1) htail

@[simp] theorem Program.readBytes_doesNotUnmap (base count : Nat) :
    (Program.readBytes base count).DoesNotUnmap := by
  induction count generalizing base with
  | zero => simp [Program.readBytes, Program.DoesNotUnmap]
  | succ count ih =>
      simp [Program.readBytes, Program.DoesNotUnmap, Prim.DoesNotUnmap, ih]

theorem Program.readBytes_wp {GF : BundledGFunctors} (base count : Nat)
    (mem : Memory)
    (hmapped : ∀ i, i < count → mem.mapped (base + i)) :
    ⊢@{IProp GF} Program.wp (Program.readBytes base count) mem
      (fun final => final = mem) := by
  induction count generalizing base with
  | zero => exact Program.wp_done mem _ rfl
  | succ count ih =>
      apply Program.wp_call
      · exact (load_safe_iff mem base).2 (by simpa using hmapped 0 (by omega))
      · intro result after hstep
        cases hstep with
        | load hload =>
            apply pure_soundness (PROP := IProp GF)
            apply ih
            intro i hi
            have h := hmapped (i + 1) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using h

/-- Loads emitted for ordinary indexed reads. Offsets retain source evaluation
order and need not be contiguous. -/
def Program.readOffsets (base : Addr) : List Nat → Program
  | [] => .done
  | offset :: rest =>
      .call (.load (base + offset)) (fun _ => readOffsets base rest)

@[simp] theorem Program.readOffsets_doesNotUnmap (base : Nat)
    (offsets : List Nat) :
    (Program.readOffsets base offsets).DoesNotUnmap := by
  induction offsets with
  | nil => simp [Program.readOffsets, Program.DoesNotUnmap]
  | cons offset rest ih =>
      simp [Program.readOffsets, Program.DoesNotUnmap, Prim.DoesNotUnmap, ih]

inductive ReadOffsetSteps (base : Addr) :
    List Nat → Memory → Prop where
  | nil {mem} : ReadOffsetSteps base [] mem
  | cons {offset rest mem value}
      (hload : PrimStep (.load (base + offset)) mem (.byte value) mem)
      (htail : ReadOffsetSteps base rest mem) :
      ReadOffsetSteps base (offset :: rest) mem

theorem readOffsetSteps_exists (base : Addr) (offsets : List Nat)
    (mem : Memory)
    (hmapped : ∀ offset ∈ offsets, mem.mapped (base + offset)) :
    ReadOffsetSteps base offsets mem := by
  induction offsets with
  | nil => exact .nil
  | cons offset rest ih =>
      obtain ⟨value, hvalue⟩ : ∃ value, mem (base + offset) = some value := by
        have h := hmapped offset (by simp)
        unfold Memory.mapped at h
        cases hmem : mem (base + offset) with
        | none => simp [hmem] at h
        | some value => exact ⟨value, rfl⟩
      exact .cons (.load hvalue) (ih (by
        intro tail htail
        exact hmapped tail (by simp [htail])))

theorem ReadOffsetSteps.program_exec {base : Addr} {offsets : List Nat}
    {mem : Memory} (hsteps : ReadOffsetSteps base offsets mem) :
    Program.Exec (Program.readOffsets base offsets) mem mem := by
  induction hsteps with
  | nil => exact .done
  | cons hload htail ih => exact .call hload ih

theorem ReadOffsetSteps.program_exec_final {base : Addr}
    {offsets : List Nat} {mem final : Memory}
    (hexec : Program.Exec (Program.readOffsets base offsets) mem final) :
    final = mem := by
  induction offsets generalizing mem final with
  | nil => cases hexec; rfl
  | cons offset rest ih =>
      cases hexec with
      | call hload htail => cases hload; exact ih htail

theorem ReadOffsetSteps.program_wp {GF : BundledGFunctors} {base : Addr}
    {offsets : List Nat} {mem : Memory}
    (hsteps : ReadOffsetSteps base offsets mem) :
    ⊢@{IProp GF} Program.wp (Program.readOffsets base offsets) mem
      (fun final => final = mem) := by
  unfold Program.wp
  ipureintro
  exact ⟨⟨mem, hsteps.program_exec⟩,
    fun final hexec => ReadOffsetSteps.program_exec_final hexec⟩

theorem Program.readOffsets_wp_of_mapped {GF : BundledGFunctors}
    (base : Addr) (offsets : List Nat) (mem : Memory)
    (hmapped : ∀ offset ∈ offsets, mem.mapped (base + offset)) :
    ⊢@{IProp GF} Program.wp (Program.readOffsets base offsets) mem
      (fun final => final = mem) :=
  (readOffsetSteps_exists base offsets mem hmapped).program_wp

/-- A generated contiguous read is safe from an Iris-owned region. This is
the compositional whole-sequence counterpart of `owned_load_wp`. -/
theorem owned_readBytes_wp {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {region : Region}
    {base count : Nat}
    (hrep : MemoryRep allocated mem)
    (hinside : ∀ i, i < count → region.contains (base + i)) :
    byteHeapInterp (G := G) allocated ∗ ghostOwnsBytes region ⊢
      Program.wp (Program.readBytes base count) mem
        (fun final => final = mem) := by
  induction count generalizing base with
  | zero =>
      iintro H
      unfold Program.readBytes Program.wp
      ipureintro
      exact ⟨⟨mem, .done⟩, fun final hexec => by cases hexec; rfl⟩
  | succ count ih =>
      have hinsideTail : ∀ i, i < count →
          region.contains (base + 1 + i) := by
        intro i hi
        have h := hinside (i + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using h
      have htailRule := ih (base := base + 1) hinsideTail
      unfold Program.wp at htailRule
      iintro H
      ihave %hsafe := owned_load_safe (G := G) hrep
        (hinside 0 (by omega)) $$ H
      ihave %htailSpec := htailRule $$ H
      unfold Program.readBytes Program.wp
      ipureintro
      obtain ⟨result, after, hstep⟩ := hsafe
      cases hstep with
      | load hload =>
          obtain ⟨final, htail⟩ := htailSpec.1
          refine ⟨⟨final, .call (.load hload) htail⟩, ?_⟩
          intro final hexec
          cases hexec with
          | call hstep' htail' =>
              cases hstep'
              exact htailSpec.2 final htail'

theorem ReadSteps.mapped {base : Addr} {values : List Byte} {mem : Memory}
    (hsteps : ReadSteps base values mem) :
    ∀ i, i < values.length → mem.mapped (base + i) := by
  induction hsteps with
  | nil => simp
  | @cons base value rest mem hload htail ih =>
      intro i hi
      cases i with
      | zero =>
          cases hload with
          | load h => simp [Memory.mapped, h]
      | succ i =>
          have h := ih i (by simpa using Nat.lt_of_succ_lt_succ hi)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using h

/-- Existing exact read traces produced by Box and Vec ownership rules now
compose directly into the closed-program WP and hence adequacy boundary. -/
theorem ReadSteps.program_wp {GF : BundledGFunctors} {base : Addr}
    {values : List Byte} {mem : Memory}
    (hsteps : ReadSteps base values mem) :
    ⊢@{IProp GF} Program.wp (Program.readBytes base values.length) mem
      (fun final => final = mem) :=
  Program.readBytes_wp base values.length mem hsteps.mapped

/-- The effect program emitted for a contiguous checked byte write. -/
def Program.writeBytes (base : Addr) : List Byte → Program
  | [] => .done
  | value :: rest =>
      .call (.store base value) (fun _ => writeBytes (base + 1) rest)

theorem Program.writeBytes_preservesRegion_of_disjoint
    (base : Addr) (values : List Byte) (region : Region)
    (hdisjoint : (Region.mk base values.length).disjoint region) :
    (Program.writeBytes base values).PreservesRegion region := by
  induction values generalizing base with
  | nil => simp [Program.writeBytes]
  | cons value rest ih =>
      intro before after hexec
      cases hexec with
      | call hstore htail =>
          cases hstore with
          | store hold =>
              have hbaseInside :
                  (Region.mk base (value :: rest).length).contains base := by
                exact contains_offset _ 0 (by simp)
              have hbaseOutside : ¬region.contains base :=
                not_contains_of_disjoint hdisjoint hbaseInside
              have hhead : before.AgreesOn region (before.write base value) := by
                intro p hp
                have hne : p ≠ base := by
                  intro heq
                  exact hbaseOutside (heq ▸ hp)
                simp [Memory.write, hne]
              have htailDisjoint :
                  (Region.mk (base + 1) rest.length).disjoint region := by
                apply Region.subregion_disjoint_left
                    (outer := Region.mk base (value :: rest).length)
                · simp
                · simp [Region.endAddr, Nat.add_assoc, Nat.add_comm 1]
                · exact hdisjoint
              exact hhead.trans (ih (base := base + 1) htailDisjoint htail)

@[simp] theorem Program.writeBytes_doesNotUnmap (base : Addr)
    (values : List Byte) : (Program.writeBytes base values).DoesNotUnmap := by
  induction values generalizing base with
  | nil => simp [Program.writeBytes, Program.DoesNotUnmap]
  | cons value rest ih =>
      simp [Program.writeBytes, Program.DoesNotUnmap, Prim.DoesNotUnmap, ih]

theorem WriteSteps.program_exec {base : Addr} {values : List Byte}
    {before after : Memory}
    (hsteps : WriteSteps base values before after) :
    Program.Exec (Program.writeBytes base values) before after := by
  induction hsteps with
  | nil => exact .done
  | cons hstore hold htail ih => exact .call hstore ih

theorem WriteSteps.program_exec_unique {base : Addr} {values : List Byte}
    {before after final : Memory}
    (hsteps : WriteSteps base values before after)
    (hexec : Program.Exec (Program.writeBytes base values) before final) :
    final = after := by
  induction hsteps generalizing final with
  | nil =>
      cases hexec
      rfl
  | cons hstore hold htail ih =>
      cases hexec with
      | call executed rest =>
          cases executed
          exact ih rest

/-- An exact generated write trace is sufficient for a closed no-stuck WP
whose postcondition identifies the complete final memory. -/
theorem WriteSteps.program_wp {GF : BundledGFunctors} {base : Addr}
    {values : List Byte} {before after : Memory}
    (hsteps : WriteSteps base values before after) :
    ⊢@{IProp GF} Program.wp (Program.writeBytes base values) before
      (fun final => final = after) := by
  unfold Program.wp
  ipureintro
  exact ⟨⟨after, hsteps.program_exec⟩,
    fun final hexec => hsteps.program_exec_unique hexec⟩

theorem WriteSteps.mapped_preserved {base : Addr} {values : List Byte}
    {before after : Memory} (hsteps : WriteSteps base values before after)
    {p : Addr} (hmapped : before.mapped p) : after.mapped p := by
  induction hsteps with
  | nil => exact hmapped
  | cons hstore hold htail ih => exact ih (Memory.mapped_write hmapped)

theorem WriteSteps.final_eq_writeBytes {base : Addr} {values : List Byte}
    {before after : Memory} (hsteps : WriteSteps base values before after) :
    after = before.writeBytes base values := by
  induction hsteps with
  | nil => rfl
  | cons hstore hold htail ih => simpa [Memory.writeBytes] using ih

/-- The byte-level effect of assigning one element of a native scalar array.
The scalar codec supplies `bytes`; this layer is deliberately agnostic about
the value representation and records only its proved width and address. -/
def Program.writeElement (base width index : Nat) (bytes : List Byte) : Program :=
  Program.writeBytes (base + index * width) bytes

@[simp] theorem Program.writeElement_doesNotUnmap (base width index : Nat)
    (bytes : List Byte) :
    (Program.writeElement base width index bytes).DoesNotUnmap := by
  simp [Program.writeElement]

/-- A mapped native element range is sufficient for a closed store program.
The exact final memory is existential because later source statements compose
through it with `Program.wp_then`. -/
theorem Program.writeElement_wp_of_mapped {GF : BundledGFunctors}
    (base width index : Nat) (bytes : List Byte) (before : Memory)
    (hwidth : bytes.length = width)
    (hmapped : ∀ i, i < width →
      before.mapped (base + index * width + i)) :
    ∃ after, ⊢@{IProp GF} Program.wp
      (Program.writeElement base width index bytes) before
      (fun final => final = after) := by
  have hmapped' : ∀ i, i < bytes.length →
      before.mapped (base + index * width + i) := by
    simpa [hwidth] using hmapped
  obtain ⟨after, hsteps⟩ := writeSteps_exists
    (base + index * width) bytes before hmapped'
  exact ⟨after, hsteps.program_wp⟩

theorem Program.writeElement_wp_preserves_mapped {GF : BundledGFunctors}
    (base width index : Nat) (bytes : List Byte) (before : Memory)
    (hwidth : bytes.length = width)
    (hmapped : ∀ i, i < width →
      before.mapped (base + index * width + i)) :
    ⊢@{IProp GF} Program.wp
      (Program.writeElement base width index bytes) before
      (fun final => ∀ p, before.mapped p → final.mapped p) := by
  have hmapped' : ∀ i, i < bytes.length →
      before.mapped (base + index * width + i) := by
    simpa [hwidth] using hmapped
  obtain ⟨after, hsteps⟩ := writeSteps_exists
    (base + index * width) bytes before hmapped'
  apply Program.wp_mono hsteps.program_wp
  intro final hfinal
  subst final
  exact fun _ hp => hsteps.mapped_preserved hp

theorem Program.writeElement_wp_exact {GF : BundledGFunctors}
    (base width index : Nat) (bytes : List Byte) (before : Memory)
    (hwidth : bytes.length = width)
    (hmapped : ∀ i, i < width →
      before.mapped (base + index * width + i)) :
    ⊢@{IProp GF} Program.wp
      (Program.writeElement base width index bytes) before
      (fun final => final =
        before.writeBytes (base + index * width) bytes) := by
  have hmapped' : ∀ i, i < bytes.length →
      before.mapped (base + index * width + i) := by
    simpa [hwidth] using hmapped
  obtain ⟨after, hsteps⟩ := writeSteps_exists
    (base + index * width) bytes before hmapped'
  apply Program.wp_mono hsteps.program_wp
  intro final hfinal
  subst final
  exact hsteps.final_eq_writeBytes

/-- A source loop assigning the same native scalar value to a consecutive
range of array elements. -/
def Program.fillElements (base width start count : Nat)
    (bytes : List Byte) : Program :=
  Program.forRange start count (fun index =>
    Program.writeElement base width index bytes)

theorem Program.fillElements_wp {GF : BundledGFunctors}
    (base width start count : Nat) (bytes : List Byte) (mem : Memory)
    (hwidth : bytes.length = width)
    (hmapped : ∀ index, start ≤ index → index < start + count →
      ∀ i, i < width → mem.mapped (base + index * width + i)) :
    ⊢@{IProp GF} Program.wp
      (Program.fillElements base width start count bytes) mem
      (fun final => ∀ p, mem.mapped p → final.mapped p) := by
  unfold Program.fillElements
  apply Program.wp_forRange_bounded _
    (fun _ current => ∀ p, mem.mapped p → current.mapped p)
    start count mem (by simp)
  intro index current hstart hend hinvariant
  apply Program.wp_mono
    (Program.writeElement_wp_preserves_mapped base width index bytes current
      hwidth (by
        intro i hi
        exact hinvariant _ (hmapped index hstart hend i hi)))
  intro final hpreserves p hp
  exact hpreserves p (hinvariant p hp)

/-- Deterministic memory result of the consecutive scalar-store loop. -/
def Memory.fillElements (mem : Memory) (base width start : Nat) :
    Nat → List Byte → Memory
  | 0, _ => mem
  | count + 1, bytes =>
      Memory.fillElements
        (mem.writeBytes (base + start * width) bytes)
        base width (start + 1) count bytes

theorem Memory.mapped_fillElements (mem : Memory) (base width start count : Nat)
    (bytes : List Byte) {p : Addr} (hmapped : mem.mapped p) :
    (Memory.fillElements mem base width start count bytes).mapped p := by
  induction count generalizing mem start with
  | zero => exact hmapped
  | succ count ih =>
      exact ih _ _ (Memory.mapped_writeBytes hmapped)

theorem Program.fillElements_wp_exact {GF : BundledGFunctors}
    (base width start count : Nat) (bytes : List Byte) (mem : Memory)
    (hwidth : bytes.length = width)
    (hmapped : ∀ index, start ≤ index → index < start + count →
      ∀ i, i < width → mem.mapped (base + index * width + i)) :
    ⊢@{IProp GF} Program.wp
      (Program.fillElements base width start count bytes) mem
      (fun final => final =
        Memory.fillElements mem base width start count bytes) := by
  induction count generalizing start mem with
  | zero =>
      simpa [Program.fillElements, Program.forRange, Memory.fillElements] using
        (Program.wp_done (GF := GF) mem (fun final => final = mem) rfl)
  | succ count ih =>
      simp only [Program.fillElements, Program.forRange, Memory.fillElements]
      apply Program.wp_then
        (Program.writeElement_wp_exact base width start bytes mem hwidth (by
          intro i hi
          exact hmapped start (by omega) (by omega) i hi))
      intro middle hmiddle
      subst middle
      apply ih (start + 1) _
      intro index hstart hend i hi
      apply Memory.mapped_writeBytes
      exact hmapped index (by omega) (by omega) i hi

/-- One scalar-array assignment in an ordered metadata transaction. Keeping
the byte representation explicit makes the transaction usable for mixed Rust
integer widths without adding a trusted native-value operation. -/
structure ElementWrite where
  base : Addr
  width : Nat
  index : Nat
  bytes : List Byte

def ElementWrite.program (write : ElementWrite) : Program :=
  Program.writeElement write.base write.width write.index write.bytes

theorem ElementWrite.program_preservesRegion_of_disjoint
    (write : ElementWrite) (region : Region)
    (hdisjoint : (Region.mk (write.base + write.index * write.width)
      write.bytes.length).disjoint region) :
    write.program.PreservesRegion region := by
  exact Program.writeBytes_preservesRegion_of_disjoint _ _ _ hdisjoint

def ElementWrite.apply (write : ElementWrite) (mem : Memory) : Memory :=
  mem.writeBytes (write.base + write.index * write.width) write.bytes

def ElementWrite.applyAll : List ElementWrite → Memory → Memory
  | [], mem => mem
  | write :: rest, mem => ElementWrite.applyAll rest (write.apply mem)

theorem ElementWrite.applyAll_mapped (writes : List ElementWrite)
    (mem : Memory) {p : Addr} (hmapped : mem.mapped p) :
    (ElementWrite.applyAll writes mem).mapped p := by
  induction writes generalizing mem with
  | nil => exact hmapped
  | cons write rest ih =>
      exact ih _ (Memory.mapped_writeBytes hmapped)

/-- A finite sequence of heterogeneous native-element assignments, in source
execution order. -/
def Program.writeElements : List ElementWrite → Program
  | [] => .done
  | write :: rest => write.program.then (Program.writeElements rest)

theorem Program.writeElements_preservesRegion_of_disjoint
    (writes : List ElementWrite) (region : Region)
    (hdisjoint : ∀ write, write ∈ writes →
      (Region.mk (write.base + write.index * write.width)
        write.bytes.length).disjoint region) :
    (Program.writeElements writes).PreservesRegion region := by
  induction writes with
  | nil => simp [Program.writeElements]
  | cons write rest ih =>
      apply Program.PreservesRegion.then
      · exact write.program_preservesRegion_of_disjoint region
          (hdisjoint write (by simp))
      · exact ih (fun tail htail => hdisjoint tail (by simp [htail]))

@[simp] theorem Program.writeElements_doesNotUnmap (writes : List ElementWrite) :
    (Program.writeElements writes).DoesNotUnmap := by
  induction writes with
  | nil => simp [Program.writeElements, Program.DoesNotUnmap]
  | cons write rest ih =>
      exact Program.DoesNotUnmap.then (by simp [ElementWrite.program]) ih

theorem Program.writeElements_wp {GF : BundledGFunctors}
    (writes : List ElementWrite) (mem : Memory)
    (hwidth : ∀ write, write ∈ writes → write.bytes.length = write.width)
    (hmapped : ∀ write, write ∈ writes → ∀ i, i < write.width →
      mem.mapped (write.base + write.index * write.width + i)) :
    ⊢@{IProp GF} Program.wp (Program.writeElements writes) mem
      (fun final => ∀ p, mem.mapped p → final.mapped p) := by
  induction writes generalizing mem with
  | nil => simpa [Program.writeElements] using
      (Program.wp_done (GF := GF) mem
        (fun final => ∀ p, mem.mapped p → final.mapped p) (by simp))
  | cons write rest ih =>
      simp only [Program.writeElements]
      apply Program.wp_then_preserves_mapped
        (Program.writeElement_wp_preserves_mapped write.base write.width
          write.index write.bytes mem (hwidth write (by simp))
          (hmapped write (by simp)))
      intro middle hmiddle
      apply ih middle
      · intro tail htail
        exact hwidth tail (by simp [htail])
      · intro tail htail i hi
        exact hmiddle _ (hmapped tail (by simp [htail]) i hi)

theorem Program.writeElements_wp_exact {GF : BundledGFunctors}
    (writes : List ElementWrite) (mem : Memory)
    (hwidth : ∀ write, write ∈ writes → write.bytes.length = write.width)
    (hmapped : ∀ write, write ∈ writes → ∀ i, i < write.width →
      mem.mapped (write.base + write.index * write.width + i)) :
    ⊢@{IProp GF} Program.wp (Program.writeElements writes) mem
      (fun final => final = ElementWrite.applyAll writes mem) := by
  induction writes generalizing mem with
  | nil => simpa [Program.writeElements, ElementWrite.applyAll] using
      (Program.wp_done (GF := GF) mem (fun final => final = mem) rfl)
  | cons write rest ih =>
      simp only [Program.writeElements, ElementWrite.applyAll]
      apply Program.wp_then
        (Program.writeElement_wp_exact write.base write.width write.index
          write.bytes mem (hwidth write (by simp)) (hmapped write (by simp)))
      intro middle hmiddle
      subst middle
      apply ih
      · intro tail htail
        exact hwidth tail (by simp [htail])
      · intro tail htail i hi
        exact Memory.mapped_writeBytes
          (hmapped tail (by simp [htail]) i hi)

/-- Stores emitted for ordinary indexed assignments. Unlike `writeBytes`, the
offsets need not be contiguous; their list order is the source execution
order. -/
def Program.writeOffsets (base : Addr) : List (Nat × Byte) → Program
  | [] => .done
  | (offset, value) :: rest =>
      .call (.store (base + offset) value) (fun _ => writeOffsets base rest)

inductive WriteOffsetSteps (base : Addr) :
    List (Nat × Byte) → Memory → Memory → Prop where
  | nil {mem} : WriteOffsetSteps base [] mem mem
  | cons {offset value rest mem next old}
      (hstore : PrimStep (.store (base + offset) value) mem .unit
        (mem.write (base + offset) value))
      (hold : mem (base + offset) = some old)
      (htail : WriteOffsetSteps base rest
        (mem.write (base + offset) value) next) :
      WriteOffsetSteps base ((offset, value) :: rest) mem next

theorem writeOffsetSteps_exists (base : Addr) (writes : List (Nat × Byte))
    (mem : Memory)
    (hmapped : ∀ write ∈ writes, mem.mapped (base + write.1)) :
    ∃ next, WriteOffsetSteps base writes mem next := by
  induction writes generalizing mem with
  | nil => exact ⟨mem, .nil⟩
  | cons write rest ih =>
      obtain ⟨offset, value⟩ := write
      obtain ⟨old, hold⟩ : ∃ old, mem (base + offset) = some old := by
        have h := hmapped (offset, value) (by simp)
        unfold Memory.mapped at h
        cases hmem : mem (base + offset) with
        | none => simp [hmem] at h
        | some old => exact ⟨old, rfl⟩
      have htailMapped :
          ∀ write ∈ rest,
            (mem.write (base + offset) value).mapped (base + write.1) := by
        intro tail htail
        exact Memory.mapped_write (hmapped tail (by simp [htail]))
      obtain ⟨next, htail⟩ :=
        ih (mem.write (base + offset) value) htailMapped
      exact ⟨next, .cons (.store hold) hold htail⟩

theorem WriteOffsetSteps.program_exec {base : Addr}
    {writes : List (Nat × Byte)} {before after : Memory}
    (hsteps : WriteOffsetSteps base writes before after) :
    Program.Exec (Program.writeOffsets base writes) before after := by
  induction hsteps with
  | nil => exact .done
  | cons hstore hold htail ih => exact .call hstore ih

theorem WriteOffsetSteps.program_exec_unique {base : Addr}
    {writes : List (Nat × Byte)} {before after final : Memory}
    (hsteps : WriteOffsetSteps base writes before after)
    (hexec : Program.Exec (Program.writeOffsets base writes) before final) :
    final = after := by
  induction hsteps generalizing final with
  | nil => cases hexec; rfl
  | cons hstore hold htail ih =>
      cases hexec with
      | call executed rest => cases executed; exact ih rest

theorem WriteOffsetSteps.program_wp {GF : BundledGFunctors} {base : Addr}
    {writes : List (Nat × Byte)} {before after : Memory}
    (hsteps : WriteOffsetSteps base writes before after) :
    ⊢@{IProp GF} Program.wp (Program.writeOffsets base writes) before
      (fun final => final = after) := by
  unfold Program.wp
  ipureintro
  exact ⟨⟨after, hsteps.program_exec⟩,
    fun final hexec => hsteps.program_exec_unique hexec⟩

/-- The generated effect program for relocation copies one byte at a time.
The encoded byte list fixes the value written after each load; a `CopySteps`
witness proves that the loaded source has exactly that value. -/
def Program.copyBytes (src dst : Addr) : List Byte → Program
  | [] => .done
  | value :: rest =>
      .call (.load src) (fun _ =>
        .call (.store dst value) (fun _ =>
          copyBytes (src + 1) (dst + 1) rest))

@[simp] theorem Program.copyBytes_doesNotUnmap (src dst : Addr)
    (values : List Byte) : (Program.copyBytes src dst values).DoesNotUnmap := by
  induction values generalizing src dst with
  | nil => simp [Program.copyBytes, Program.DoesNotUnmap]
  | cons value rest ih =>
      simp [Program.copyBytes, Program.DoesNotUnmap, Prim.DoesNotUnmap, ih]

theorem CopySteps.program_exec {src dst : Addr} {values : List Byte}
    {before after : Memory}
    (hsteps : CopySteps src dst values before after) :
    Program.Exec (Program.copyBytes src dst values) before after := by
  induction hsteps with
  | nil => exact .done
  | cons hload hstore htail ih => exact .call hload (.call hstore ih)

theorem CopySteps.program_exec_unique {src dst : Addr} {values : List Byte}
    {before after final : Memory}
    (hsteps : CopySteps src dst values before after)
    (hexec : Program.Exec (Program.copyBytes src dst values) before final) :
    final = after := by
  induction hsteps generalizing final with
  | nil =>
      cases hexec
      rfl
  | cons hload hstore htail ih =>
      cases hexec with
      | call executedLoad restExec =>
          cases executedLoad
          cases restExec with
          | call executedStore tailExec =>
              cases executedStore
              exact ih tailExec

/-- The concrete byte-copy trace supplied by the allocator/Vec ownership proof
is a closed no-stuck proof for the generated relocation program. -/
theorem CopySteps.program_wp {GF : BundledGFunctors} {src dst : Addr}
    {values : List Byte} {before after : Memory}
    (hsteps : CopySteps src dst values before after) :
    ⊢@{IProp GF} Program.wp (Program.copyBytes src dst values) before
      (fun final => final = after) := by
  unfold Program.wp
  ipureintro
  exact ⟨⟨after, hsteps.program_exec⟩,
    fun final hexec => hsteps.program_exec_unique hexec⟩

/-- Exclusive ownership of an allocated region proves a whole generated store
sequence safe even when the destination bytes are not initialized in the
separate contents map. `MemoryRep.write` keeps the allocation/mapping relation
valid after every byte. -/
theorem owned_writeBytes_wp {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {region : Region}
    {base : Nat} (values : List Byte)
    (hrep : MemoryRep allocated mem)
    (hinside : ∀ i, i < values.length → region.contains (base + i)) :
    byteHeapInterp (G := G) allocated ∗ OwnsBytes region ⊢
      ⌜∃ next, WriteSteps base values mem next ∧
        (⊢@{IProp GF} Program.wp (Program.writeBytes base values) mem
          (fun final => final = next))⌝ := by
  change byteHeapInterp (G := G) allocated ∗ ghostOwnsBytes region ⊢ _
  induction values generalizing base mem with
  | nil =>
      iintro H
      ipureintro
      exact ⟨mem, .nil, WriteSteps.program_wp .nil⟩
  | cons value rest ih =>
      iintro H
      ihave %hsafe := owned_store_safe (G := G) hrep
        (hinside 0 (by simp)) value $$ H
      obtain ⟨result, after, hstep⟩ := hsafe
      cases hstep with
      | @store _ _ old _ hold =>
          have hrepNext : MemoryRep allocated (mem.write base value) :=
            hrep.write hold
          have hinsideTail : ∀ i, i < rest.length →
              region.contains (base + 1 + i) := by
            intro i hi
            have h := hinside (i + 1) (by simp; omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using h
          have htailRule := ih (base := base + 1)
            (mem := mem.write base value) hrepNext hinsideTail
          ihave %htail := htailRule $$ H
          ipureintro
          obtain ⟨next, hsteps, _⟩ := htail
          let hall : WriteSteps base (value :: rest) mem next :=
            .cons (.store hold) hold hsteps
          exact ⟨next, hall, hall.program_wp⟩

/-- Iris adequacy for the Luffs primitive language. This is the closed-proof
boundary: semantic validity of a WP yields an actual complete execution. -/
theorem Program.wp_adequacy {GF : BundledGFunctors} {program : Program}
    {mem : Memory} {post : Memory → Prop}
    (hwp : ⊢@{IProp GF} Program.wp program mem post) :
    Program.Safe program mem ∧
      ∀ final, Program.Exec program mem final → post final := by
  apply pure_soundness (PROP := IProp GF)
  exact hwp

/-- The non-stuck projection of closed weakest-precondition adequacy. -/
theorem Program.wp_safe {GF : BundledGFunctors} {program : Program}
    {mem : Memory} {post : Memory → Prop}
    (hwp : ⊢@{IProp GF} Program.wp program mem post) :
    Program.Safe program mem :=
  (Program.wp_adequacy hwp).1

def Program.single (op : Prim) : Program := .call op (fun _ => .done)

theorem Program.single_doesNotUnmap {op : Prim} (hop : op.DoesNotUnmap) :
    (Program.single op).DoesNotUnmap := by
  simp [Program.single, Program.DoesNotUnmap, hop]

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

/-- Shared-borrow WP rule. Fractional ownership is preserved by the premise,
so siblings may read concurrently and later recombine to restore `&mut`. -/
theorem shared_load_wp {GF : BundledGFunctors} [G : ByteRegionGS GF]
    {allocated : ByteMap Unit} {mem : Memory} {r : Region} {p : Addr}
    (q : Qp) (hrep : MemoryRep allocated mem) (hp : r.contains p) :
    byteHeapInterp (G := G) allocated ∗ SharedBorrow q r ⊢
      Program.wp (Program.single (.load p)) mem (fun final => final = mem) := by
  iintro H
  ihave %hsafe := shared_load_safe (G := G) q hrep hp $$ H
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
