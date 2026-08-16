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

end Luffs.Memory
