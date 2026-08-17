import Iris
import Luffs.Memory.Layout

set_option autoImplicit false

namespace Luffs.Memory

open Iris Iris.BI

/--
The Iris assertion exposed by Luffs memory primitives. `OwnsBytes r` is deliberately
abstract: clients can split and recombine it only through the proved laws below.
The implementation will be an Iris authoritative finite-map resource, not a second
separation logic.
-/
class ByteRegionLogic (PROP : Type) [BI PROP] where
  ownsBytes : Region -> PROP
  split {r : Region} {left right : Nat} :
    r.bytes = left + right ->
    ownsBytes r ⊣⊢
      ownsBytes { base := r.base, bytes := left } ∗
      ownsBytes { base := r.base + left, bytes := right }
  exclusive {r : Region} : 0 < r.bytes -> ownsBytes r ∗ ownsBytes r ⊢ False

def OwnsBytes {PROP : Type} [BI PROP] [ByteRegionLogic PROP] (r : Region) : PROP :=
  ByteRegionLogic.ownsBytes r

theorem ownsBytes_exclusive {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (r : Region) (h : 0 < r.bytes) :
    OwnsBytes (PROP := PROP) r ∗ OwnsBytes r ⊢ False :=
  ByteRegionLogic.exclusive (PROP := PROP) h

theorem ownsBytes_split3 {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (r : Region) (first middle last : Nat)
    (hlength : r.bytes = first + middle + last) :
    OwnsBytes (PROP := PROP) r ⊣⊢
      OwnsBytes { base := r.base, bytes := first } ∗
        (OwnsBytes { base := r.base + first, bytes := middle } ∗
          OwnsBytes { base := r.base + first + middle, bytes := last }) := by
  have hfirst : r.bytes = first + (middle + last) := by omega
  have hrest : (middle + last) = middle + last := rfl
  refine (ByteRegionLogic.split (PROP := PROP) hfirst).trans ?_
  refine sep_congr_right ?_
  simpa [OwnsBytes, Nat.add_assoc] using
    (ByteRegionLogic.split (PROP := PROP)
      (r := { base := r.base + first, bytes := middle + last }) hrest)

/--
The sole trusted allocator boundary. A platform implementation must refine this
contract to `mmap`: success returns exclusive ownership of a fresh, page-aligned
nonempty region; failure changes no owned memory.

TLSF does not appear here. It is a client of this interface and must prove that it
partitions `OwnsBytes` without duplication or loss.
-/
class MMapSpec (PROP : Type) [BI PROP] [ByteRegionLogic PROP] where
  pageSize : Nat
  pageSize_pos : 0 < pageSize
  mmapPost : Nat -> Option Region -> PROP
  success (bytes : Nat) (hbytes : 0 < bytes) (r : Region) :
    mmapPost bytes (some r) ⊢
      ⌜r.bytes = bytes ∧ r.base % pageSize = 0⌝ ∗ OwnsBytes (PROP := PROP) r
  failure (bytes : Nat) : mmapPost bytes none ⊣⊢ emp
  munmap (r : Region) : OwnsBytes (PROP := PROP) r ⊢ mmapPost r.bytes none

/-- A failed mmap is resource-neutral, so every disjoint caller frame is
preserved exactly. This is the separation-logic statement of transactional
failure at the sole trusted allocation boundary. -/
theorem mmap_failure_preserves_frame
    {PROP : Type} [BI PROP] [ByteRegionLogic PROP] [MMapSpec PROP]
    (frame : PROP) (bytes : Nat) :
    frame ∗ MMapSpec.mmapPost (PROP := PROP) bytes none ⊣⊢ frame := by
  exact (sep_congr_right (MMapSpec.failure (PROP := PROP) bytes)).trans sep_emp

end Luffs.Memory
