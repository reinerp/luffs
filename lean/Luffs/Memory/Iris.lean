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
  exclusive {r : Region} : ownsBytes r ∗ ownsBytes r ⊢ False

def OwnsBytes {PROP : Type} [BI PROP] [ByteRegionLogic PROP] (r : Region) : PROP :=
  ByteRegionLogic.ownsBytes r

theorem ownsBytes_exclusive {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    (r : Region) : OwnsBytes (PROP := PROP) r ∗ OwnsBytes r ⊢ False :=
  ByteRegionLogic.exclusive (PROP := PROP)

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
  failure (bytes : Nat) : mmapPost bytes none ⊢ True
  munmap (r : Region) : OwnsBytes (PROP := PROP) r ⊢ mmapPost r.bytes none

end Luffs.Memory
