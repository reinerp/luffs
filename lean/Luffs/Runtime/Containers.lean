import Luffs.Containers.Vec
import Luffs.Memory.Scalar

set_option autoImplicit false

namespace Luffs.Runtime.Containers

open Luffs.Memory
open Luffs.Allocator.TLSF

/-- Pure reference semantics for the first byte-monomorphized Luffs lowering.
These definitions deliberately expose both the mutated storage and scalar
return value; the Rust functions mutate the first component in place. -/
def boxLoadU8 (storage : List Byte) (begin : Nat) : Option Byte :=
  storage[begin]?

def boxStoreU8 (storage : List Byte) (begin : Nat) (value : Byte) :
    Option (List Byte) :=
  if begin ≥ storage.length then none else some (storage.set begin value)

def vecPushU8 (storage : List Byte) (len capacity : Nat) (value : Byte) :
    Option (List Byte × Nat) :=
  if len ≥ capacity then none
  else if capacity > storage.length then none
  else some (storage.set len value, len + 1)

def vecLastU8 (storage : List Byte) (len : Nat) : Option Byte :=
  if len = 0 then none
  else if len > storage.length then none
  else storage[len - 1]?

def vecLenAfterPop (len : Nat) : Option Nat :=
  if 0 < len then some (len - 1) else none

def vecGetU8 (storage : List Byte) (len index : Nat) : Option Byte :=
  if index ≥ len then none
  else if len > storage.length then none
  else storage[index]?

def vecSliceU8 (storage : List Byte) (len begin end_ : Nat) :
    Option (List Byte) :=
  if begin > end_ then none
  else if end_ > len then none
  else if len > storage.length then none
  else some ((storage.drop begin).take (end_ - begin))

def vecCopyGrowU8 (source destination : List Byte) (len : Nat) :
    Option (List Byte) :=
  if len ≤ source.length ∧ len ≤ destination.length then
    some (source.take len ++ destination.drop len)
  else none

theorem boxLoadU8_result {storage : List Byte} {begin : Nat} {value : Byte}
    (hload : boxLoadU8 storage begin = some value) :
    begin < storage.length ∧ storage[begin]? = some value := by
  unfold boxLoadU8 at hload
  exact ⟨(getElem?_eq_some_iff.mp hload).1, hload⟩

theorem boxStoreU8_result {storage next : List Byte} {begin : Nat}
    {value : Byte} (hstore : boxStoreU8 storage begin value = some next) :
    begin < storage.length ∧ next = storage.set begin value ∧
      next.length = storage.length := by
  unfold boxStoreU8 at hstore
  split at hstore
  next => contradiction
  next hbound =>
    simp only [Option.some.injEq] at hstore
    subst next
    exact ⟨Nat.lt_of_not_ge hbound, rfl, List.length_set⟩

theorem vecPushU8_result {storage next : List Byte} {len capacity nextLen : Nat}
    {value : Byte}
    (hpush : vecPushU8 storage len capacity value = some (next, nextLen)) :
    len < capacity ∧ capacity ≤ storage.length ∧
      next = storage.set len value ∧ nextLen = len + 1 ∧
      next.length = storage.length := by
  unfold vecPushU8 at hpush
  split at hpush
  next => contradiction
  next hlen =>
    split at hpush
    next => contradiction
    next hcapacity =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hpush
      rcases hpush with ⟨hnext, hnextLen⟩
      subst next
      subst nextLen
      exact ⟨Nat.lt_of_not_ge hlen, Nat.le_of_not_gt hcapacity,
        rfl, rfl, List.length_set⟩

theorem vecPushU8_refines_handle {storage next : List Byte}
    {handle : Luffs.Containers.Vec.Handle} {nextLen : Nat} {value : Byte}
    (hpush : vecPushU8 storage handle.len handle.capacity value =
      some (next, nextLen)) :
    Luffs.Containers.Vec.push handle =
      some { handle with len := nextLen } := by
  have hresult := vecPushU8_result hpush
  simp [Luffs.Containers.Vec.push, hresult.1, hresult.2.2.2.1]

theorem vecLastU8_result {storage : List Byte} {len : Nat} {value : Byte}
    (hlast : vecLastU8 storage len = some value) :
    0 < len ∧ len ≤ storage.length ∧ storage[len - 1]? = some value := by
  unfold vecLastU8 at hlast
  split at hlast
  next => contradiction
  next hpositive =>
    split at hlast
    next => contradiction
    next hbound =>
      exact ⟨Nat.pos_of_ne_zero hpositive, Nat.le_of_not_gt hbound, hlast⟩

theorem vecLenAfterPop_refines_handle {handle : Luffs.Containers.Vec.Handle}
    {nextLen : Nat} (hpop : vecLenAfterPop handle.len = some nextLen) :
    Luffs.Containers.Vec.pop handle = some { handle with len := nextLen } := by
  unfold vecLenAfterPop at hpop
  split at hpop
  next hpositive =>
    simp only [Option.some.injEq] at hpop
    subst nextLen
    simp [Luffs.Containers.Vec.pop, hpositive]
  next => contradiction

theorem vecGetU8_result {storage : List Byte} {len index : Nat} {value : Byte}
    (hget : vecGetU8 storage len index = some value) :
    index < len ∧ len ≤ storage.length ∧ storage[index]? = some value := by
  unfold vecGetU8 at hget
  split at hget
  next => contradiction
  next hindex =>
    split at hget
    next => contradiction
    next hlen =>
      exact ⟨Nat.lt_of_not_ge hindex, Nat.le_of_not_gt hlen, hget⟩

theorem vecSliceU8_result {storage slice : List Byte} {len begin end_ : Nat}
    (hslice : vecSliceU8 storage len begin end_ = some slice) :
    begin ≤ end_ ∧ end_ ≤ len ∧ len ≤ storage.length ∧
      slice = (storage.drop begin).take (end_ - begin) := by
  unfold vecSliceU8 at hslice
  split at hslice
  next => contradiction
  next hbegin =>
    split at hslice
    next => contradiction
    next hend =>
      split at hslice
      next => contradiction
      next hlen =>
        simp only [Option.some.injEq] at hslice
        exact ⟨Nat.le_of_not_gt hbegin, Nat.le_of_not_gt hend,
          Nat.le_of_not_gt hlen, hslice.symm⟩

theorem vecCopyGrowU8_result {source destination next : List Byte} {len : Nat}
    (hcopy : vecCopyGrowU8 source destination len = some next) :
    len ≤ source.length ∧ len ≤ destination.length ∧
      next = source.take len ++ destination.drop len ∧
      next.length = destination.length := by
  unfold vecCopyGrowU8 at hcopy
  split at hcopy
  next hbounds =>
    simp only [Option.some.injEq] at hcopy
    subst next
    refine ⟨hbounds.1, hbounds.2, rfl, ?_⟩
    rw [List.length_append, List.length_take, List.length_drop,
      Nat.min_eq_left hbounds.1]
    omega
  next => contradiction

end Luffs.Runtime.Containers
