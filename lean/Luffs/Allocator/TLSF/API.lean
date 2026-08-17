import Luffs.Allocator.TLSF.Ownership
import Luffs.Allocator.TLSF.Dealloc

set_option autoImplicit false

namespace Luffs.Allocator.TLSF.API

open Iris Iris.BI
open Luffs.Memory
open Luffs.Allocator.TLSF

/-- A live allocation is an allocated physical block in the current TLSF
partition. Its bytes are deliberately absent from `OwnsFree`: the client owns
them through the capability returned by `allocate`. -/
def Live (state : Alloc.State) (block : Block) : Prop :=
  block ∈ state.physical ∧ block.free = false

/-- The pure safety half of the allocator API: distinct live allocations never
overlap. -/
theorem live_regions_disjoint {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state) {left right : Block}
    (hleft : Live state left) (hright : Live state right) (hne : left ≠ right) :
    (left.region pool).disjoint (right.region pool) :=
  wellFormed_regions_disjoint hvalid.1 hleft.1 hright.1 hne

/-- Successful TLSF allocation satisfies the public allocator API. It returns
a live block disjoint from every old live block, preserves every old live
region, and transfers exactly one exclusive byte capability while leaving an
arbitrary client frame untouched. -/
theorem allocate
    {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    {pool : Region} {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    {request : Nat} {hrequest : 0 < request}
    {hkeyMax : requestKey request < 2 ^ firstLevelCount}
    (haligned : alignment ∣ request) {result : Alloc.Result}
    (hsuccess : Alloc.allocate state request hrequest hkeyMax = some result)
    (frame : PROP) :
    Alloc.Valid pool result.state ∧ Live result.state result.allocated ∧
    (∀ old, Live state old →
      ∃ updated, Live result.state updated ∧
        Bins.SamePhysical updated old ∧ updated ≠ result.allocated ∧
        (result.allocated.region pool).disjoint (updated.region pool)) ∧
    (frame ∗ Ownership.OwnsFree (PROP := PROP) pool state.physical ⊣⊢
      OwnsBytes (result.allocated.region pool) ∗
        (frame ∗ Ownership.OwnsFree pool result.state.physical)) := by
  have hnext := Alloc.allocate_preserves_valid hvalid haligned hsuccess
  have hallocatedMem := Alloc.allocate_allocated_mem hsuccess
  have hsafe := Alloc.allocate_safe hvalid hsuccess
  have hownership := Ownership.allocate_ownsFree (PROP := PROP) pool hvalid hsuccess
  refine ⟨hnext, ⟨hallocatedMem, hsafe.1⟩, ?_, ?_⟩
  · intro old hold
    obtain ⟨updated, hupdated, hsame, hne⟩ :=
      Alloc.allocate_preserves_allocated hvalid hsuccess hold.1 hold.2
    have hupdatedAllocated : updated.free = false :=
      (Bins.samePhysical_free hsame).trans hold.2
    exact ⟨updated, ⟨hupdated, hupdatedAllocated⟩, hsame, hne,
      wellFormed_regions_disjoint hnext.1 hallocatedMem hupdated (Ne.symm hne)⟩
  · refine (sep_congr_right hownership).trans ?_
    exact sep_assoc.symm.trans ((sep_congr_left sep_comm).trans sep_assoc)

/-- Successful TLSF deallocation satisfies the other half of the API: the
caller must return the exact live-region capability, which is consumed into
the allocator's free-byte invariant. An arbitrary disjoint client frame is
preserved. -/
theorem deallocate
    {PROP : Type} [BI PROP] [ByteRegionLogic PROP]
    {pool : Region} {state next : Alloc.State} {index : Nat} {returned : Region}
    (hvalid : Alloc.Valid pool state)
    (hsuccess : Dealloc.deallocate pool state index returned = some next)
    (frame : PROP) :
    Alloc.Valid pool next ∧
    (frame ∗ (OwnsBytes (PROP := PROP) returned ∗
        Ownership.OwnsFree pool state.physical) ⊣⊢
      frame ∗ Ownership.OwnsFree pool next.physical) := by
  refine ⟨Dealloc.deallocate_preserves_valid hvalid hsuccess, ?_⟩
  exact sep_congr_right (Dealloc.deallocate_ownsFree (PROP := PROP) hsuccess)

end Luffs.Allocator.TLSF.API
