import Luffs.Allocator.TLSF

set_option autoImplicit false

namespace Luffs.Allocator.TLSF.FreeList

def withLinks (b : Block) (previous next : Option Nat) : Block :=
  { offset := b.offset, bytes := b.bytes, free := true,
    prevFree := b.prevFree, prevFreeLink := previous, nextFreeLink := next }

def linkedFrom : Option Nat -> List Block -> Prop
  | _, [] => True
  | previous, b :: rest =>
      b.free = true ∧
      b.prevFreeLink = previous ∧
      b.nextFreeLink = rest.head?.map Block.offset ∧
      linkedFrom (some b.offset) rest

def Valid (blocks : List Block) : Prop :=
  linkedFrom none blocks ∧ (blocks.map Block.offset).Nodup

def insertFront (b : Block) : List Block -> List Block
  | [] => [withLinks b none none]
  | head :: rest =>
      withLinks b none (some head.offset) ::
        withLinks head (some b.offset) head.nextFreeLink :: rest

theorem withLinks_fields (b : Block) (previous next : Option Nat) :
    (withLinks b previous next).offset = b.offset ∧
    (withLinks b previous next).bytes = b.bytes ∧
    (withLinks b previous next).free = true ∧
    (withLinks b previous next).prevFreeLink = previous ∧
    (withLinks b previous next).nextFreeLink = next := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem insertFront_linked (b : Block) (blocks : List Block)
    (hlinked : linkedFrom none blocks) :
    linkedFrom none (insertFront b blocks) := by
  cases blocks with
  | nil => simp [insertFront, linkedFrom, withLinks]
  | cons head rest =>
      simp only [linkedFrom] at hlinked
      rcases hlinked with ⟨hfree, hprev, hnext, hrest⟩
      simp [insertFront, linkedFrom, withLinks, hnext, hrest]

theorem insertFront_offsets (b : Block) (blocks : List Block) :
    (insertFront b blocks).map Block.offset = b.offset :: blocks.map Block.offset := by
  cases blocks <;> simp [insertFront, withLinks]

theorem insertFront_valid (b : Block) (blocks : List Block) (hvalid : Valid blocks)
    (hfresh : b.offset ∉ blocks.map Block.offset) : Valid (insertFront b blocks) := by
  constructor
  · exact insertFront_linked b blocks hvalid.1
  · rw [insertFront_offsets]
    exact List.nodup_cons.2 ⟨hfresh, hvalid.2⟩

def removeFront : List Block -> Option (Block × List Block)
  | [] => none
  | head :: [] => some (withLinks head none none, [])
  | head :: next :: rest =>
      some (withLinks head none none, withLinks next none next.nextFreeLink :: rest)

theorem removeFront_valid {blocks : List Block} {removed : Block} {rest : List Block}
    (hvalid : Valid blocks) (hremove : removeFront blocks = some (removed, rest)) :
    Valid rest := by
  cases blocks with
  | nil => simp [removeFront] at hremove
  | cons head tail =>
      cases tail with
      | nil =>
          simp [removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          exact ⟨trivial, List.nodup_nil⟩
      | cons next more =>
          simp [removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          rcases hvalid with ⟨hlinked, hnodup⟩
          simp only [linkedFrom] at hlinked
          rcases hlinked with ⟨_, _, _, htail⟩
          rcases htail with ⟨hfree, _, hnext, hmore⟩
          constructor
          · simp [linkedFrom, withLinks, hnext, hmore]
          · simpa [withLinks] using (List.nodup_cons.mp hnodup).2

theorem removeFront_detaches {blocks : List Block} {removed : Block} {rest : List Block}
    (hremove : removeFront blocks = some (removed, rest)) :
    removed.free = true ∧ removed.prevFreeLink = none ∧ removed.nextFreeLink = none := by
  cases blocks with
  | nil => simp [removeFront] at hremove
  | cons head tail =>
      cases tail with
      | nil =>
          simp [removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | cons next more =>
          simp [removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem removeFront_removes_head {blocks : List Block} {removed : Block}
    {rest : List Block} (hremove : removeFront blocks = some (removed, rest)) :
    (blocks.map Block.offset).head? = some removed.offset ∧
      rest.map Block.offset = (blocks.map Block.offset).tail := by
  cases blocks with
  | nil => simp [removeFront] at hremove
  | cons head tail =>
      cases tail with
      | nil =>
          simp [removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          simp [withLinks]
      | cons next more =>
          simp [removeFront] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          simp [withLinks]

end Luffs.Allocator.TLSF.FreeList
