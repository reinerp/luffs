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

/-- Rebuild intrusive links from list order. This is an executable, bounded
fallback for unlinking a non-head block; later code generation may lower it to
the conventional O(1) predecessor/successor writes after proving refinement. -/
def relinkFrom : Option Nat -> List Block -> List Block
  | _, [] => []
  | previous, b :: rest =>
      withLinks b previous (rest.head?.map Block.offset) ::
        relinkFrom (some b.offset) rest

def relink (blocks : List Block) : List Block := relinkFrom none blocks

def findOffset? : List Block -> Nat -> Option Block
  | [], _ => none
  | b :: rest, offset => if b.offset = offset then some b else findOffset? rest offset

def eraseOffset : List Block -> Nat -> List Block
  | [], _ => []
  | b :: rest, offset => if b.offset = offset then rest else b :: eraseOffset rest offset

def removeOffset (blocks : List Block) (offset : Nat) : Option (Block × List Block) :=
  match findOffset? blocks offset with
  | none => none
  | some found => some (withLinks found none none, relink (eraseOffset blocks offset))

theorem relinkFrom_offsets (previous : Option Nat) (blocks : List Block) :
    (relinkFrom previous blocks).map Block.offset = blocks.map Block.offset := by
  induction blocks generalizing previous with
  | nil => rfl
  | cons b rest => simp [relinkFrom, withLinks, *]

theorem relinkFrom_linked (previous : Option Nat) (blocks : List Block) :
    linkedFrom previous (relinkFrom previous blocks) := by
  induction blocks generalizing previous with
  | nil => trivial
  | cons b rest ih =>
      simp only [relinkFrom, linkedFrom, withLinks]
      refine ⟨trivial, trivial, ?_, ih (some b.offset)⟩
      cases rest <;> simp [relinkFrom, withLinks]

theorem relinkFrom_member_origin (previous : Option Nat) {blocks : List Block}
    {updated : Block} (hfree : ∀ b ∈ blocks, b.free = true)
    (hmem : updated ∈ relinkFrom previous blocks) :
    ∃ old ∈ blocks, updated.offset = old.offset ∧
      updated.bytes = old.bytes ∧ updated.free = old.free := by
  induction blocks generalizing previous with
  | nil => simp [relinkFrom] at hmem
  | cons head rest ih =>
      simp only [relinkFrom, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact ⟨head, by simp, by
          simp [withLinks, hfree head (by simp)]⟩
      · have hrestFree : ∀ b ∈ rest, b.free = true :=
          fun b hb => hfree b (by simp [hb])
        obtain ⟨old, hold, hsame⟩ := ih (some head.offset) hrestFree htail
        exact ⟨old, by simp [hold], hsame⟩

theorem eraseOffset_member {blocks : List Block} {offset : Nat} {b : Block}
    (hmem : b ∈ eraseOffset blocks offset) : b ∈ blocks := by
  induction blocks with
  | nil => simp [eraseOffset] at hmem
  | cons head rest ih =>
      by_cases heq : head.offset = offset
      · simp [eraseOffset, heq] at hmem
        exact by simp [hmem]
      · simp only [eraseOffset, heq, ↓reduceIte, List.mem_cons] at hmem
        rcases hmem with rfl | htail
        · simp
        · exact by simp [ih htail]

theorem relink_member_origin {blocks : List Block} {updated : Block}
    (hfree : ∀ b ∈ blocks, b.free = true) (hmem : updated ∈ relink blocks) :
    ∃ old ∈ blocks, updated.offset = old.offset ∧
      updated.bytes = old.bytes ∧ updated.free = old.free :=
  relinkFrom_member_origin none hfree hmem

theorem relink_valid {blocks : List Block}
    (hnodup : (blocks.map Block.offset).Nodup) : Valid (relink blocks) := by
  exact ⟨relinkFrom_linked none blocks, by
    simpa [relink, relinkFrom_offsets] using hnodup⟩

theorem findOffset?_some_mem {blocks : List Block} {offset : Nat} {found : Block}
    (hfind : findOffset? blocks offset = some found) :
    found ∈ blocks ∧ found.offset = offset := by
  induction blocks with
  | nil => simp [findOffset?] at hfind
  | cons b rest ih =>
      simp only [findOffset?] at hfind
      split at hfind
      next heq =>
        simp only [Option.some.injEq] at hfind
        subst found
        exact ⟨by simp, heq⟩
      next =>
        have htail := ih hfind
        exact ⟨by simp [htail.1], htail.2⟩

theorem findOffset?_complete {blocks : List Block} {b : Block}
    (hmem : b ∈ blocks) : ∃ found, findOffset? blocks b.offset = some found := by
  induction blocks with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact ⟨b, by simp [findOffset?]⟩
      · by_cases heq : head.offset = b.offset
        · exact ⟨head, by simp [findOffset?, heq]⟩
        · obtain ⟨found, hfind⟩ := ih htail
          exact ⟨found, by simp [findOffset?, heq, hfind]⟩

theorem eraseOffset_offsets {blocks : List Block} {offset : Nat}
    (hmem : offset ∈ blocks.map Block.offset) :
    (eraseOffset blocks offset).map Block.offset =
      (blocks.map Block.offset).erase offset := by
  induction blocks with
  | nil => simp at hmem
  | cons b rest ih =>
      by_cases heq : b.offset = offset
      · simp [eraseOffset, heq]
      · simp only [List.map_cons, List.mem_cons] at hmem
        have htail : offset ∈ rest.map Block.offset :=
          hmem.resolve_left (Ne.symm heq)
        simp [eraseOffset, heq, ih htail]

theorem removeOffset_valid {blocks rest : List Block} {offset : Nat}
    {removed : Block} (hvalid : Valid blocks)
    (hremove : removeOffset blocks offset = some (removed, rest)) :
    Valid rest := by
  unfold removeOffset at hremove
  cases hfind : findOffset? blocks offset with
  | none => simp [hfind] at hremove
  | some found =>
      simp [hfind] at hremove
      rcases hremove with ⟨rfl, rfl⟩
      have hfound := findOffset?_some_mem hfind
      have hoffsetMem : offset ∈ blocks.map Block.offset := by
        rw [← hfound.2]
        exact List.mem_map_of_mem hfound.1
      apply relink_valid
      rw [eraseOffset_offsets hoffsetMem]
      exact hvalid.2.erase _

theorem removeOffset_detaches {blocks rest : List Block} {offset : Nat}
    {removed : Block} (hremove : removeOffset blocks offset = some (removed, rest)) :
    removed.free = true ∧ removed.prevFreeLink = none ∧ removed.nextFreeLink = none := by
  unfold removeOffset at hremove
  cases hfind : findOffset? blocks offset with
  | none => simp [hfind] at hremove
  | some found =>
      simp [hfind] at hremove
      rcases hremove with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩

theorem removeFront_none_iff {blocks : List Block} :
    removeFront blocks = none ↔ blocks = [] := by
  cases blocks with
  | nil => simp [removeFront]
  | cons head rest =>
      cases rest <;> simp [removeFront]

theorem removeFront_exists {blocks : List Block} (hnonempty : blocks ≠ []) :
    ∃ removed rest, removeFront blocks = some (removed, rest) := by
  cases hremove : removeFront blocks with
  | none => exact ((removeFront_none_iff.mp hremove) |> hnonempty).elim
  | some result =>
      obtain ⟨removed, rest⟩ := result
      exact ⟨removed, rest, rfl⟩

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
