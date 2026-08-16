set_option autoImplicit false

namespace Luffs.Allocator.TLSF

/-- Reference semantics for a count-trailing-zeros bitmap operation. The list
is statically bounded by the TLSF bitmap width in clients. -/
def firstTrueIndex : List Bool -> Option Nat
  | [] => none
  | bit :: rest =>
      if bit then some 0 else (firstTrueIndex rest).map Nat.succ

def firstSetFrom (bits : List Bool) (start : Nat) : Option Nat :=
  (firstTrueIndex (bits.drop start)).map (start + ·)

theorem firstTrueIndex_sound {bits : List Bool} {i : Nat}
    (h : firstTrueIndex bits = some i) : bits[i]? = some true := by
  induction bits generalizing i with
  | nil => simp [firstTrueIndex] at h
  | cons bit rest ih =>
      cases bit with
      | true =>
        simp [firstTrueIndex] at h
        subst h
        rfl
      | false =>
        simp [firstTrueIndex] at h
        obtain ⟨j, hj, rfl⟩ := h
        simp only [List.getElem?_cons_succ]
        exact ih hj

theorem firstTrueIndex_lt_length {bits : List Bool} {i : Nat}
    (h : firstTrueIndex bits = some i) : i < bits.length := by
  exact (List.getElem?_eq_some_iff.mp (firstTrueIndex_sound h)).1

theorem firstTrueIndex_complete {bits : List Bool} {i : Nat}
    (hget : bits[i]? = some true) :
    ∃ found, firstTrueIndex bits = some found := by
  induction bits generalizing i with
  | nil => simp at hget
  | cons bit rest ih =>
      cases bit with
      | true => exact ⟨0, by simp [firstTrueIndex]⟩
      | false =>
          cases i with
          | zero => simp at hget
          | succ i =>
              simp only [List.getElem?_cons_succ] at hget
              obtain ⟨found, hfound⟩ := ih hget
              exact ⟨found + 1, by simp [firstTrueIndex, hfound]⟩

theorem firstTrueIndex_minimal {bits : List Bool} {i j : Nat}
    (h : firstTrueIndex bits = some i) (hj : j < i) :
    bits[j]? = some false := by
  induction bits generalizing i j with
  | nil => simp [firstTrueIndex] at h
  | cons bit rest ih =>
      cases bit with
      | true =>
          simp [firstTrueIndex] at h
          omega
      | false =>
          simp [firstTrueIndex] at h
          obtain ⟨offset, hoffset, rfl⟩ := h
          cases j with
          | zero => rfl
          | succ k =>
              simp only [List.getElem?_cons_succ]
              apply ih hoffset
              omega

theorem firstSetFrom_sound {bits : List Bool} {start i : Nat}
    (h : firstSetFrom bits start = some i) :
    start ≤ i ∧ i < bits.length ∧ bits[i]? = some true := by
  unfold firstSetFrom at h
  obtain ⟨offset, hoffset, rfl⟩ := Option.map_eq_some_iff.mp h
  have hget := firstTrueIndex_sound hoffset
  have hlt := firstTrueIndex_lt_length hoffset
  rw [List.getElem?_drop] at hget
  simp only [List.length_drop] at hlt
  constructor
  · exact Nat.le_add_right _ _
  constructor
  · omega
  · simpa only [Nat.add_comm] using hget

theorem firstSetFrom_complete {bits : List Bool} {start i : Nat}
    (hstart : start ≤ i) (hget : bits[i]? = some true) :
    ∃ found, firstSetFrom bits start = some found := by
  obtain ⟨delta, rfl⟩ := Nat.exists_eq_add_of_le hstart
  have hdrop : (bits.drop start)[delta]? = some true := by
    rw [List.getElem?_drop]
    simpa only [Nat.add_comm] using hget
  obtain ⟨found, hfound⟩ := firstTrueIndex_complete hdrop
  exact ⟨start + found, by simp [firstSetFrom, hfound]⟩

theorem firstSetFrom_minimal {bits : List Bool} {start i j : Nat}
    (h : firstSetFrom bits start = some i) (hstart : start ≤ j) (hj : j < i) :
    bits[j]? = some false := by
  unfold firstSetFrom at h
  obtain ⟨offset, hoffset, hi⟩ := Option.map_eq_some_iff.mp h
  subst hi
  obtain ⟨delta, rfl⟩ := Nat.exists_eq_add_of_le hstart
  have hd := firstTrueIndex_minimal hoffset (j := delta) (by omega)
  rw [List.getElem?_drop] at hd
  simpa only [Nat.add_comm] using hd

end Luffs.Allocator.TLSF
