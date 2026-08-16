import Luffs.Memory.Layout
import Luffs.Memory.Iris
import Luffs.Memory.ConcreteIris
import Luffs.Allocator.TLSF

namespace Luffs

/-- The logical shape of a conventional `(begin, length)` slice. -/
def BeginLenValid (arrayLen begin len : Nat) : Prop := begin + len ≤ arrayLen

/-- The logical shape of an explicit `(begin, end)` slice. -/
def BeginEndValid (arrayLen begin end_ : Nat) : Prop := begin ≤ end_ ∧ end_ ≤ arrayLen

end Luffs

export Luffs (BeginLenValid BeginEndValid)
