import Luffs.Memory.Layout
import Luffs.Memory.Iris
import Luffs.Memory.ConcreteIris
import Luffs.Memory.Semantics
import Luffs.Memory.TypedIris
import Luffs.Memory.Value
import Luffs.Allocator.TLSF
import Luffs.Allocator.TLSF.Bitmap
import Luffs.Allocator.TLSF.FreeList
import Luffs.Allocator.TLSF.Bins
import Luffs.Allocator.TLSF.Alloc
import Luffs.Allocator.TLSF.Ownership
import Luffs.Allocator.TLSF.Dealloc
import Luffs.Containers.Box

namespace Luffs

/-- The logical shape of a conventional `(begin, length)` slice. -/
def BeginLenValid (arrayLen begin len : Nat) : Prop := begin + len ≤ arrayLen

/-- The logical shape of an explicit `(begin, end)` slice. -/
def BeginEndValid (arrayLen begin end_ : Nat) : Prop := begin ≤ end_ ∧ end_ ≤ arrayLen

end Luffs

export Luffs (BeginLenValid BeginEndValid)
