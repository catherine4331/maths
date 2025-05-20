import MathematicsInLean.Common
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ

namespace GaussInt

instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One GaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im + y.re⟩⟩

end GaussInt
