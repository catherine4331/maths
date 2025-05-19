import MathematicsInLean.Common
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Real.Basic

noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  simp [add, add_assoc]

def smul (r : ℝ) (a : Point) : Point :=
  ⟨r * a.x, r * a.y, r * a.z⟩

theorem smul_distrib (r : ℝ) (a b : Point) : (smul r a).add (smul r b) = smul r (a.add b) := by
  -- rw [smul, smul, smul, add, add]
  -- ext <;> dsimp
  -- repeat' rw [← mul_add]
  simp [smul, add, mul_add]

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

def swapXY (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

def weightedAverage (lambda : ℝ) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
 (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (by linarith) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (by linarith) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (by linarith) b.z_nonneg)
  sum_eq := by
    trans (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda)
    · ring
    · simp [a.sum_eq, b.sum_eq]

end StandardTwoSimplex

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    · norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, a.sum_eq_one, b.sum_eq_one]
    field_simp

def weightedAverage (n : ℕ) (lambda : ℝ) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
  (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i * lambda + b.V i * (1 - lambda))
  NonNeg := by
    intro i
    apply add_nonneg
    · apply mul_nonneg (a.NonNeg i) lambda_nonneg
    · apply mul_nonneg (b.NonNeg i) (by linarith)
  sum_eq_one := by
    trans (∑ i, a.V i) * lambda + (∑ i, b.V i) * (1 - lambda)
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    · simp [a.sum_eq_one, b.sum_eq_one]

end StandardSimplex

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section

variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end
