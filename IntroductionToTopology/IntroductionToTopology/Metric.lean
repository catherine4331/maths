import Mathlib.Tactic
import Mathlib.Util.Delaborators

class Metric (α : Type*) where
  dist : α → α → ℝ
  dist_nonneg : ∀ x y : α, dist x y ≥ 0
  dist_zero : ∀ x y : α, dist x y = 0 ↔ x = y
  dist_symm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
