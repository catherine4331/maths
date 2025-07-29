import Mathlib.Tactic
import Mathlib.Util.Delaborators

structure Metric (α : Type*) where
  δ : α → α → ℝ
  δ_nonneg : ∀ x y : α, δ x y ≥ 0
  δ_zero : ∀ x y : α, δ x y = 0 ↔ x = y
  δ_symm : ∀ x y : α, δ x y = δ y x
  δ_triangle : ∀ x y z : α, δ x z ≤ δ x y + δ y z
