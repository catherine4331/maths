import Mathlib.Tactic
import Mathlib.Util.Delaborators

open Set

example (a b : ℝ) : (∀ ε > 0, |a - b| < ε) → a = b := by
  intro h
  by_contra hab
  have h_pos : |a - b| > 0 := abs_pos.mpr (sub_ne_zero.mpr hab)
  let ε₀ := |a - b|
  have hε_pos : ε₀ > 0 := by
    apply abs_pos.mpr
    exact sub_ne_zero_of_ne hab
  have h_lt : |a - b| < ε₀ := by
    apply h
    apply hε_pos
  have: |a - b| < |a - b| := by calc
    |a - b| < ε₀ := by apply h_lt
            _ = |a - b| := by ring
  rw [← lt_self_iff_false |a - b|]
  exact this

example {α : Type*} (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw [← compl_compl (Aᶜ ∪ Bᶜ)]
  rw [compl_union]
  rw [compl_compl, compl_compl]

example {α : Type*} (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro h₁
    rw [mem_compl_iff] at h₁
    rw [mem_union] at h₁
    push_neg at h₁
    exact h₁
  · intro h₁
    rw [mem_compl_iff]
    rw [mem_union]
    push_neg
    exact h₁
