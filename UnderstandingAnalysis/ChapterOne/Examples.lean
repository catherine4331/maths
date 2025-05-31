import Mathlib.Tactic
import Mathlib.Util.Delaborators

open Set

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
