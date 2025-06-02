import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

open Set Finset

-- 1.2.6
lemma aux (a b : ℝ) : (a + b)^2 ≤ (|a| + |b|)^2 := by
  have : a*b ≤ |a * b| := le_abs_self (a * b)
  calc
    (a + b)^2 = a^2 + b^2 + 2*a*b := by ring
            _ ≤ a^2 + b^2 + 2*|a*b| := by linarith [this]
            _ = a^2 + b^2 + 2*|a| * |b| := by rw [abs_mul]; ring
            _ = (|a| + |b|)^2 := by
              ring_nf
              rw [sq_abs, sq_abs]
              ring

theorem triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have : |a + b|^2 ≤ (|a| + |b|)^2 := by
    calc
      |a + b|^2 = (a + b)^2 := by apply sq_abs (a + b)
              _ ≤ (|a| + |b|)^2 := by apply aux
  rw [sq_le_sq₀] at this
  apply this
  apply abs_nonneg
  apply add_nonneg (abs_nonneg a) (abs_nonneg b)

example (a b c d : ℝ) : |a - b| ≤ |a - c| + |c - d| + |d - b| := by calc
  |a - b| = |(a - c) + (c - b)| := by ring_nf
        _ ≤ |a - c| + |c - b| := triangle (a - c) (c - b)
        _ = |a - c| + |(c - d) + (d - b)| := by ring_nf
        _ ≤ |a - c| + |c - d| + |d - b| := by
          rw [add_assoc, add_le_add_iff_left]
          apply triangle

theorem reverse_triangle (a b : ℝ) : |(|a| - |b|)| ≤ |a - b| := by
  have : |a| ≤ |a - b| + |b| := by calc
    |a| = |a - b + b| := by ring_nf
      _ ≤ |a - b| + |b| := triangle (a - b) b
  have pos : |a| - |b| ≤ |a - b| := by linarith
  have : |b| ≤ |a - b| + |a| := by calc
    |b| = |b - a + a| := by ring_nf
      _ ≤ |b - a| + |a| := triangle (b - a) a
      _ = |a - b| + |a| := by rw [abs_sub_comm]
  have neg : -|a - b| ≤ |a| - |b| := by linarith
  rw [abs_le]
  exact And.intro neg pos

-- 1.2.7
example (A B : Set ℝ) (g : ℝ → ℝ) : g '' (A ∩ B) ⊆ g '' A ∩ g '' B := by
  rintro y ⟨x, ⟨inter, rfl⟩⟩
  constructor
  · use x, inter.left
  · use x, inter.right

example (A B : Set ℝ) (g : ℝ → ℝ) : g '' A ∪ g '' B = g '' (A ∪ B) := by
  ext y
  constructor
  · rintro (⟨x, ⟨x_in, rfl⟩⟩ | ⟨x, ⟨x_in, rfl⟩⟩)
    · use x
      apply And.intro (Or.inl x_in) (by rfl)
    · use x
      apply And.intro (Or.inr x_in) (by rfl)
  · rintro ⟨x, ⟨(x_in| x_in), rfl⟩⟩
    · apply Or.inl (by use x)
    · apply Or.inr (by use x)

-- 1.2.9
example (A B : Set ℝ) (g : ℝ → ℝ) : g ⁻¹' (A ∩ B) = g ⁻¹' A ∩ g ⁻¹' B := by
  ext x
  constructor
  · rintro ⟨x_A, x_B⟩
    exact And.intro x_A x_B
  · rintro ⟨x_A, x_B⟩
    exact And.intro x_A x_B

example (A B : Set ℝ) (g : ℝ → ℝ) : g ⁻¹' (A ∪ B) = g ⁻¹' A ∪ g ⁻¹' B := by
  ext x
  constructor
  · rintro (ga | gb)
    · apply Or.inl ga
    · apply Or.inr gb
  · rintro (ga | gb)
    · apply Or.inl ga
    · apply Or.inr gb

example (A : ℕ → Set α) (n : ℕ) :
    (⋃ i ∈ Finset.range (n + 1), A i)ᶜ = ⋂ i ∈ Finset.range (n + 1), (A i)ᶜ := by
  induction' n with n ih
  · simp
  · simp
