import MathematicsInLean.Common
import Mathlib.Data.Real.Basic

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  -- This works too
  apply Or.inl
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

end

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h₁ | h₁
  · rw [abs_of_nonneg h₁]
    constructor
    · intro h₂
      exact Or.inl h₂
    · rintro (h₂ | h₂)
      exact h₂
      linarith
  · rw [abs_of_neg h₁]
    constructor
    · intro h₂
      exact Or.inr h₂
    · rintro (h₂ | h₂)
      linarith
      exact h₂

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h₁ | h₁
  · rw [abs_of_nonneg h₁]
    constructor
    · intro h₂
      constructor
      · linarith
      · exact h₂
    · rintro ⟨h₂, h₃⟩
      exact h₃
  · rw [abs_of_neg h₁]
    constructor
    · intro h₂
      constructor
      · linarith
      · linarith
    · rintro ⟨h₂, h₃⟩
      linarith

-- We can split out into more than two cases with rcases
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

-- We can also still use rfl in there as well
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a, b, rfl | rfl⟩ <;> linarith [sq_nonneg a, sq_nonneg b]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ : x^2 - 1 = 0 := by rw [h, sub_self]
  have h₂ : (x + 1) * (x - 1) = 0 := by
    rw [← h₁]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with h₃ | h₃
  · right
    rw [eq_neg_iff_add_eq_zero]
    exact h₃
  · left
    exact eq_of_sub_eq_zero h₃

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
