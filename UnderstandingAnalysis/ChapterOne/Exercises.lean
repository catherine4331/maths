import Mathlib.Tactic
import Mathlib.Util.Delaborators

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
