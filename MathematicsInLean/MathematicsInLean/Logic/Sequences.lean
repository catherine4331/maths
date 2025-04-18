import MathematicsInLean.Common
import Mathlib.Data.Real.Basic

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- The ext function allows us to prove function equality
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext u v
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

-- A nice intro real analysis proof
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

-- A more complicated one. We'll come back to this when we start doing real analysis properly
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have hns : n ≥ Ns := le_of_max_le_left hn
  have hnt : n ≥ Nt := le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := abs_add (s n - a) (t n - b)
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add (hs n hns) (ht n hnt)
    _ = ε := by
      norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εdibvcpos : 0 < ε / |c| := by exact div_pos εpos acpos
  rcases cs (ε / |c|) εdibvcpos with ⟨N, hs⟩
  use N
  intro n hn
  calc
    |c * s n - c * a| = |c * (s n - a)| := by
      rw [← mul_sub_left_distrib]
    _ = |c| * |s n - a| := abs_mul c (s n - a)
    _ = |s n - a| * |c| := by ring
    _ <  ε / |c| * |c| := by
      apply mul_lt_mul (hs n hn) (le_refl |c|) acpos
      · linarith
    _ = ε := by
      rw [mul_comm, ← mul_div_assoc, mul_div_cancel_left |c| ε]
