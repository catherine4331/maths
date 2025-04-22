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
      rw [mul_comm, mul_div_cancel₀]
      linarith

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc
    |s n| = |s n - a + a| := by ring_nf
        _ ≤ |s n - a| + |a| := abs_add (s n - a) a
        _ < 1 + |a| := by
          apply add_lt_add_right (h n hn)
        _ = |a| + 1 := by ring

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  calc
    |s n * t n - 0| = |s n * t n| := by ring_nf
                  _ = |s n| * |t n| := abs_mul (s n) (t n)
                  _ < B * (ε / B) := by
                    apply mul_lt_mul''
                    · apply h₀ n (le_of_max_le_left hn)
                    · rw [← sub_zero (t n)]
                      apply h₁ n (le_of_max_le_right hn)
                    · apply abs_nonneg
                    · apply abs_nonneg
                  _ = ε := by
                    rw [mul_div_cancel₀]
                    linarith

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

-- Serious stuff
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    · intro h₁
      apply abne
      apply eq_of_abs_sub_eq_zero h₁.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb N (le_max_right Na Nb)
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |-(s N - a) + (s N - b)| := by congr; linarith
            _ ≤ |-(s N - a)| + |s N - b| := abs_add _ _
            _ = |s N - a| + |s N - b| := by rw [abs_neg]
            _ < ε + ε := add_lt_add absa absb
            _ = |a - b| := by ring
  exact lt_irrefl _ this
