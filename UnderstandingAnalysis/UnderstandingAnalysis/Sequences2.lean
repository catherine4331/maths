import Mathlib.Tactic
import Mathlib.Util.Delaborators

namespace Function

@[simp]
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε

@[simp]
def Convergent (s : ℕ → ℝ) :=
  ∃ a : ℝ, s.ConvergesTo a

@[simp]
def Divergent (s : ℕ → ℝ) :=
  ¬s.Convergent

@[simp]
def Bounded (s : ℕ → ℝ) :=
  ∃ M > 0, ∀ n : ℕ, |s n| ≤ M

end Function

theorem convergent_sequence_bounded {s : ℕ → ℝ} (h_sb : s.Convergent) : s.Bounded := by
  obtain ⟨l, hl⟩ := h_sb
  -- Get N such that all terms beyond it are within 1 of l
  obtain ⟨N, hN⟩ := hl 1 zero_lt_one
  -- For n ≥ N, terms are bounded by |l| + 1
  have h_tail : ∀ n ≥ N, |s n| < |l| + 1 := by
    intro n hn
    have := hN n hn
    calc
      |s n| = |(s n - l) + l| := by ring_nf
          _ ≤ |s n - l| + |l| := abs_add (s n - l) l
          _ < 1 + |l| := by linarith [this]
          _ = |l| + 1 := by ring

  -- There are only a finite number of other terms, so they have a finite max
  by_cases h : N = 0
  · use |l| + 1
    constructor
    · exact add_pos_of_nonneg_of_pos (abs_nonneg l) zero_lt_one
    · intro n
      exact h_tail n (by linarith)
  -- This is the meat of things
  · let t := Finset.image (fun n => |s n|) (Finset.range N)
    have t_nonempty : t.Nonempty := by
      have : 0 ∈ Finset.range N := by
        rw [Finset.mem_range]
        exact Nat.zero_lt_of_ne_zero h
      exact ⟨|s 0|, Finset.mem_image_of_mem (fun n => |s n|) this⟩
    let M₀ := t.max' t_nonempty
    let M := max (M₀ + 1) (|l| + 1)
    use M
    constructor
    · have : |l| + 1 > 0 := by
        exact add_pos_of_nonneg_of_pos (abs_nonneg l) zero_lt_one
      exact lt_of_lt_of_le this (le_max_right (M₀ + 1) (|l| + 1))
    · -- Show M bounds all terms
      intro n
      by_cases hn : n < N
      · -- For n < N, use M₀ bound
        have : |s n| ∈ t := by
          exact Finset.mem_image_of_mem (fun n => |s n|) (Finset.mem_range.2 hn)
        have : |s n| ≤ M₀ := by
          exact t.le_max' (|s n|) this
        --unfold M
        rw [lt_max_iff]
        exact Or.inl (by linarith)
      · -- For n ≥ N, use |l| + 1 bound
        have := h_tail n (not_lt.mp hn)
        exact lt_of_lt_of_le this (le_max_right (M₀ + 1) (|l| + 1))

theorem algebraic_limit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : s.ConvergesTo a) :
    (fun n ↦ c * s n).ConvergesTo (c * a) := by
  by_cases h : c = 0
  · intro ε ε_pos
    use 0; simp [h, ε_pos]
  · push_neg at h
    have c_pos : 0 < |c| := abs_pos.mpr h
    rintro ε ε_pos
    -- As usual, the trick is picking the right number at this stage
    -- Here we use ε / |c|
    have pos : ε / |c| > 0 := div_pos ε_pos c_pos
    obtain ⟨N, hN⟩ := cs (ε / |c|) pos
    use N
    intro n hn
    calc
      |c * s n - c * a| = |c * (s n - a)| := by rw [← mul_sub_left_distrib]
                      _ = |c| * |s n - a| := abs_mul c (s n - a)
                      _ = |s n - a| * |c| := by ring
                      _ < ε / |c| * |c| := mul_lt_mul (hN n hn) (le_refl |c|) c_pos (le_of_lt pos)
                      _ = ε := by rw [mul_comm, (mul_div_cancel₀ ε (abs_ne_zero.mpr h))]

theorem algebraic_limit_sum {sa sb : ℕ → ℝ} {a b : ℝ} (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) :
    (fun n ↦ sa n + sb n).ConvergesTo (a + b) := by
  · intro ε ε_pos
    have ε2_pos : ε / 2 > 0 := by linarith
    -- Here we use ε / 2 as our ε for sa & sb. This is because we're adding them together
    obtain ⟨Na, hNa⟩ := csa (ε / 2) ε2_pos
    obtain ⟨Nb, hNb⟩ := csb (ε / 2) ε2_pos
    use max Na Nb
    intro n hn
    calc
      |sa n + sb n - (a + b)| = |(sa n - a) + (sb n - b)| := by ring_nf
                            _ ≤ |sa n - a| + |sb n - b| := abs_add (sa n - a) (sb n - b)
                            _ < ε / 2 + ε / 2 := add_lt_add (hNa n (le_of_max_le_left hn)) (hNb n (le_of_max_le_right hn))
                            _ = ε := by ring

-- Removing a > 0 is a exercise, we'll get to that
theorem algebraic_limit_mul {sa sb : ℕ → ℝ} {a b : ℝ} (a_pos : a > 0) (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) :
    (fun n ↦ sa n * sb n).ConvergesTo (a * b) := by
  intro ε ε_pos
  -- Firstly, since sb is bounded, it has a max value. We'll need this
  have b_conv : sb.Convergent := by use b
  obtain ⟨M, ⟨M_pos, hM⟩⟩ := convergent_sequence_bounded b_conv
  have εa_pos : 1 / M * (ε / 2) > 0 := mul_pos (one_div_pos.mpr M_pos) (by linarith)
  -- Let's get the other ε we'll use
  have εb_pos : 1 / |a| * (ε / 2) > 0 := mul_pos (one_div_pos.mpr (abs_pos_of_pos a_pos)) (by linarith)
  obtain ⟨Na, hNa⟩ := csa (1 / M * (ε / 2)) εa_pos
  obtain ⟨Nb, hNb⟩ := csb (1 / |a| * (ε / 2)) εb_pos
  use max Na Nb
  intro n hn
  have t := hM n
  calc
    |sa n * sb n - (a * b)| = |(sa n * sb n - a * sb n) + (a * sb n - a * b)| := by ring_nf
                          _ ≤ |sa n * sb n - a * sb n| + |a * sb n - a * b| := abs_add (sa n * sb n - a * sb n) (a * sb n - a * b)
                          _ = |sb n| * |sa n - a| + |a| * |sb n - b| := by rw [← mul_sub_right_distrib, ← mul_sub_left_distrib, abs_mul, mul_comm, abs_mul]
                          _ ≤ M * |sa n - a| + |a| * |sb n - b| := by apply add_le_add_right; apply mul_le_mul_of_nonneg_right t (abs_nonneg (sa n - a))
                          _ < M * (1 / M * (ε / 2)) + |a| * (1 / |a| * (ε / 2)) := by
                            apply add_lt_add
                            apply (mul_lt_mul_left M_pos).mpr
                            apply (hNa n (le_of_max_le_left hn))
                            apply (mul_lt_mul_left (abs_pos_of_pos a_pos)).mpr
                            apply (hNb n (le_of_max_le_right hn))
                          _ = ε := by sorry

lemma algebraic_limit_inv {sa : ℕ → ℝ} {a : ℝ} (a_ne_zero : a ≠ 0) (csa : sa.ConvergesTo a) :
    (fun n ↦ 1 / sa n).ConvergesTo (1 / a) := by
  intro ε ε_pos
  have ε₁_pos : |a| / 2 > 0 := by linarith [abs_pos.mpr a_ne_zero]
  have ε₂_pos : (ε * |a|^2) / 2 > 0 := by linarith [sq_pos_of_pos (abs_pos.mpr a_ne_zero)]

theorem algebraic_limit_div {sa sb : ℕ → ℝ} {a b : ℝ} (a_pos : a > 0) (b_ne_zero : b ≠ 0) (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) :
    (fun n ↦ sa n / sb n).ConvergesTo (a / b) := by
  have : (fun n ↦ 1 / sb n).ConvergesTo (1 / b) := algebraic_limit_inv b_ne_zero csb
  apply algebraic_limit_mul a_pos csa
  have inv_b : 1 / b = b⁻¹ := by ring
  have inv_sb :  (fun n => 1 / sb n) = (fun n => (sb n)⁻¹) := by ring_nf
  rw [← inv_b, ← inv_sb]
  exact this
