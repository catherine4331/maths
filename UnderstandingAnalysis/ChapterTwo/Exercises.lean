import Mathlib.Tactic
import Mathlib.Util.Delaborators
import UnderstandingAnalysis

def alternating_sequence (x y : ℕ → ℝ) : ℕ → ℝ :=
  fun n => if n % 2 = 0 then x (n / 2) else y (n / 2)

-- 2.3.5
example {sx sy : ℕ → ℝ} {l: ℝ} (csx : sx.ConvergesTo l) (csy : sy.ConvergesTo l) :
    (alternating_sequence sx sy).ConvergesTo l := by
  intro ε ε_pos
  obtain ⟨Nx, hNx⟩ := csx ε ε_pos
  obtain ⟨Ny, hNy⟩ := csy ε ε_pos
  use (max Nx Ny) * 2
  intro n hn
  -- Given our sequence alternates, we need to consider two cases: The term is from x, or the term is from y
  by_cases h : n % 2 = 0
  · simp [alternating_sequence, h]
    have : n / 2 ≥ Nx := by
      calc
        n / 2 ≥ ((max Nx Ny) * 2) / 2 := by exact Nat.div_le_div_right hn
            _ = max Nx Ny := Nat.mul_div_left (max Nx Ny) two_pos
            _ ≥ Nx := le_max_left Nx Ny
    apply hNx (n / 2) this
  · simp [alternating_sequence, h]
    have : n / 2 ≥ Ny := by
      calc
        n / 2 ≥ ((max Nx Ny) * 2) / 2 := by exact Nat.div_le_div_right hn
            _ = max Nx Ny := Nat.mul_div_left (max Nx Ny) two_pos
            _ ≥ Ny := le_max_right Nx Ny
    apply hNy (n / 2) this

section

variable {sa sb: ℕ → ℝ} {a b: ℝ}

-- 2.3.10
example (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) (a_sub_b_conv : (fun n ↦ sa n - sb n).ConvergesTo 0) : a = b := by
  have : (fun n ↦ sa n - sb n).ConvergesTo (a - b) := algebraic_limit_sum csa (algebraic_limit_neg csb)
  have : (a - b) = 0 := limits_unique this a_sub_b_conv
  rw [sub_eq_zero] at this
  exact this

example (csa : sa.ConvergesTo a) : (fun n ↦ |sa n|).ConvergesTo |a| := by
  intro ε ε_pos
  obtain ⟨N, hN⟩ := csa ε ε_pos
  use N
  intro n hn
  simp
  calc
    |(|sa n| - |a|)| ≤ |sa n - a| := by exact  abs_abs_sub_abs_le (sa n) a
                   _ < ε := hN n hn

example (csa : sa.ConvergesTo a) (b_sub_a_conv : (fun n ↦ sb n - sa n).ConvergesTo 0) : sb.ConvergesTo a := by
  intro ε ε_pos
  obtain ⟨Na, hNa⟩ := csa (ε / 2) (by linarith)
  obtain ⟨Nba, hNba⟩ := b_sub_a_conv (ε / 2) (by linarith)
  simp at hNba
  use max Na Nba
  intro n hn
  calc
    |sb n - a| = |(sb n - sa n) + (sa n - a)| := by ring_nf
             _ ≤ |sb n - sa n| + |sa n - a| := abs_add (sb n - sa n) (sa n - a)
             _ < ε / 2 + ε / 2 := add_lt_add (hNba n (le_of_max_le_right hn)) (hNa n (le_of_max_le_left hn))
             _ = ε := by ring_nf

example (csa : sa.ConvergesTo 0) (h_sb : ∀ n, |sb n - b| ≤ sa n) : sb.ConvergesTo b := by
  intro ε ε_pos
  obtain ⟨N, hN⟩ := csa ε ε_pos
  simp at hN
  use N
  intro n hn
  obtain ⟨sal, sar⟩ := abs_lt.mp (hN n hn)
  obtain ⟨bl, br⟩ := abs_le.mp (h_sb n)
  apply abs_lt.mpr
  constructor
  · apply neg_lt_neg at sar
    apply lt_of_lt_of_le sar bl
  · exact lt_of_le_of_lt br sar

-- 2.3.11
example {B : Set ℝ} (csa : sa.ConvergesTo a) (aub : ∀ n, B.UpperBound (sa n)) : B.UpperBound a := by
  simp
  by_contra! h_contra
  obtain ⟨b, ⟨hb, a_le_b⟩⟩ := h_contra
  obtain ⟨N, hN⟩ := csa (b - a) (by linarith)
  have hub : b ≤ sa N := aub N b hb
  have := hN N (by linarith)
  obtain ⟨_, l⟩ := abs_lt.mp this
  rw [sub_lt_sub_iff_right] at l
  apply lt_irrefl b (lt_of_le_of_lt hub l)
end

-- 2.4.4
example {x : ℝ} (x_pos : x > 0) : ∃ n : ℕ, n > x := by
  by_contra! h_contra
  -- We will consider the sequence of the natural numbers
  let sa : ℕ → ℝ := fun n ↦ n
  have bsa : sa.Bounded := by
    use x, x_pos
    intro n
    unfold sa
    rw [abs_le]
    constructor
    · exact le_trans (by linarith) (Nat.cast_nonneg' n)
    · apply h_contra n
  have isa : sa.Increasing₁ := by
    intro n
    unfold sa
    rw [Nat.cast_add]
    linarith
  obtain ⟨a, ha⟩ := monotone_convergence_increasing isa bsa
  obtain ⟨N, hN⟩ := ha (1 / 2) (by linarith)
  -- Now, we will obtain our contradiction by using subsequent terms from our sequence
  have := hN N (by rfl)
  obtain ⟨r, _⟩ := abs_lt.mp this
  have r : a - (1 / 2) < N := by linarith
  have := hN (N + 1) (by linarith)
  obtain ⟨_, l⟩ := abs_lt.mp this
  have l : (N : ℝ) < a - (1 / 2) := by
    have : sa (N + 1) = (sa N) + 1 := by
      unfold sa
      rw [@Nat.cast_add]
      rw [@Nat.cast_one]
    linarith
  apply lt_irrefl (N : ℝ) (lt_trans l r)
