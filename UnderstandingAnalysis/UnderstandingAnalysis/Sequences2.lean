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
  ∃ M > 0, ∀ n : ℕ, |s n| < M

end Function

theorem convergent_sequence_bounded (s : ℕ → ℝ) (h_sb : s.Convergent) : s.Bounded := by
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
