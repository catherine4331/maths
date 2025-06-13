import Mathlib.Tactic
import Mathlib.Util.Delaborators

namespace Function

@[simp]
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

def Converges (s : ℕ → ℝ) :=
  ∃ a : ℝ, s.ConvergesTo a

def Diverges (s : ℕ → ℝ) :=
  ¬s.Converges

@[simp]
def εNeighbourhood (a ε : ℝ) :=
  {x | |x - a| < ε}

@[simp]
def ConvergesToTopological (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, s n ∈ εNeighbourhood a ε

end Function

theorem converges_equivalent {s : ℕ → ℝ} {a : ℝ} : s.ConvergesTo a ↔ s.ConvergesToTopological a := by
  constructor
  · rintro h ε ε_pos
    obtain ⟨N, hN⟩ := h ε ε_pos
    use N
    intro n hn
    simp [(hN n hn)]
  · rintro h ε ε_pos
    obtain ⟨N, hN⟩ := h ε ε_pos
    use N
    intro n hn
    have : s n ∈ {x | |x - a| < ε} := hN n hn
    rw [Set.mem_setOf] at this
    exact this

theorem limits_unique {s : ℕ → ℝ} {a b : ℝ} (sa : s.ConvergesTo a) (sb : s.ConvergesTo b) : a = b := by
  by_contra h_contra
  push_neg at h_contra
  have : |a - b| > 0 := abs_sub_pos.mpr h_contra
  let ε := |a - b| / 2
  have ε_pos : ε > 0 := by unfold ε; linarith
  obtain ⟨Na, hNa⟩ := sa ε ε_pos
  obtain ⟨Nb, hNb⟩ := sb ε ε_pos
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb N (le_max_right Na Nb)
  have : |a - b| < |a - b| := by calc
    |a - b| = |-(s N - a) + (s N - b)| := by congr; linarith
          _ ≤ |-(s N - a)| + |s N - b| := abs_add_le (-(s N - a)) (s N - b)
          _ = |s N - a| + |s N - b| := by rw [@abs_neg]
          _ < ε + ε := add_lt_add absa absb
          _ = |a - b| := by unfold ε; ring
  apply lt_irrefl at this
  exact this
