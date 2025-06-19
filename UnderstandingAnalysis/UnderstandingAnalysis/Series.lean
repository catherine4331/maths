import Mathlib.Tactic
import Mathlib.Util.Delaborators
import UnderstandingAnalysis.Sequences

namespace Function

@[simp]
def PartialSum (s : ℕ → ℝ) (m : ℕ) :=
  (Finset.range m).sum s

-- If this sequence converges to some limit b, then the series whose terms are given by s is convergent, and equals b
@[simp]
def PartialSumSeq (s : ℕ → ℝ) :=
  fun n ↦ s.PartialSum n

end Function

section

variable {sb : ℕ → ℝ}

theorem cauchy_condensation (dsb : sb.Decreasing) (sb_pos : ∀ n, sb n ≥ 0) :
    sb.PartialSumSeq.Convergent ↔ (fun n ↦ 2^n * sb (2 * n)).Convergent := by
  constructor
  · sorry -- This direction is handled in 2.7.5
  · intro ht
    obtain ⟨M, ⟨M_pos, hM⟩⟩ := convergent_sequence_bounded ht
    -- If we can show sb.PartialSumSeq is monotone and bounded, then we can conclude it is convergent
    have isb : sb.PartialSumSeq.Increasing := by
      intro n₁ n₂ h₁_le_n₂
      simp
      have : Finset.range n₁ ⊆ Finset.range n₂ := by
        intro i hi
        simp at hi
        simp
        exact le_trans hi h₁_le_n₂
      -- The sum over a subset is ≤ the sum over the full set when all terms are non-negative
      exact Finset.sum_le_sum_of_subset_of_nonneg this (fun x _ => by simp [sb_pos x])
    have bsb : sb.PartialSumSeq.Bounded := by
      use M, M_pos
      intro m
      sorry
    exact monotone_convergence_increasing isb bsb

end
