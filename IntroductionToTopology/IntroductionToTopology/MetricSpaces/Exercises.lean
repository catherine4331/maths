import Mathlib.Tactic
import Mathlib.Util.Delaborators
import IntroductionToTopology.Metric

-- Exercise 2.1
example {M : Type*} [Metric M] (k : ℝ) (k_pos : k > 0) : Metric α := by
