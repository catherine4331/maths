import Mathlib.Tactic
import Mathlib.Util.Delaborators

namespace Set

def BoundedAbove (A : Set ℝ) : Prop :=
  ∃ b : ℝ, ∀ a ∈ A, a ≤ b

def BoundedBelow (A : Set ℝ) : Prop :=
  ∃ l : ℝ, ∀ a ∈ A, l ≤ a

@[simp]
def UpperBound (A : Set ℝ) (u : ℝ) : Prop :=
  ∀ a ∈ A, a ≤ u

@[simp]
def LowerBound (A : Set ℝ) (l : ℝ) : Prop :=
  ∀ a ∈ A, l ≤ a

@[simp]
def Supremum (A : Set ℝ) (s : ℝ) : Prop :=
  UpperBound A s ∧ ∀ b : ℝ, UpperBound A b → s ≤ b

@[simp]
def Infimum (A : Set ℝ) (i : ℝ) : Prop :=
  LowerBound A i ∧ ∀ l : ℝ, LowerBound A l → l ≤ i

@[simp]
def Maximum (A : Set ℝ) (a₀ : A) : Prop :=
  ∀ a ∈ A, a₀ ≥ a

@[simp]
def Minimum (A : Set ℝ) (a₁ : A) : Prop :=
  ∀ a ∈ A, a₁ ≤ a

end Set

axiom aoc {A : Set ℝ} (hne : A.Nonempty) (hb : A.BoundedAbove) : ∃ s : ℝ, A.Supremum s

lemma sup_analytic {A : Set ℝ} (h : A.UpperBound s) :
    A.Supremum s ↔ ∀ ε > 0, ∃ a : A, s - ε < a := by
  simp
  constructor
  · rintro h ε ε_pos
    have sε : s - ε < s := by linarith
    have := mt (h.right (s - ε))
    push_neg at this
    rcases this sε with ⟨a, ha⟩
    use a
  · rintro hanalytic
    constructor
    · exact h
    · rintro b b_ub
      by_contra h_not_le
      have b_lt_s : b < s := lt_of_not_le h_not_le
      obtain ⟨a, ha_mem, ha_gt⟩ := hanalytic (s - b) (by linarith)
      have : b < a := by linarith
      apply lt_irrefl b (this.trans_le (b_ub a ha_mem))

lemma inf_analytic {A : Set ℝ} (h : A.LowerBound i) :
    A.Infimum i ↔ ∀ ε > 0, ∃ a : A, a < i + ε := by
  simp
  constructor
  · rintro h ε ε_pos
    have iε : i < i + ε := by linarith
    have := mt (h.right (i + ε))
    push_neg at this
    rcases this iε with ⟨a, ha⟩
    use a
  · rintro hanalytic
    constructor
    · exact h
    · rintro l l_lb
      by_contra h_not_le
      have i_lt_l : i < l := lt_of_not_ge h_not_le
      obtain ⟨a, ha_mem, ha_lt⟩ := hanalytic (l - i) (by linarith)
      have : a < l := by linarith
      apply lt_irrefl l (lt_of_le_of_lt (l_lb a ha_mem) this)
