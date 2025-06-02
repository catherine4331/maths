import Mathlib.Tactic
import Mathlib.Util.Delaborators

def BoundedAbove (A : Set ℝ) : Prop :=
  ∃ b : ℝ, ∀ a ∈ A, a ≤ b

def BoundedBelow (A : Set ℝ) : Prop :=
  ∃ l : ℝ, ∀ a ∈ A, l ≤ a

def UpperBound (A : Set ℝ) (s : ℝ) : Prop :=
  ∀ a ∈ A, a ≤ s

def LowerBound (A : Set ℝ) (i : ℝ) : Prop :=
  ∀ a ∈ A, i ≤ a

def Supremum (A : Set ℝ) (s : ℝ) : Prop :=
  UpperBound A s ∧ ∀ b : ℝ, UpperBound A b → s ≤ b

def Infimum (A : Set ℝ) (i : ℝ) : Prop :=
  LowerBound A i ∧ ∀ l : ℝ, LowerBound A l → l ≤ i

def Maximum (A : Set ℝ) (a₀ : A) : Prop :=
  ∀ a ∈ A, a₀ ≥ a

def Minimum (A : Set ℝ) (a₁ : A) : Prop :=
  ∀ a ∈ A, a₁ ≤ a

lemma sup_eps {A : Set ℝ} (h : UpperBound A s) :
    Supremum A s ↔ ∀ ε > 0, ∃ a : A, s - ε < a := by
  constructor
  ·
