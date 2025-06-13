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

axiom aoc {A : Set ℝ} : A.Nonempty ∧ A.BoundedAbove ↔ ∃ s : ℝ, A.Supremum s

lemma sup_analytic {A : Set ℝ} {s : ℝ} (h : A.UpperBound s) :
    A.Supremum s ↔ ∀ ε > 0, ∃ a ∈ A, s - ε < a := by
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
      have b_lt_s : b < s := lt_of_not_ge h_not_le
      obtain ⟨a, ha_mem, ha_gt⟩ := hanalytic (s - b) (by linarith)
      have : b < a := by linarith
      apply lt_irrefl b (this.trans_le (b_ub a ha_mem))

lemma inf_analytic {A : Set ℝ} (h : A.LowerBound i) :
    A.Infimum i ↔ ∀ ε > 0, ∃ a ∈ A, a < i + ε := by
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

theorem nested_interval_principle
    (a b : ℕ → ℝ)
    (h_nested : ∀ n, a (n + 1) ≥ a n ∧ b (n + 1) ≤ b n)
    (h_order : ∀ n, a n ≤ b n)
    (h_cross:  ∀ n m, a n ≤ b m) :
    ∃ c, ∀ n, a n ≤ c ∧ c ≤ b n := by
  let A : Set ℝ := {x | ∃ n : ℕ, x = a n}
  have a_ne : A.Nonempty := ⟨a 0, 0, rfl⟩
  have a_bu : A.BoundedAbove := by
    use b 0
    rintro x ⟨n, rfl⟩
    induction' n with n ih
    · exact h_order 0
    · calc a (n + 1)
        ≤ b (n + 1) := h_order (n + 1)
        _ ≤ b n := (h_nested n).2
        _ ≤ b 0 := by
          clear ih
          induction' n with k jh
          · rfl
          · exact le_trans (h_nested k).2 jh
  have ⟨s, hs⟩ := aoc.mp ⟨a_ne, a_bu⟩
  use s
  intro n
  constructor
  · exact hs.left (a n) ⟨n, rfl⟩
  · have b_ub : A.UpperBound (b n) := by
      intro a_val ⟨k, ak⟩
      rw [ak]
      exact h_cross k n
    exact hs.right (b n) b_ub

theorem archimedian {x : ℝ} : ∃ n : ℕ, n > x := by
  by_contra h
  push_neg at h
  let A : Set ℝ := {n : ℝ | ∃ k : ℕ, n = k}
  have ne : A.Nonempty := by use 0, 0; simp
  have bu : A.BoundedAbove := by
    use x
    intro y ⟨k, ak⟩
    rw [ak]
    exact h k
  obtain ⟨s, hs⟩ := aoc.mp ⟨ne, bu⟩
  have s_ub := hs.left
  rw [sup_analytic hs.left] at hs
  obtain ⟨n, hn⟩ := hs 1 (by norm_num)
  have contra : s < n + 1 := by linarith
  have : n + 1 ∈ A := by
    obtain ⟨⟨k_nat, ak⟩, _⟩ := hn
    use k_nat + 1
    rw [ak]
    norm_num
  have : n + 1 ≤ s := by
    apply s_ub (n + 1) this
  linarith

theorem archimedian_corollary (y : ℝ) (y_pos : y > 0) : ∃ n : ℕ,  1 / n < y := by
  obtain ⟨n, hn⟩ := archimedian (x := 1 / y)
  use n
  refine (one_div_lt y_pos ?_).mp hn
  linarith [one_div_pos.mpr y_pos]

theorem q_dense_r (a b : ℝ) : ∃ r : ℚ, a < r ∧ r < b := by
  sorry
