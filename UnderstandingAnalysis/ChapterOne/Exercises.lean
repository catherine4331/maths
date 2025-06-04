import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import UnderstandingAnalysis.Reals

open Set Finset

-- 1.2.6
lemma aux (a b : ℝ) : (a + b)^2 ≤ (|a| + |b|)^2 := by
  have : a*b ≤ |a * b| := le_abs_self (a * b)
  calc
    (a + b)^2 = a^2 + b^2 + 2*a*b := by ring
            _ ≤ a^2 + b^2 + 2*|a*b| := by linarith [this]
            _ = a^2 + b^2 + 2*|a| * |b| := by rw [abs_mul]; ring
            _ = (|a| + |b|)^2 := by
              ring_nf
              rw [sq_abs, sq_abs]
              ring

theorem triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have : |a + b|^2 ≤ (|a| + |b|)^2 := by
    calc
      |a + b|^2 = (a + b)^2 := by apply sq_abs (a + b)
              _ ≤ (|a| + |b|)^2 := by apply aux
  rw [sq_le_sq₀] at this
  apply this
  apply abs_nonneg
  apply add_nonneg (abs_nonneg a) (abs_nonneg b)

example (a b c d : ℝ) : |a - b| ≤ |a - c| + |c - d| + |d - b| := by calc
  |a - b| = |(a - c) + (c - b)| := by ring_nf
        _ ≤ |a - c| + |c - b| := triangle (a - c) (c - b)
        _ = |a - c| + |(c - d) + (d - b)| := by ring_nf
        _ ≤ |a - c| + |c - d| + |d - b| := by
          rw [add_assoc, add_le_add_iff_left]
          apply triangle

theorem reverse_triangle (a b : ℝ) : |(|a| - |b|)| ≤ |a - b| := by
  have : |a| ≤ |a - b| + |b| := by calc
    |a| = |a - b + b| := by ring_nf
      _ ≤ |a - b| + |b| := triangle (a - b) b
  have pos : |a| - |b| ≤ |a - b| := by linarith
  have : |b| ≤ |a - b| + |a| := by calc
    |b| = |b - a + a| := by ring_nf
      _ ≤ |b - a| + |a| := triangle (b - a) a
      _ = |a - b| + |a| := by rw [abs_sub_comm]
  have neg : -|a - b| ≤ |a| - |b| := by linarith
  rw [abs_le]
  exact And.intro neg pos

-- 1.2.7
example (A B : Set ℝ) (g : ℝ → ℝ) : g '' (A ∩ B) ⊆ g '' A ∩ g '' B := by
  rintro y ⟨x, ⟨inter, rfl⟩⟩
  constructor
  · use x, inter.left
  · use x, inter.right

example (A B : Set ℝ) (g : ℝ → ℝ) : g '' A ∪ g '' B = g '' (A ∪ B) := by
  ext y
  constructor
  · rintro (⟨x, ⟨x_in, rfl⟩⟩ | ⟨x, ⟨x_in, rfl⟩⟩)
    · use x
      apply And.intro (Or.inl x_in) (by rfl)
    · use x
      apply And.intro (Or.inr x_in) (by rfl)
  · rintro ⟨x, ⟨(x_in| x_in), rfl⟩⟩
    · apply Or.inl (by use x)
    · apply Or.inr (by use x)

-- 1.2.9
example (A B : Set ℝ) (g : ℝ → ℝ) : g ⁻¹' (A ∩ B) = g ⁻¹' A ∩ g ⁻¹' B := by
  ext x
  constructor
  · rintro ⟨x_A, x_B⟩
    exact And.intro x_A x_B
  · rintro ⟨x_A, x_B⟩
    exact And.intro x_A x_B

example (A B : Set ℝ) (g : ℝ → ℝ) : g ⁻¹' (A ∪ B) = g ⁻¹' A ∪ g ⁻¹' B := by
  ext x
  constructor
  · rintro (ga | gb)
    · apply Or.inl ga
    · apply Or.inr gb
  · rintro (ga | gb)
    · apply Or.inl ga
    · apply Or.inr gb

example (A : ℕ → Set α) (n : ℕ) :
    (⋃ i ∈ Finset.range (n + 1), A i)ᶜ = ⋂ i ∈ Finset.range (n + 1), (A i)ᶜ := by
  induction' n with n ih
  · simp
  · simp

-- 1.3.3
example (A : Set ℝ) (hne : A.Nonempty) (hb : A.BoundedBelow) :
    let B := {b : ℝ | LowerBound A b}
    ∃ s i, Supremum B s ∧ Infimum A i ∧ s = i := by
  intro B
  have B_nonempty : B.Nonempty := by
    rcases hb with ⟨l, hl⟩
    use l, hl
  have b_bu : B.BoundedAbove := by
    rcases hne with ⟨a, ha⟩
    use a
    rintro b hb
    exact hb a ha
  have ⟨s, hs⟩ := aoc B_nonempty b_bu
  use s, s
  constructor
  · exact hs
  · constructor
    -- Show that s is the infimum of A
    · constructor
      -- Show that s is a lower bound for A
      · rintro a ha
        have : UpperBound B a := by
          rintro b hb
          exact hb a ha
        exact hs.right a this
      -- s is the greatest lower bound
      · rintro l hl
        apply hs.left l hl
    -- s = s
    · rfl

-- 1.3.5
def mul_set (c : ℝ) (A : Set ℝ) : Set ℝ := {x | ∃ a ∈ A, x = c * a}

lemma onethreefive {A : Set ℝ} (c : ℝ) (h : A.Supremum s) (c_pos : 0 < c) :
    Supremum (mul_set c A) (c * s) := by
  constructor
  -- Show c * s is an upper bound
  · rintro ca ⟨a, ⟨a_in, rfl⟩⟩
    rw [mul_le_mul_left c_pos]
    apply h.left a a_in
  -- Show c * s is the greatest upper bound
  · rintro b b_ub
    have h_upper : UpperBound A (b / c) := by
      rintro a ha
      have h_in_mul : c * a ∈ mul_set c A := ⟨a, ha, rfl⟩
      have : c * a ≤ b := b_ub (c * a) h_in_mul
      rw [le_div_iff₀' c_pos]
      exact this
    have : s ≤ b / c := h.right (b / c) h_upper
    rw [← le_div_iff₀' c_pos]
    exact this

theorem onethreefivefull {A : Set ℝ} (c : ℝ) (h : A.Supremum s) (h_ane : A.Nonempty) (c_nonneg : 0 ≤ c) :
    Supremum (mul_set c A) (c * s) := by
  rcases eq_or_lt_of_le c_nonneg with (c_zero | c_pos)
  -- Case: c = 0
  · constructor
    -- Show c * s is an upper bound
    · rintro ca ⟨a, ⟨a_in, rfl⟩⟩
      rw [← c_zero]
      linarith
    -- Show c * s is the least upper bound
    · rintro b h
      have : c * s ∈ mul_set c A := by
        rw [← c_zero]
        rcases h_ane with ⟨a, ha⟩
        use a, ha
        simp
      apply h
      apply this
  -- Case: 0 < c
  exact onethreefive c h c_pos

example (A : Set ℝ) (c : ℝ) (h : A.Supremum s) (c_neg : c < 0) :
    Infimum (mul_set c A) (c * s) := by
  constructor
  -- Show c * s is a lower bound
  · rintro ca ⟨a, ⟨a_in, rfl⟩⟩
    rw [mul_le_mul_left_of_neg c_neg]
    apply h.left a a_in
  -- Show c * s is the greatest lower bound
  · rintro b b_lb
    have h_upper : UpperBound A (b / c) := by
      rintro a ha
      have h_in_mul : c * a ∈ mul_set c A := ⟨a, ha, rfl⟩
      have : b ≤ c * a := b_lb (c * a) h_in_mul
      rw [le_div_iff_of_neg c_neg]
      linarith
    have : s ≤ b / c := h.right (b / c) h_upper
    rw [← le_div_iff_of_neg' c_neg]
    exact this

def add_sets (A B : Set ℝ) : Set ℝ := {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}

-- 1.3.6
lemma onethreesixa {A B : Set ℝ} {s t : ℝ} (sa : A.Supremum s) (sb : B.Supremum t) : (add_sets A B).UpperBound (s + t) := by
  rintro ab ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩
  exact add_le_add (sa.left a ha) (sb.left b hb)

lemma onethreesixb {A B : Set ℝ} {t u a : ℝ} (sb : B.Supremum t) (ab_ub : (add_sets A B).UpperBound u) (ha : a ∈ A) : t ≤ u - a := by
  have : B.UpperBound (u - a) := by
    rintro b hb
    have h_in_sum : a + b ∈ add_sets A B := ⟨a, ha, b, hb, rfl⟩
    have : a + b ≤ u := ab_ub (a + b) h_in_sum
    linarith
  exact sb.right (u - a) this

lemma onethreesix (A B : Set ℝ) (sa : A.Supremum s) (sb : B.Supremum t) : (add_sets A B).Supremum (s + t) := by
  constructor
  -- Show s + t is an upper bound for A + B
  · exact onethreesixa sa sb
  -- Show that s + t is the least upper bound for A + B
  rintro u u_ub
  have : A.UpperBound (u - t) := by
    rintro a ha
    have : t ≤ u - a := onethreesixb sb u_ub ha
    linarith
  have : s ≤ (u - t) := sa.right (u - t) this
  linarith
