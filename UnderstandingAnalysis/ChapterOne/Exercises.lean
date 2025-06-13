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
  have ⟨s, hs⟩ := aoc.mp ⟨B_nonempty, b_bu⟩
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

lemma onethreesix {A B : Set ℝ} (sa : A.Supremum s) (sb : B.Supremum t) : (add_sets A B).Supremum (s + t) := by
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

example {A B : Set ℝ} (s t : ℝ) (sa : A.Supremum s) (sb : B.Supremum t) : (add_sets A B).Supremum (s + t) := by
  rw [sup_analytic (onethreesixa sa sb)]
  rw [sup_analytic sa.left] at sa
  rw [sup_analytic sb.left] at sb
  rintro ε ε_pos
  have ε2pos : 0 < ε / 2 := by linarith
  rcases sa (ε / 2) ε2pos with ⟨a, ⟨ha, a_ieq⟩⟩
  rcases sb (ε / 2) ε2pos with ⟨b, ⟨hb, b_ieq⟩⟩
  have h_in_sum : a + b ∈ add_sets A B := ⟨a, ha, b, hb, rfl⟩
  use (a + b), h_in_sum
  linarith

-- 1.3.7
example {A : Set ℝ} {a : ℝ} (ha : a ∈ A) (h_ub : A.UpperBound a) : A.Supremum a := by
  constructor
  -- Show ab is an upper bound
  · exact h_ub
  -- Show ab is the least upper bound
  · intro b b_ub
    exact b_ub a ha

-- 1.3.9
example {A B : Set ℝ} (s t : ℝ) (sa : A.Supremum s) (sb : B.Supremum t) (a_le_b : s < t) : ∃ b ∈ B, A.UpperBound b := by
  rw [sup_analytic sb.left] at sb
  have ε_pos : t - s > 0 := by linarith
  rcases sb (t - s) ε_pos with ⟨b, ⟨hb, b_ieq⟩⟩
  simp at b_ieq
  use b, hb
  intro a ha
  trans s
  · exact sa.left a ha
  · linarith

-- 1.4.2
example {A : Set ℝ} {s : ℝ} (h_ub : ∀ n : ℕ, A.UpperBound (s + 1 / n))
    (h_nub : ∀ n : ℕ, ¬ A.UpperBound (s - 1 / n)) : A.Supremum s := by
  have : A.UpperBound s := by
    -- Contradiction implies there is some a such that s < a
    by_contra h_contra
    simp only [UpperBound] at h_contra
    push_neg at h_contra
    obtain ⟨a, ⟨ha, sa⟩⟩ := h_contra
    -- But this means we can find an n such that 1 / n < a - s
    have : a - s > 0 := by linarith
    obtain ⟨n, hn⟩ := archimedian_corollary (a - s) this
    have contra : s + 1 / n < a := by linarith
    -- However, since s + 1 / n is an upper bound, a ≤ s + 1 / n
    have := by exact h_ub n
    have := this a ha
    -- This implies s + 1 \ n < s + 1 \ n, which is our contradiction
    apply lt_irrefl (s + 1 / n) (lt_of_lt_of_le contra this)
  -- Now we've show s is an upper bound, we can use the analytic form of the supremem theorem
  rw [sup_analytic this]
  rintro ε hε
  obtain ⟨n, hn⟩ := archimedian_corollary ε hε
  have : ¬ A.UpperBound (s - 1 / n) := h_nub n
  simp only [UpperBound] at this
  push_neg at this
  -- Since s - 1 / n is not an upper bound, we can find an a such that s - 1 / n < a
  obtain ⟨a, ⟨ha, sa⟩⟩ := this
  use a, ha
  calc
    s - ε < s - 1 / n := by linarith
        _ < a := by exact sa

-- 1.4.3
example : ⋂ n : ℕ, Set.Ioo (0 : ℝ) (1/n) = ∅ := by
  ext x
  constructor
  · intro hx
    rw [mem_iInter] at hx
    have : x > 0 := by
      have := hx 1
      exact this.left
    -- Since x > 0 for all x, we can always find some 1 / n < x
    obtain ⟨n, hn⟩ := archimedian_corollary x this
    -- Which means that x is not in (0, 1/n)
    have : x ∉ Ioo (0 : ℝ) (1/n) := by
      exact notMem_Ioo_of_ge (le_of_lt hn)
    exact this (hx n)
  · intro h
    exfalso
    exact h

-- 1.4.4
-- The set we're working with is ℚ ∩ [a, b], this definition is equivalent
example (a b : ℝ) (a_le_b: a < b) : {x | ∃ q : ℚ, x = (q : ℝ) ∧ a ≤ x ∧ x ≤ b}.Supremum b := by
  -- Firstly show b is an upper bound
  have : {x | ∃ q : ℚ, x = (q : ℝ) ∧ a ≤ x ∧ x ≤ b}.UpperBound b := by
    rintro c ⟨_, hq, ⟨ha, hb⟩⟩
    exact hb
  -- Use the analytic form
  rw [sup_analytic this]
  · rintro ε ε_pos
    -- We need to find a rational between b - ε and b (but be careful if b - ε < a)
    have : max a (b - ε) < b := by
      rw [max_lt_iff]
      exact And.intro a_le_b (by linarith)
    obtain ⟨r, hra, hrb⟩ := q_dense_r (max a (b - ε)) b this
    rw [max_lt_iff] at hra
    use r
    constructor
    -- Firstly we need to show r is in our set
    · rw [mem_setOf]
      use r, rfl
      exact And.intro (le_of_lt hra.left) (le_of_lt hrb)
    -- And now to show it's greater than b - ε
    · exact hra.right

-- 1.4.5
example (a b : ℝ) (a_le_b : a < b) : ∃ t : ℝ, Irrational t ∧ a < t ∧ t < b := by
  -- We can get a rational number using the density of Q in R
  obtain ⟨r, hra, hrb⟩ := q_dense_r (a - √2) (b - √2) (by linarith)
  have left : a < r + √2 := by linarith
  have right : r + √2 < b := by linarith
  use r + √2
  constructor
  -- Show that r + √2 is irrational
  · simp
    exact irrational_sqrt_two
  exact And.intro left right
