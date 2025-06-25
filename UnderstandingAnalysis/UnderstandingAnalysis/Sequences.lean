import Mathlib.Tactic
import Mathlib.Util.Delaborators
import UnderstandingAnalysis.Reals

namespace Function

@[simp]
def Subsequence (s : ℕ → ℝ) (φ : ℕ → ℕ) (_ : StrictMono φ) :=
  s ∘ φ

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
  ∃ M > 0, ∀ n : ℕ, |s n| ≤ M

@[simp]
def εNeighbourhood (a ε : ℝ) :=
  {x | |x - a| < ε}

@[simp]
def ConvergesToTopological (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, s n ∈ εNeighbourhood a ε

@[simp]
def Increasing (s : ℕ → ℝ) :=
  ∀ n₁ n₂ : ℕ, n₁ ≤ n₂ → s n₁ ≤ s n₂

@[simp]
def Increasing₁ (s : ℕ → ℝ) :=
  ∀ n : ℕ, s n ≤ s (n + 1)

@[simp]
def Decreasing (s : ℕ → ℝ) :=
  ∀ n₁ n₂ : ℕ, n₁ ≤ n₂ → s n₁ ≥ s n₂

@[simp]
def Decreasing₁ (s : ℕ → ℝ) :=
  ∀ n : ℕ, s n ≥ s (n + 1)

@[simp]
def Monotone (s : ℕ → ℝ) :=
  s.Increasing₁ ∨ s.Decreasing₁

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

theorem convergent_sequence_bounded {s : ℕ → ℝ} (h_sb : s.Convergent) : s.Bounded := by
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
      exact le_of_lt (h_tail n (by linarith))
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
        apply le_of_lt
        rw [lt_max_iff]
        exact Or.inl (by linarith)
      · -- For n ≥ N, use |l| + 1 bound
        have := h_tail n (not_lt.mp hn)
        exact le_of_lt (lt_of_lt_of_le this (le_max_right (M₀ + 1) (|l| + 1)))

theorem const_convergent {c : ℝ} : (fun _ ↦ c).ConvergesTo c := by
  intro ε ε_pos
  use 0
  -- We let simp to the heavy lifting here. Our inequality will become |c - c| < ε in the middle step
  simp
  exact ε_pos

section

variable {sa sb sc : ℕ → ℝ} {a b c: ℝ}

theorem algebraic_limit_mul_const (c : ℝ) (cs : sa.ConvergesTo a) :
    (fun n ↦ c * sa n).ConvergesTo (c * a) := by
  by_cases h : c = 0
  · intro ε ε_pos
    use 0; simp [h, ε_pos]
  · push_neg at h
    have c_pos : 0 < |c| := abs_pos.mpr h
    rintro ε ε_pos
    -- As usual, the trick is picking the right number at this stage
    -- Here we use ε / |c|
    have pos : ε / |c| > 0 := div_pos ε_pos c_pos
    obtain ⟨N, hN⟩ := cs (ε / |c|) pos
    use N
    intro n hn
    calc
      |c * sa n - c * a| = |c * (sa n - a)| := by rw [← mul_sub_left_distrib]
                      _ = |c| * |sa n - a| := abs_mul c (sa n - a)
                      _ = |sa n - a| * |c| := by ring
                      _ < ε / |c| * |c| := mul_lt_mul (hN n hn) (le_refl |c|) c_pos (le_of_lt pos)
                      _ = ε := by rw [mul_comm, (mul_div_cancel₀ ε (abs_ne_zero.mpr h))]

lemma algebraic_limit_neg (csa : sa.ConvergesTo a) :
    (fun n ↦ -sa n).ConvergesTo (-a) := by
  intro ε ε_pos
  obtain ⟨N, hN⟩ := csa ε ε_pos
  use N
  intro n hn
  simp
  calc
    |-sa n + a| = |-(sa n - a)| := by ring_nf
              _ = |sa n - a| := abs_neg (sa n - a)
              _ < ε := hN n hn

theorem algebraic_limit_sum (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) :
    (fun n ↦ sa n + sb n).ConvergesTo (a + b) := by
  intro ε ε_pos
  have ε2_pos : ε / 2 > 0 := by linarith
  -- Here we use ε / 2 as our ε for sa & sb. This is because we're adding them together
  obtain ⟨Na, hNa⟩ := csa (ε / 2) ε2_pos
  obtain ⟨Nb, hNb⟩ := csb (ε / 2) ε2_pos
  use max Na Nb
  intro n hn
  calc
    |sa n + sb n - (a + b)| = |(sa n - a) + (sb n - b)| := by ring_nf
                          _ ≤ |sa n - a| + |sb n - b| := abs_add (sa n - a) (sb n - b)
                          _ < ε / 2 + ε / 2 := add_lt_add (hNa n (le_of_max_le_left hn)) (hNb n (le_of_max_le_right hn))
                          _ = ε := by ring

-- Needed to remove the a > 0 restriction in algebraic_limit_mul
--- 2.3.9
lemma bounded_mul_zero_conv (bsa : sa.Bounded) (csb : sb.ConvergesTo 0) :
    (fun n ↦ sa n * sb n).ConvergesTo 0 := by
  intro ε ε_pos
  -- First we need the bound of sa
  obtain ⟨M, ⟨M_pos, hM⟩⟩ := bsa
  -- The ε we want is ε / M
  have ε₀_pos : ε / M > 0 := div_pos ε_pos M_pos
  obtain ⟨N, hN⟩ := csb (ε / M) ε₀_pos
  use N
  intro n hn
  simp
  by_cases h₀ : sa n = 0
  · rw [h₀]; simp; exact ε_pos
  · push_neg at h₀
    calc
    |sa n * sb n| = |sa n| * |sb n| := by exact abs_mul (sa n) (sb n)
                _ = |sa n| * |sb n - 0| := by ring_nf
                _ < |sa n| * (ε / M) := (mul_lt_mul_left (abs_pos.mpr h₀)).mpr (hN n hn)
                _ ≤ M * (ε / M) := by apply mul_le_mul_of_nonneg_right (hM n) (le_of_lt ε₀_pos)
                _ = ε := by rw [mul_div_cancel₀ ε (ne_of_gt M_pos)]

lemma algebraic_limit_mul_a_zero (a_zero : a = 0) (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) :
    (fun n ↦ sa n * sb n).ConvergesTo (a * b) := by
  rw [a_zero, zero_mul]
  rw [a_zero] at csa
  have : (fun n ↦ sa n * sb n) = (fun n ↦ sb n * sa n) := by ext; rw [mul_comm]
  rw [this]
  have : sb.Convergent := by use b
  apply bounded_mul_zero_conv (convergent_sequence_bounded (by use b)) csa

theorem algebraic_limit_mul (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) :
    (fun n ↦ sa n * sb n).ConvergesTo (a * b) := by
  by_cases ha : a = 0
  · exact algebraic_limit_mul_a_zero ha csa csb
  · intro ε ε_pos
    -- Firstly, since sb is bounded, it has a max value. We'll need this
    have b_conv : sb.Convergent := by use b
    obtain ⟨M, ⟨M_pos, hM⟩⟩ := convergent_sequence_bounded b_conv
    have εa_pos : 1 / M * (ε / 2) > 0 := mul_pos (one_div_pos.mpr M_pos) (by linarith)
    -- Let's get the other ε we'll use
    have εb_pos : 1 / |a| * (ε / 2) > 0 := mul_pos (one_div_pos.mpr (abs_pos.mpr ha)) (by linarith)
    obtain ⟨Na, hNa⟩ := csa (1 / M * (ε / 2)) εa_pos
    obtain ⟨Nb, hNb⟩ := csb (1 / |a| * (ε / 2)) εb_pos
    use max Na Nb
    intro n hn
    have t := hM n
    calc
      |sa n * sb n - (a * b)| = |(sa n * sb n - a * sb n) + (a * sb n - a * b)| := by ring_nf
                            _ ≤ |sa n * sb n - a * sb n| + |a * sb n - a * b| := abs_add (sa n * sb n - a * sb n) (a * sb n - a * b)
                            _ = |sb n| * |sa n - a| + |a| * |sb n - b| := by rw [← mul_sub_right_distrib, ← mul_sub_left_distrib, abs_mul, mul_comm, abs_mul]
                            _ ≤ M * |sa n - a| + |a| * |sb n - b| := by apply add_le_add_right; apply mul_le_mul_of_nonneg_right t (abs_nonneg (sa n - a))
                            _ < M * (1 / M * (ε / 2)) + |a| * (1 / |a| * (ε / 2)) := by
                              apply add_lt_add
                              apply (mul_lt_mul_left M_pos).mpr
                              apply (hNa n (le_of_max_le_left hn))
                              apply (mul_lt_mul_left (abs_pos.mpr ha)).mpr
                              apply (hNb n (le_of_max_le_right hn))
                            _ = ε := by sorry

-- Might finish this one off later, it's kinda a pain with calc terms
lemma algebraic_limit_inv (a_ne_zero : a ≠ 0) (csa : sa.ConvergesTo a) :
    (fun n ↦ 1 / sa n).ConvergesTo (1 / a) := by
  intro ε ε_pos
  -- We're gonnna need two different values for ε to use with our convergence hypothesis
  have ε₁_pos : |a| / 2 > 0 := by linarith [abs_pos.mpr a_ne_zero]
  have ε₂_pos : (ε * |a|^2) / 2 > 0 := by sorry
  obtain ⟨N₁, HN₁⟩ := csa (|a| / 2) ε₁_pos
  obtain ⟨N₂, HN₂⟩ := csa ((ε * |a|^2) / 2) ε₂_pos
  use max N₁ N₂
  intro n hn
  have : |sa n| > |a| / 2 := by sorry
  sorry

theorem algebraic_limit_div (b_ne_zero : b ≠ 0) (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) :
    (fun n ↦ sa n / sb n).ConvergesTo (a / b) := by
  have : (fun n ↦ 1 / sb n).ConvergesTo (1 / b) := algebraic_limit_inv b_ne_zero csb
  apply algebraic_limit_mul csa
  have inv_b : 1 / b = b⁻¹ := by ring
  have inv_sb :  (fun n => 1 / sb n) = (fun n => (sb n)⁻¹) := by ring_nf
  rw [← inv_b, ← inv_sb]
  exact this

theorem order_limit_nonneg (csa : sa.ConvergesTo a) (a_pos: ∀ n, sa n ≥ 0) : a ≥ 0 := by
  by_contra! h_contra
  have ε_pos : |a| > 0 := abs_pos_of_neg h_contra
  obtain ⟨N, hN⟩ := csa |a| ε_pos
  -- |sa N - a| < |a| implies |sa N| < 0, which is our contradiction
  have : |sa N - a| < |a| := hN N (by linarith)
  obtain ⟨_, h⟩ := abs_lt.mp this
  have a_neg : |a| = -a := abs_of_neg h_contra
  -- We could elide this line, but let's make our contradictory hypothesis explicit
  have : sa N < 0 := by linarith
  exact absurd (a_pos N) (not_le_of_gt this)

theorem order_limit_le (csa : sa.ConvergesTo a) (csb : sb.ConvergesTo b) (a_le_b : ∀ n, sa n ≤ sb n) : a ≤ b := by
  have b_sub_a_conv : (fun n ↦ sb n - sa n).ConvergesTo (b - a) := by apply algebraic_limit_sum csb (algebraic_limit_neg csa)
  have b_sub_a_pos : ∀ n : ℕ, sb n - sa n ≥ 0 := by intro n; linarith [a_le_b n]
  have : (b - a) ≥ 0 := by apply order_limit_nonneg b_sub_a_conv b_sub_a_pos
  linarith

theorem order_limit_const_le (csa : sa.ConvergesTo a) (hc : ∀ n, sa n ≤ c) : a ≤ c :=
  order_limit_le csa const_convergent hc

theorem order_limit_const_ge (csa : sa.ConvergesTo a) (hc : ∀ n, c ≤ sa n) : c ≤ a :=
  order_limit_le const_convergent csa hc

theorem seq_squeeze {l : ℝ} (csa : sa.ConvergesTo a) (csc : sc.ConvergesTo c) (a_l : a = l) (c_l : c = l) (a_le_b : ∀ n, sa n ≤ sb n)
    (b_le_c : ∀ n, sb n ≤ sc n) : sb.ConvergesTo l := by
  rw [a_l] at csa
  rw [c_l] at csc
  intro ε ε_pos
  obtain ⟨Na, hNa⟩ := csa ε ε_pos
  obtain ⟨Nb, hNb⟩ := csc ε ε_pos
  use max Na Nb
  intro n hn
  rw [abs_lt]
  constructor
  -- Firstly we use sa to constrain sb from below
  · calc
    -ε < sa n - l := by exact (abs_lt.mp (hNa n (le_of_max_le_left hn))).left
     _ ≤ sb n - l := tsub_le_tsub_right (a_le_b n) l
  -- Now we use sc to constrain sb from above
  · calc
    sb n - l ≤ sc n - l := by exact tsub_le_tsub_right (b_le_c n) l
           _ < ε := by exact (abs_lt.mp (hNb n (le_of_max_le_right hn))).right

lemma increasing_equivalent (h : sa.Increasing₁) : sa.Increasing := by
  intro n₁ n₂ hn
  induction' n₂ using Nat.strongRec with n₂ ih
  · by_cases h₁ : n₁ = n₂
    · rw [h₁]
    · have : n₁ < n₂ := by omega
      have l := ih (n₂ - 1) (by omega) (by omega)
      have r : sa (n₂ - 1) ≤ sa n₂ := by
        have : n₂ - 1 + 1 = n₂ := by omega
        rw [← this]
        exact h (n₂ - 1)
      exact le_trans l r

lemma decreasing_equivalent (h : sa.Decreasing₁) : sa.Decreasing := by
  intro n₁ n₂ hn
  induction' n₂ using Nat.strongRec with n₂ ih
  · by_cases h₁ : n₁ = n₂
    · rw [h₁]
    · have : n₁ < n₂ := by omega
      have l := ih (n₂ - 1) (by omega) (by omega)
      have r : sa (n₂ - 1) ≥ sa n₂ := by
        have : n₂ - 1 + 1 = n₂ := by omega
        rw [← this]
        exact h (n₂ - 1)
      apply le_trans r l

lemma monotone_convergence_increasing (isa : sa.Increasing₁) (bsa : sa.Bounded) : sa.Convergent := by
  let A := {a : ℝ | ∃ n : ℕ, a = sa n}
  obtain ⟨M, ⟨M_pos, hM⟩⟩ := bsa
  have ab : A.BoundedAbove := by
    use M
    intro a ha
    obtain ⟨n, rfl⟩ := Set.mem_setOf.mp ha
    exact le_of_max_le_left (hM n)
  have ane : A.Nonempty := by use sa 0, 0
  obtain ⟨a, ha⟩ := aoc.mp ⟨ane, ab⟩
  clear ane ab hM M M_pos
  -- It seems likely that a is the limit we're looking for
  use a
  intro ε ε_pos
  -- We can use the fact that a is the supremum to find an element of sa that's close enough
  have ab := ha.left
  rw [sup_analytic ha.left] at ha
  obtain ⟨aN, ⟨haN, aN_ε⟩⟩ := ha ε ε_pos
  obtain ⟨N, rfl⟩ := Set.mem_setOf.mp haN
  use N
  intro n hn
  apply abs_lt.mpr
  constructor
  · have := increasing_equivalent isa N n hn
    linarith
  · have := ab (sa n) ⟨n, rfl⟩
    linarith

lemma monotone_convergence_decreasing (dsa : sa.Decreasing₁) (bsa : sa.Bounded) : sa.Convergent := by
  let A := {a : ℝ | ∃ n : ℕ, a = sa n}
  obtain ⟨M, ⟨M_pos, hM⟩⟩ := bsa
  have ab : A.BoundedBelow := by
    use -M
    intro a ha
    obtain ⟨n, rfl⟩ := Set.mem_setOf.mp ha
    exact neg_le_of_abs_le (hM n)
  have ane : A.Nonempty := by use sa 0, 0
  obtain ⟨a, ha⟩ := infimum_exists ane ab
  clear ane ab hM M M_pos
    -- It seems likely that a is the limit we're looking for
  use a
  intro ε ε_pos
  -- We can use the fact that a is the infimum to find an element of sa that's close enough
  have ab := ha.left
  rw [inf_analytic ha.left] at ha
  obtain ⟨aN, ⟨haN, aN_ε⟩⟩ := ha ε ε_pos
  obtain ⟨N, rfl⟩ := Set.mem_setOf.mp haN
  use N
  intro n hn
  apply abs_lt.mpr
  constructor
  · have := ab (sa n) ⟨n, rfl⟩
    linarith
  · have := decreasing_equivalent dsa N n hn
    linarith

theorem monotone_convergence (msa : sa.Monotone) (bsa : sa.Bounded) : sa.Convergent := by
  rcases msa with (i | d)
  exact monotone_convergence_increasing i bsa
  exact monotone_convergence_decreasing d bsa

end

section

variable {sa : ℕ → ℝ} {φ : ℕ → ℕ} {a : ℝ}

-- The subsequence map always moves us further forward in the sequence
-- This is often handy
lemma ss_index_ge (φ_sm : StrictMono φ) : ∀ n, φ n ≥ n := by
  intro n
  induction' n with n ih
  · simp
  · trans φ n + 1
    · simp
      rw [add_comm, add_comm n 1]
      exact φ_sm.add_le_nat 1 n
    · linarith

theorem sc_same_limit (csa : sa.ConvergesTo a) (φ_sm : StrictMono φ) : (sa.Subsequence φ φ_sm).ConvergesTo a := by
  intro ε ε_pos
  obtain ⟨N, hN⟩ := csa ε ε_pos
  use N
  intro n hn
  apply hN (φ n)
  exact le_trans hn (ss_index_ge φ_sm n)

end
