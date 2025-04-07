import MathematicsInLean.Common
import Mathlib.Data.Real.Basic

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

-- The extra dots at the end aren't actually required, but I like how they keep the proof structure clear
example : min a b = min b a := by
  apply le_antisymm
  -- The show isn't doing anything here, but it tells us the goal we're trying to prove in this section
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    · apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    · apply min_le_left

-- That proof is a little repetetive. Let's use a lemma to tidy it up
-- I quite like using the dot & indent notation for all sub goals, even though we don't need to do it that way
example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    · apply min_le_right
    · apply min_le_left
  apply le_antisymm
  · apply h
  · apply h

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    · apply le_max_right
    · apply le_max_left
  apply le_antisymm
  · apply h
  · apply h

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    · apply le_min
      · apply le_trans
        apply min_le_left
        apply min_le_right
      · apply min_le_right
  · apply le_min
    · apply le_min
      · apply min_le_left
      · apply le_trans
        apply min_le_right
        apply min_le_left
    · apply le_trans
      apply min_le_right
      apply min_le_right

example : max (max a b) c = max a (max b c) := by
  apply le_antisymm
  · apply max_le
    · apply max_le
      · apply le_max_left
      · apply le_trans
        apply le_max_left b c
        apply le_max_right
    · apply le_trans
      apply le_max_right b c
      apply le_max_right
  · apply max_le
    · apply le_trans
      apply le_max_left a b
      apply le_max_left
    · apply max_le
      · apply le_trans
        apply le_max_right a b
        apply le_max_left
      · apply le_max_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  apply le_antisymm
  · apply aux
  · rw [h]
    apply add_le_add_right
    rw [sub_eq_add_neg]
    apply le_trans
    apply aux
    rw [add_neg_cancel_right, add_neg_cancel_right]

-- It's the triangle inequality!
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith

end

variable (x y z : ℝ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  rw [dvd_add_left, dvd_add_left]
  · rw [mul_comm x z, ← mul_assoc]
    apply dvd_mul_left
  · apply dvd_mul_left
  · rw [pow_two]
    apply dvd_mul_of_dvd_left h

variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · apply Nat.gcd_dvd_right
    · apply Nat.gcd_dvd_left
  · apply Nat.dvd_gcd
    · apply Nat.gcd_dvd_right
    · apply Nat.gcd_dvd_left
