import MathematicsInLean.Common
import Mathlib.Data.Nat.GCD.Basic

-- How the natural numbers are defined in lean
-- inductive Nat where
--   | zero : Nat
--   | succ (n : Nat) : Nat

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · norm_num [fac]
  · rw [fac]
    norm_num [ih]

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  · rcases Nat.of_le_succ ile with h | h
    · apply dvd_mul_of_dvd_right (ih h)
    · rw [h]
      apply dvd_mul_right

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  · induction' n with n ih
    · simp [fac]
    · simp at *
      rw [pow_succ', fac]
      apply Nat.mul_le_mul _ ih
      repeat apply Nat.succ_le_succ
      apply zero_le

section

open BigOperators
open Finset

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x ∈ range n.succ, f x = ∑ x ∈ range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x ∈ range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x ∈ range n.succ, f x = (∏ x ∈ range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  induction' n with n ih
  · simp [fac]
  · rw [fac, ih, prod_range_succ, mul_comm]

theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num)
  induction' n with n ih
  · ring
  · rw [Finset.sum_range_succ, mul_add 2, ← ih]
    ring

theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num)
  induction' n with n ih
  · ring
  · rw [Finset.sum_range_succ, mul_add 6, ← ih]
    ring

end

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  · rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  · rw [add, ih]
    rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  · rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  · rw [succ_add, add, succ_add, ih, add]

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' n with n ih
  · rw [zero_add, mul, zero_add]
  · rw [succ_add, mul, ih]

end MyNat
