import MathematicsInLean.Common

variable (a b c d e f : ℝ)

example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 := by
  rw [add_mul, mul_sub, mul_sub]
  ring

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

-- Proving identities on algebraic structures
variable (R: Type*) [Ring R]
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R,-a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

-- We can use the ring tactic to prove indentities about generic ring structures
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
example : (a + b) * (a- b) = a ^ 2- b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

namespace MyRing

variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]
theorem add_right_neg (a : R) : a +-a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

theorem neg_add_cancel_left (a b : R) :-a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b]
  rw [← neg_add_cancel_left a c]
  rw [h]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b]
  rw [← add_neg_cancel_right c b]
  rw [h]

-- Look, we're using have now
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, add_zero, zero_add]
  rw [add_right_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) :-a = b := by
  rw [← add_neg_cancel_left a b, add_comm (-a) b, ← add_assoc, h]
  rw [zero_add]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a =-b := by
  rw [← add_neg_cancel_right a b, h, zero_add]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  rw [neg_eq_of_add_eq_zero (neg_add_cancel a)]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg a a]
  rw [add_comm, neg_add_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing
