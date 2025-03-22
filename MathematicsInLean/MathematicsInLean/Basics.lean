import MathematicsInLean.Common

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_comm a c]
  rw [mul_assoc b c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- We don't have to provide full (or any) arguments sometimes
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [mul_comm c]

example (a b c d e f : ℝ) (h₁ : a * b = c * d) (h₂ : e = f) : a * (b * e) = c * (d * f) := by
  rw [h₂]
  rw [← mul_assoc]
  rw [h₁]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (h₁ : c = b * a - d) (h₂ : d = a * b) : c = 0 := by
  rw [h₁]
  rw [h₂]
  rw [mul_comm]
  rw [sub_self]

-- We can declare are reuse variables
variable (a b c d e f : ℝ)

example (h₁ : a * b = c * d) (h₂ : e = f) : a * (b * e) = c * (d * f) := by
  rw [h₂, ← mul_assoc, h₁, mul_assoc]

-- We can use sections
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- This proof is a little hard to follow in the info view
-- Lean provides us a more structured way of writing proofs
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul]
  rw [add_assoc, add_assoc]
  ring
