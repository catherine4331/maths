import MathematicsInLean.Common
import Mathlib.Data.Real.Basic

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

section

variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl

end

def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc _ _ _ := (Equiv.trans_assoc _ _ _)
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

structure AddGroup₁ (α : Type*) where
  add :  α → α → α
  zero : α
  neg :  α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point :=
  ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₁ Point
    where
  add a b := add a b
  zero := Point.zero
  neg a := neg a
  add_assoc a b c := by simp [add, add_assoc]
  add_zero := by simp [add, zero]
  zero_add := by simp [add, zero]
  neg_add_cancel := by simp [add, neg, zero]

end Point

section

variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹
#check g ^ n

example : f * g * g⁻¹ = f := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

end

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc _ _ _ := (Equiv.trans_assoc _ _ _)
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

#check Group₂.mul

def mySquare {α: Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section

variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

instance {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section

variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl
