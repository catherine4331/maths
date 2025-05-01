import MathematicsInLean.Common
import Mathlib.Data.Real.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

-- Preimage
example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

-- Image
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro hf x xs
    simp
    apply hf
    use x
  · intro h y ymem
    rcases ymem with ⟨x, xs, fxeq⟩
    rw [← fxeq]
    apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xmem, rfl⟩
  exact xmem

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, rfl⟩
  use x
  apply And.intro yu rfl

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y ⟨x, xmem, fxeq⟩
  apply h at xmem
  use x

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; constructor
  · rintro (xmemu | xmemv)
    · exact Or.inl xmemu
    · exact Or.inr xmemv
  · rintro (xmemu | xmemv)
    · exact Or.inl xmemu
    · exact Or.inr xmemv

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  · use x
  · use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂s, fxeq⟩⟩
  apply h at fxeq
  rw [fxeq] at x₂s
  use x₁
  exact And.intro (And.intro x₁s x₂s) rfl

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ynt⟩
  use x
  constructor
  · constructor
    · exact xs
    · intro xt
      apply ynt
      use x
  · rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun _ ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, yv⟩
    use x
    exact And.intro (And.intro xs yv) rfl
  · rintro ⟨x, ⟨xs, xv⟩, rfl⟩
    constructor
    · use x
    · exact xv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, xu⟩, rfl⟩
  constructor
  · use x
  · exact xu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, xu⟩
  constructor
  · use x
  · exact xu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | xu)
  · left
    use x
  · right
    exact xu

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro h
  calc
    x = (√x)^2 := by rw [sq_sqrt xpos]
    _ = (√y)^2 := by rw [h]
    _ = y := by rw [sq_sqrt ypos]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  dsimp
  intro h
  rw [← sq_eq_sq₀ xpos ypos, h]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, _, rfl⟩
    exact sqrt_nonneg x
  · intro ypos
    use y^2
    exact And.intro (sq_nonneg y) (sqrt_sq ypos)

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    exact sq_nonneg x
  · rintro h
    use √y
    exact sq_sqrt h

end

noncomputable section

variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · rintro h x
    apply h
    apply inverse_spec
    use x
  · intro h x₁ x₂ e
    rw [← h x₁, ← h x₂, e]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · rintro h y
    rcases h y with ⟨x, h⟩
    apply inverse_spec
    use x
  · intro h y
    use (inverse f) y
    apply h

end

theorem Cantor : ∀ f : α → Set α, ¬Function.Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    apply h₁
  have h₃ : j ∉ S := by
    rw [h] at h₁
    exact h₁
  contradiction
