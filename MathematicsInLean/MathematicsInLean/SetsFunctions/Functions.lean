import MathematicsInLean.Common
import Mathlib.Data.Real.Basic

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
