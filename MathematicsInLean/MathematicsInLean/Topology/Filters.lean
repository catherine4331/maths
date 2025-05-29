import MathematicsInLean.Common
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter Topology

def principle {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t}
  univ_sets := subset_univ s
  sets_of_superset := by
    intro x y h₁ h₂
    apply Subset.trans h₁ h₂
  inter_sets := by
    intro z y h₁ h₂
    apply subset_inter h₁ h₂

example : Filter ℕ :=
  {
    sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      use 42
      intro b h
      tauto
    sets_of_superset := by
      rintro x y ⟨a, ha⟩ h
      use a
      tauto
    inter_sets := by
      rintro x y ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
      use max a₁ a₂
      intro b hb
      rw [max_le_iff] at hb
      tauto
  }

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f⁻¹' V ∈ F
