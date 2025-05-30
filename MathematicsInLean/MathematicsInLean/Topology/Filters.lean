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

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  rintro z zh
  apply hg at zh
  apply hf at zh
  apply zh

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)
#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)
#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

-- Now working in ℝ2
example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check le_inf_iff
