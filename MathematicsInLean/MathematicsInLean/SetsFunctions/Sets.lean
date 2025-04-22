import MathematicsInLean.Common
import Mathlib.Data.Real.Basic

variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  -- simp only tells the simplifier to only expand those definitions
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

-- See how we can use intro direction to prove the subset relation
-- And also how we can prove the implied and in the intersection definition using the angle brackets syntax
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

-- Some more examples of how we can tighten up proofs
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

-- See how rintro pulls the various layers of our premise apart (look at hx in the above proof if it's not clear)
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨hs, ht⟩ | ⟨hs, hu⟩)
  · exact ⟨hs, (Or.inl ht)⟩
  · exact ⟨hs, (Or.inr hu)⟩

-- We have the set difference operator as well
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

-- And a more compact proof
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  · constructor
    · exact xs
    · intro xt
      exact xntu (Or.inl xt)
  · intro xu
    exact xntu (Or.inr xu)

-- We use ext for set equality as well
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

-- Or the familiar Subset.antisymm
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _ ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun _ ⟨xt, xs⟩ ↦ ⟨xs, xt⟩

example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  rintro x ⟨xs, (xs | xt)⟩
  · exact xs
  · exact xs
  intro x xs
  constructor
  · exact xs
  · exact Or.inl xs

example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  · rintro x (xs | ⟨xs, _⟩) <;> exact xs
  · intro x xs
    exact Or.inl xs

example : s \ t ∪ t = s ∪ t := by
  apply Subset.antisymm
  · rintro x (⟨xs, xnt⟩ | xt)
    · exact Or.inl xs
    · exact Or.inr xt
  · rintro x (xs | xt)
    · by_cases h : x ∈ t
      · exact Or.inr h
      · exact Or.inl (And.intro xs h)
    · exact Or.inr xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  · rintro x (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      · exact Or.inl xs
      · rintro ⟨_, xt⟩
        contradiction
    · constructor
      · exact Or.inr xt
      · rintro ⟨xs, _⟩
        contradiction
  · rintro x ⟨(xs | xt), xnst⟩
    · left
      constructor
      · exact xs
      · intro xt
        apply xnst
        exact And.intro xs xt
    · right
      constructor
      · exact xt
      · intro xs
        apply xnst
        exact And.intro xs xt

-- Some set builder notation
def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry
