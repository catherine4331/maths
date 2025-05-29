import MathematicsInLean.Common
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x
example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) : f 1 = 1 :=
  f.map_one

example {M N P : Type*} [Monoid M] [Monoid N] [Monoid P] (f : M →* N) (g : N →* P) : M →* P :=
  g.comp f

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm

noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

-- Subgroups
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx

example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1
    apply And.intro H.one_mem
    · rw [mul_one, mul_inv_cancel]
  inv_mem' := by
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹
    constructor
    apply H.inv_mem h_in
    group
  mul_mem' := by
    dsimp
    rintro a b  ⟨h₁, h₁_in, rfl⟩ ⟨h₂, h₂_in, rfl⟩
    use h₁ * h₂
    constructor
    apply H.mul_mem h₁_in h₂_in
    group

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

section exercises

variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  intro h hx
  apply hST hx

example (φ : G →* H) (S T : Subgroup G) (hST: S ≤ T) : map φ S ≤ map φ T := by
  intro h hx
  rcases hx with ⟨g, gs, rfl⟩
  use g, hST gs

variable {K : Type*} [Group K]

example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext g
  constructor
  · rintro g_in
    apply g_in
  · rintro g_in
    apply g_in

example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext x
  constructor
  · rintro ⟨s, s_in, rfl⟩
    use φ s
    constructor
    · use s, s_in
    · rfl
  · rintro ⟨h, ⟨s, s_in, rfl⟩, rfl⟩
    use s, s_in
    rfl

end exercises

open scoped Classical

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G := by
  use G'.index
  rw [← mul_comm G'.index _]
  use G'.index_mul_card.symm
