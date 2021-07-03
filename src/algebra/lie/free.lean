/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.of_associative
import algebra.lie.non_unital_non_assoc_algebra
import algebra.free_non_unital_non_assoc_algebra

/-!
# Free Lie algebras

Given a commutative ring `R` and a type `X` we construct the free Lie algebra on `X` with
coefficients in `R` together with its universal property.

## Main definitions

  * `free_lie_algebra`
  * `free_lie_algebra.lift`
  * `free_lie_algebra.of`

## Implementation details

### Quotient of free non-unital, non-associative algebra

We follow [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) and construct
the free Lie algebra as a quotient of the free non-unital, non-associative algebra. Since we do not
currently have definitions of ideals, lattices of ideals, and quotients for
`non_unital_non_assoc_semiring`, we construct our quotient using the low-level `quot` function on
an inductively-defined relation.

### Alternative construction (often used over field of characteristic zero, but not by us)

By universality of the free Lie algebra, there is a natural morphism of Lie algebras:
`ρ : free_lie_algebra R X →ₗ⁅R⁆ free_algebra R X`, where `free_algebra R X` is the free unital,
associative algebra, regarded as a Lie algebra via the ring commutator.

By uniqueness, the image of `ρ` is the Lie subalgebra generated by `X` in the free algebra, i.e.:
`lie_subalgebra.lie_span R (free_algebra R X) (set.range (free_algebra.ι R))`. If `ρ` is injective
we could thus take the Lie subalgebra generated by `X` in the free associative algebra as the
definition of the free Lie algebra, and indeed some authors do this. This is valid at least over a
field of characteristic zero but I do not believe `ρ` is injective for general `R`. Indeed the only
proof I know that `ρ` is injective relies on using the injectivity of the map from a Lie algebra to
its universal enveloping algebra, which does not hold in general. Furthermore, even when a Lie
algebra does inject into its universal enveloping algebra, the only proofs I know of this fact
use the Poincaré–Birkhoff–Witt theorem. Some related MathOverflow questions are
[this one](https://mathoverflow.net/questions/61954/) and
[this one](https://mathoverflow.net/questions/114701/).

## Tags

lie algebra, free algebra, non-unital, non-associative, universal property, forgetful functor,
adjoint functor
-/

universes u v w

noncomputable theory

variables (R : Type u) (X : Type v) [comm_ring R]

/-- We save characters by using Bourbaki's name `lib` (as in «libre») for
`free_non_unital_non_assoc_algebra` in this file. -/
local notation `lib` := free_non_unital_non_assoc_algebra
local notation `lib.lift` := free_non_unital_non_assoc_algebra.lift
local notation `lib.of` := free_non_unital_non_assoc_algebra.of
local notation `lib.lift_of_apply` := free_non_unital_non_assoc_algebra.lift_of_apply
local notation `lib.lift_comp_of` := free_non_unital_non_assoc_algebra.lift_comp_of

namespace free_lie_algebra

/-- The quotient of `lib R X` by the equivalence relation generated by this relation will give us
the free Lie algebra. -/
inductive rel : lib R X → lib R X → Prop
| lie_self (a : lib R X) : rel (a * a) 0
| leibniz_lie (a b c : lib R X) : rel (a * (b * c)) (((a * b) * c) + (b * (a * c)))
| smul (t : R) (a b : lib R X) : rel a b → rel (t • a) (t • b)
| add_right (a b c : lib R X) : rel a b → rel (a + c) (b + c)
| mul_left (a b c : lib R X) : rel b c → rel (a * b) (a * c)
| mul_right (a b c : lib R X) : rel a b → rel (a * c) (b * c)

variables {R X}

lemma rel.add_left (a b c : lib R X) (h : rel R X b c) : rel R X (a + b) (a + c) :=
by { rw [add_comm _ b, add_comm _ c], exact rel.add_right _ _ _ h, }

lemma rel.neg (a b : lib R X) (h : rel R X a b) : rel R X (-a) (-b) :=
h.smul (-1) _ _

end free_lie_algebra

/-- The free Lie algebra on the type `X` with coefficients in the commutative ring `R`. -/
@[derive inhabited]
def free_lie_algebra := quot (free_lie_algebra.rel R X)

namespace free_lie_algebra

instance : add_comm_group (free_lie_algebra R X) :=
{ add            := quot.map₂ (+) rel.add_left rel.add_right,
  add_comm       := by { rintros ⟨a⟩ ⟨b⟩, change quot.mk _ _ = quot.mk _ _, rw add_comm, },
  add_assoc      := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, change quot.mk _ _ = quot.mk _ _, rw add_assoc, },
  zero           := quot.mk _ 0,
  zero_add       := by { rintros ⟨a⟩, change quot.mk _ _ = _, rw zero_add, },
  add_zero       := by { rintros ⟨a⟩, change quot.mk _ _ = _, rw add_zero, },
  neg            := quot.map has_neg.neg rel.neg,
  add_left_neg   := by { rintros ⟨a⟩, change quot.mk _ _ = quot.mk _ _ , rw add_left_neg, } }

instance : module R (free_lie_algebra R X) :=
{ smul      := λ t, quot.map ((•) t) (rel.smul t),
  one_smul  := by { rintros ⟨a⟩, change quot.mk _ _ = quot.mk _ _, rw one_smul, },
  mul_smul  := by { rintros t₁ t₂ ⟨a⟩, change quot.mk _ _ = quot.mk _ _, rw mul_smul, },
  add_smul  := by { rintros t₁ t₂ ⟨a⟩, change quot.mk _ _ = quot.mk _ _, rw add_smul, },
  smul_add  := by { rintros t ⟨a⟩ ⟨b⟩, change quot.mk _ _ = quot.mk _ _, rw smul_add, },
  zero_smul := by { rintros ⟨a⟩, change quot.mk _ _ = quot.mk _ _, rw zero_smul, },
  smul_zero := λ t, by { change quot.mk _ _ = quot.mk _ _, rw smul_zero, }, }

/-- Note that here we turn the `has_mul` coming from the `non_unital_non_assoc_semiring` structure
on `lib R X` into a `has_bracket` on `free_lie_algebra`. -/
instance : lie_ring (free_lie_algebra R X) :=
{ bracket     := quot.map₂ (*) rel.mul_left rel.mul_right,
  add_lie     := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, change quot.mk _ _ = quot.mk _ _, rw add_mul, },
  lie_add     := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, change quot.mk _ _ = quot.mk _ _, rw mul_add, },
  lie_self    := by { rintros ⟨a⟩, exact quot.sound (rel.lie_self a), },
  leibniz_lie := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, exact quot.sound (rel.leibniz_lie a b c), }, }

instance : lie_algebra R (free_lie_algebra R X) :=
{ lie_smul :=
  begin
    rintros t ⟨a⟩ ⟨c⟩,
    change quot.mk _ (a • (t • c)) = quot.mk _ (t • (a • c)),
    rw ← smul_comm,
  end, }

variables {X}

/-- The embedding of `X` into the free Lie algebra of `X` with coefficients in the commutative ring
`R`. -/
def of : X → free_lie_algebra R X := λ x, quot.mk _ (lib.of R x)

variables {L : Type w} [lie_ring L] [lie_algebra R L]

local attribute [instance] lie_ring.to_non_unital_non_assoc_semiring

/-- An auxiliary definition used to construct the equivalence `lift` below. -/
def lift_aux (f : X → L) := lib.lift R f

lemma lift_aux_map_smul (f : X → L) (t : R) (a : lib R X) :
  lift_aux R f (t • a) = t • lift_aux R f a :=
non_unital_alg_hom.map_smul _ t a

lemma lift_aux_map_add (f : X → L) (a b : lib R X) :
  lift_aux R f (a + b) = (lift_aux R f a) + (lift_aux R f b) :=
non_unital_alg_hom.map_add _ a b

lemma lift_aux_map_mul (f : X → L) (a b : lib R X) :
  lift_aux R f (a * b) = ⁅lift_aux R f a, lift_aux R f b⁆ :=
non_unital_alg_hom.map_mul _ a b

lemma lift_aux_spec (f : X → L) (a b : lib R X) (h : free_lie_algebra.rel R X a b) :
  lift_aux R f a = lift_aux R f b :=
begin
  induction h,
  case rel.lie_self : a'
  { simp only [lift_aux_map_mul, non_unital_alg_hom.map_zero, lie_self], },
  case rel.leibniz_lie : a' b' c'
  { simp only [lift_aux_map_mul, lift_aux_map_add, sub_add_cancel, lie_lie], },
  case rel.smul : t a' b' h₁ h₂
  { simp only [lift_aux_map_smul, h₂], },
  case rel.add_right : a' b' c' h₁ h₂
  { simp only [lift_aux_map_add, h₂], },
  case rel.mul_left : a' b' c' h₁ h₂
  { simp only [lift_aux_map_mul, h₂], },
  case rel.mul_right : a' b' c' h₁ h₂
  { simp only [lift_aux_map_mul, h₂], },
end

/-- The quotient map as a `non_unital_alg_hom`. -/
def mk : non_unital_alg_hom R (lib R X) (free_lie_algebra R X) :=
{ to_fun    := quot.mk (rel R X),
  map_smul' := λ t a, rfl,
  map_zero' := rfl,
  map_add'  := λ a b, rfl,
  map_mul'  := λ a b, rfl, }

/-- The functor `X ↦ free_lie_algebra R X` from the category of types to the category of Lie
algebras over `R` is adjoint to the forgetful functor in the other direction. -/
def lift : (X → L) ≃ (free_lie_algebra R X →ₗ⁅R⁆ L) :=
{ to_fun    := λ f,
    { to_fun    := λ c, quot.lift_on c (lift_aux R f) (lift_aux_spec R f),
      map_add'  := by { rintros ⟨a⟩ ⟨b⟩, rw ← lift_aux_map_add, refl, },
      map_smul' := by { rintros t ⟨a⟩, rw ← lift_aux_map_smul, refl, },
      map_lie'  := by { rintros ⟨a⟩ ⟨b⟩, rw ← lift_aux_map_mul, refl, }, },
  inv_fun   := λ F, F ∘ (of R),
  left_inv  := λ f, by { ext x, simp only [lift_aux, of, quot.lift_on_mk, lie_hom.coe_mk,
    function.comp_app, lib.lift_of_apply], },
  right_inv := λ F,
    begin
      ext ⟨a⟩,
      let F' := F.to_non_unital_alg_hom.comp (mk R),
      exact non_unital_alg_hom.congr_fun (lib.lift_comp_of R F') a,
    end, }

@[simp] lemma lift_symm_apply (F : free_lie_algebra R X →ₗ⁅R⁆ L) : (lift R).symm F = F ∘ (of R) :=
rfl

variables {R}

@[simp] lemma of_comp_lift (f : X → L) : (lift R f) ∘ (of R) = f :=
(lift R).left_inv f

@[simp] lemma lift_unique (f : X → L) (g : free_lie_algebra R X →ₗ⁅R⁆ L) :
  g ∘ (of R) = f ↔ g = lift R f :=
(lift R).symm_apply_eq

attribute [irreducible] of lift

@[simp] lemma lift_of_apply (f : X → L) (x) : lift R f (of R x) = f x :=
by rw [← function.comp_app (lift R f) (of R) x, of_comp_lift]

@[simp] lemma lift_comp_of (F : free_lie_algebra R X →ₗ⁅R⁆ L) : lift R (F ∘ (of R)) = F :=
by { rw ← lift_symm_apply, exact (lift R).apply_symm_apply F, }

@[ext] lemma hom_ext {F₁ F₂ : free_lie_algebra R X →ₗ⁅R⁆ L} (h : ∀ x, F₁ (of R x) = F₂ (of R x)) :
  F₁ = F₂ :=
have h' : (lift R).symm F₁ = (lift R).symm F₂, { ext, simp [h], },
(lift R).symm.injective h'

end free_lie_algebra
