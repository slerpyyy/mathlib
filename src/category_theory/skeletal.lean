/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.isomorphism_classes
import category_theory.thin

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of a thin category as a partial ordering, and (noncomputably) show it is
a skeleton of the original category. The advantage of this special case being handled separately
is that lemmas and definitions about orderings can be used directly, for example for the subobject
lattice (TODO). In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.

(TODO): Construct the skeleton of a general category using choice, and show it is a skeleton.
-/

universes v₁ v₂ v₃ u₁ u₂ u₃

namespace category_theory

open category

variables (C : Type u₁) [category.{v₁} C]
variables (D : Type u₂) [category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E]

/-- A category is skeletal if isomorphic objects are equal. -/
def skeletal : Prop := ∀ ⦃X Y : C⦄, is_isomorphic X Y → X = Y

/--
`is_skeleton_of C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subcategory of `C`,
in particular `F` is a (strong) equivalence and `D` is skeletal.
-/
structure is_skeleton_of (F : D ⥤ C) :=
(skel : skeletal D)
(eqv : is_equivalence F)

local attribute [instance] is_isomorphic_setoid

variables {C D}
/-- If `C` is thin and skeletal, then any naturally isomorphic functors to `C` are equal. -/
lemma functor.eq_of_iso {F₁ F₂ : D ⥤ C} [∀ X Y : C, subsingleton (X ⟶ Y)] (hC : skeletal C)
  (hF : F₁ ≅ F₂) : F₁ = F₂ :=
functor.ext (λ X, hC ⟨hF.app X⟩) (λ _ _ _, subsingleton.elim _ _)

/--
If `C` is thin and skeletal, `D ⥤ C` is skeletal.
`category_theory.functor_thin` shows it is thin also.
-/
lemma functor_skeletal [∀ X Y : C, subsingleton (X ⟶ Y)] (hC : skeletal C) : skeletal (D ⥤ C) :=
λ F₁ F₂ h, h.elim (functor.eq_of_iso hC)
variables (C D)

/--
Construct the skeleton category by taking the quotient of objects. This construction gives a
preorder with nice definitional properties, but is only really appropriate for thin categories.
-/
def thin_skeleton : Type u₁ := quotient (is_isomorphic_setoid C)

instance inhabited_thin_skeleton [inhabited C] : inhabited (thin_skeleton C) :=
⟨quotient.mk (default _)⟩

instance thin_skeleton.preorder : preorder (thin_skeleton C) :=
{ le := quotient.lift₂ (λ X Y, nonempty (X ⟶ Y))
  begin
    rintros _ _ _ _ ⟨i₁⟩ ⟨i₂⟩,
    exact propext ⟨nonempty.map (λ f, i₁.inv ≫ f ≫ i₂.hom),
      nonempty.map (λ f, i₁.hom ≫ f ≫ i₂.inv)⟩,
  end,
  le_refl :=
  begin
    refine quotient.ind (λ a, _),
    exact ⟨𝟙 _⟩,
  end,
  le_trans := λ a b c, quotient.induction_on₃ a b c $ λ A B C, nonempty.map2 (≫) }

/-- The functor from a category to its thin skeleton. -/
@[simps]
def to_thin_skeleton : C ⥤ thin_skeleton C :=
{ obj := quotient.mk,
  map := λ X Y f, hom_of_le (nonempty.intro f) }

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/
namespace thin_skeleton

/-- The thin skeleton is thin. -/
instance thin {X Y : thin_skeleton C} : subsingleton (X ⟶ Y) :=
⟨by { rintros ⟨⟨f₁⟩⟩ ⟨⟨f₂⟩⟩, refl }⟩

variables {C} {D}

/-- A functor `C ⥤ D` computably lowers to a functor `thin_skeleton C ⥤ thin_skeleton D`. -/
@[simps]
def map (F : C ⥤ D) : thin_skeleton C ⥤ thin_skeleton D :=
{ obj := quotient.map F.obj $ λ X₁ X₂ ⟨hX⟩, ⟨F.map_iso hX⟩,
  map := λ X Y, quotient.rec_on_subsingleton₂ X Y $
           λ x y k, hom_of_le ((le_of_hom k).elim (λ t, ⟨F.map t⟩)) }

lemma comp_to_thin_skeleton (F : C ⥤ D) : F ⋙ to_thin_skeleton D = to_thin_skeleton C ⋙ map F := rfl

/-- Given a natural transformation `F₁ ⟶ F₂`, induce a natural transformation `map F₁ ⟶ map F₂`.-/
def map_nat_trans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ :=
{ app := λ X, quotient.rec_on_subsingleton X (λ x, ⟨⟨⟨k.app x⟩⟩⟩) }

-- TODO: state the lemmas about what happens when you compose with `to_thin_skeleton`
/-- A functor `C ⥤ D ⥤ E` computably lowers to a functor
`thin_skeleton C ⥤ thin_skeleton D ⥤ thin_skeleton E` -/
@[simps]
def map₂ (F : C ⥤ D ⥤ E) :
  thin_skeleton C ⥤ thin_skeleton D ⥤ thin_skeleton E :=
{ obj := λ x,
  { obj := λ y, quotient.map₂ (λ X Y, (F.obj X).obj Y)
                (λ X₁ X₂ ⟨hX⟩ Y₁ Y₂ ⟨hY⟩, ⟨(F.obj X₁).map_iso hY ≪≫ (F.map_iso hX).app Y₂⟩) x y,
    map := λ y₁ y₂, quotient.rec_on_subsingleton x $
            λ X, quotient.rec_on_subsingleton₂ y₁ y₂ $
              λ Y₁ Y₂ hY, hom_of_le ((le_of_hom hY).elim (λ g, ⟨(F.obj X).map g⟩)) },
  map := λ x₁ x₂, quotient.rec_on_subsingleton₂ x₁ x₂ $
           λ X₁ X₂ f,
           { app := λ y, quotient.rec_on_subsingleton y
              (λ Y, hom_of_le ((le_of_hom f).elim (λ f', ⟨(F.map f').app Y⟩))) } }

variables (C) [∀ X Y : C, subsingleton (X ⟶ Y)]

instance to_thin_skeleton_faithful : faithful (to_thin_skeleton C) := {}

/-- Use `quotient.out` to create a functor out of the thin skeleton. -/
@[simps]
noncomputable def from_thin_skeleton : thin_skeleton C ⥤ C :=
{ obj := quotient.out,
  map := λ x y, quotient.rec_on_subsingleton₂ x y $
    λ X Y f,
            (nonempty.some (quotient.mk_out X)).hom
          ≫ (le_of_hom f).some
          ≫ (nonempty.some (quotient.mk_out Y)).inv }

noncomputable instance from_thin_skeleton_equivalence : is_equivalence (from_thin_skeleton C) :=
{ inverse := to_thin_skeleton C,
  counit_iso := nat_iso.of_components (λ X, (nonempty.some (quotient.mk_out X))) (by tidy),
  unit_iso :=
    nat_iso.of_components
      (λ x, quotient.rec_on_subsingleton x
        (λ X, eq_to_iso (quotient.sound ⟨(nonempty.some (quotient.mk_out X)).symm⟩)))
      (by tidy) }

variables {C}

lemma equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
⟨iso_of_both_ways f g⟩

instance thin_skeleton_partial_order : partial_order (thin_skeleton C) :=
{ le_antisymm := quotient.ind₂
  begin
    rintros _ _ ⟨f⟩ ⟨g⟩,
    apply quotient.sound (equiv_of_both_ways f g),
  end,
  ..category_theory.thin_skeleton.preorder C }

lemma skeletal : skeletal (thin_skeleton C) :=
λ X Y, quotient.induction_on₂ X Y $ λ x y h, h.elim $ λ i, (le_of_hom i.1).antisymm (le_of_hom i.2)

lemma map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G :=
functor.eq_of_iso skeletal $
  nat_iso.of_components (λ X, quotient.rec_on_subsingleton X (λ x, iso.refl _)) (by tidy)

lemma map_id_eq : map (𝟭 C) = 𝟭 (thin_skeleton C) :=
functor.eq_of_iso skeletal $
  nat_iso.of_components (λ X, quotient.rec_on_subsingleton X (λ x, iso.refl _)) (by tidy)

lemma map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
functor.eq_of_iso skeletal { hom := map_nat_trans h.hom, inv := map_nat_trans h.inv }

/-- `from_thin_skeleton C` exhibits the thin skeleton as a skeleton. -/
noncomputable def thin_skeleton_is_skeleton : is_skeleton_of C (thin_skeleton C)
  (from_thin_skeleton C) :=
{ skel := skeletal,
  eqv := thin_skeleton.from_thin_skeleton_equivalence C }

noncomputable instance is_skeleton_of_inhabited :
  inhabited (is_skeleton_of C (thin_skeleton C) (from_thin_skeleton C)) :=
⟨thin_skeleton_is_skeleton⟩

end thin_skeleton

end category_theory
