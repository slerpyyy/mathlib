/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.times_cont_mdiff
import topology.continuous_map

/-!
# Smooth bundled map

In this file we define the type `smooth_map` of smooth bundled maps.

-/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H'']
{I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']

variables (I) (I') (M) (M')

/-- Bundled smooth maps. -/
@[protect_proj]
structure smooth_map :=
(to_fun             : M → M')
(smooth_to_fun      : smooth I I' to_fun)

notation `C∞(` I `, ` M `; ` I' `, ` M' `)` := smooth_map I I' M M'

notation `C∞(` I `, ` M `; ` k `)` := smooth_map I (model_with_corners_self k k) M k

notation `C∞(` I `, ` M `)` := smooth_map I (model_with_corners_self ℝ ℝ) M ℝ

namespace smooth_map

variables {I} {I'} {M} {M'}

instance : has_coe_to_fun C∞(I, M; I', M') := ⟨_, smooth_map.to_fun⟩
instance : has_coe C∞(I, M; I', M') C(M, M') :=
⟨λ f, ⟨f.to_fun, f.smooth_to_fun.continuous⟩⟩

variables {f g : C∞(I, M; I', M')}

lemma coe_inj ⦃f g : C∞(I, M; I', M')⦄ (h : (f : M → M') = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext h

/-- The identity as a smooth map. -/
def id : C∞(I, M; I, M) := ⟨id, smooth_id⟩

/-- The composition of smooth maps, as a smooth map. -/
def comp (f : C∞(I', M'; I'', M'')) (g : C∞(I, M; I', M')) : C∞(I, M; I'', M'') :=
{ to_fun := λ a, f (g a),
  smooth_to_fun := f.smooth_to_fun.comp g.smooth_to_fun, }

@[simp] lemma comp_apply (f : C∞(I', M'; I'', M'')) (g : C∞(I, M; I', M')) (x : M) :
  f.comp g x = f (g x) := rfl

instance [inhabited M'] : inhabited C∞(I, M; I', M') :=
⟨⟨λ _, default _, smooth_const⟩⟩

protected lemma smooth (f : C∞(I, M; I', M')) : smooth I I' f := f.smooth_to_fun

/-- Constant map as a smooth map -/
def const (y : M') : C∞(I, M; I', M') := ⟨λ x, y, smooth_const⟩

end smooth_map
