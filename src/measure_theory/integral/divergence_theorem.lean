/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.divergence_theorem
import analysis.box_integral.integrability
import measure_theory.integral.interval_integral

open set finset topological_space box_integral
open_locale big_operators classical

namespace measure_theory

universes u
variables {E : Type u} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E] {n : ℕ}

local notation `ℝⁿ` := fin n → ℝ
local notation `ℝⁿ⁺¹` := fin (n + 1) → ℝ
local notation `Eⁿ⁺¹` := fin (n + 1) → E

/-- Divergence theorem for Bochner integral. If `f : ℝⁿ → Eⁿ` is differentiable on a rectangular box
`[a, b] : set ℝⁿ`, `a ≤ b`, with derivative `f' : ℝⁿ → ℝⁿ →L[ℝ] Eⁿ` and the divergence
`λ x, ∑ i, f' x (pi.single i 1) i` is integrable on `[a, b]`, then its integral is equal to the sum
of integrals of `f` over the faces of `[a, b]`, taken with appropriat signs. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
  (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (a b : ℝⁿ⁺¹) (hle : a ≤ b)
  (s : set ℝⁿ⁺¹) (hs : countable s) (Hc : ∀ x ∈ Icc a b ∩ s, continuous_within_at f (Icc a b) x)
  (Hd : ∀ x ∈ Icc a b \ s, has_fderiv_within_at f (f' x) (Icc a b) x)
  (Hi : integrable_on (λ x, ∑ i, f' x (pi.single i 1) i) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' x (pi.single i 1) i =
    ∑ i : fin (n + 1),
      ((∫ x in Icc (a ∘ i.succ_above) (b ∘ i.succ_above), f (i.insert_nth (b i) x) i) -
      ∫ x in Icc (a ∘ i.succ_above) (b ∘ i.succ_above), f (i.insert_nth (a i) x) i) :=
begin
  simp only [volume_pi, ← set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc],
  by_cases heq : ∃ i, a i = b i,
  { rcases heq with ⟨i, hi⟩,
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt,
    have : pi set.univ (λ j, Ioc (a j) (b j)) = ∅, from univ_pi_eq_empty hi',
    rw [this, integral_empty, sum_eq_zero],
    rintro j -,
    rcases eq_or_ne i j with rfl|hne,
    { simp [hi] },
    { rcases fin.exists_succ_above_eq hne with ⟨i, rfl⟩,
      have : pi set.univ (λ k : fin n, Ioc (a $ j.succ_above k) (b $ j.succ_above k)) = ∅,
        from univ_pi_eq_empty hi',
      rw [this, integral_empty, integral_empty, sub_self] } },
  { push_neg at heq,
    obtain ⟨I, rfl, rfl⟩ : ∃ I : box_integral.box (fin (n + 1)), I.lower = a ∧ I.upper = b,
      from ⟨⟨a, b, λ i, (hle i).lt_of_ne (heq i)⟩, rfl, rfl⟩,
    simp only [← box.coe_eq_pi, ← box.face_lower, ← box.face_upper],
    have A := ((Hi.mono_set box.coe_subset_Icc).has_box_integral ⊥ rfl),
    have B := has_integral_bot_divergence_of_forall_has_deriv_within_at I f f' s hs Hc Hd,
    have Hc : continuous_on f I.Icc,
    { intros x hx,
      by_cases hxs : x ∈ s,
      exacts [Hc x ⟨hx, hxs⟩, (Hd x ⟨hx, hxs⟩).continuous_within_at] },
    rw continuous_on_pi at Hc,
    refine (A.unique B).trans (sum_congr rfl $ λ i hi, _),
    refine congr_arg2 has_sub.sub _ _,
    { have := box.continuous_on_face_Icc (Hc i) (right_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact box.is_compact_Icc).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance },
    { have := box.continuous_on_face_Icc (Hc i) (left_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact box.is_compact_Icc).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance } }
end

end measure_theory
