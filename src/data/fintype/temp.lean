import data.finset.sort
import data.fintype.basic
import data.fintype.sort
import order.monovary
import group_theory.perm.support

namespace fintype

variables {α β : Type*} [linear_order β] (f : α → β)

@[simps] def lex.fst {α β} [preorder α] [preorder β] : lex (α × β) →o α :=
{ to_fun := prod.fst,
  monotone' := λ i j h, by { cases h, { apply le_of_lt, assumption }, { refl } } }

variables {m : ℕ} [fintype α]  (h : fintype.card α = m)
include h

/-- Sorting a function. Informally, given an indexed collection of ordered values, we order the
indices to match the values. -/
lemma exists_monotone_replacement : ∃ (e : fin m ≃ α), monotone (f ∘ e) :=
begin
  have e0 : α ≃ fin m := fintype.equiv_fin_of_card_eq h,
  let f' : α → lex (β × fin m) := λ a, (f a, e0 a),
  letI : linear_order α := linear_order.lift f' _,
  swap, { intros a b ab, apply e0.injective, convert congr_arg prod.snd ab },
  have eo : fin m ≃o α := mono_equiv_of_fin _ h,
  refine ⟨eo.to_equiv, monotone.comp _ eo.monotone⟩,
  change monotone (lex.fst ∘ f'),
  exact monotone.comp lex.fst.monotone (λ a b h, h),
end

/-- Sorting a function. We permute the values of the domain of the function `α` -/
lemma exists_monotone_perm [linear_order α] : ∃ (σ : equiv.perm α), monotone (f ∘ σ) :=
begin
  cases exists_monotone_replacement f h with e he,
  set γ : fin m ≃o α := mono_equiv_of_fin _ h with hγ,
  set σ : equiv.perm α :=
  begin
    refine ⟨e ∘ γ.symm, γ ∘ e.symm, λ x, _, λ x, _⟩;
    simp
  end with hσ,
  refine ⟨σ, λ x y hxy, _⟩,
  simp only [function.comp_app, equiv.coe_fn_mk],
  exact he ((order_iso.symm γ).monotone hxy)
end

end fintype

namespace finset

variables {α β : Type*} [linear_order β] (f : α → β) {m : ℕ} (s : finset α)

lemma exists_monotone_replacement (hs : s.card = m) : ∃ (e : fin m → α), monotone (f ∘ e) :=
begin
  replace hs : fintype.card s = m := by simpa,
  cases fintype.exists_monotone_replacement (f ∘ (coe : s → α)) hs with e he,
  refine ⟨(coe ∘ e), he⟩
end

lemma exists_monotone_perm [linear_order α] : ∃ (σ : equiv.perm α), {x | σ x ≠ x} ⊆ s ∧
  monotone_on (f ∘ σ) s :=
begin
  cases (show ∃ m, s.card = m, by exact exists_eq') with m hs,
  replace hs : fintype.card s = m := by simpa,
  cases fintype.exists_monotone_perm (f ∘ (coe : s → α)) hs with σ hσ,
  refine ⟨equiv.perm.subtype_congr σ (equiv.refl _), _, _⟩,
  { intros x hx,
    contrapose hx,
    simp only [set.mem_set_of_eq, not_not],
    rw mem_coe at hx,
    rw equiv.perm.subtype_congr.right_apply,
    { simp only [equiv.coe_refl, id.def, subtype.coe_mk]},
    exact hx },
  { intros x hx y hy hxy,
    replace hxy : (⟨x, hx⟩ : s) ≤ ⟨y, hy⟩, by simpa,
    convert hσ hxy using 1,
    { simp only [function.comp_app],
      congr,
      rw equiv.perm.subtype_congr.left_apply },
    { simp only [function.comp_app],
      congr,
      rw equiv.perm.subtype_congr.left_apply }}
end


end finset

namespace monovary

variables {ι α β : Type*} {f : ι → α} {g : ι → β}

lemma comp [preorder α] [preorder β] (σ : ι → ι) : monovary f g → monovary (f ∘ σ) (g ∘ σ) :=
λ h x y hxy, h hxy

lemma perm_iff [preorder α] [preorder β] (σ : equiv.perm ι) :
  monovary f g ↔ monovary (f ∘ σ) (g ∘ σ) :=
begin
  refine ⟨comp σ, λ h x y hxy, _⟩,
  { replace hxy : g (σ (σ⁻¹ x)) < g (σ (σ⁻¹ y)) := by simpa using hxy,
    simpa using (h hxy) }
end

lemma exists_perm_monovary [linear_order ι] [linear_order α] [linear_order β] [fintype ι] :
  ∃ σ: equiv.perm ι, monovary (f ∘ σ) g :=
begin
  cases (show ∃ m, fintype.card ι = m, by exact exists_eq') with m hι,
  cases fintype.exists_monotone_perm f hι with τ hτ,
  cases fintype.exists_monotone_perm g hι with π hπ,
  set σ : equiv.perm ι :=
  begin
    refine ⟨τ ∘ π.symm, π ∘ τ.symm,λ x, _ ,λ x, _⟩;
    simp
  end with hσ,
  refine ⟨σ, _⟩,
  rw [perm_iff π, hσ],
  convert (hτ.monovary hπ) using 1,
  ext; simp
end

end monovary

namespace equiv.perm

lemma image_set_eq {ι : Type*} {σ : equiv.perm ι} {s : set ι} (hσ : {x | σ x ≠ x} ⊆ s) :
  σ '' s = s :=
begin
  ext,
  split,
  { rintro ⟨y, hys, hy⟩,
    obtain rfl | hxy := eq_or_ne y x,
    { exact hys },
    { apply hσ,
      simp only [← hy, ne.def, set.mem_set_of_eq, embedding_like.apply_eq_iff_eq],
      simpa [hy] using (ne.symm hxy) }},
  { intro h,
    obtain hx | hx := eq_or_ne (σ x) x,
    { rw ← hx,
      exact set.mem_image_of_mem σ h },
    { refine ⟨σ⁻¹ x, _, apply_inv_self σ x⟩,
      { apply hσ,
        simp only [ne.def, set.mem_set_of_eq, apply_inv_self, eq_inv_iff_eq, hx, not_false_iff] }}}
end

lemma set_subset_of_subset {ι : Type*} {τ π : equiv.perm ι} {s : set ι} (hτ : {x | τ x ≠ x} ⊆ s)
  (hπ : {x | π x ≠ x} ⊆ s) : {x | (τ ∘ π) x ≠ x} ⊆ s :=
begin
  intros x hx,
  contrapose hx,
  replace hπ : π x = x,
  { contrapose hx,
    push_neg,
    convert hπ hx },
  replace hτ : (τ ∘ π) x = x,
  { simp only [hπ, function.comp_app],
    contrapose hx,
    push_neg,
    convert hτ hx },
  simpa using hτ
end

end equiv.perm

namespace monovary_on

variables {ι α β : Type*} {f : ι → α} {g : ι → β} {s : set ι}

lemma comp [preorder α] [preorder β] (σ : ι → ι) :
  monovary_on f g (σ '' s) → monovary_on (f ∘ σ) (g ∘ σ) s :=
λ h x hx y hy hxy, h (set.mem_image_of_mem σ hx) (set.mem_image_of_mem σ hy) hxy

lemma perm_iff [preorder α] [preorder β] (σ : equiv.perm ι) :
  monovary_on f g (σ '' s) ↔ monovary_on (f ∘ σ) (g ∘ σ) s :=
begin
  refine ⟨comp σ, λ h x hx y hy hxy, _⟩,
  { replace hxy : g (σ (σ⁻¹ x)) < g (σ (σ⁻¹ y)) := by simpa using hxy,
    replace hx : σ⁻¹ x ∈ s,
    { cases hx with z hz,
      simp only [← hz.2, equiv.perm.inv_apply_self, hz.1] },
    replace hy : σ⁻¹ y ∈ s,
    { cases hy with z hz,
      simp only [← hz.2, equiv.perm.inv_apply_self, hz.1] },
    simpa using (h hx hy hxy) }
end

lemma perm_iff_of_support_subset [preorder α] [preorder β] {σ : equiv.perm ι}
  (hσ : {x | σ x ≠ x} ⊆ s) : monovary_on f g s ↔ monovary_on (f ∘ σ) (g ∘ σ) s :=
begin
  convert perm_iff σ,
  rw equiv.perm.image_set_eq hσ
end

lemma exists_perm_monovary_on [linear_order ι] [linear_order α] [linear_order β] (s : finset ι) :
  ∃ σ : equiv.perm ι, {x | σ x ≠ x} ⊆ s ∧ monovary_on (f ∘ σ) g s :=
begin
  rcases s.exists_monotone_perm g with ⟨τ, hτs, hτ⟩,
  rcases s.exists_monotone_perm f with ⟨π, hπs, hπ⟩,
  set σ : equiv.perm ι :=
  begin
    refine ⟨π ∘ τ.symm, τ ∘ π.symm,λ x, _ ,λ x, _⟩;
    simp
  end with hσ,
  have hσs : {x | σ x ≠ x} ⊆ s := equiv.perm.set_subset_of_subset hπs _,
  refine ⟨σ, hσs, _⟩,
  rw [perm_iff_of_support_subset hτs, hσ],
  convert (hπ.monovary_on hτ) using 1,
  { ext; simp },
  { convert hτs using 1,
    rw ← equiv.perm.set_support_inv_eq τ,
    congr }
end

end monovary_on
