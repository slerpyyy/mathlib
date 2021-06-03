/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import analysis.special_functions.exp_log
import analysis.special_functions.pow

/-!
# Szemerédi's Regularity Lemma

In this file, we define edge density, equipartitions, and prove Szemerédi's Regularity Lemma.
-/

universe u

open_locale big_operators
open finset fintype

/-! ### Things that belong to mathlib -/

lemma prod_quotient_sym2_not_diag {α : Type u} [decidable_eq α] (s : finset α) :
  (finset.filter (λ (a : sym2 α), ¬a.is_diag) (finset.image quotient.mk (s.product s))).card =
    s.card.choose 2 :=
begin
  let ordered_pairs : finset (α × α) := (s.product s).filter (λ (x : α × α), ¬(x.1 = x.2)),
  have : ordered_pairs.card = s.card * (s.card - 1),
  { rw [nat.mul_sub_left_distrib, mul_one],
    change finset.card (finset.filter _ _) = _,
    rw [finset.filter_not, card_sdiff (filter_subset _ _), finset.card_product],
    congr' 1,
    refine finset.card_congr (λ (x : _ × _) _, x.1) _ _ _,
    { rintro ⟨x, y⟩ h,
      simp only [mem_filter, mem_product] at h,
      apply h.1.1 },
    { simp only [true_and, prod.forall, mem_filter, mem_product],
      rintro a b ⟨x, y⟩ ⟨⟨_, _⟩, rfl⟩ ⟨_, rfl : x = y⟩ (rfl : a = x),
      refl },
    { simp only [exists_prop, mem_filter, imp_self, exists_and_distrib_right, implies_true_iff,
        exists_eq_right, exists_eq_right', and_self, prod.exists, mem_product] } },
  rw [nat.choose_two_right, ←this],
  symmetry,
  apply nat.div_eq_of_eq_mul_right (show 0 < 2, by norm_num),
  have : ∀ x ∈ ordered_pairs,
    quotient.mk x ∈ ((s.product s).image quotient.mk).filter (λ (a : sym2 α), ¬a.is_diag),
  { rintro ⟨x, y⟩ hx,
    simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
      prod.exists, mem_product],
    simp only [mem_filter, mem_product] at hx,
    refine ⟨⟨_, _, hx.1, or.inl ⟨rfl, rfl⟩⟩, hx.2⟩ },
  rw [card_eq_sum_card_fiberwise this, finset.sum_const_nat, mul_comm],
  refine quotient.ind _,
  rintro ⟨x, y⟩ hxy,
  simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
    prod.exists, mem_product] at hxy,
  have : x ∈ s ∧ y ∈ s,
  { rcases hxy with ⟨⟨x, y, ⟨_, _⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _⟩;
    refine ⟨‹_›, ‹_›⟩ },
  have : filter (λ (z : α × α), ⟦z⟧ = ⟦(x, y)⟧) ordered_pairs = ({(x,y), (y,x)} : finset _),
  { ext ⟨x₁, y₁⟩,
    simp only [true_and, mem_filter, mem_insert, mem_product, mem_singleton, sym2.eq_iff,
      and_iff_right_iff_imp, prod.mk.inj_iff],
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
    { refine ⟨‹_›, hxy.2⟩, },
    refine ⟨⟨this.2, this.1⟩, ne.symm hxy.2⟩ },
  rw [this, card_insert_of_not_mem, card_singleton],
  simp only [not_and, prod.mk.inj_iff, mem_singleton],
  rintro rfl,
  apply hxy.2
end

lemma card_sym2_not_diag {α : Type u} [decidable_eq α] [fintype α] :
  (univ.filter (λ (a : sym2 α), ¬a.is_diag)).card = (card α).choose 2 :=
prod_quotient_sym2_not_diag (univ : finset α)

lemma sym2.injective {α : Type u} : function.injective (sym2.diag : α → sym2 α) :=
begin
  rintro x y (h : ⟦_⟧ = ⟦_⟧),
  rw sym2.eq_iff at h,
  simpa using h
end

lemma card_sym2 {α : Type u} [decidable_eq α] [fintype α] :
  card (sym2 α) = card α * (card α + 1) / 2 :=
begin
  have : univ.filter (λ (x : sym2 α), x.is_diag) = univ.image sym2.diag,
  { ext,
    simp [sym2.is_diag] },
  rw [←finset.card_univ, ←filter_union_filter_neg_eq sym2.is_diag (univ : finset (sym2 α)),
    card_disjoint_union, this, card_image_of_injective _ sym2.injective, card_sym2_not_diag,
    nat.choose_two_right, finset.card_univ, add_comm, ←nat.triangle_succ, nat.succ_sub_one,
    mul_comm],
  rw disjoint_iff_inter_eq_empty,
  apply filter_inter_filter_neg_eq,
end

lemma between_nat_iff {a t : ℕ} :
  (a = t ∨ a = t+1) ↔ (t ≤ a ∧ a ≤ t+1) :=
begin
  split,
  { rintro (rfl | rfl);
    simp },
  rintro ⟨h₁, h₂⟩,
  obtain h | h := h₁.eq_or_lt,
  { exact or.inl h.symm },
  exact or.inr (le_antisymm h₂ (nat.succ_le_of_lt h)),
end

/-! ### Prerequisites for SRL -/

/-- A set is equitable if no element value is more than one bigger than another. -/
def equitable_on {α : Type*} (s : set α) (f : α → ℕ) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ → f a₂ - f a₁ ≤ 1

@[simp]
lemma equitable_on_empty {α : Type*} (f : α → ℕ) :
  equitable_on ∅ f :=
by simp [equitable_on]

lemma equitable_on_iff {α : Type*} (s : set α) (f : α → ℕ) :
  equitable_on s f ↔ ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₂ - f a₁ ≤ 1 :=
begin
  split,
  { intros hf a₁ a₂ ha₁ ha₂,
    cases le_total (f a₁) (f a₂),
    { apply hf ha₁ ha₂ h },
    rw nat.sub_eq_zero_of_le h,
    apply zero_le_one },
  intros hf a₁ a₂ ha₁ ha₂ _,
  apply hf ha₁ ha₂
end

lemma equitable_iff_almost_eq_constant {α : Type*} (s : set α) (f : α → ℕ) :
  equitable_on s f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 :=
begin
  classical,
  split,
  { rw equitable_on_iff,
    rcases s.eq_empty_or_nonempty with rfl | hs,
    { simp },
    { intros h,
      refine ⟨nat.find (set.nonempty.image f hs), _⟩,
      obtain ⟨w, hw₁, hw₂⟩ := nat.find_spec (set.nonempty.image f hs),
      intros a ha,
      have : nat.find (set.nonempty.image f hs) ≤ f a := nat.find_min' _ ⟨_, ha, rfl⟩,
      cases eq_or_lt_of_le this with q q,
      { exact or.inl q.symm },
      { refine or.inr (le_antisymm _ (nat.succ_le_of_lt q)),
        rw [←hw₂, ←nat.sub_le_left_iff_le_add],
        apply h hw₁ ha } } },
  { rintro ⟨b, hb⟩ x₁ x₂ hx₁ hx₂ h,
    rcases hb x₁ hx₁ with rfl | hx₁';
    cases hb x₂ hx₂ with hx₂' hx₂',
    { simp [hx₂'] },
    { simp [hx₂'] },
    { simpa [hx₁', hx₂'] using h },
    { simp [hx₁', hx₂'] } }
end

lemma equitable_on_finset_iff_eq_average {α : Type*} (s : finset α) (f : α → ℕ) :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 :=
begin
  rw equitable_iff_almost_eq_constant,
  split,
  { rintro ⟨b, hb⟩,
    by_cases h : ∀ a ∈ s, f a = b+1,
    { clear hb,
      intros a ha,
      left,
      symmetry,
      apply nat.div_eq_of_eq_mul_left (finset.card_pos.2 ⟨_, ha⟩),
      rw [mul_comm, sum_const_nat],
      intros c hc,
      rw [h _ ha, h _ hc] },
    { suffices : b = (∑ i in s, f i) / s.card,
      { simp_rw [←this],
          apply hb },
      simp_rw between_nat_iff at hb,
      symmetry,
      apply nat.div_eq_of_lt_le,
      { apply le_trans _ (sum_le_sum (λ a ha, (hb a ha).1)),
        simp [mul_comm] },
      push_neg at h,
      rcases h with ⟨x, hx₁, hx₂⟩,
      apply (sum_lt_sum (λ a ha, (hb a ha).2) ⟨_, hx₁, lt_of_le_of_ne (hb _ hx₁).2 hx₂⟩).trans_le,
      rw [mul_comm, sum_const_nat],
      simp } },
  { intro h,
    refine ⟨_, h⟩ }
end

lemma equitable_on_finset_iff {α : Type*} (s : finset α) (f : α → ℕ) :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 :=
begin
  rw equitable_on_finset_iff_eq_average,
  simp_rw [between_nat_iff],
end

namespace simple_graph
variables {V : Type u} [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj]

/-- Finset of edges between two finsets of vertices -/
def edges_pair_finset (U W : finset V) : finset (V × V) :=
(U.product W).filter (λ e, G.adj e.1 e.2)

lemma mem_edges_pair_finset (U W : finset V) (x : V × V) :
  x ∈ G.edges_pair_finset U W ↔ x.1 ∈ U ∧ x.2 ∈ W ∧ G.adj x.1 x.2 :=
by simp [edges_pair_finset, and_assoc]

lemma mem_edges_pair_finset' (U W : finset V) (x y : V) :
  (x, y) ∈ G.edges_pair_finset U W ↔ x ∈ U ∧ y ∈ W ∧ G.adj x y :=
mem_edges_pair_finset _ _ _ _

/-- Number of edges between two finsets of vertices -/
def edges_count_pair (U W : finset V) : ℕ :=
(G.edges_pair_finset U W).card

lemma edges_count_pair_symm (U W : finset V) :
  G.edges_count_pair U W = G.edges_count_pair W U :=
begin
  apply finset.card_congr (λ (i : V × V) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    simp only [mem_edges_pair_finset'] at h ⊢,
    rwa [G.edge_symm, and.left_comm] },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    rcases h,
    refl },
  rintro ⟨i₁, j₁⟩ h,
  refine ⟨⟨j₁, i₁⟩, _, rfl⟩,
  simp only [mem_edges_pair_finset'] at h ⊢,
  rwa [G.edge_symm, and.left_comm],
end

/-- Number of edges between a pair of finsets of vertices. `sym2` variant of `edges_count_pair`. -/
def edges_count_sym2 : sym2 (finset V) → ℕ :=
quotient.lift (function.uncurry (edges_count_pair G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply edges_count_pair_symm })

/-- Edge density between two finsets of vertices -/
noncomputable def density_pair (U W : finset V) : ℝ :=
G.edges_count_pair U W / (U.card * W.card)

lemma density_pair_symm (U W : finset V) : G.density_pair U W = G.density_pair W U :=
begin
  rw [density_pair, mul_comm, edges_count_pair_symm],
  refl
end

lemma density_pair_nonneg (U W : finset V) :
  0 ≤ G.density_pair U W :=
begin
  apply div_nonneg;
  exact_mod_cast nat.zero_le _,
end

lemma density_pair_le_one (U W : finset V) :
  G.density_pair U W ≤ 1 :=
begin
  refine div_le_one_of_le _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
  norm_cast,
  rw [edges_count_pair, edges_pair_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

/-- Edge density between a pair of finsets of vertices. `sym2` variant of `density_pair`. -/
noncomputable def density_sym2 : sym2 (finset V) → ℝ :=
quotient.lift (function.uncurry (density_pair G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply density_pair_symm })

lemma density_sym2_nonneg (s : sym2 (finset V)) :
  0 ≤ G.density_sym2 s :=
quotient.induction_on s (λ xy, density_pair_nonneg _ _ _)

lemma density_sym2_le_one (s : sym2 (finset V)) :
  G.density_sym2 s ≤ 1 :=
quotient.induction_on s (λ xy, density_pair_le_one _ _ _)

/-- A pair of finsets of vertices is ε-uniform iff their edge density is close to the density of any
big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (ε : ℝ) (U W : finset V) : Prop :=
∀ U', U' ⊆ U → ∀ W', W' ⊆ W → ε * U.card ≤ U'.card → ε * W.card ≤ W'.card →
abs (density_pair G U' W' - density_pair G U W) < ε

/-- If the pair `(U,W)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
lemma is_uniform_mono {ε ε' : ℝ} {U W : finset V} (h : ε ≤ ε') (hε : is_uniform G ε U W) :
  is_uniform G ε' U W :=
begin
  intros U' hU' W' hW' hU hW,
  apply (hε _ hU' _ hW' (le_trans _ hU) (le_trans _ hW)).trans_le h;
  apply mul_le_mul_of_nonneg_right h (nat.cast_nonneg _),
end

lemma is_uniform_symmetric (ε : ℝ) : symmetric (is_uniform G ε) :=
begin
  intros U W h W' hW' U' hU' hW hU,
  rw density_pair_symm _ W',
  rw density_pair_symm _ W,
  apply h _ hU' _ hW' hU hW,
end

/-- `sym2` variant of `is_uniform` -/
def is_uniform_sym2 (ε : ℝ) : sym2 (finset V) → Prop :=
sym2.from_rel (is_uniform_symmetric G ε)

end simple_graph

/-- An equipartition of a type `V` is a partition whose maximal part has size at most one more than
the size of the minimal part. This is enforced using `equitable_on`. -/
structure equipartition (V : Type u) [decidable_eq V] :=
(parts : finset (finset V))
(disjoint : ∀ (a₁ a₂ ∈ parts) x, x ∈ a₁ → x ∈ a₂ → a₁ = a₂)
(covering : ∀ v, ∃ (a ∈ parts), v ∈ a) -- TODO: add a lemma saying the union is everything
(sizes : equitable_on (parts : set (finset V)) card)

namespace equipartition
variables {V : Type u} [decidable_eq V] (P : equipartition V)

/-lemma Union_eq_univ : (⋃ (s : finset V) (s ∈ P.parts), s) : set V) = set.univ :=
begin

end-/

lemma ext (P Q : equipartition V) : P.parts = Q.parts → P = Q :=
by { cases P, cases Q, intro h, congr' 1 }

/-- The size of an equipartition is its number of parts. -/
protected def size : ℕ := P.parts.card

/-- `sym2` variant of `equipartition.parts`. We exclude the diagonal, as these do not make sense nor
behave well in the context of Szemerédi's Regularity Lemma. -/
def distinct_unordered_parts_pairs [fintype V] (P : equipartition V) :
  finset (sym2 (finset V)) :=
((P.parts.product P.parts).image quotient.mk).filter (λ (a : sym2 _), ¬a.is_diag)

lemma mem_distinct_unordered_parts_pairs [fintype V] (P : equipartition V)
  (U W : finset V) :
  ⟦(U, W)⟧ ∈ P.distinct_unordered_parts_pairs ↔ U ∈ P.parts ∧ W ∈ P.parts ∧ U ≠ W :=
begin
  rw [equipartition.distinct_unordered_parts_pairs, finset.mem_filter],
  simp only [mem_image, exists_prop, sym2.is_diag_iff_proj_eq, sym2.eq_iff, prod.exists,
    mem_product],
  split,
  { rintro ⟨⟨U, W, ⟨_, _⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _⟩;
    exact ⟨‹_›, ‹_›, ‹_›⟩ },
  rintro ⟨h₁, h₂, h₃⟩,
  exact ⟨⟨_, _, ⟨h₁, h₂⟩, or.inl ⟨rfl, rfl⟩⟩, h₃⟩,
end

lemma distinct_unordered_parts_pairs_size [fintype V] (P : equipartition V) :
  P.distinct_unordered_parts_pairs.card = P.size.choose 2 :=
by rw [distinct_unordered_parts_pairs, equipartition.size, prod_quotient_sym2_not_diag]

variables (G : simple_graph V)
open_locale classical

noncomputable def non_uniform_parts [fintype V] (ε : ℝ) :
  finset (sym2 (finset V)) :=
P.distinct_unordered_parts_pairs.filter (λ a, ¬G.is_uniform_sym2 ε a)

/-- An equipartition is ε-uniform iff at most a proportion of ε of its pairs of parts are
not ε-uniform. -/
def is_uniform [fintype V] (ε : ℝ) : Prop :=
((P.non_uniform_parts G ε).card : ℝ) ≤ ε * P.size.choose 2

/-- The index is the auxiliary quantity that drives the induction process in the proof of
Szemerédi's Regularity Lemma (see `increment`). As long as we do not have a suitable equipartition,
we will find a new one that has an index greater than the previous one plus some fixed constant.
Then `index_le_half` ensures this process only happens finitely many times. -/
noncomputable def index [fintype V] (P : equipartition V) : ℝ :=
(∑ x in P.distinct_unordered_parts_pairs, G.density_sym2 x^2)/P.size^2

lemma index_nonneg [fintype V] (P : equipartition V) :
  0 ≤ P.index G :=
begin
  rw equipartition.index,
  refine div_nonneg _ (sq_nonneg _),
  rw ←finset.sum_const_zero,
  apply finset.sum_le_sum, -- this may be `apply` abuse
  exact λ _ _, sq_nonneg _,
end

-- TODO: generalise
lemma nat.choose_two_le_half_sq (n : ℕ) : (n.choose 2 : ℝ) ≤ n^2 / 2 :=
begin
  rw le_div_iff (show 0 < (2:ℝ), by norm_num),
  norm_cast,
  induction n with n ih,
  { simp },
  { rw [nat.choose_succ_succ, nat.choose_one_right, add_mul],
    apply le_trans (add_le_add_left ih _) _,
    rw [nat.succ_eq_one_add, add_sq, one_pow, add_assoc, mul_one, mul_comm 2 n],
    apply nat.le_add_left, }
end

lemma index_le_half [fintype V] (P : equipartition V) :
  P.index G ≤ 1/2 :=
begin
  rw equipartition.index,
  apply div_le_of_nonneg_of_le_mul (sq_nonneg _),
  { norm_num },
  suffices h : (∑ (x : sym2 (finset V)) in P.distinct_unordered_parts_pairs, G.density_sym2 x ^ 2) ≤
    P.distinct_unordered_parts_pairs.card,
  {
    apply h.trans,
    rw [distinct_unordered_parts_pairs_size, div_mul_eq_mul_div, one_mul],
    sorry
  },
  rw [finset.card_eq_sum_ones, sum_nat_cast, nat.cast_one],
  apply finset.sum_le_sum,
  rintro s _,
  rw [sq, ←abs_le_one_iff_mul_self_le_one, abs_eq_self.2 (G.density_sym2_nonneg _)],
  exact G.density_sym2_le_one _,
end

end equipartition

/-! ### Discrete and dummy equipartitions -/

/-- The discrete equipartition of a fintype is the partition in singletons. -/
@[simps]
def discrete_equipartition (V : Type*) [decidable_eq V] [fintype V] : equipartition V :=
{ parts := finset.univ.image singleton,
  disjoint :=
  begin
    simp only [mem_image, mem_univ, exists_true_left, exists_imp_distrib],
    rintro a₁ a₂ i ⟨⟩ rfl j ⟨⟩ rfl k,
    simp only [mem_singleton],
    rintro rfl rfl,
    refl
  end,
  covering := λ v, ⟨{v}, mem_image.2 ⟨v, mem_univ v, rfl⟩, finset.mem_singleton_self v⟩,
  sizes := λ a b,
  begin
    simp only [set.image_univ, set.mem_range, coe_univ, exists_imp_distrib, coe_image],
    rintro _ rfl _ rfl _,
    rw [card_singleton, card_singleton],
    exact zero_le_one,
  end }

namespace discrete_equipartition
variables {V : Type u} [decidable_eq V] [fintype V] (G : simple_graph V)

protected lemma size : (discrete_equipartition V).size = card V :=
begin
  change finset.card (finset.univ.image _) = _,
  rw [finset.card_image_of_injective, finset.card_univ],
  intros i j k,
  rwa singleton_inj at k,
end

open equipartition -- used for `rw non_uniform_parts at hUW`. Shouldn't be though...

lemma non_uniform_parts {ε : ℝ} (hε : 0 < ε) :
  (discrete_equipartition V).non_uniform_parts G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  intro x,
  apply quotient.induction_on x,
  rintro ⟨U, W⟩ hUW,
  rw [non_uniform_parts, finset.mem_filter, mem_distinct_unordered_parts_pairs,
    discrete_equipartition_parts, mem_image, mem_image] at hUW, --problem with `non_uniform_parts`
  apply hUW.2,
  rintro U' (hU' : U' ⊆ U) W' (hW' : W' ⊆ W) (hU : ε * U.card ≤ _) (hW : ε * W.card ≤ _),
  obtain ⟨⟨x, _, rfl⟩, ⟨y, _, rfl⟩, t⟩ := hUW.1,
  rw [card_singleton, nat.cast_one, mul_one] at hU hW,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hU',
  { rw [finset.card_empty, nat.cast_zero] at hU,
    exfalso,
    exact hε.not_le hU },
  obtain rfl | rfl := finset.subset_singleton_iff.1 hW',
  { rw [finset.card_empty, nat.cast_zero] at hW,
    exfalso,
    exact hε.not_le hW },
  rw [sub_self, abs_zero],
  exact hε,
end

lemma is_uniform {ε : ℝ} (hε : 0 < ε) :
  (discrete_equipartition V).is_uniform G ε :=
begin
  rw [is_uniform, discrete_equipartition.size, discrete_equipartition.non_uniform_parts _ hε,
    finset.card_empty, nat.cast_zero],
  exact mul_nonneg hε.le (nat.cast_nonneg _),
end

end discrete_equipartition

open encodable

/-- Arbitrary equipartition into `n` parts -/
@[simps]
noncomputable def dummy_equipartition (V : Type*) [decidable_eq V] [fintype V] (n : ℕ) : equipartition V :=
{ parts := finset.image (begin--first attempt. Wrong cut.
  intro k,
  refine finset.image _ (univ : finset (fin (fintype.card V - k * n))),
  intro i,
  haveI : encodable V := fintype.encodable V,
  apply list.nth_le (sorted_univ V) (k*n + i),
  rw length_sorted_univ,
  exact nat.add_lt_of_lt_sub_left i.2,
end) (finset.range n),
  disjoint :=
  begin
    simp only [mem_image],
    rintro a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩ x hxa hxb,
    rw [←ha, mem_image] at hxa,
    rw [←hb, mem_image] at hxb,
    obtain ⟨i, -, hi⟩ := hxa,
    obtain ⟨j, -, hj⟩ := hxb,
    sorry
  end,
  covering := λ v, sorry,
  sizes := λ a b,
  begin
    sorry
  end }

protected lemma dummy_equipartition.size {V : Type u} [decidable_eq V] [fintype V] {n : ℕ} :
  (dummy_equipartition V n).size = n :=
begin
  sorry, -- this is false in general
end

/-! ### The actual proof -/

/-- Auxiliary function to explicit the bound on the size of the equipartition in the proof of
Szemerédi's Regularity Lemma -/
def exp_bound (n : ℕ) : ℕ := n * 4^n

lemma le_exp_bound (n : ℕ) :
  n ≤ exp_bound n :=
nat.le_mul_of_pos_right (pow_pos (by norm_num) n)

/-- An explicit bound on the size of the equipartition in the proof of Szemerédi's Regularity Lemma
-/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
let t : ℕ := max l (⌈real.log (100 / ε^5) / real.log 4⌉ + 1).nat_abs,
    N : ℕ := exp_bound^[nat_ceil (4/ε^5)] t
 in N * 16^N

open_locale classical
variables {V : Type u} [fintype V] {G : simple_graph V} {P : equipartition V} {ε : ℝ}

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher index. This is helpful since the
index is bounded by a constant (see `index_le_half`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
theorem increment (hε : 100 < ε^5 * 4^P.size) (hPV : P.size * 16^P.size ≤ card V)
  (hPG : ¬P.is_uniform G ε) :
  ∃ (Q : equipartition V), Q.size = exp_bound P.size ∧ P.index G + ε^5 / 8 ≤ Q.index G :=
begin
  sorry
end

noncomputable def blowup_equipartition (hε : 100 < ε^5 * 4^P.size)
  (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  equipartition V :=
classical.some (increment hε hPV hPG)

namespace blowup_equipartition

protected lemma size (hε : 100 < ε^5 * 4^P.size)
  (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  (blowup_equipartition hε hPV hPG).size = exp_bound P.size :=
(classical.some_spec (increment hε hPV hPG)).1

protected lemma index (hε : 100 < ε^5 * 4^P.size)
  (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  P.index G + ε^5 / 8 ≤ (blowup_equipartition hε hPV hPG).index G :=
(classical.some_spec (increment hε hPV hPG)).2

protected lemma size_le_size (hε : 100 < ε^5 * 4^P.size)
  (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  P.size ≤ (blowup_equipartition hε hPV hPG).size :=
by { rw blowup_equipartition.size hε hPV hPG, exact le_exp_bound _ }

end blowup_equipartition


open discrete_equipartition

--have the problem that I must prove stuff (namely the equivalent of `hl`) while defining data
/-- The equipartition refinement operation -/
noncomputable def szemeredi_equipartition (G : simple_graph V) (ε : ℝ) (l : ℕ) :
  ℕ → equipartition V
| 0       := dummy_equipartition V l
| (n + 1) := dite (100 < ε ^ 5 * 4^(szemeredi_equipartition n).size ∧
  (szemeredi_equipartition n).size * 16^(szemeredi_equipartition n).size ≤ card V
  ∧ ¬(szemeredi_equipartition n).is_uniform G ε)
  (λ h, blowup_equipartition h.1 h.2.1 h.2.2)
  (λ _, szemeredi_equipartition n)

namespace szemeredi_equipartition

lemma εl_condition {l : ℕ} (hε : 100 < ε ^ 5 * 4^l) :
  ∀ n : ℕ, 100 < ε ^ 5 * 4^(szemeredi_equipartition G ε l n).size
| 0       := begin
    rw [szemeredi_equipartition, dummy_equipartition.size],
    exact hε,
  end
| (n + 1) := begin
    rw szemeredi_equipartition,
    split_ifs, swap,
    { exact εl_condition n },
    refine lt_of_lt_of_le (εl_condition n) (mul_le_mul_of_nonneg_left
      (pow_le_pow (by norm_num) _)
      (nonneg_of_mul_nonneg_right (le_trans (by norm_num) hε.le) (pow_pos (by norm_num) _))),
    convert (le_exp_bound _),
    exact blowup_equipartition.size h.1 h.2.1 h.2.2,
  end

protected lemma size {ε : ℝ} {l n : ℕ} (hε : 100 < ε^5 * 4^l)
  (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  (szemeredi_equipartition G ε l n).size * 16^(szemeredi_equipartition G ε l n).size ≤ card V
  → ¬(szemeredi_equipartition G ε l n).is_uniform G ε
  → (szemeredi_equipartition G ε l n).size = nat.iterate exp_bound n l :=
begin
  induction n with n hn,
  { rintro _ _,
    rw [function.iterate_zero, id.def, szemeredi_equipartition],
    exact dummy_equipartition.size },
  rw szemeredi_equipartition,
  split_ifs,
  { rintro _ _,
    simp_rw [function.iterate_succ' exp_bound n, function.comp_app, ←hn h.2.1 h.2.2],
    exact blowup_equipartition.size h.1 h.2.1 h.2.2 },
  rintro h₁ h₂,
  exfalso,
  exact h ⟨εl_condition hε n, h₁, h₂⟩,
end

protected lemma index {ε : ℝ} {l n : ℕ} (hε : 100 < ε^5 * 4^l)
  (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  (szemeredi_equipartition G ε l n).size * 16^(szemeredi_equipartition G ε l n).size ≤ card V
  → ¬(szemeredi_equipartition G ε l n).is_uniform G ε
  → ε^5 / 8 * n ≤ (szemeredi_equipartition G ε l n).index G :=
begin
  induction n with n hn,
  { rw [nat.cast_zero, mul_zero],
    exact λ _ _, equipartition.index_nonneg G _ },
  rw szemeredi_equipartition,
  split_ifs,
  { simp only [nat.cast_succ, mul_add, mul_one],
    rintro _ _,
    apply (add_le_add_right (hn h.2.1 h.2.2) (ε^5/8)).trans,
    apply blowup_equipartition.index h.1 h.2.1 h.2.2 },
  rintro h₁ h₂,
  exfalso,
  exact h ⟨εl_condition hε n, h₁, h₂⟩,
end

lemma le_size (G : simple_graph V) (ε : ℝ) (l : ℕ) :
  ∀ n : ℕ, l ≤ (szemeredi_equipartition G ε l n).size
| 0       := by { rw szemeredi_equipartition, exact dummy_equipartition.size.ge }
| (n + 1) := begin
  rw szemeredi_equipartition,
  split_ifs,
  {
    sorry,
  },
  exact le_size n,
end

end szemeredi_equipartition

/-- Effective Szemerédi's regularity lemma: For any sufficiently big graph, there is an ε-uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε < 1) (l : ℕ) (hG : l ≤ card V) :
  ∃ (P : equipartition V), l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
begin
  cases le_total (card V) (szemeredi_bound ε l),
  { use discrete_equipartition V,
    rw discrete_equipartition.size,
    exact ⟨hG, h, discrete_equipartition.is_uniform G hε₁⟩ },
  refine ⟨szemeredi_equipartition G ε l (nat_ceil (4/ε^5)), szemeredi_equipartition.le_size G ε l _, _, _⟩,
  sorry,
  sorry
end
