/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import set_theory.cardinal

/-!
# Denumerability of ℚ

This file proves that ℚ is infinite, denumerable, and deduces that it has cardinality `omega`.
-/

namespace rat
open denumerable

instance : infinite ℚ :=
infinite.of_injective (coe : ℕ → ℚ) nat.cast_injective

private def denumerable_aux : ℚ ≃ { x : ℤ × ℕ // 0 < x.2 ∧ x.1.nat_abs.coprime x.2 } :=
{ to_fun := λ x, ⟨⟨x.1, x.2⟩, x.3, x.4⟩,
  inv_fun := λ x, ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩,
  left_inv := λ ⟨_, _, _, _⟩, rfl,
  right_inv := λ ⟨⟨_, _⟩, _, _⟩, rfl }

/-- **Denumerability of the Rational Numbers** -/
instance : denumerable ℚ :=
begin
  let T := { x : ℤ × ℕ // 0 < x.2 ∧ x.1.nat_abs.coprime x.2 },
  letI : infinite T := infinite.of_injective _ denumerable_aux.injective,
  letI : encodable T := subtype.encodable,
  letI : denumerable T := of_encodable_of_infinite T,
  exact denumerable.of_equiv T denumerable_aux
end

end rat

namespace cardinal

open_locale cardinal

@[simp] lemma mk_rat : #ℚ = ω := mk_denumerable ℚ

end cardinal
