import Mathlib

/-!
# The Frobenius endomorphism on a finite field

Elementary facts about the Frobenius map `x ↦ x^{p^r}` on a finite field `F` of
characteristic `p`, together with the companion "coprime power permutation".
These are the reusable finite-field building blocks used throughout the
development; nothing here is specific to Kasami polynomials.

* `frob_cycle`        — `x^{|F|} = x` (Fermat's little theorem for fields);
* `frob_mod`          — `x^{p^r}` depends only on `r mod n` when `|F| = pⁿ`;
* `frob_bijective`    — every Frobenius power `x ↦ x^{p^r}` is a permutation;
* `pow_field_bijective` — `x ↦ x^a` is a permutation whenever `gcd(|F|−1, a) = 1`.

(The names were previously in the `DempwolffMueller` prerequisites file.)
-/

namespace Kasami.FiniteField

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

/-- Fermat's little theorem for fields: `x^{|F|} = x`. -/
lemma frob_cycle (x : F) : x ^ Fintype.card F = x := FiniteField.pow_card x

omit hp [CharP F p] in
/-- `x^{p^r}` is periodic in `r` with period `n` when `|F| = pⁿ`. -/
lemma frob_mod {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (r : ℕ) :
    x ^ (p ^ r) = x ^ (p ^ (r % n)) := by
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
    pow_add, pow_mul]
  have : ∀ k : ℕ, x ^ (p ^ (n * k)) = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ← hn, frob_cycle, ih]
  rw [this]

/-- Every Frobenius power `x ↦ x^{p^r}` is a permutation of `F`. -/
lemma frob_bijective (r : ℕ) : Function.Bijective (fun x : F => x ^ (p ^ r)) :=
  ⟨iterateFrobenius_inj F p r,
   (Finite.injective_iff_surjective).mp (iterateFrobenius_inj F p r)⟩

omit hp [CharP F p] in
/-- The coprime-power permutation: `x ↦ x^a` is a bijection whenever `a` is
coprime to `|F| − 1` (and positive). -/
lemma pow_field_bijective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a)
    (ha_pos : 0 < a) :
    Function.Bijective (fun x : F => x ^ a) := by
  obtain ⟨b, hb⟩ : ∃ b, a * b ≡ 1 [MOD (Fintype.card F - 1)] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime ha.symm;
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
    grind +splitIndPred;
  have h_exp : ∀ x : F, x ≠ 0 → x ^ (a * b) = x := by
    intro x hx; rw [ ← Nat.mod_add_div ( a * b ) ( Fintype.card F - 1 ), hb ] ; simp +decide [ pow_add, pow_mul ] ;
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
    · have := FiniteField.pow_card_sub_one_eq_one x; aesop;
    · have := FiniteField.pow_card_sub_one_eq_one x; simp_all +decide [ pow_succ' ] ;
  have h_inj : Function.Injective (fun x : F => x ^ a) := by
    intro x y hxy;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ pow_mul ];
    · rw [ zero_pow ha_pos.ne', eq_comm ] at hxy ; aesop;
    · cases a <;> simp_all +decide;
    · rw [ ← h_exp x hx, ← h_exp y hy, hxy ];
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

end Kasami.FiniteField
