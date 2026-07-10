import Mathlib

/-!
# Equation (1) MVP — finite-field prerequisites (`DempwolffMueller`)

This module collects the **minimal** set of finite-field lemmas from the
`DempwolffMueller` layer that are actually used, end to end, by the proof of
**equation (1)** in the proof of Dobbertin's Theorem 1:

* Frobenius cycling `frob_cycle`, periodicity `frob_mod`, and bijectivity
  `frob_bijective` (from `FiniteField/FrobAlg.lean`);
* the coprime-power bijection `pow_field_bijective` (from `FiniteField/ExpArith.lean`);
* the truncated trace `truncTrace`, its additivity `truncTrace_add`, and the
  telescoping identity `truncTrace_sq_add_self` (from `FiniteField/Thm32.lean`).

Every declaration here is copied verbatim from the original library files; only
the ones on the dependency path of equation (1) are retained.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

lemma frob_cycle (x : F) : x ^ Fintype.card F = x := FiniteField.pow_card x
omit hp [CharP F p] in
lemma frob_mod {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (r : ℕ) :
    x ^ (p ^ r) = x ^ (p ^ (r % n)) := by
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
    pow_add, pow_mul]
  have : ∀ k : ℕ, x ^ (p ^ (n * k)) = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ← hn, frob_cycle, ih]
  rw [this]

lemma frob_bijective (r : ℕ) : Function.Bijective (fun x : F => x ^ (p ^ r)) :=
  ⟨iterateFrobenius_inj F p r,
   (Finite.injective_iff_surjective).mp (iterateFrobenius_inj F p r)⟩

omit hp [CharP F p] in
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

/-- The truncated trace map L(x) = ∑_{i=0}^{m-1} x^{2^i}. -/
def truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

lemma truncTrace_add {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x y : F) :
    truncTrace m (x + y) = truncTrace m x + truncTrace m y := by
  simp only [truncTrace, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_char_pow (p := 2) (n := i) x y

lemma truncTrace_sq_add_self {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (x : F) :
    truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x := by
  unfold truncTrace; induction m <;> simp_all +decide [ Finset.sum_range_succ, pow_succ ] ; ring;
  · rw [ mul_two, CharTwo.add_self_eq_zero ];
  · simp_all +decide [ add_mul, mul_add, pow_mul ] ; ring;
    simp_all +decide [ CharTwo.two_eq_zero ];
    simp_all +decide [ add_comm, add_left_comm, add_assoc, sq ];
    simp_all +decide [ ← add_assoc, ← two_mul, CharTwo.two_eq_zero ]

end DempwolffMueller
