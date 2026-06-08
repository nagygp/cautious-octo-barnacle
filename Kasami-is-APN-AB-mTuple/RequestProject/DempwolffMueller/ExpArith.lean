import Mathlib
import RequestProject.DempwolffMueller.FrobAlg

/-!
# Foundational Layer F3: Exponent Arithmetic Engine

Units group facts, power map bijectivity, Mersenne GCD, congruent exponents.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- F3.1 : Units group
-- ═══════════════════════════════════════════

omit hp [CharP F p] in
lemma card_units_eq : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units F

omit hp [CharP F p] in
lemma units_pow_card_sub_one (u : Fˣ) : u ^ (Fintype.card F - 1) = 1 := by
  rw [← card_units_eq]; exact pow_card_eq_one

/-
═══════════════════════════════════════════
F3.2 : Power map bijectivity
═══════════════════════════════════════════
-/
omit hp [CharP F p] in
lemma pow_field_bijective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a)
    (ha_pos : 0 < a) :
    Function.Bijective (fun x : F => x ^ a) := by
  obtain ⟨b, hb⟩ : ∃ b, a * b ≡ 1 [MOD (Fintype.card F - 1)] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime ha.symm;
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
    grind +splitIndPred;
  have h_exp : ∀ x : F, x ≠ 0 → x ^ (a * b) = x := by
    intro x hx; rw [ ← Nat.mod_add_div ( a * b ) ( Fintype.card F - 1 ), hb ] ; simp +decide [ pow_add, pow_mul, hx ] ;
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc ];
    · have := FiniteField.pow_card_sub_one_eq_one x; aesop;
    · have := FiniteField.pow_card_sub_one_eq_one x; simp_all +decide [ pow_succ', mul_assoc ] ;
  have h_inj : Function.Injective (fun x : F => x ^ a) := by
    intro x y hxy;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ pow_mul ];
    · rw [ zero_pow ha_pos.ne', eq_comm ] at hxy ; aesop;
    · cases a <;> simp_all +decide;
    · rw [ ← h_exp x hx, ← h_exp y hy, hxy ];
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

-- ═══════════════════════════════════════════
-- F3.3 : Inverse power
-- ═══════════════════════════════════════════

lemma pow_pow_eq_self {a b : ℕ}
    (hab : a * b % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    {x : F} (hx : x ≠ 0) : (x ^ a) ^ b = x := by
  rw [← pow_mul]
  exact (pow_eq_pow_of_mod_eq hx hab).trans (pow_one x)

-- ═══════════════════════════════════════════
-- F3.4 : Mersenne GCD
-- ═══════════════════════════════════════════

omit [Fintype F] hp [CharP F p] in
lemma mersenne_gcd (p' a b : ℕ) :
    Nat.gcd (p' ^ a - 1) (p' ^ b - 1) = p' ^ Nat.gcd a b - 1 :=
  Nat.pow_sub_one_gcd_pow_sub_one p' a b

omit [Fintype F] hp [CharP F p] in
lemma mersenne_coprime_two {a b : ℕ} (hab : Nat.Coprime a b) :
    Nat.Coprime (2 ^ a - 1) (2 ^ b - 1) := by
  show Nat.gcd _ _ = 1; rw [mersenne_gcd, hab]; simp

/-
═══════════════════════════════════════════
F3.6 : Arithmetic identity
═══════════════════════════════════════════
-/
omit [Fintype F] hp [CharP F p] in
lemma two_k_add_eq {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m < n) :
    2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) = 2 ^ n - 1 := by
  zify at *;
  rcases n with ( _ | n ) <;> rcases m with ( _ | m ) <;> norm_num [ pow_succ' ] at *;
  rw [ Nat.sub_sub, Nat.cast_sub ] <;> push_cast <;> linarith [ pow_pos ( by decide : 0 < 2 ) m, pow_lt_pow_right₀ ( by decide : 1 < 2 ) hmn ]

end DempwolffMueller
