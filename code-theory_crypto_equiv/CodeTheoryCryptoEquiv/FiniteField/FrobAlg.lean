import Mathlib
import CodeTheoryCryptoEquiv.FiniteField.AutBase

/-!
# Foundational Layer F1: Frobenius Operator Algebra

Frobenius cycling, periodicity, linearized polynomial identities,
and Frobenius-composition preserves bijection.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- F1.1 : Frobenius cycling
-- ═══════════════════════════════════════════

lemma frob_cycle (x : F) : x ^ Fintype.card F = x := FiniteField.pow_card x

lemma frob_periodic {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (k : ℕ) :
    x ^ (p ^ (n + k)) = x ^ (p ^ k) := by
  rw [pow_add, pow_mul, ← hn, frob_cycle]

lemma frob_mod {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (r : ℕ) :
    x ^ (p ^ r) = x ^ (p ^ (r % n)) := by
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
    pow_add, pow_mul]
  have : ∀ k : ℕ, x ^ (p ^ (n * k)) = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ← hn, frob_cycle, ih]
  rw [this]

-- ═══════════════════════════════════════════
-- F1.2 : Frobenius as ring homomorphism
-- ═══════════════════════════════════════════

lemma mul_frob_eq (a b : F) (r : ℕ) :
    (a * b) ^ (p ^ r) = a ^ (p ^ r) * b ^ (p ^ r) := mul_pow a b _

lemma add_frob_eq (a b : F) (r : ℕ) :
    (a + b) ^ (p ^ r) = a ^ (p ^ r) + b ^ (p ^ r) :=
  add_pow_char_pow (p := p) (n := r) a b

lemma finset_sum_frob_eq {ι : Type*} (s : Finset ι) (f : ι → F) (r : ℕ) :
    (∑ i ∈ s, f i) ^ (p ^ r) = ∑ i ∈ s, (f i) ^ (p ^ r) := by
  simp_rw [← show ∀ x : F, (iterateFrobenius F p r) x = x ^ (p ^ r) from
    fun x => by simp [iterateFrobenius]]
  rw [← map_sum]

lemma neg_frob_eq (a : F) (r : ℕ) :
    (-a) ^ (p ^ r) = -(a ^ (p ^ r)) := by
  have : (iterateFrobenius F p r) (-a) = -(iterateFrobenius F p r a) := map_neg _ _
  simp only [iterateFrobenius] at this; exact this

-- ═══════════════════════════════════════════
-- F1.3 : Frobenius on linearized polynomials (output)
-- ═══════════════════════════════════════════

lemma linpoly_frob_output (n : ℕ) (coeffs : Fin n → F) (x : F) (s : ℕ) :
    (additivePolyEval p n coeffs x) ^ (p ^ s) =
    ∑ i : Fin n, (coeffs i) ^ (p ^ s) * x ^ (p ^ ((i : ℕ) + s)) := by
  rw [additivePolyEval, finset_sum_frob_eq]
  congr 1; ext i
  rw [mul_frob_eq, ← pow_mul, ← pow_add]

lemma truncTrace_frob_output_general (m : ℕ) (x : F) (s : ℕ) :
    (∑ i ∈ Finset.range m, x ^ (p ^ i)) ^ (p ^ s) =
    ∑ i ∈ Finset.range m, x ^ (p ^ (i + s)) := by
  induction m with
  | zero => simp [zero_pow (Nat.pos_of_ne_zero (pow_ne_zero s hp.out.ne_zero)).ne']
  | succ m ih =>
    rw [Finset.sum_range_succ, add_pow_char_pow (p := p) (n := s), ih,
        Finset.sum_range_succ, ← pow_mul, ← pow_add]

-- ═══════════════════════════════════════════
-- F1.4 : Frobenius on linearized polynomials (input)
-- ═══════════════════════════════════════════

lemma linpoly_frob_input (n : ℕ) (coeffs : Fin n → F) (x : F) (s : ℕ) :
    additivePolyEval p n coeffs (x ^ (p ^ s)) =
    ∑ i : Fin n, coeffs i * x ^ (p ^ (s + (i : ℕ))) := by
  simp only [additivePolyEval, ← pow_mul, ← pow_add]

lemma linpoly_frob_comm (n : ℕ) (coeffs : Fin n → F) (x : F) (s : ℕ)
    (hcoeffs : ∀ i : Fin n, (coeffs i) ^ (p ^ s) = coeffs i) :
    additivePolyEval p n coeffs (x ^ (p ^ s)) =
    (additivePolyEval p n coeffs x) ^ (p ^ s) := by
  rw [linpoly_frob_input, linpoly_frob_output]
  congr 1; ext i; rw [hcoeffs, add_comm]

-- ═══════════════════════════════════════════
-- F1.5 : Frobenius preserves bijection
-- ═══════════════════════════════════════════

lemma frob_bijective (r : ℕ) : Function.Bijective (fun x : F => x ^ (p ^ r)) :=
  ⟨iterateFrobenius_inj F p r,
   (Finite.injective_iff_surjective).mp (iterateFrobenius_inj F p r)⟩

lemma frob_comp_bijective_right {f : F → F} (hf : Function.Bijective f) (r : ℕ) :
    Function.Bijective (fun x : F => (f x) ^ (p ^ r)) :=
  (frob_bijective p r).comp hf

lemma frob_comp_bijective_left {f : F → F} (hf : Function.Bijective f) (r : ℕ) :
    Function.Bijective (fun x : F => f (x ^ (p ^ r))) :=
  hf.comp (frob_bijective p r)

-- ═══════════════════════════════════════════
-- F1.6 : Key Frobenius-bijection transfer
-- ═══════════════════════════════════════════

lemma linpoly_mul_pow_frob (n : ℕ) (coeffs : Fin n → F)
    (k : ℕ) (x : F) (s : ℕ) :
    (additivePolyEval p n coeffs x * x ^ k) ^ (p ^ s) =
    (additivePolyEval p n coeffs x) ^ (p ^ s) * x ^ (k * p ^ s) := by
  rw [mul_pow, ← pow_mul]

lemma linpoly_mul_pow_frob_bijective (n : ℕ) (coeffs : Fin n → F) (k : ℕ)
    (hbij : Function.Bijective (fun x : F => additivePolyEval p n coeffs x * x ^ k))
    (s : ℕ) :
    Function.Bijective (fun x : F =>
      (additivePolyEval p n coeffs x) ^ (p ^ s) * x ^ (k * p ^ s)) := by
  have : Function.Bijective (fun x : F =>
      (additivePolyEval p n coeffs x * x ^ k) ^ (p ^ s)) :=
    frob_comp_bijective_right p hbij s
  convert this using 1
  ext x; exact (linpoly_mul_pow_frob p n coeffs k x s).symm

-- ═══════════════════════════════════════════
-- F1.7 : GF(p) coefficient stability
-- ═══════════════════════════════════════════

lemma gfp_frob_stable {c : F} (hc : c ^ p = c) (r : ℕ) :
    c ^ (p ^ r) = c := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, pow_mul, ih, hc]

lemma one_frob_stable (r : ℕ) : (1 : F) ^ (p ^ r) = 1 := one_pow _

-- ═══════════════════════════════════════════
-- F1.8 : Fermat's little theorem for power maps
-- ═══════════════════════════════════════════

lemma pow_card_sub_one_eq_one' {x : F} (hx : x ≠ 0) :
    x ^ (Fintype.card F - 1) = 1 :=
  FiniteField.pow_card_sub_one_eq_one x hx

lemma pow_mod_card_sub_one {x : F} (hx : x ≠ 0) (a : ℕ) :
    x ^ a = x ^ (a % (Fintype.card F - 1)) := by
  have hord := orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx)
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x (a % (Fintype.card F - 1))]
  congr 1; exact (Nat.mod_mod_of_dvd a hord).symm

lemma pow_eq_pow_of_mod_eq {x : F} (hx : x ≠ 0) {a b : ℕ}
    (hab : a % (Fintype.card F - 1) = b % (Fintype.card F - 1)) :
    x ^ a = x ^ b := by
  have hord := orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx)
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x b]; congr 1
  rw [show a % orderOf x = a % (Fintype.card F - 1) % orderOf x from
      (Nat.mod_mod_of_dvd a hord).symm,
    show b % orderOf x = b % (Fintype.card F - 1) % orderOf x from
      (Nat.mod_mod_of_dvd b hord).symm, hab]

end DempwolffMueller
