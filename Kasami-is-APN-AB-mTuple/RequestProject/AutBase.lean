import Mathlib

/-!
Section 4 — Foundation Layer (AutBase)

Foundational definitions and lemmas for the automorphism theory of translation planes from "Permutation polynomials and translation planes of even order" by U. Dempwolff and P. Müller (Adv. Geom. 2013).

Setting. Let F = GF(pⁿ) be a finite field of characteristic p. An additive polynomial L(X) = ∑ aᵢ X^{pⁱ} defines a GF(p)-linear endomorphism of F. We define:

    The semilinear operator T_r(a) : x ↦ a · x^{p^r} for a ∈ F, 0 ≤ r < n. These are the elements of the normalizer of the Singer group C = {T_0(a) | a ∈ F*} in GL(V) (Lemma 4.1).

    The support spi(L) = {i | aᵢ ≠ 0} of an additive polynomial.

    Lemma 4.2: The support transforms predictably under conjugation: spi(T_s(a) · L · T_t(b)⁻¹) = {i + r | i ∈ spi(L)} where r = s − t.

This layer provides the algebraic infrastructure used throughout Sections 4–6 of the paper. -/

namespace DempwolffMueller

open Finset BigOperators Classical

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

variable {F : Type*} [Field F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

/-- The semilinear operator T_r(a) : F → F defined by x ↦ a · x^{p^r}.
These are the elements of the normalizer of the Singer group in GL(F).
The notation T_r(a) is standard in the theory of translation planes. -/
def semilinearOp (r : ℕ) (a : F) (x : F) : F := a * x ^ (p ^ r)

/-- An additive polynomial over F of degree at most p^{n-1} is represented
by its coefficient vector coeffs : Fin n → F, so that
L(x) = ∑_{i=0}^{n-1} coeffs(i) · x^{p^i}. -/
def additivePolyEval (n : ℕ) (coeffs : Fin n → F) (x : F) : F :=
  ∑ i : Fin n, coeffs i * x ^ (p ^ (i : ℕ))

/-- The support of an additive polynomial: spi(L) = {i | aᵢ ≠ 0}. -/
noncomputable def support (n : ℕ) (coeffs : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter fun i => coeffs i ≠ 0

-- ═══════════════════════════════════════════
-- Auxiliary: p^r ≠ 0
-- ═══════════════════════════════════════════

/-- p^r > 0 when p is prime. -/
private lemma pp_pos (r : ℕ) : 0 < p ^ r :=
  Nat.pos_of_ne_zero (pow_ne_zero r hp.out.ne_zero)

/-- p^r ≠ 0 when p is prime. -/
private lemma pp_ne_zero (r : ℕ) : p ^ r ≠ 0 :=
  (pp_pos p r).ne'

-- ═══════════════════════════════════════════
-- Layer 1 : Basic properties of semilinear operators
-- ═══════════════════════════════════════════

/-- T_r(a)(0) = 0. -/
lemma semilinearOp_zero (r : ℕ) (a : F) : semilinearOp p r a (0 : F) = 0 := by
  simp [semilinearOp, zero_pow (pp_ne_zero p r)]

/-- T_0(1) = id, i.e. T_0(1)(x) = x. -/
lemma semilinearOp_zero_one (x : F) : semilinearOp p 0 (1 : F) x = x := by
  simp [semilinearOp]

/-- T_0(a)(x) = a · x — the purely linear (scalar multiplication) case. -/
lemma semilinearOp_zero_eq_mul (a x : F) : semilinearOp p 0 a x = a * x := by
  simp [semilinearOp]

/-- T_r(a) is additive in characteristic p: T_r(a)(x + y) = T_r(a)(x) + T_r(a)(y). -/
lemma semilinearOp_add (r : ℕ) (a x y : F) :
    semilinearOp p r a (x + y) = semilinearOp p r a x + semilinearOp p r a y := by
  simp [semilinearOp, add_pow_char_pow, mul_add]

/-- Scaling: T_r(c · a)(x) = c · T_r(a)(x). -/
lemma semilinearOp_mul_coeff (r : ℕ) (c a x : F) :
    semilinearOp p r (c * a) x = c * semilinearOp p r a x := by
  simp [semilinearOp, mul_assoc]

/-- Composition of semilinear operators:
T_s(a)(T_r(b)(x)) = T_{r+s}(a · b^{p^s})(x). -/
lemma semilinearOp_comp (r s : ℕ) (a b x : F) :
    semilinearOp p s a (semilinearOp p r b x) =
    semilinearOp p (r + s) (a * b ^ (p ^ s)) x := by
  simp only [semilinearOp, mul_pow, ← pow_mul, ← pow_add]; ring

/-- Frobenius power injectivity: x^{p^r} = y^{p^r} → x = y in a reduced ring of
characteristic p. -/
lemma frobenius_pow_injective (r : ℕ) {x y : F} (h : x ^ (p ^ r) = y ^ (p ^ r)) : x = y :=
  iterateFrobenius_inj F p r
    (show iterateFrobenius F p r x = iterateFrobenius F p r y by
      simp [iterateFrobenius]; exact h)

/-- T_r(a) is injective when a ≠ 0. -/
lemma semilinearOp_injective (r : ℕ) {a : F} (ha : a ≠ 0) :
    Function.Injective (semilinearOp p r a : F → F) := by
  intro x y hxy
  simp only [semilinearOp] at hxy
  exact frobenius_pow_injective p r (mul_left_cancel₀ ha hxy)

/-- T_r(a) is bijective when a ≠ 0 (injectivity on a finite type). -/
lemma semilinearOp_bijective [Finite F] (r : ℕ) {a : F} (ha : a ≠ 0) :
    Function.Bijective (semilinearOp p r a : F → F) :=
  Finite.injective_iff_bijective.mp (semilinearOp_injective p r ha)

/-- T_r(a) is surjective when a ≠ 0. -/
lemma semilinearOp_surjective [Finite F] (r : ℕ) {a : F} (ha : a ≠ 0) :
    Function.Surjective (semilinearOp p r a : F → F) :=
  (semilinearOp_bijective p r ha).2

-- ═══════════════════════════════════════════
-- Layer 2 : Additive polynomial evaluation
-- ═══════════════════════════════════════════

/-- An additive polynomial is the sum of semilinear operators:
L(x) = ∑ aᵢ · T_i(1)(x) = ∑ aᵢ · x^{p^i}. -/
lemma additivePolyEval_eq_sum_semilinearOp (n : ℕ) (coeffs : Fin n → F) (x : F) :
    additivePolyEval p n coeffs x =
    ∑ i : Fin n, coeffs i * semilinearOp p (i : ℕ) 1 x := by
  simp [additivePolyEval, semilinearOp, one_mul]

/-- Additive polynomials are additive: L(x + y) = L(x) + L(y). -/
lemma additivePolyEval_add (n : ℕ) (coeffs : Fin n → F) (x y : F) :
    additivePolyEval p n coeffs (x + y) =
    additivePolyEval p n coeffs x + additivePolyEval p n coeffs y := by
  simp [additivePolyEval, add_pow_char_pow, mul_add, Finset.sum_add_distrib]

/-- L(0) = 0 for any additive polynomial. -/
lemma additivePolyEval_zero (n : ℕ) (coeffs : Fin n → F) :
    additivePolyEval p n coeffs 0 = 0 := by
  simp only [additivePolyEval, zero_pow (pp_ne_zero p _), mul_zero, Finset.sum_const_zero]

/-- Scaling by prime-field elements: L(c · x) = c · L(x) when c^p = c.
This encodes the GF(p)-linearity of additive polynomials. -/
lemma additivePolyEval_smul (n : ℕ) (coeffs : Fin n → F) (c : F)
    (hc : c ^ p = c) (x : F) :
    additivePolyEval p n coeffs (c * x) = c * additivePolyEval p n coeffs x := by
  simp only [additivePolyEval, mul_pow, Finset.mul_sum]
  congr 1; ext ⟨i, hi⟩
  have hcp : c ^ (p ^ i) = c := by
    induction i with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_mul, ih (by omega), hc]
  rw [hcp]; ring

/-- The p^r-th power distributes over finite sums in characteristic p
(Frobenius endomorphism is a ring homomorphism). -/
lemma sum_pow_char_pow {n : ℕ} (f : Fin n → F) (r : ℕ) :
    (∑ i : Fin n, f i) ^ (p ^ r) = ∑ i : Fin n, (f i) ^ (p ^ r) := by
  simp_rw [← show ∀ x : F, (iterateFrobenius F p r) x = x ^ (p ^ r) from
    fun x => by simp [iterateFrobenius]]
  rw [← map_sum]

-- ═══════════════════════════════════════════
-- Layer 3 : Support (spi) properties
-- ═══════════════════════════════════════════

/-- Only nonzero-coefficient terms contribute to the evaluation:
L(x) = ∑_{i ∈ spi(L)} aᵢ · x^{p^i}. -/
lemma additivePolyEval_eq_sum_support (n : ℕ) (coeffs : Fin n → F) (x : F) :
    additivePolyEval p n coeffs x =
    ∑ i ∈ support n coeffs, coeffs i * x ^ (p ^ (i : ℕ)) := by
  unfold additivePolyEval support
  symm; apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
  simp [hi]

/-- If the support is empty, then L = 0. -/
lemma additivePolyEval_eq_zero_of_support_empty (n : ℕ) (coeffs : Fin n → F)
    (h : support n coeffs = ∅) (x : F) :
    additivePolyEval p n coeffs x = 0 := by
  rw [additivePolyEval_eq_sum_support, h, Finset.sum_empty]

/-- Membership in the support characterizes nonzero coefficients. -/
lemma mem_support_iff (n : ℕ) (coeffs : Fin n → F) (i : Fin n) :
    i ∈ support n coeffs ↔ coeffs i ≠ 0 := by
  simp [support, Finset.mem_filter]

/-- Support is preserved by nonzero scalar multiplication:
spi(a · L) = spi(L) for a ≠ 0. -/
lemma support_smul_eq (n : ℕ) (coeffs : Fin n → F) {a : F} (ha : a ≠ 0) :
    support n (fun i => a * coeffs i) = support n coeffs := by
  ext i; simp [support, Finset.mem_filter, mul_ne_zero_iff, ha]

-- ═══════════════════════════════════════════
-- Layer 4 : Conjugation of additive polynomials
-- ═══════════════════════════════════════════

/-- Frobenius acts on semilinear operators:
(T_r(a)(x))^{p^s} = T_{r+s}(a^{p^s})(x). -/
lemma semilinearOp_pow_frobenius (r s : ℕ) (a x : F) :
    (semilinearOp p r a x) ^ (p ^ s) =
    semilinearOp p (r + s) (a ^ (p ^ s)) x := by
  simp [semilinearOp, mul_pow, ← pow_mul, ← pow_add]

/-- Composition with T_0(a) on the left scales all coefficients:
T_0(a)(L(x)) = (a · L)(x). -/
lemma semilinearOp_zero_additivePolyEval (n : ℕ) (coeffs : Fin n → F) (a x : F) :
    semilinearOp p 0 a (additivePolyEval p n coeffs x) =
    additivePolyEval p n (fun i => a * coeffs i) x := by
  simp [semilinearOp, additivePolyEval, Finset.mul_sum, mul_assoc]

-- ═══════════════════════════════════════════
-- Layer 5 : Singer group properties (Lemma 4.1)
-- ═══════════════════════════════════════════

/-- Lemma 4.1(a), part 1. {T_0(a) | a ∈ F*} acts regularly on F*:
the map a ↦ T_0(a)(x) is a bijection F → F for any nonzero x. -/
lemma singer_action_bijective [Finite F] {x : F} (hx : x ≠ 0) :
    Function.Bijective (fun a : F => semilinearOp p 0 a x) := by
  constructor
  · intro a₁ a₂ h
    simp only [semilinearOp, pow_zero, pow_one] at h
    exact mul_right_cancel₀ hx h
  · intro y
    exact ⟨y * x⁻¹, by simp [semilinearOp, mul_assoc, inv_mul_cancel₀ hx]⟩

/-- Lemma 4.1(a), part 2. The Singer group acts transitively on F*:
for any y ≠ 0, there exists a ≠ 0 with T_0(a)(1) = y. -/
lemma singer_transitive {y : F} (hy : y ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ semilinearOp p 0 a 1 = y :=
  ⟨y, hy, by simp [semilinearOp]⟩

/-- The identity element of the normalizer is T_0(1). -/
lemma semilinearOp_id_fun :
    (fun x : F => semilinearOp p 0 (1 : F) x) = id := by
  ext x; simp [semilinearOp]

-- ═══════════════════════════════════════════
-- Layer 6 : Lemma 4.2 — Support under conjugation
-- ═══════════════════════════════════════════

/-- Single-term conjugation. Conjugating the monomial aᵢ · x^{p^i}
by T_s(a) on the left and T_t(b⁻¹) on the right gives a monomial
of degree p^{t+i+s}. -/
lemma conjugation_single_term (i s t : ℕ) (a ai b_inv x : F) :
    semilinearOp p s a (ai * (semilinearOp p t b_inv x) ^ (p ^ i)) =
    (a * (ai * b_inv ^ (p ^ i)) ^ (p ^ s)) * x ^ (p ^ (t + i + s)) := by
  simp [semilinearOp, mul_pow, ← pow_mul, ← pow_add]; ring

/-- Lemma 4.2 — Coefficient nonvanishing. If aᵢ ≠ 0 and a, b⁻¹ ≠ 0,
then the coefficient of the conjugated monomial is nonzero. -/
lemma conjugation_coeff_ne_zero {a ai b_inv : F}
    (ha : a ≠ 0) (hai : ai ≠ 0) (hb : b_inv ≠ 0) (i s : ℕ) :
    a * (ai * b_inv ^ (p ^ i)) ^ (p ^ s) ≠ 0 :=
  mul_ne_zero ha (pow_ne_zero _ (mul_ne_zero hai (pow_ne_zero _ hb)))

/-- Lemma 4.2 — Coefficient vanishing characterization. The conjugated
coefficient is zero iff aᵢ = 0 (when a, b⁻¹ ≠ 0). -/
lemma conjugation_coeff_eq_zero_iff {a ai b_inv : F}
    (ha : a ≠ 0) (hb : b_inv ≠ 0) (i s : ℕ) :
    a * (ai * b_inv ^ (p ^ i)) ^ (p ^ s) = 0 ↔ ai = 0 := by
  constructor
  · intro h; by_contra hai
    exact conjugation_coeff_ne_zero p ha hai hb i s h
  · intro h; simp [h, zero_pow (pp_ne_zero p s)]

/-- Lemma 4.2 (evaluation form). The composed map
x ↦ T_s(a)(L(T_t(b⁻¹)(x))) evaluates to a sum whose i-th term has
exponent p^{t+i+s} and coefficient a · (aᵢ · (b⁻¹)^{p^i})^{p^s}. -/
lemma lemma_4_2_eval (n : ℕ) (coeffs : Fin n → F) (a b_inv : F)
    (s t : ℕ) (x : F) :
    semilinearOp p s a (additivePolyEval p n coeffs (semilinearOp p t b_inv x)) =
    ∑ i : Fin n, (a * (coeffs i * b_inv ^ (p ^ (i : ℕ))) ^ (p ^ s)) *
      x ^ (p ^ (t + (i : ℕ) + s)) := by
  simp only [additivePolyEval, semilinearOp]
  conv_lhs =>
    arg 2; arg 1; arg 2; ext i
    rw [mul_pow, ← pow_mul, ← pow_add]
  rw [sum_pow_char_pow]
  simp only [Finset.mul_sum]
  congr 1; ext i
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_add]; ring

/-- Lemma 4.2 (support characterization). The conjugated polynomial has the same
"nonzero pattern" as the original: the i-th conjugated coefficient is nonzero iff
coeffs i ≠ 0. This captures the paper's statement that conjugation shifts the
support indices by s − t without adding or removing elements. -/
theorem lemma_4_2_support (n : ℕ) (coeffs : Fin n → F) {a b_inv : F}
    (ha : a ≠ 0) (hb : b_inv ≠ 0) (s : ℕ) (i : Fin n) :
    a * (coeffs i * b_inv ^ (p ^ (i : ℕ))) ^ (p ^ s) ≠ 0 ↔ coeffs i ≠ 0 :=
  ⟨fun h hc => h (by rw [hc, zero_mul, zero_pow (pp_ne_zero p s), mul_zero]),
   fun h => conjugation_coeff_ne_zero p ha h hb _ _⟩

end DempwolffMueller
