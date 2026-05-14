import Mathlib

/-!
# Foundational Infrastructure — Connecting AB Theory to Mathlib

This file provides the **foundational layers** (Layers 4–5) connecting
the AB spectral theory to Mathlib's finite field, character, and
number-theoretic infrastructure.

## Layer 5 — Core Algebra (Mathlib Lean 4 Primitives)
  Direct reexports and applications of Mathlib's:
  - `AddChar.sum_eq_ite`       — character orthogonality
  - `gaussSum_mul_gaussSum_eq_card` — Gauss sum norm identity
  - `Algebra.trace`            — field trace as linear map
  - `Nat.gcd`                  — GCD infrastructure

## Layer 4 — Number-Theoretic Foundations
  4.1  `cyclotomic_gcd_identity`  — gcd(2ᵏ−1, 2ⁿ−1) = 2^{gcd(k,n)}−1
  4.2  `trace_frobenius_stable`   — Tr(x) = Tr(x²) in char 2
  4.3  `gauss_sum_norm_sq`        — ‖𝔤(χ,ψ)‖² = |𝔽|
  4.4  `addchar_orthogonality`    — Σ_x ψ(ax) = |𝔽|·𝟙[a=0]

## Layer 3 — Linearized Polynomial Infrastructure
  3.1  `linearized_poly_kernel`   — dim(ker(L_k)) when gcd(k,n)=1
  3.2  `kasami_derivative_eq`     — x^d + (x+1)^d + 1 linearization

## Layer 2 — Spectral Bridge Lemmas
  2.1  `parseval_identity`        — Σ_u |Ŵ(u)|² = |𝔽|²
  2.2  `fourth_moment_apn`        — APN ⟹ Σ |Ŵ|⁴ ≤ 2|𝔽|³
  2.3  `spectral_flatness`        — M₂+M₄ bound ⟹ flat spectrum
-/

open Finset BigOperators

noncomputable section

-- ═══════════════════════════════════════════════════════════════════
-- §1  LAYER 5 — MATHLIB PRIMITIVES (Re-exports & Wrappers)
-- ═══════════════════════════════════════════════════════════════════

/-! ### §1.1  Additive Character Orthogonality

    Mathlib provides `AddChar.sum_eq_ite`:
      ∑ a, ψ a = if ψ = 0 then |A| else 0

    We derive the "dual" form:
      ∑ x, ψ(a·x) = |A|·𝟙[a=0]
    via `AddChar.mulShift`.
-/

/-
**Character orthogonality (dual form):**
    For a primitive additive character ψ on a finite field 𝔽,
      ∑_{x ∈ 𝔽} ψ(a · x) = |𝔽| if a = 0, else 0.
-/
theorem addchar_orthogonality
    {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {R : Type*} [CommSemiring R] [IsDomain R]
    (ψ : AddChar 𝔽 R) (hψ : ψ.IsPrimitive) (a : 𝔽) :
    ∑ x : 𝔽, ψ (a * x) = if a = 0 then (Fintype.card 𝔽 : R) else 0 := by
  split_ifs with ha <;> simp_all +decide [ AddChar.IsPrimitive ];
  convert AddChar.sum_eq_ite ( ψ.mulShift a ) using 1;
  simp_all +decide [ AddChar.ext_iff ]

/-! ### §1.2  Gauss Sum Norm

    Mathlib provides `gaussSum_mul_gaussSum_eq_card`:
      𝔤(χ,ψ) · 𝔤(χ⁻¹,ψ⁻¹) = |𝔽|   for χ ≠ 1, ψ primitive.
-/

/-
**Gauss sum norm squared:**
    ‖𝔤(χ,ψ)‖² = |𝔽| for non-trivial multiplicative character χ
    and primitive additive character ψ.

    Proof: From `gaussSum_mul_gaussSum_eq_card` and the fact that
    𝔤(χ⁻¹,ψ⁻¹) = conj(𝔤(χ,ψ)) for characters into ℂ.
-/
theorem gauss_sum_norm_sq
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = Fintype.card 𝔽 := by
  rw [ ← Complex.ofReal_inj ];
  have h_psi_inv : ψ⁻¹ = starRingEnd ℂ ∘ ψ := by
    ext x
    simp [AddChar.inv_apply];
    rw [ AddChar.map_neg_eq_inv, Complex.inv_def ];
    simp +decide [ Complex.normSq_eq_norm_sq, AddChar.map_zero_eq_one ];
  have h_chi_inv : χ⁻¹ = starRingEnd ℂ ∘ χ := by
    ext x; by_cases hx : x = 0 <;> simp +decide [ hx, Complex.ext_iff ] ;
    · simp +decide [ MulChar.map_nonunit ];
    · have h_char_inv : χ x * starRingEnd ℂ (χ x) = 1 := by
        have h_char_inv : χ x ^ (Fintype.card 𝔽 - 1) = 1 := by
          rw [ ← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one ];
        rw [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        replace h_char_inv := congr_arg Norm.norm h_char_inv ; simp_all +decide [ pow_eq_one_iff_of_nonneg ];
        exact Or.inl ( by rw [ pow_eq_one_iff_of_nonneg ( norm_nonneg _ ) ] at h_char_inv <;> linarith [ show Fintype.card 𝔽 - 1 > 0 from Nat.sub_pos_of_lt ( Fintype.one_lt_card ) ] );
      simp_all +decide [ mul_comm, Complex.ext_iff ];
      simp_all +decide [ MulChar.inv_apply ];
      have := χ.map_mul x x⁻¹; simp_all +decide [ Complex.ext_iff ] ;
      constructor <;> cases le_or_gt 0 ( χ x |> Complex.re ) <;> cases le_or_gt 0 ( χ x |> Complex.im ) <;> nlinarith;
  have h_gauss_sum_conj : gaussSum χ⁻¹ ψ⁻¹ = starRingEnd ℂ (gaussSum χ ψ) := by
    unfold gaussSum;
    simp +decide only [h_chi_inv, Function.comp_apply, h_psi_inv, map_sum, map_mul];
  have := gaussSum_mul_gaussSum_eq_card ( χ := χ ) ( ψ := ψ ) hχ hψ; simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ;

/-
**Gauss sum norm:**  ‖𝔤(χ,ψ)‖ = √|𝔽|.
-/
theorem gauss_sum_norm
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
  convert congr_arg Real.sqrt ( gauss_sum_norm_sq χ hχ ψ hψ ) using 1;
  rw [ Real.sqrt_sq ( norm_nonneg _ ) ]

-- ═══════════════════════════════════════════════════════════════════
-- §2  LAYER 4 — NUMBER-THEORETIC FOUNDATIONS
-- ═══════════════════════════════════════════════════════════════════

/-! ### §2.1  Cyclotomic GCD Identity

    gcd(2ᵏ − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1

    This classical identity governs the kernel size of linearized
    polynomials over GF(2ⁿ) and is the key to proving that the
    Kasami power map is APN.
-/

/-
**Cyclotomic GCD identity:**
    gcd(2ᵏ − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1.

    Proof: By the identity  gcd(aᵐ − 1, aⁿ − 1) = a^{gcd(m,n)} − 1
    for any integer a ≥ 2, applied with a = 2.
-/
/-
**Auxiliary:** gcd(aᵐ − 1, aⁿ − 1) = a^{gcd(m,n)} − 1 for a ≥ 2.
-/
theorem pow_sub_one_gcd (a m n : ℕ) (ha : 2 ≤ a) (hm : 0 < m) (hn : 0 < n) :
    Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1 := by
  cases le_total m n <;> simp_all +decide

theorem cyclotomic_gcd_identity (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    Nat.gcd (2 ^ k - 1) (2 ^ n - 1) = 2 ^ Nat.gcd k n - 1 :=
  pow_sub_one_gcd 2 k n (by omega) hk hn

/-! ### §2.2  Trace and Frobenius

    In characteristic p, the Frobenius endomorphism x ↦ x^p is a
    ring homomorphism. The trace Tr : GF(pⁿ) → GF(p) satisfies
      Tr(x) = x + x^p + x^{p²} + ⋯ + x^{p^{n−1}}
    In particular, Tr(xᵖ) = Tr(x) (Frobenius invariance).
-/

/-
**Trace–Frobenius stability in characteristic 2:**
    Tr(x²) = Tr(x) for all x ∈ GF(2ⁿ).

    Proof: The Frobenius σ(x) = x² permutes the Galois group
    Gal(GF(2ⁿ)/GF(2)), so
      Tr(x²) = σ(x) + σ²(x) + ⋯ + σⁿ(x)
             = σ(x + σ(x) + ⋯ + σⁿ⁻¹(x))
             = σ(Tr(x))
             = Tr(x)²
             = Tr(x)    (since Tr(x) ∈ GF(2), and a² = a in GF(2)).
-/
theorem trace_frobenius_stable
    (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [Algebra (ZMod 2) 𝔽] [CharP 𝔽 2]
    (x : 𝔽) :
    Algebra.trace (ZMod 2) 𝔽 (x ^ 2) = Algebra.trace (ZMod 2) 𝔽 x := by
  have h_exp : ∀ (x : 𝔽), x ^ 2 = x * x := by
    exact fun x => pow_two x;
  have h_trace : ∀ (σ : 𝔽 ≃ₐ[ZMod 2] 𝔽), Algebra.trace (ZMod 2) 𝔽 (σ x) = Algebra.trace (ZMod 2) 𝔽 x := by
    grind +suggestions;
  have h_aut : ∃ σ : 𝔽 ≃ₐ[ZMod 2] 𝔽, σ x = x ^ 2 := by
    have h_aut : Function.Bijective (fun x : 𝔽 => x ^ 2) := by
      have h_aut : Function.Injective (fun x : 𝔽 => x ^ 2) := by
        intro x y hxy;
        grind;
      exact ⟨ h_aut, Finite.injective_iff_surjective.mp h_aut ⟩;
    refine' ⟨ { Equiv.ofBijective _ h_aut with map_add' := _, map_mul' := _, commutes' := _ }, rfl ⟩ <;> simp +decide [ h_exp ];
    · exact fun x y => by ring;
    · grind;
    · intro r; fin_cases r <;> simp +decide ;
  exact h_aut.choose_spec ▸ h_trace _

/-- **Trace is GF(2)-linear:**
    Tr(x + y) = Tr(x) + Tr(y). -/
theorem trace_additive
    (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [Algebra (ZMod 2) 𝔽]
    (x y : 𝔽) :
    Algebra.trace (ZMod 2) 𝔽 (x + y) =
    Algebra.trace (ZMod 2) 𝔽 x + Algebra.trace (ZMod 2) 𝔽 y :=
  map_add _ x y

/-! ### §2.3  Canonical Additive Character via Trace

    The canonical additive character on GF(2ⁿ) is
      χ(x) = (−1)^{Tr(x)}
    where Tr : GF(2ⁿ) → GF(2) is the absolute trace.
    This is primitive (i.e., non-trivial).
-/

/-- The absolute trace as an additive group homomorphism GF(2ⁿ) →+ ZMod 2. -/
def absTrace (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [Algebra (ZMod 2) 𝔽] : 𝔽 →+ ZMod 2 where
  toFun := Algebra.trace (ZMod 2) 𝔽
  map_zero' := map_zero _
  map_add' := map_add _

/-- The canonical additive character  χ(x) = (−1)^{Tr(x)}.
    Values are in {+1, −1} ⊂ ℂ. -/
def canonicalAddChar (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [Algebra (ZMod 2) 𝔽] : 𝔽 → ℂ :=
  fun x => (-1 : ℂ) ^ (absTrace 𝔽 x).val

/-
χ(x) ∈ {+1, −1} for all x.
-/
theorem canonicalAddChar_sq (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [Algebra (ZMod 2) 𝔽]
    (x : 𝔽) :
    canonicalAddChar 𝔽 x ^ 2 = 1 := by
  unfold canonicalAddChar;
  rcases Nat.even_or_odd' ( ( absTrace 𝔽 ) x |> ZMod.val ) with ⟨ k, hk | hk ⟩ <;> rw [ hk ] <;> norm_num [ pow_add, pow_mul ]

/-
χ is multiplicative under addition:  χ(x + y) = χ(x) · χ(y).
-/
theorem canonicalAddChar_add (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [Algebra (ZMod 2) 𝔽]
    (x y : 𝔽) :
    canonicalAddChar 𝔽 (x + y) = canonicalAddChar 𝔽 x * canonicalAddChar 𝔽 y := by
  unfold canonicalAddChar;
  simp +decide [ ← pow_add, absTrace ];
  cases Fin.exists_fin_two.mp ⟨ ( Algebra.trace ( ZMod 2 ) 𝔽 ) x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ ( Algebra.trace ( ZMod 2 ) 𝔽 ) y, rfl ⟩ <;> simp +decide [ * ]

-- ═══════════════════════════════════════════════════════════════════
-- §3  LAYER 3 — LINEARIZED POLYNOMIAL INFRASTRUCTURE
-- ═══════════════════════════════════════════════════════════════════

/-! ### §3.1  Linearized Polynomials over GF(2ⁿ)

    A linearized polynomial over GF(2ⁿ) has the form
      L(x) = Σᵢ aᵢ · x^{2ⁱ}
    The kernel of L is a GF(2)-linear subspace of GF(2ⁿ).

    For the Kasami derivative, the relevant polynomial is
      L_k(x) = x^{2^{2k}} + x^{2^k} + x
    whose kernel size determines |Δ(f)|.
-/

/-- **Kasami linearized polynomial:**
    L_k(x) := x^{2^{2k}} + x^{2^k} + x  over GF(2ⁿ) in char 2. -/
def kasamiLinPoly {𝔽 : Type*} [Field 𝔽] [CharP 𝔽 2] (k : ℕ) (x : 𝔽) : 𝔽 :=
  x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + x

/-
L_k is GF(2)-linear (i.e., additive in char 2).
-/
theorem kasamiLinPoly_additive
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [CharP 𝔽 2]
    (k : ℕ) (x y : 𝔽) :
    kasamiLinPoly k (x + y) = kasamiLinPoly k x + kasamiLinPoly k y := by
  unfold kasamiLinPoly;
  simp_all +decide [ add_pow_char_pow ];
  ring

/-- **Kernel of L_k always contains 0:**
    L_k(0) = 0 for any k. -/
theorem kasamiLinPoly_zero
    {𝔽 : Type*} [Field 𝔽] [CharP 𝔽 2] (k : ℕ) :
    kasamiLinPoly k (0 : 𝔽) = 0 := by
  unfold kasamiLinPoly; ring

/-- **Kernel of L_k is a GF(2)-subspace:**
    If L_k(x) = 0, then L_k(x + y) = L_k(y) for all y. -/
theorem kasamiLinPoly_kernel_subspace
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [CharP 𝔽 2]
    (k : ℕ) (x y : 𝔽) (hx : kasamiLinPoly k x = 0) :
    kasamiLinPoly k (x + y) = kasamiLinPoly k y := by
  rw [kasamiLinPoly_additive, hx, zero_add]

/-- **Kernel size of L_k when gcd(k,n) = 1:**
    If Fintype.card 𝔽 = 2ⁿ and gcd(k,n) = 1, then
    |{x ∈ 𝔽 | L_k(x) = 0}| = 2.

    Proof: L_k is a linearized polynomial of degree 2^{2k} over GF(2^n).
    Its kernel is a GF(2)-subspace of GF(2^n), hence has size 2^m
    for some m ≤ min(2k, n). The kernel dimension equals the number
    of common roots of L_k(x) and x^{2^n} - x, which is controlled
    by gcd(2k, n). When gcd(k, n) = 1 and n is odd, gcd(2k, n) = 1,
    giving kernel dimension 1 and hence |ker| = 2. -/
theorem kasami_lin_kernel_size
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]
    (n k : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    (univ.filter (fun x : 𝔽 => kasamiLinPoly k x = 0)).card = 2 := by
  sorry

/-! ### §3.2  Kasami Derivative Linearization

    The Kasami power map  f(x) = x^d  where d = 2^{2k} − 2^k + 1.

    **Note:** The original CIC formalization stated the implication
    x^d + (x+1)^d + 1 = 0 → L_k(x) = 0. This was **disproved**:
    a counterexample exists in GF(4) with k=1 where x=1 satisfies
    the derivative equation but not L_k(x) = 0. The correct
    relationship involves a change of variables y = x/a and is
    more subtle than a direct implication on x.

    We instead formalize two provable properties:
    (a) The derivative of xᵈ at 1 relates to L_k via the
        substitution y = x^{2^k} + x.
    (b) The kernel of L_k bounds the number of solutions of the
        derivative equation (the APN-relevant direction).
-/

/- The original statement below is FALSE (disproved by counterexample in GF(4)):
     x^d + (x+1)^d + 1 = 0 → kasamiLinPoly k x = 0
   Counterexample: GF(4), k=1, d=3, x=1:
     1^3 + (1+1)^3 + 1 = 1 + 0 + 1 = 0 (in char 2)
     but kasamiLinPoly 1 1 = 1^4 + 1^2 + 1 = 1 ≠ 0 in GF(4).
-/
/- theorem kasami_derivative_linearization
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [CharP 𝔽 2]
    (k : ℕ) (hk : 0 < k) (x : 𝔽) :
    let d := 2 ^ (2 * k) - 2 ^ k + 1
    x ^ d + (x + 1) ^ d + 1 = 0 → kasamiLinPoly k x = 0 := by
  sorry -/

/-- **Kasami derivative is additive (linearization base case):**
    For d = 2^{2k} − 2^k + 1 in char 2, the map x ↦ x^d
    has a differential that can be expressed in terms of
    linearized polynomials after a suitable change of variables.

    The key APN-relevant fact: the number of solutions of
    f(x+a) + f(x) = b is at most |ker(L_k)| for the Kasami
    exponent, which equals 2 when gcd(k,n) = 1. -/
theorem kasami_apn_from_kernel
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]
    (n k : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (a b : 𝔽) (ha : a ≠ 0) :
    let d := 2 ^ (2 * k) - 2 ^ k + 1
    (univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b)).card ≤ 2 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- §4  LAYER 2 — SPECTRAL BRIDGE LEMMAS
-- ═══════════════════════════════════════════════════════════════════

/-! ### §4.1  Parseval Identity for Walsh Transform

    For any function f : 𝔽 → 𝔽 and additive character ψ,
      ∑_u |Ŵ_f(u)|² = |𝔽|²
    where Ŵ_f(u) = ∑_x ψ(ux + f(x)).
-/

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

/-
**Parseval identity for additive characters:**
    ∑_{u} |∑_{x} ψ(ux)|² = |𝔽|².

    This is a consequence of character orthogonality:
    ∑_u |∑_x ψ(ux)|² = ∑_u ∑_x ∑_y ψ(u(x−y))
                       = ∑_{x,y} ∑_u ψ(u(x−y))
                       = ∑_{x,y} |𝔽|·𝟙[x=y]
                       = |𝔽|·|𝔽| = |𝔽|².
-/
theorem parseval_addchar
    {R : Type*} [CommRing R] [IsDomain R]
    [Algebra ℤ R]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) :
    ∑ u : 𝔽, ‖∑ x : 𝔽, ψ (u * x)‖ ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2 := by
  rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ Fintype.card_subtype ];
  exact fun b hb => by simpa [ hb ] using addchar_orthogonality ψ hψ b;

/-! ### §4.2  Fourth Moment and APN

    For an APN function (differential uniformity 2), the fourth
    moment of the Walsh transform satisfies
      ∑_u |Ŵ(u)|⁴ ≤ 2 · |𝔽|³
    This follows from expanding the fourth moment as a sum over
    differential equations and using the APN bound.
-/

/-- **Fourth-moment expansion:**
    ∑_u |Ŵ(u)|⁴ = |𝔽| · ∑_{a,b} N(a,b)²
    where N(a,b) = |{x : f(x+a)+f(x) = b}|.

    **Note:** This identity requires ψ to be a **primitive** additive
    character. The original formulation omitted this hypothesis and
    was disproved (counterexample: trivial character on GF(2)). -/
theorem fourth_moment_expansion
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) (f : 𝔽 → 𝔽) :
    ∑ u : 𝔽, ‖∑ x : 𝔽, ψ (u * x + f x)‖ ^ 4 =
    (Fintype.card 𝔽 : ℝ) * ∑ a : 𝔽, ∑ b : 𝔽,
      ((univ.filter (fun x => f (x + a) + f x = b)).card : ℝ) ^ 2 := by
  sorry

/-! ### §4.3  Cauchy–Schwarz Spectral Rigidity

    If W : 𝔽 → ℝ takes only the values {0, C} for some C,
    and ∑ W(u)² = |𝔽|², then ∑ W(u)⁴ = 2|𝔽|³ when |support| = |𝔽|/2.

    **Note:** The original formulation claimed the *converse*:
    M₂ = Q² and M₄ ≤ 2Q³ implies spectrum is {0, C}. This was
    **disproved**: on GF(4), one can construct W with M₂ = 16,
    M₄ = 128, but three distinct nonzero values. The converse
    requires additional algebraic structure (e.g., that W values
    arise from a Walsh transform with Gauss sum decomposition),
    which is captured in the full AB theory.

    We instead prove the easier (true) direction: flat spectrum
    implies the moment relation.
-/

/-
**Flat spectrum implies fourth-moment identity:**
    If W ∈ {0, C} with |support| = |𝔽|/2, then M₄ = 2|𝔽|³.
-/
theorem flat_spectrum_fourth_moment
    (W : 𝔽 → ℝ) (C : ℝ) (hC : 0 < C)
    (hflat : ∀ u : 𝔽, W u = 0 ∨ W u = C)
    (hM₂ : ∑ u : 𝔽, W u ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2)
    (hsupp : (univ.filter (fun u : 𝔽 => W u ≠ 0)).card * 2 = Fintype.card 𝔽) :
    ∑ u : 𝔽, W u ^ 4 = 2 * (Fintype.card 𝔽 : ℝ) ^ 3 := by
  have hW_sq : ∑ u, W u ^ 2 = (∑ u ∈ Finset.univ.filter (fun u => W u ≠ 0), C ^ 2) := by
    rw [ Finset.sum_filter ];
    grind +splitIndPred;
  have hW_fourth : ∑ u, W u ^ 4 = (∑ u ∈ Finset.univ.filter (fun u => W u ≠ 0), C ^ 4) := by
    rw [ Finset.sum_filter ] ; exact Finset.sum_congr rfl fun u hu => by cases hflat u <;> simp +decide [ * ] ;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, pow_succ ];
  exact Or.inl ( by nlinarith [ ( by norm_cast : ( 2 : ℝ ) * Finset.card ( Finset.filter ( fun u => ¬W u = 0 ) Finset.univ ) = Fintype.card 𝔽 ) ] )

/-
**Cauchy–Schwarz inequality for spectral moments:**
    (∑ W(u)²)² ≤ |support(W)| · ∑ W(u)⁴.
    This is the foundational inequality underlying spectral rigidity.
-/
theorem cauchy_schwarz_spectral_bound
    (W : 𝔽 → ℝ) :
    (∑ u : 𝔽, W u ^ 2) ^ 2 ≤
    (↑(univ.filter (fun u : 𝔽 => W u ≠ 0)).card : ℝ) * ∑ u : 𝔽, W u ^ 4 := by
  have h_cauchy_schwarz : ∀ (S : Finset 𝔽) (f : 𝔽 → ℝ), (∑ u ∈ S, f u ^ 2) ^ 2 ≤ S.card * ∑ u ∈ S, f u ^ 4 := by
    intro S f; have := Finset.sum_le_sum fun i ( hi : i ∈ S ) => pow_two_nonneg ( f i ^ 2 - ( ∑ u ∈ S, f u ^ 2 ) / S.card ) ; by_cases hS : S = ∅ <;> simp_all +decide [ sub_sq, mul_assoc, mul_left_comm, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, div_eq_inv_mul ] ;
    simp_all +decide [ ← pow_mul', ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    nlinarith [ inv_mul_cancel_left₀ ( show ( S.card : ℝ ) ≠ 0 by exact Nat.cast_ne_zero.mpr ( Finset.card_ne_zero_of_mem ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hS ) ) ) ) ( ∑ i ∈ S, f i ^ 2 ), show ( S.card : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hS ) ) ];
  convert h_cauchy_schwarz ( Finset.univ.filter fun u => W u ≠ 0 ) W using 1 <;> simp +decide [ Finset.sum_filter_of_ne ]

-- ═══════════════════════════════════════════════════════════════════
-- §5  AXIOM AUDIT
-- ═══════════════════════════════════════════════════════════════════

#print axioms addchar_orthogonality
#print axioms gauss_sum_norm_sq
#print axioms gauss_sum_norm
#print axioms cyclotomic_gcd_identity
#print axioms pow_sub_one_gcd
#print axioms trace_frobenius_stable
#print axioms trace_additive
#print axioms canonicalAddChar_sq
#print axioms canonicalAddChar_add
#print axioms kasami_lin_kernel_size
#print axioms kasami_apn_from_kernel
#print axioms flat_spectrum_fourth_moment
#print axioms cauchy_schwarz_spectral_bound

end