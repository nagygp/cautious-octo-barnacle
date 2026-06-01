import Mathlib

/-!
# Dickson Polynomial Theory for Kasami APN

Formalization following Cohen-Matthews (1994) "A Class of Exceptional Polynomials"
and Dempwolff-Müller (2013, Theorem 3.2).
-/

set_option maxHeartbeats 800000

noncomputable section
open Finset BigOperators

namespace DicksonKasami

-- ═══════════════════════════════════════
-- Section 1: General field of char 2 (no Fintype)
-- ═══════════════════════════════════════

variable {K : Type*} [Field K] [CharP K 2]

/-- The Dickson-like polynomial. -/
def dicksonF (k : ℕ) (x : K) : K :=
  ∑ j ∈ Finset.range k, x ^ (2 ^ k + 1 - 2 ^ (j + 1))

lemma dicksonF_map {L : Type*} [Field L] [CharP L 2]
    (f : K →+* L) (k : ℕ) (x : K) :
    dicksonF k (f x) = f (dicksonF k x) := by
  simp only [dicksonF, map_sum, map_pow]

lemma eq_or_eq_inv_of_add_inv_eq {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + a⁻¹ = b + b⁻¹) : a = b ∨ a = b⁻¹ := by
  grind

lemma dicksonF_functional (k : ℕ) (hk : 0 < k) {z : K} (hz : z ≠ 0) :
    dicksonF k (z + z⁻¹) = z ^ (2 ^ k - 1) + z⁻¹ ^ (2 ^ k - 1) := by
  induction' k using Nat.case_strong_induction_on with k ih generalizing z;
  · contradiction;
  · by_cases h2 : z + z⁻¹ = 0;
    · -- Since $z + z⁻¹ = 0$, we have $z = 1$ or $z = -1$.
      have hz_cases : z = 1 ∨ z = -1 := by
        grind +suggestions;
      cases hz_cases <;> simp_all +decide [ dicksonF ];
      · rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ pow_add, pow_mul ];
        exact ne_of_gt ( Nat.sub_pos_of_lt ( by linarith [ pow_pos ( zero_lt_two' ℕ ) k, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ‹_› ] ) );
      · rw [ Finset.sum_eq_single ( k ) ] <;> simp_all +decide [ Nat.one_le_iff_ne_zero, parity_simps ];
        exact fun b hb hb' => Nat.sub_ne_zero_of_lt ( by linarith [ pow_lt_pow_right₀ ( by decide : 1 < 2 ) ( by linarith [ Nat.lt_of_le_of_ne hb hb' ] : b + 1 < k + 1 ) ] );
    · have h_rec : (z + z⁻¹) * dicksonF (k + 1) (z + z⁻¹) = dicksonF k (z + z⁻¹) ^ 2 + (z + z⁻¹) ^ (2 ^ (k + 1)) := by
        have h_rec : ∀ k : ℕ, ∀ x : K, x ≠ 0 → x * dicksonF (k + 1) x = dicksonF k x ^ 2 + x ^ (2 ^ (k + 1)) := by
          intro k x hx; rw [ dicksonF, dicksonF ] ; simp +decide [ Finset.sum_range_succ', pow_succ, pow_mul ] ; ring;
          rw [ show ( ∑ i ∈ Finset.range k, x ^ ( 1 + 2 ^ k - 2 ^ i * 2 ) ) ^ 2 = ∑ i ∈ Finset.range k, x ^ ( 2 * ( 1 + 2 ^ k - 2 ^ i * 2 ) ) from ?_ ];
          · congr! 1;
            · rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr ( by positivity ) ) ];
            · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ show 1 + 2 ^ k * 2 - 2 ^ i * 4 = 2 * ( 1 + 2 ^ k - 2 ^ i * 2 ) - 1 from _ ] ; ring;
              · rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| mul_ne_zero ( Nat.sub_ne_zero_of_lt <| by linarith [ Nat.pow_le_pow_right two_pos ( show i + 1 ≤ k from Finset.mem_range.mp hi ), pow_succ' 2 i ] ) two_ne_zero ) ];
              · grind;
          · induction' ( Finset.range k ) using Finset.induction <;> simp_all +decide [ pow_succ', pow_mul', Finset.sum_range_succ ];
            grind;
        exact h_rec k _ h2;
      by_cases hk : 0 < k <;> simp_all +decide;
      · refine' mul_left_cancel₀ h2 _;
        convert h_rec using 1;
        rw [ show 2 ^ ( k + 1 ) - 1 = 2 * ( 2 ^ k - 1 ) + 1 by zify ; norm_num ; ring ] ; ring;
        simp +decide [ add_pow_char_pow, mul_two, pow_add, pow_mul', hz ] ; ring;
        simp +decide [ show z ^ ( 2 ^ k * 2 ) = z ^ ( ( 2 ^ k - 1 ) * 2 ) * z ^ 2 by rw [ ← pow_add, show 2 ^ k * 2 = ( 2 ^ k - 1 ) * 2 + 2 by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ) ] ], show z⁻¹ ^ ( 2 ^ k * 2 ) = z⁻¹ ^ ( ( 2 ^ k - 1 ) * 2 ) * z⁻¹ ^ 2 by rw [ ← pow_add, show 2 ^ k * 2 = ( 2 ^ k - 1 ) * 2 + 2 by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ) ] ], hz ] ; ring;
        grind;
      · unfold dicksonF; simp +decide [ Finset.sum_range_succ ] ;

lemma frob_2n_fix {n : ℕ} {a z : K} (hz_ne : z ≠ 0)
    (hz : z ^ 2 + a * z + 1 = 0) (ha : a ^ (2 ^ n) = a) :
    z ^ (2 ^ (2 * n)) = z := by
  have h_root : (z ^ (2 ^ n)) ^ 2 + a * (z ^ (2 ^ n)) + 1 = 0 := by
    convert congr_arg ( · ^ 2 ^ n ) hz using 1 <;> ring;
    simp +decide [ add_pow_char_pow, mul_pow, ha ] ; ring;
  -- Since $a$ is a root of $t^{2^n} = t$, we have $t^2 + at + 1 = 0$ has roots $z$ and $a + z$.
  have h_roots : z ^ (2 ^ n) = z ∨ z ^ (2 ^ n) = a + z := by
    grind +ring;
  cases' h_roots with h h <;> simp_all +decide [ pow_mul' ];
  · simp +decide [ *, sq, pow_mul ];
  · simp_all +decide [ pow_succ, pow_mul, add_pow_char_pow ];
    grind

lemma eq_of_pow_eq_coprime {N d : ℕ} (hcop : Nat.Coprime d (N - 1))
    {z w : K} (hz : z ≠ 0) (hw : w ≠ 0)
    (hz_fix : z ^ N = z) (hw_fix : w ^ N = w)
    (hpow : z ^ d = w ^ d) : z = w := by
  -- From $z^d = w^d$, � we� get $(z/w �)^�d = 1$.
  have h_ratio : (z / w) ^ d = 1 := by
    rw [ div_pow, hpow, div_self ( pow_ne_zero _ hw ) ];
  -- From $z^N = z$, we get $z^{N-1} = 1$.
  have h_z_pow : z ^ (N - 1) = 1 := by
    cases N <;> simp_all +decide [ pow_succ' ];
  -- From $w^N = w$, we get $w^{N-1} = 1$.
  have h_w_pow : w ^ (N - 1) = 1 := by
    cases N <;> simp_all +decide [ pow_succ' ]
  have h_ratio_pow : (z / w) ^ (N - 1) = 1 := by
    rw [ div_pow, h_z_pow, h_w_pow, div_one ];
  -- Since $\gcd(d, N-1 �) = 1$, we have $(z/w)^{\gcd(d, N-1)} = 1$.
  have h_gcd : (z / w) ^ Nat.gcd d (N - 1) = 1 := by
    rw [ pow_gcd_eq_one ] ; aesop;
  simp_all +decide [ div_eq_iff ]

lemma S_sq_mul_eq_dicksonF (k : ℕ) {x : K} (hx : x ≠ 0) :
    (∑ i ∈ Finset.range k, x⁻¹ ^ (2 ^ i)) ^ 2 * x ^ (2 ^ k + 1) =
    dicksonF k x := by
  rw [ dicksonF ];
  -- In characteristic 2, squaring is linear, so we can distribute the square over the sum.
  have h_square : (∑ i ∈ Finset.range k, x⁻¹ ^ 2 ^ i) ^ 2 = ∑ i ∈ Finset.range k, x⁻¹ ^ (2 ^ (i + 1)) := by
    induction' k with k ih <;> simp_all +decide [ Finset.sum_range_succ, pow_succ, pow_mul ];
    grobner;
  have h_rewrite : ∀ i ∈ Finset.range k, x⁻¹ ^ (2 ^ (i + 1)) * x ^ (2 ^ k + 1) = x ^ (2 ^ k + 1 - 2 ^ (i + 1)) := by
    intro i hi; rw [ inv_pow, inv_mul_eq_div, div_eq_iff ( pow_ne_zero _ hx ) ] ; rw [ ← pow_add, tsub_add_cancel_of_le ( show 2 ^ ( i + 1 ) ≤ 2 ^ k + 1 from Nat.le_succ_of_le ( pow_le_pow_right₀ ( by decide ) ( by linarith [ Finset.mem_range.mp hi ] ) ) ) ] ;
  rw [ h_square, Finset.sum_mul _ _ _, Finset.sum_congr rfl h_rewrite ]

-- ═══════════════════════════════════════
-- Section 2: Finite field specifics
-- ═══════════════════════════════════════

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

lemma exists_add_inv_rep' {x : F} (hx : x ≠ 0) :
    ∃ z : AlgebraicClosure F, z ≠ 0 ∧
      z + z⁻¹ = algebraMap F (AlgebraicClosure F) x := by
  -- Let $z$ be a root of the � polynomial� $t^2 - xt + 1$ in the algebraic closure.
  obtain ⟨z, hz⟩ : ∃ z : AlgebraicClosure F, z^2 + (algebraMap F (AlgebraicClosure F) x) * z + 1 = 0 := by
    have h_root : IsAlgClosed (AlgebraicClosure F) := by
      infer_instance;
    convert h_root.exists_root ( Polynomial.X ^ 2 + Polynomial.C ( algebraMap F ( AlgebraicClosure F ) x ) * Polynomial.X + 1 ) _ using 1;
    · aesop;
    · rw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> rw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> simp +decide [ hx ];
  refine' ⟨ z, _, _ ⟩;
  · aesop;
  · grind

lemma coprime_mersenne_double' {k n : ℕ} (hk_odd : Odd k) (hcop : Nat.Coprime k n) :
    Nat.Coprime (2 ^ k - 1) (2 ^ (2 * n) - 1) := by
  have : Nat.Coprime k (2 * n) :=
    Nat.Coprime.mul_right (by obtain ⟨m, rfl⟩ := hk_odd; norm_num) hcop
  show Nat.gcd _ _ = 1; rw [Nat.pow_sub_one_gcd_pow_sub_one, this]; simp

/-
Helper: z is a root of t²+at+1=0 when z+z⁻¹=a.
-/
lemma quad_root_of_add_inv {a z : AlgebraicClosure F}
    (hz : z ≠ 0) (h : z + z⁻¹ = a) : z ^ 2 + a * z + 1 = 0 := by
  grind +ring

/-
**Dickson injectivity on units** (Cohen-Matthews 1994, Theorem 9).
-/
lemma dicksonF_injective_on_units'
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk_pos : 0 < k) (hk_odd : Odd k) (hcop : Nat.Coprime k n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hf : dicksonF k x = dicksonF k y) : x = y := by
  -- Step 1: obtain ⟨z, hz_ne, � h�z_eq⟩ := exists_add_inv_rep' hx; obtain ⟨w, hw_ne, hw �_eq�⟩ := exists_add_inv_rep' hy
  obtain ⟨z, hz_ne, hz_eq⟩ := exists_add_inv_rep' hx
  obtain ⟨w, hw_ne, hw_eq⟩ := exists_add_inv_rep' hy;
  -- Step 2: Apply dicksonF_functional to both sides: z^(2^k-1) + z⁻¹^(2^k-1) = w^(2^k-1) + w⁻¹^(2^k-1).
  have h_eq : z ^ (2 ^ k - 1) + z⁻¹ ^ (2 ^ k - 1) = w ^ (2 ^ k - 1) + w⁻¹ ^ (2 ^ k - 1) := by
    have h_eq : dicksonF k (algebraMap F (AlgebraicClosure F) x) = dicksonF k (algebraMap F (AlgebraicClosure F) y) := by
      convert congr_arg ( algebraMap F ( AlgebraicClosure F ) ) hf using 1 <;> simp +decide [ dicksonF_map ];
    rw [ ← hz_eq, ← hw_eq, dicksonF_functional k hk_pos hz_ne, dicksonF_functional k hk_pos hw_ne ] at * ; aesop;
  -- Step 3: Apply eq_or_eq_inv_of_add_inv_eq with a := z^(2^k-1), b := w^(2^k-1) (both nonzero by pow_ne_zero). Need to rewrite z⁻¹^(2^k-1) as (z^(2^k-1))⁻¹ using � inv�_pow.
  have h_eq_or_inv : z ^ (2 ^ k - 1) = w ^ (2 ^ k - 1) ∨ z ^ (2 ^ k - 1) = (w ^ (2 ^ k - 1))⁻¹ := by
    apply eq_or_eq_inv_of_add_inv_eq;
    · exact pow_ne_zero _ hz_ne;
    · exact pow_ne_zero _ hw_ne;
    · simpa using h_eq;
  -- Step 4: Apply frob_2n_fix to get z^(2^(2*n)) = z and w^(2^(2*n)) = w.
  have hz_fix : z ^ (2 ^ (2 * n)) = z := by
    apply frob_2n_fix hz_ne;
    convert quad_root_of_add_inv hz_ne hz_eq using 1;
    rw [ ← map_pow, ← hn, FiniteField.pow_card ]
  have hw_fix : w ^ (2 ^ (2 * n)) = w := by
    apply frob_2n_fix hw_ne (quad_root_of_add_inv hw_ne hw_eq);
    rw [ ← map_pow, ← hn, FiniteField.pow_card ];
  -- Step 5: Apply coprime_mersenne_double' hk_odd hcop to get gcd(2^k-1, 2^(2n)-1) = 1.
  have h_coprime : Nat.Coprime (2 ^ k - 1) (2 ^ (2 * n) - 1) := by
    exact?;
  -- Step 6: In each case from step 3:
  -- - Case z^(2^k-1) = w^(2^k-1): apply eq_of_pow_eq_coprime with N := 2^(2*n), d :=  �2�^k-1 to get z = w.
  -- - Case z^(2^k-1) = w⁻¹^(2^k-1): apply eq_of_pow_eq_coprime to get z = w⁻¹. For w⁻¹ fixed point: (w⁻¹)^(2^(2n)) = (w^(2^(2n)))⁻¹ = w⁻¹, using inv_pow and hw_fix.
  have hz_eq_w : z = w ∨ z = w⁻¹ := by
    apply Or.imp (fun h => by
      apply eq_of_pow_eq_coprime h_coprime hz_ne hw_ne hz_fix hw_fix h) (fun h => by
      apply eq_of_pow_eq_coprime h_coprime hz_ne (inv_ne_zero hw_ne) hz_fix (by
      rw [ inv_pow, hw_fix ]) (by
      rw [ h, inv_pow ])) h_eq_or_inv;
  cases' hz_eq_w with h h <;> simp_all +decide [ add_comm ]

end DicksonKasami