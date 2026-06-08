import RequestProject.DempwolffMueller.TruncTrace

/-!
# Dickson Polynomial — Functional Equation and Injectivity

The Dickson-like polynomial `f_m` satisfies a functional equation and is
injective on units under coprimality conditions.

## Key results
- `dicksonF_functional`: f_m(z + z⁻¹) = z^{2^m-1} + z^{-(2^m-1)}
- `dicksonF_injective_on_units`: f_m is injective on F* when m odd, gcd(m,n) = 1
-/

namespace DempwolffMueller

set_option maxHeartbeats 800000

open Finset BigOperators

-- ═══════════════════════════════════════════
-- Layer 4-5: Dickson polynomial
-- ═══════════════════════════════════════════

lemma dicksonF_one {F : Type*} [CommSemiring F] (x : F) :
    dicksonF 1 x = x := by simp [dicksonF]

/-- x · f_{m+1}(x) = f_m(x)² + x^{2^{m+1}} -/
lemma dicksonF_recursion_mul {F : Type*} [Field F] [CharP F 2] (m : ℕ) (x : F) :
    x * dicksonF (m + 1) x = dicksonF m x ^ 2 + x ^ (2 ^ (m + 1)) := by
  unfold dicksonF;
  rw [ Finset.mul_sum _ _ _, Finset.sum_range_succ' ];
  simp +decide [ ← pow_succ', ← pow_add, Nat.sub_sub, add_comm 1, add_assoc ];
  rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ];
  rw [ ← Finset.sum_congr rfl fun i hi => ?_ ];
  rotate_left;
  use fun i => x ^ ( 2 * ( 2 ^ m + 1 - 2 ^ ( i + 1 ) ) );
  · rw [ show 2 ^ ( m + 1 ) + 1 - 2 ^ ( i + 2 ) = 2 * ( 2 ^ m + 1 - 2 ^ ( i + 1 ) ) - 1 from ?_ ];
    · rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr ( mul_ne_zero two_ne_zero ( Nat.sub_ne_zero_of_lt ( by linarith [ Nat.pow_le_pow_right two_pos ( show i + 1 ≤ m from Finset.mem_range.mp hi ) ] ) ) ) ) ];
    · grind;
  · induction' ( range m ) using Finset.induction <;> simp_all +decide [ pow_succ', pow_mul', Finset.sum_range_succ ];
    grind

/-- f_m(z + z⁻¹) = z^{2^m-1} + z^{-(2^m-1)} for z ≠ 0 -/
lemma dicksonF_functional {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) (hm : 0 < m) {z : F} (hz : z ≠ 0) :
    dicksonF m (z + z⁻¹) = z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) := by
  induction' m with m ih generalizing z <;> simp_all +decide [ pow_succ' ];
  have h_simp : (z + z⁻¹) * dicksonF (m + 1) (z + z⁻¹) = (z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1)) ^ 2 + (z + z⁻¹) ^ (2 ^ (m + 1)) := by
    by_cases hm : 0 < m <;> simp_all +decide [ dicksonF_recursion_mul ];
    simp +decide [ dicksonF ];
    grind;
  by_cases h : z + z⁻¹ = 0 <;> simp_all +decide [ pow_succ', pow_mul ];
  · have hz_one : z = 1 := by
      have hz_sq : z^2 = 1 := by
        grind
      grind +suggestions;
    simp_all +decide [ CharTwo.add_self_eq_zero ];
    unfold dicksonF; simp +decide [ Finset.sum_range_succ' ] ;
    rw [ Finset.sum_eq_zero ] <;> simp +decide [ Nat.sub_eq_zero_iff_le ];
    exact fun x hx => pow_le_pow_right₀ ( by decide ) ( by linarith );
  · refine' mul_left_cancel₀ h _;
    convert h_simp using 1 ; ring;
    rw [ show 2 ^ m * 2 - 1 = ( 2 ^ m - 1 ) * 2 + 1 by zify ; norm_num ; ring ] ; norm_num [ pow_add, pow_mul, hz ] ; ring;
    simp +decide [ hz, pow_mul', add_pow_char_pow ] ; ring;
    simp +decide [ show 2 ^ m * 2 = ( 2 ^ m - 1 ) * 2 + 2 by zify ; norm_num ; ring, pow_add, pow_mul', hz ] ; ring;
    rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;

-- ═══════════════════════════════════════════
-- Layer 6-8: Coprimality and power maps
-- ═══════════════════════════════════════════

/-- In char 2: a + a⁻¹ = b + b⁻¹ implies a = b or a = b⁻¹. -/
lemma eq_or_eq_inv_of_add_inv_eq {F : Type*} [Field F] [CharP F 2]
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + a⁻¹ = b + b⁻¹) : a = b ∨ a = b⁻¹ := by
  grind +splitIndPred

lemma dicksonF_map_ringHom {F K : Type*} [CommSemiring F] [CommSemiring K]
    (f : F →+* K) (m : ℕ) (x : F) :
    dicksonF m (f x) = f (dicksonF m x) := by
  simp [dicksonF, map_sum, map_pow]

/-- For x ∈ F* in char 2, ∃ z in AlgClosure with z ≠ 0 and z + z⁻¹ = x. -/
lemma exists_add_inv_rep {F : Type*} [Field F] [CharP F 2]
    {x : F} (hx : x ≠ 0) :
    ∃ z : AlgebraicClosure F, z ≠ 0 ∧
      z + z⁻¹ = algebraMap F (AlgebraicClosure F) x := by
  obtain ⟨z, hz⟩ : ∃ z : AlgebraicClosure F, z ^ 2 + (algebraMap F (AlgebraicClosure F) x) * z + 1 = 0 := by
    have := @IsAlgClosed.exists_root ( AlgebraicClosure F ) _ _;
    exact this ( Polynomial.X ^ 2 + Polynomial.C ( algebraMap F ( AlgebraicClosure F ) x ) * Polynomial.X + 1 ) ( by erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> by_cases h : algebraMap F ( AlgebraicClosure F ) x = 0 <;> simp +decide [ h ] ) |> fun ⟨ z, hz ⟩ => ⟨ z, by simpa using hz ⟩;
  refine' ⟨ z, _, _ ⟩; all_goals grind

/-- If z² + az + 1 = 0 and a^{2^n} = a, then z^{2^{2n}} = z. -/
lemma frob_2n_eq_self_of_quad_root {K : Type*} [Field K] [CharP K 2]
    {n : ℕ} {a z : K} (hz : z ^ 2 + a * z + 1 = 0) (ha : a ^ (2 ^ n) = a) :
    z ^ (2 ^ (2 * n)) = z := by
  have hz_pow : (z ^ (2 ^ n)) ^ 2 + a * (z ^ (2 ^ n)) + 1 = 0 := by
    convert congr_arg ( · ^ 2 ^ n ) hz using 1 <;> ring;
    simp +decide [ add_pow_char_pow, mul_pow, ha ] ; ring;
  have hz_cases : z ^ (2 ^ n) = z ∨ z ^ (2 ^ n) = a + z := by
    grind +ring;
  cases' hz_cases with h h <;> simp_all +decide [ pow_mul', pow_two ];
  rw [ add_pow_char_pow, ha ];
  grind +ring

/-- When m odd and gcd(m,n) = 1, gcd(2^m - 1, 2^{2n} - 1) = 1. -/
lemma coprime_mersenne_double' {m n : ℕ}
    (hm_odd : Odd m) (hcop : Nat.Coprime m n) :
    Nat.Coprime (2 ^ m - 1) (2 ^ (2 * n) - 1) := by
  have h_coprime : Nat.gcd m (2 * n) = 1 := by
    exact Nat.Coprime.mul_right ( Nat.Coprime.symm ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using hm_odd ) ) hcop;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.symm ]

-- ═══════════════════════════════════════════
-- Layer 9: Dickson injectivity on units
-- ═══════════════════════════════════════════

/-- f_m is injective on F* when m odd, gcd(m,n) = 1, |F| = 2^n. -/
lemma dicksonF_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 0 < m) (hm_odd : Odd m) (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hf : dicksonF m x = dicksonF m y) : x = y := by
  have := @exists_add_inv_rep F;
  obtain ⟨z, hz₁, hz₂⟩ := this hx
  obtain ⟨w, hw₁, hw₂⟩ := this hy;
  have h_fun_eq : z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) = w ^ (2 ^ m - 1) + w⁻¹ ^ (2 ^ m - 1) := by
    have h_fun_eq : dicksonF m (z + z⁻¹) = z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) ∧ dicksonF m (w + w⁻¹) = w ^ (2 ^ m - 1) + w⁻¹ ^ (2 ^ m - 1) := by
      grind +suggestions;
    have h_fun_eq : dicksonF m (algebraMap F (AlgebraicClosure F) x) = algebraMap F (AlgebraicClosure F) (dicksonF m x) ∧ dicksonF m (algebraMap F (AlgebraicClosure F) y) = algebraMap F (AlgebraicClosure F) (dicksonF m y) := by
      exact ⟨ dicksonF_map_ringHom _ _ _, dicksonF_map_ringHom _ _ _ ⟩;
    aesop;
  have h_eq_or_inv : z ^ (2 ^ m - 1) = w ^ (2 ^ m - 1) ∨ z ^ (2 ^ m - 1) = w⁻¹ ^ (2 ^ m - 1) := by
    have := @eq_or_eq_inv_of_add_inv_eq ( AlgebraicClosure F );
    convert this ( pow_ne_zero ( 2 ^ m - 1 ) hz₁ ) ( pow_ne_zero ( 2 ^ m - 1 ) hw₁ ) _ using 1;
    · rw [ inv_pow ];
    · simpa using h_fun_eq
  have h_eq_or_inv' : z = w ∨ z = w⁻¹ := by
    have h_eq_or_inv' : z ^ (2 ^ (2 * n) - 1) = 1 ∧ w ^ (2 ^ (2 * n) - 1) = 1 := by
      have h_eq_or_inv' : z ^ (2 ^ (2 * n)) = z ∧ w ^ (2 ^ (2 * n)) = w := by
        have h_eq_or_inv' : ∀ (z : AlgebraicClosure F), z ^ 2 + (algebraMap F (AlgebraicClosure F)) x * z + 1 = 0 → z ^ (2 ^ (2 * n)) = z := by
          intros z hz
          have h_eq_or_inv' : (algebraMap F (AlgebraicClosure F)) x ^ (2 ^ n) = (algebraMap F (AlgebraicClosure F)) x := by
            rw [ ← hn, ← map_pow, FiniteField.pow_card ];
          apply frob_2n_eq_self_of_quad_root; assumption; assumption;
        have h_eq_or_inv' : ∀ (z : AlgebraicClosure F), z ^ 2 + (algebraMap F (AlgebraicClosure F)) y * z + 1 = 0 → z ^ (2 ^ (2 * n)) = z := by
          intros z hz
          apply frob_2n_eq_self_of_quad_root;
          exact hz;
          rw [ ← hn, ← map_pow, FiniteField.pow_card ];
        grind +ring;
      exact ⟨ mul_left_cancel₀ hz₁ <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ; aesop, mul_left_cancel₀ hw₁ <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ; aesop ⟩;
    have h_coprime : Nat.Coprime (2 ^ m - 1) (2 ^ (2 * n) - 1) :=
      coprime_mersenne_double' hm_odd hcop
    have h_eq_or_inv' : ∀ {a b : AlgebraicClosure F}, a ^ (2 ^ m - 1) = b ^ (2 ^ m - 1) → a ^ (2 ^ (2 * n) - 1) = 1 → b ^ (2 ^ (2 * n) - 1) = 1 → a = b := by
      intros a b hab ha hb
      have h_eq_or_inv' : (a / b) ^ (2 ^ m - 1) = 1 ∧ (a / b) ^ (2 ^ (2 * n) - 1) = 1 := by
        by_cases hb : b = 0 <;> simp_all +decide [ div_pow ];
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.pow_succ' ];
        · exact absurd hn ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
        · exact absurd hb ( by rw [ zero_pow ( Nat.sub_ne_zero_of_lt ( by linarith [ Nat.pow_le_pow_right two_pos ( show 2 * ( n + 1 + 1 ) ≥ 2 by linarith ) ] ) ) ] ; norm_num );
      have h_eq_or_inv' : (a / b) ^ Nat.gcd (2 ^ m - 1) (2 ^ (2 * n) - 1) = 1 := by
        rw [ Nat.gcd_comm, pow_gcd_eq_one ] ; aesop;
      simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ];
      exact eq_of_div_eq_one h_eq_or_inv';
    cases' h_eq_or_inv with h h;
    · exact Or.inl ( h_eq_or_inv' h ( by tauto ) ( by tauto ) );
    · specialize @h_eq_or_inv' z w⁻¹ ; aesop;
  cases' h_eq_or_inv' with h h <;> simp_all +decide [ add_comm ]

end DempwolffMueller
