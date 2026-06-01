import Mathlib
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg
import RequestProject.AdjointBij

/-!
# Theorem 3.2 — Dempwolff & Müller

L(X)·X^k and L(X)·X^{k'} are permutation polynomials on GF(2ⁿ),
where L(X) = ∑_{i=0}^{m-1} X^{2^i} is the truncated trace,
k = 2^{n-1} - 2^{m-1} - 1, and k·k' ≡ 2^{m-1} (mod 2ⁿ-1).
-/

namespace DempwolffMueller

set_option maxHeartbeats 800000

open Finset BigOperators

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- The truncated trace map L(x) = ∑_{i=0}^{m-1} x^{2^i}. -/
def truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

/-- The Dickson-like polynomial f_m(x) = ∑_{j=0}^{m-1} x^{2^m + 1 - 2^{j+1}}. -/
noncomputable def dicksonF {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ j ∈ Finset.range m, x ^ (2 ^ m + 1 - 2 ^ (j + 1))

-- ═══════════════════════════════════════════
-- Layer 1: Additivity
-- ═══════════════════════════════════════════

lemma truncTrace_add {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x y : F) :
    truncTrace m (x + y) = truncTrace m x + truncTrace m y := by
  simp only [truncTrace, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_char_pow (p := 2) (n := i) x y

lemma truncTrace_zero {F : Type*} [CommSemiring F] (m : ℕ) :
    truncTrace m (0 : F) = 0 := by simp [truncTrace]

lemma truncTrace_one_eq_one {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (hm : Odd m) : truncTrace m (1 : F) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := hm
  unfold truncTrace
  simp_all +decide [show (2 : F) = 0 by exact CharTwo.two_eq_zero]

-- ═══════════════════════════════════════════
-- Layer 2: Telescoping identity
-- L(x)² + L(x) = x^{2^m} + x
-- ═══════════════════════════════════════════

lemma truncTrace_sq_add_self {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (x : F) :
    truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x := by
  unfold truncTrace
  induction m <;> simp_all +decide [Finset.sum_range_succ, pow_succ]; ring
  · rw [mul_two, CharTwo.add_self_eq_zero]
  · simp_all +decide [add_mul, mul_add, pow_mul]; ring
    simp_all +decide [← add_assoc, ← two_mul, CharTwo.two_eq_zero]
    simp_all +decide [add_comm, add_left_comm, add_assoc, sq]
    simp_all +decide [← add_assoc, ← two_mul, CharTwo.two_eq_zero]

-- ═══════════════════════════════════════════
-- Layer 3: Kernel triviality
-- ═══════════════════════════════════════════

lemma frob_fixed_of_truncTrace_zero {F : Type*} [CommRing F] [CharP F 2]
    (m : ℕ) {x : F} (hLx : truncTrace m x = 0) :
    x ^ (2 ^ m) = x := by
  have h_kernel : truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x :=
    truncTrace_sq_add_self m x
  grind

lemma sq_eq_self_imp {F : Type*} [Field F] {x : F} (h : x ^ 2 = x) :
    x = 0 ∨ x = 1 := by
  have hx : x * (x - 1) = 0 := by
    have h2 := h; rw [sq] at h2; linear_combination h2 - x
  rcases mul_eq_zero.mp hx with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- If gcd(m,n) = 1 and m odd, then L(x) = 0 implies x = 0 in GF(2^n). -/
lemma truncTrace_ker_trivial {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_odd : Odd m) (_hm_pos : 1 < m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) {x : F} (hLx : truncTrace m x = 0) :
    x = 0 := by
  have h_x_two : x ^ 2 = x := by
    have h_x_gcd : x ^ (2 ^ Nat.gcd m n) = x := by
      have h_exp : x ^ (2 ^ m) = x ∧ x ^ (2 ^ n) = x :=
        ⟨frob_fixed_of_truncTrace_zero m hLx, by rw [← hn, FiniteField.pow_card]⟩
      have h_exp_gcd : ∀ k l : ℕ,
          x ^ (2 ^ k) = x → x ^ (2 ^ l) = x → x ^ (2 ^ (Nat.gcd k l)) = x := by
        intros k l hk hl
        have h_mod : ∀ a b : ℕ,
            x ^ (2 ^ a) = x → x ^ (2 ^ b) = x → x ^ (2 ^ (a % b)) = x := by
          intros a b ha hb
          have : x ^ (2 ^ a) = (x ^ (2 ^ (a % b))) ^ (2 ^ (b * (a / b))) := by
            rw [← pow_mul, ← pow_add, Nat.mod_add_div]
          have h_iter : ∀ k : ℕ,
              (x ^ (2 ^ (a % b))) ^ (2 ^ (b * k)) = x ^ (2 ^ (a % b)) := by
            intro k; induction k <;> simp_all +decide [pow_succ, pow_mul]
            rw [pow_right_comm, hb]
          grind
        induction' l using Nat.strong_induction_on with l ih generalizing k
        by_cases hl_zero : l = 0
        · aesop
        · rw [Nat.gcd_comm, Nat.gcd_rec]
          simpa [Nat.gcd_comm] using
            ih (k % l) (Nat.mod_lt _ (Nat.pos_of_ne_zero hl_zero)) l hl
              (h_mod k l hk hl)
      exact h_exp_gcd m n (by tauto) (by tauto)
    aesop
  cases eq_or_ne x 0 <;> simp_all +decide [sq]
  exact absurd hLx (by rw [truncTrace_one_eq_one m hm_odd]; simp +decide)

-- ═══════════════════════════════════════════
-- Layer 4-5: Dickson polynomial
-- ═══════════════════════════════════════════

lemma dicksonF_one {F : Type*} [CommSemiring F] (x : F) :
    dicksonF 1 x = x := by simp [dicksonF]

/-
x · f_{m+1}(x) = f_m(x)² + x^{2^{m+1}}
-/
lemma dicksonF_recursion_mul {F : Type*} [Field F] [CharP F 2] (m : ℕ) (x : F) :
    x * dicksonF (m + 1) x = dicksonF m x ^ 2 + x ^ (2 ^ (m + 1)) := by
  rw [ show dicksonF m x = ∑ j ∈ Finset.range m, x ^ ( 2 ^ m + 1 - 2 ^ ( j + 1 ) ) from rfl ] ; rw [ show dicksonF ( m + 1 ) x = ∑ j ∈ Finset.range ( m + 1 ), x ^ ( 2 ^ ( m + 1 ) + 1 - 2 ^ ( j + 1 ) ) from rfl ] ; simp +decide [ Finset.sum_range_succ', pow_succ, pow_mul ] ; ring;
  rw [ ← pow_succ' ];
  rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr ( by positivity ) ) ] ; rw [ show ( ∑ i ∈ Finset.range m, x ^ ( 1 + 2 ^ m - 2 ^ i * 2 ) ) ^ 2 = ∑ i ∈ Finset.range m, x ^ ( 2 * ( 1 + 2 ^ m - 2 ^ i * 2 ) ) from ?_ ] ; simp +decide [ pow_mul', Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ] ; ring;
  · refine' Finset.sum_congr rfl fun i hi => _ ; rw [ ← pow_succ' ] ; rw [ tsub_mul ] ; ring;
    rw [ ← pow_succ' ] ; rw [ show 2 + 2 ^ m * 2 - 2 ^ i * 4 = 1 + 2 ^ m * 2 - 2 ^ i * 4 + 1 from ?_ ] ; ring;
    rw [ ← Nat.add_sub_assoc ] ; ring;
    have := pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( show i + 1 ≤ m from Finset.mem_range.mp hi ) ; ring_nf at *; linarith [ pow_pos ( by decide : 0 < 2 ) i ] ;
  · induction' ( range m : Finset ℕ ) using Finset.induction <;> simp_all +decide [ pow_succ', pow_mul', Finset.sum_range_succ ];
    grind

/-
f_m(z + z⁻¹) = z^{2^m-1} + z^{-(2^m-1)} for z ≠ 0
-/
lemma dicksonF_functional {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) (hm : 0 < m) {z : F} (hz : z ≠ 0) :
    dicksonF m (z + z⁻¹) = z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) := by
  induction' hm with m hm ih;
  · simp +decide [ dicksonF ];
  · -- If $z+z⁻¹=0$, then $z²=1$ so $z=1$ in char $2$, then $dicksonF m 0 = 0$ and $z^{2^m-1}+z^{-(2^m-1)} = 1+1 = 0$.
    by_cases h : z + z⁻¹ = 0;
    · have hz_one : z = 1 := by
        grind;
      simp_all +decide [ Nat.one_le_iff_ne_zero, pow_succ' ];
      unfold dicksonF; simp +decide [ Finset.sum_range_succ' ] ;
      rw [ Finset.sum_eq_zero ] <;> simp +decide [ Nat.sub_eq_zero_iff_le, pow_le_pow_iff_right₀ ];
    · have h_rec : (z + z⁻¹) * dicksonF (m + 1) (z + z⁻¹) = (z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1)) ^ 2 + (z + z⁻¹) ^ (2 ^ (m + 1)) := by
        rw [ ← ih, dicksonF_recursion_mul ];
      refine' mul_left_cancel₀ h _;
      rw [ h_rec ] ; ring;
      simp +decide [ ← mul_pow, pow_succ, pow_mul ] ; ring;
      rw [ show 2 ^ m * 2 - 1 = ( 2 ^ m - 1 ) * 2 + 1 by zify ; cases m <;> simp_all +decide [ pow_succ' ] ; ring ] ; simp +decide [ pow_add, pow_mul, hz ] ; ring;
      simp +decide [ hz, pow_mul', add_pow_char_pow ] ; ring;
      rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;
      rw [ add_pow_char_pow ] ; ring;
      rw [ show 2 ^ m * 2 = ( 2 ^ m - 1 ) * 2 + 2 by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow m 2 zero_lt_two ) ] ] ; ring

-- ═══════════════════════════════════════════
-- Layer 6-8: Coprimality and power maps
-- ═══════════════════════════════════════════

lemma eq_or_eq_inv_of_add_inv_eq {F : Type*} [Field F] [CharP F 2]
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + a⁻¹ = b + b⁻¹) : a = b ∨ a = b⁻¹ := by
  grind +splitIndPred

lemma dicksonF_map_ringHom {F K : Type*} [CommSemiring F] [CommSemiring K]
    (f : F →+* K) (m : ℕ) (x : F) :
    dicksonF m (f x) = f (dicksonF m x) := by
  simp [dicksonF, map_sum, map_pow]

-- ═══════════════════════════════════════════
-- Layer 9: Dickson injectivity on units
-- ═══════════════════════════════════════════

lemma exists_add_inv_rep {F : Type*} [Field F] [CharP F 2]
    {x : F} (hx : x ≠ 0) :
    ∃ z : AlgebraicClosure F, z ≠ 0 ∧
      z + z⁻¹ = algebraMap F (AlgebraicClosure F) x := by
  obtain ⟨z, hz⟩ : ∃ z : AlgebraicClosure F,
      z ^ 2 + (algebraMap F (AlgebraicClosure F) x) * z + 1 = 0 := by
    have := @IsAlgClosed.exists_root (AlgebraicClosure F) _ _
    exact this (Polynomial.X ^ 2 +
      Polynomial.C (algebraMap F (AlgebraicClosure F) x) * Polynomial.X + 1) (by
      erw [Polynomial.degree_add_eq_left_of_degree_lt] <;>
      erw [Polynomial.degree_add_eq_left_of_degree_lt] <;>
      by_cases h : algebraMap F (AlgebraicClosure F) x = 0 <;>
      simp +decide [h]) |> fun ⟨z, hz⟩ => ⟨z, by simpa using hz⟩
  refine' ⟨z, _, _⟩; all_goals grind

lemma frob_2n_eq_self_of_quad_root {K : Type*} [Field K] [CharP K 2]
    {n : ℕ} {a z : K} (hz : z ^ 2 + a * z + 1 = 0) (ha : a ^ (2 ^ n) = a) :
    z ^ (2 ^ (2 * n)) = z := by
  have hz_pow : (z ^ (2 ^ n)) ^ 2 + a * (z ^ (2 ^ n)) + 1 = 0 := by
    convert congr_arg (· ^ 2 ^ n) hz using 1 <;> ring
    simp +decide [add_pow_char_pow, mul_pow, ha]; ring
  have hz_cases : z ^ (2 ^ n) = z ∨ z ^ (2 ^ n) = a + z := by
    grind +ring
  cases' hz_cases with h h <;> simp_all +decide [pow_mul', pow_two]
  rw [add_pow_char_pow, ha]; grind +ring

lemma coprime_mersenne_double' {m n : ℕ}
    (hm_odd : Odd m) (hcop : Nat.Coprime m n) :
    Nat.Coprime (2 ^ m - 1) (2 ^ (2 * n) - 1) := by
  have h_coprime : Nat.gcd m (2 * n) = 1 := by
    exact Nat.Coprime.mul_right
      (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr <| by
        simpa [← even_iff_two_dvd] using hm_odd)) hcop
  simp_all +decide [Nat.Coprime, Nat.Coprime.symm]

lemma dicksonF_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 0 < m) (hm_odd : Odd m) (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hf : dicksonF m x = dicksonF m y) : x = y := by
  have := @exists_add_inv_rep F
  obtain ⟨z, hz₁, hz₂⟩ := this hx
  obtain ⟨w, hw₁, hw₂⟩ := this hy
  have h_fun_eq : z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) =
      w ^ (2 ^ m - 1) + w⁻¹ ^ (2 ^ m - 1) := by
    have h_fun := And.intro
      (dicksonF_functional m hm_pos hz₁) (dicksonF_functional m hm_pos hw₁)
    have h_map := And.intro
      (dicksonF_map_ringHom (algebraMap F (AlgebraicClosure F)) m x)
      (dicksonF_map_ringHom (algebraMap F (AlgebraicClosure F)) m y)
    aesop
  have h_eq_or_inv : z ^ (2 ^ m - 1) = w ^ (2 ^ m - 1) ∨
      z ^ (2 ^ m - 1) = w⁻¹ ^ (2 ^ m - 1) := by
    have := @eq_or_eq_inv_of_add_inv_eq (AlgebraicClosure F)
    convert this (pow_ne_zero (2 ^ m - 1) hz₁) (pow_ne_zero (2 ^ m - 1) hw₁) _
      using 1
    · rw [inv_pow]
    · simpa using h_fun_eq
  have h_eq_or_inv' : z = w ∨ z = w⁻¹ := by
    have h_orders : z ^ (2 ^ (2 * n) - 1) = 1 ∧ w ^ (2 ^ (2 * n) - 1) = 1 := by
      have h_frob : z ^ (2 ^ (2 * n)) = z ∧ w ^ (2 ^ (2 * n)) = w := by
        have h_quad : ∀ (z : AlgebraicClosure F),
            z ^ 2 + (algebraMap F (AlgebraicClosure F)) x * z + 1 = 0 →
            z ^ (2 ^ (2 * n)) = z := by
          intros z hz
          apply frob_2n_eq_self_of_quad_root hz
          rw [← hn, ← map_pow, FiniteField.pow_card]
        have h_quad' : ∀ (z : AlgebraicClosure F),
            z ^ 2 + (algebraMap F (AlgebraicClosure F)) y * z + 1 = 0 →
            z ^ (2 ^ (2 * n)) = z := by
          intros z hz
          apply frob_2n_eq_self_of_quad_root hz
          rw [← hn, ← map_pow, FiniteField.pow_card]
        grind +ring
      exact ⟨mul_left_cancel₀ hz₁ <| by
          rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]
          aesop,
        mul_left_cancel₀ hw₁ <| by
          rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]
          aesop⟩
    have h_coprime : Nat.Coprime (2 ^ m - 1) (2 ^ (2 * n) - 1) :=
      coprime_mersenne_double' hm_odd hcop
    have h_unique : ∀ {a b : AlgebraicClosure F},
        a ^ (2 ^ m - 1) = b ^ (2 ^ m - 1) →
        a ^ (2 ^ (2 * n) - 1) = 1 → b ^ (2 ^ (2 * n) - 1) = 1 → a = b := by
      intros a b hab ha hb
      have h_ratio : (a / b) ^ (2 ^ m - 1) = 1 ∧
          (a / b) ^ (2 ^ (2 * n) - 1) = 1 := by
        by_cases hb : b = 0 <;> simp_all +decide [div_pow]
        rcases n with (_ | _ | n) <;> simp_all +decide [Nat.pow_succ']
        · exact absurd hn (Nat.ne_of_gt (Fintype.one_lt_card))
        · exact absurd hb (by
            rw [zero_pow (Nat.sub_ne_zero_of_lt (by
              linarith [Nat.pow_le_pow_right two_pos
                (show 2 * (n + 1 + 1) ≥ 2 by linarith)]))]
            norm_num)
      have h_gcd : (a / b) ^ Nat.gcd (2 ^ m - 1) (2 ^ (2 * n) - 1) = 1 := by
        rw [Nat.gcd_comm, pow_gcd_eq_one]; aesop
      simp_all +decide [Nat.Coprime, Nat.Coprime.gcd_eq_one]
      exact eq_of_div_eq_one h_gcd
    cases' h_eq_or_inv with h h
    · exact Or.inl (h_unique h (by tauto) (by tauto))
    · specialize @h_unique z w⁻¹; aesop
  cases' h_eq_or_inv' with h h <;> simp_all +decide [add_comm]

/-
═══════════════════════════════════════════
Layer 10: Reduction to Dickson
L(x⁻¹)² · x^{2^m+1} = f_m(x) for x ≠ 0
═══════════════════════════════════════════
-/
lemma truncTrace_sq_mul_inv_eq_dicksonF {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) {x : F} (hx : x ≠ 0) :
    truncTrace m x⁻¹ ^ 2 * x ^ (2 ^ m + 1) = dicksonF m x := by
  unfold truncTrace dicksonF;
  induction' m with m ih;
  · simp +decide;
  · simp_all +decide [ Finset.sum_range_succ ];
    rw [ CharTwo.add_sq ];
    simp_all +decide [ add_mul, pow_succ, pow_mul ];
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, pow_add, pow_mul ];
    convert congr_arg ( · * x ^ 2 ^ m ) ih using 1 ; ring;
    rw [ Finset.sum_mul _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ ← pow_add ] ; rw [ tsub_add_eq_add_tsub ( show 2 * 2 ^ i ≤ 2 ^ m + 1 from _ ) ] ; ring;
    rw [ ← pow_succ' ] ; exact Nat.le_succ_of_le ( pow_le_pow_right₀ ( by decide ) ( by linarith [ Finset.mem_range.mp hi ] ) )

/-
═══════════════════════════════════════════
Layer 11: Main injectivity of L(x)·x^k
═══════════════════════════════════════════
-/
lemma LxXk_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1) =
           truncTrace m y * y ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :
    x = y := by
  -- By squaring both sides of the equation, we get $(truncTrace m x)^2 * x^{2K} = (truncTrace m y)^2 * y^{2K}$.
  have h_sq : (truncTrace m x) ^ 2 * x ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) = (truncTrace m y) ^ 2 * y ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
    convert congr_arg ( · ^ 2 ) heq using 1 <;> ring;
  -- By the arithmetic identity $2K + (2^m + 1) = 2^n - 1$, we get $x^{2K} \cdot x^{2^m + 1} = 1$ on units.
  have h_arith : x ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) * x ^ (2 ^ m + 1) = 1 ∧ y ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) * y ^ (2 ^ m + 1) = 1 := by
    have h_arith : 2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) = 2 ^ n - 1 := by
      convert two_k_add_eq ( show 1 ≤ n from by linarith ) ( show 1 ≤ m from by linarith ) hm_lt using 1;
    rw [ ← pow_add, ← pow_add, h_arith ];
    exact ⟨ by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx ], by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one y hy ] ⟩;
  -- By multiplying both sides of the equation by $x^{2^m + 1} \cdot y^{2^m + 1}$, we get $(truncTrace m x)^2 \cdot x^{-(2^m + 1)} = (truncTrace m y)^2 \cdot y^{-(2^m + 1)}$.
  have h_mul : (truncTrace m x) ^ 2 * x⁻¹ ^ (2 ^ m + 1) = (truncTrace m y) ^ 2 * y⁻¹ ^ (2 ^ m + 1) := by
    simp_all +decide [ mul_assoc, eq_inv_of_mul_eq_one_left h_arith.1, eq_inv_of_mul_eq_one_left h_arith.2 ];
  -- By truncTrace_sq_mul_inv_eq_dicksonF, this gives dicksonF m x⁻¹ = dicksonF m y⁻¹.
  have h_dickson : dicksonF m x⁻¹ = dicksonF m y⁻¹ := by
    rw [ ← truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hx ), ← truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hy ) ];
    grind +locals;
  have := dicksonF_injective_on_units hn m ( by linarith ) hm_odd hcop ( inv_ne_zero hx ) ( inv_ne_zero hy ) h_dickson; aesop;

lemma LxXk_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
  refine' And.intro _ (Finite.injective_iff_surjective.mp _)
  · intro x y hxy
    by_cases hx : x = 0
    · by_cases hy : y = 0 <;> simp_all +decide [truncTrace_zero]
      exact Eq.symm (truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy)
    · by_cases hy : y = 0 <;> simp_all +decide
      · simp_all +decide [truncTrace_zero]
        exact absurd (truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy) hx
      · apply LxXk_injective_on_units hn m hm_pos hm_odd hm_lt hn_odd hcop hx hy hxy
  · intro x y hxy
    by_cases hx : x = 0
    · by_cases hy : y = 0 <;> simp_all +decide [truncTrace_zero]
      exact Eq.symm (truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy)
    · by_cases hy : y = 0
      · simp_all +decide [truncTrace_zero]
        exact absurd (truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy) hx
      · exact LxXk_injective_on_units hn m hm_pos hm_odd hm_lt hn_odd hcop hx hy hxy

-- ═══════════════════════════════════════════
-- Layer 12: The k' part
-- ═══════════════════════════════════════════

lemma truncTrace_adj_frob {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ) (hm : m ≤ n) (x : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) ^ (2 ^ (m - 1)) =
    truncTrace m x := by
  by_cases hm : m = 0
  · aesop
  · have h_frob : (∑ i ∈ Finset.Ico (n - m + 1) (n + 1),
        x ^ (2 ^ i)) ^ (2 ^ (m - 1)) =
        ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ (i + (m - 1))) := by
      induction' (Finset.Ico (n - m + 1) (n + 1)) using Finset.induction <;>
        simp_all +decide [pow_add, pow_mul]
      rw [add_pow_char_pow, ‹(∑ i ∈ _, x ^ 2 ^ i) ^ 2 ^ (m - 1) = _›]
    have h_sum : ∑ i ∈ Finset.Ico (n - m + 1) (n + 1),
        x ^ (2 ^ (i + (m - 1))) =
        ∑ i ∈ Finset.range m,
          x ^ (2 ^ ((n - m + 1 + i + (m - 1)) % n)) := by
      have h_sum : ∀ i ∈ Finset.Ico (n - m + 1) (n + 1),
          x ^ (2 ^ (i + (m - 1))) = x ^ (2 ^ ((i + (m - 1)) % n)) := by
        intro i hi
        exact frob_mod 2 hn x (i + (m - 1))
      rw [Finset.sum_congr rfl h_sum, Finset.sum_Ico_eq_sum_range]
      rw [show n + 1 - (n - m + 1) = m by omega]
    have h_exp : ∀ i ∈ Finset.range m,
        (n - m + 1 + i + (m - 1)) % n = i := by
      intro i hi; rw [Nat.mod_eq_sub_mod]
      · rw [Nat.mod_eq_of_lt] <;> norm_num at * <;> omega
      · linarith [Nat.sub_add_cancel ‹m ≤ n›,
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm),
          Finset.mem_range.mp hi]
    rw [h_frob, h_sum, Finset.sum_congr rfl fun i hi => by rw [h_exp i hi]]; rfl

lemma LxXk'_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) (k' : ℕ)
    (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
            2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by
  apply adjoint_swap_bij;
  exact hn;
  grind +suggestions;
  case L₁ => exact fun x => ∑ i ∈ Finset.Ico ( n - m + 1 ) ( n + 1 ), x ^ ( 2 ^ i );
  any_goals exact ( 2 ^ ( n - 1 ) - 2 ^ ( m - 1 ) - 1 ) * 2 ^ ( n - m + 1 );
  any_goals intro a b; simp +decide [ ← Finset.sum_add_distrib, add_pow_char_pow ];
  · grind +suggestions;
  · intro w z;
    convert frobSum_adjoint_Ico _ _ _ _ using 1;
    rotate_left;
    exact F;
    all_goals try infer_instance;
    exact ⟨ Nat.prime_two ⟩;
    exact n;
    exact hn;
    exact m;
    · linarith;
    · constructor <;> intro h;
      · convert frobSum_adjoint_Ico _ _ _ _ using 1;
        all_goals try infer_instance;
        · exact hn;
        · linarith;
      · convert h z w using 1;
        · convert h z w |> Eq.symm using 1;
          rw [ mul_comm ];
        · convert h z w using 1;
          simp +decide [ mul_comm, frobSum, truncTrace ];
  · have := trace_nondegenerate ( p := 2 ) hn ( by linarith ) b; aesop;
  · rw [ hn ];
    rw [ mul_right_comm, Nat.ModEq.mul_right _ hk' ];
    rw [ ← pow_add, show m - 1 + ( n - m + 1 ) = n by omega ];
    exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] );
  · have h_bijective : Function.Bijective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
      apply LxXk_bijective hn m hm_pos hm_odd hm_lt hn_odd hcop;
    have h_bijective : Function.Bijective (fun x : F => (truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ (2 ^ (n - m + 1))) := by
      apply frob_comp_bijective_right; assumption;
    convert h_bijective using 2 ; ring;
    rw [ ← truncTrace_adj_frob hn m ( by linarith ) ] ; ring;
    simp +decide [ ← pow_add, add_comm, add_left_comm, add_assoc ];
    rw [ show n - m + ( m - 1 ) = n - 1 by omega ];
    have h_frob : ∀ x : F, x ^ (2 ^ n) = x := by
      exact fun x => by rw [ ← hn, FiniteField.pow_card ] ;
    rw [ ← pow_succ, Nat.sub_add_cancel ( by linarith ) ] ; aesop;

-- ═══════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════

/-- **Theorem 3.2** (Dempwolff–Müller). L(X)·X^k is a permutation polynomial
on GF(2ⁿ). -/
theorem theorem_3_2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :=
  LxXk_bijective hn m hm_pos hm_odd hm_lt hn_odd hcop

end DempwolffMueller