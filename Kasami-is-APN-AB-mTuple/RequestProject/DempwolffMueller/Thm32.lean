import RequestProject.DempwolffMueller.DicksonPoly
import RequestProject.DempwolffMueller.AdjointBij

/-!
# Theorem 3.2 — Main Bijectivity

L(X)·X^k and L(X)·X^{k'} are permutation polynomials on GF(2ⁿ),
where L(X) = ∑_{i=0}^{m-1} X^{2^i} is the truncated trace,
k = 2^{n-1} - 2^{m-1} - 1, and k·k' ≡ 2^{m-1} (mod 2ⁿ-1).

## Key results
- `LxXk_bijective`: L(x)·x^k is bijective
- `LxXk'_bijective`: L(x)·x^{k'} is bijective
- `theorem_3_2`: Main theorem statement
-/

namespace DempwolffMueller

set_option maxHeartbeats 800000

open Finset BigOperators

-- ═══════════════════════════════════════════
-- Layer 10: Reduction to Dickson
-- L(x⁻¹)² · x^{2^m+1} = f_m(x) for x ≠ 0
-- ═══════════════════════════════════════════

lemma truncTrace_sq_mul_inv_eq_dicksonF {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (m : ℕ) {x : F} (hx : x ≠ 0) :
    truncTrace m x⁻¹ ^ 2 * x ^ (2 ^ m + 1) = dicksonF m x := by
  have h_expand : (truncTrace m x⁻¹) ^ 2 = ∑ i ∈ Finset.range m, x⁻¹ ^ (2 ^ (i + 1)) := by
    show truncTrace m x⁻¹ ^ (2 ^ 1) = _
    rw [truncTrace, truncTrace_frob_output_general 2 m x⁻¹ 1]
  rw [ h_expand, Finset.sum_mul ];
  refine' Finset.sum_congr rfl fun i hi => _;
  rw [ inv_pow, inv_mul_eq_div, div_eq_iff ( pow_ne_zero _ hx ) ];
  rw [ ← pow_add, Nat.sub_add_cancel ( show 2 ^ ( i + 1 ) ≤ 2 ^ m + 1 from Nat.le_succ_of_le ( pow_le_pow_right₀ ( by decide ) ( by linarith [ Finset.mem_range.mp hi ] ) ) ) ]

-- ═══════════════════════════════════════════
-- Layer 11: Main injectivity of L(x)·x^k
-- ═══════════════════════════════════════════

/-- L(x)·x^k is injective on F*. -/
lemma LxXk_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1) =
           truncTrace m y * y ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :
    x = y := by
  have h_exp : x ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) * x ^ (2 ^ m + 1) = 1 ∧ y ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) * y ^ (2 ^ m + 1) = 1 := by
    have h_exp : 2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) = 2 ^ n - 1 := by
      rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> simp_all +decide [ pow_succ' ];
      exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show 2 * 2 ^ n ≥ 2 * 2 ^ m from Nat.mul_le_mul_left 2 ( pow_le_pow_right₀ ( by decide ) hm_lt.le ) ), Nat.sub_add_cancel ( show 2 * 2 ^ n - 2 * 2 ^ m ≥ 1 from Nat.sub_pos_of_lt ( by gcongr ; linarith ) ) ] );
    simp +decide [ ← pow_add, h_exp ];
    exact ⟨ by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx ], by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one y hy ] ⟩;
  have h_sq : (truncTrace m x) ^ 2 * x ^ (-(2 ^ m + 1) :) = (truncTrace m y) ^ 2 * y ^ (-(2 ^ m + 1) :) := by
    have h_sq : (truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ 2 = (truncTrace m y * y ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ 2 := by
      rw [heq];
    convert h_sq using 1 <;> norm_cast <;> simp_all +decide [ mul_pow, pow_mul' ];
    · grind;
    · exact Or.inl ( inv_eq_of_mul_eq_one_left h_exp.2 );
  have h_dickson : dicksonF m x⁻¹ = dicksonF m y⁻¹ := by
    convert h_sq using 1;
    · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hx ) |> Eq.symm using 1 ; simp +decide [ pow_add ] ; ring_nf;
      group;
      rw [ ← zpow_add₀ hx ] ; ring_nf ; norm_num;
    · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hy ) using 1 ; simp +decide [ ];
      · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hy ) |> Eq.symm using 1 ; simp +decide [ ];
      · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hy ) using 1 ; simp +decide [ ];
        rw [ ← zpow_natCast, ← zpow_neg ] ; group ; norm_num;
  have := dicksonF_injective_on_units hn m ( by linarith ) hm_odd hcop ( inv_ne_zero hx ) ( inv_ne_zero hy ) h_dickson; aesop;

/-- L(x)·x^k is a bijection on F. -/
lemma LxXk_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
  refine' And.intro _ ( Finite.injective_iff_surjective.mp _ );
  · intro x y hxy
    by_cases hx : x = 0;
    · by_cases hy : y = 0 <;> simp_all +decide [ truncTrace_zero ];
      exact Eq.symm ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy );
    · by_cases hy : y = 0 <;> simp_all +decide;
      · simp_all +decide [ truncTrace_zero ];
        exact absurd ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy ) hx;
      · apply LxXk_injective_on_units hn m hm_pos hm_odd hm_lt hcop hx hy hxy;
  · intro x y hxy
    by_cases hx : x = 0
    ·
      by_cases hy : y = 0 <;> simp_all +decide [ truncTrace_zero ];
      exact Eq.symm ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy )
    by_cases hy : y = 0
    ·
      simp_all +decide [ truncTrace_zero ];
      exact absurd ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy ) hx
    have h_eq : x = y := by
      exact LxXk_injective_on_units hn m hm_pos hm_odd hm_lt hcop hx hy hxy
    exact h_eq

-- ═══════════════════════════════════════════
-- Layer 12: The k' part
-- ═══════════════════════════════════════════

/-- Frobenius adjoint relation for the truncated trace. -/
lemma truncTrace_adj_frob {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ) (hm : m ≤ n) (x : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) ^ (2 ^ (m - 1)) =
    truncTrace m x := by
  by_cases hm : m = 0;
  · aesop;
  · have h_frob : (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) ^ (2 ^ (m - 1)) = ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ (i + (m - 1))) := by
      induction' ( Finset.Ico ( n - m + 1 ) ( n + 1 ) ) using Finset.induction <;> simp_all +decide [ pow_add, pow_mul ];
      rw [ add_pow_char_pow, ‹ ( ∑ i ∈ _, x ^ 2 ^ i ) ^ 2 ^ ( m - 1 ) = _ › ];
    have h_sum : ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ (i + (m - 1))) = ∑ i ∈ Finset.range m, x ^ (2 ^ ((n - m + 1 + i + (m - 1)) % n)) := by
      have h_sum : ∀ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ (i + (m - 1))) = x ^ (2 ^ ((i + (m - 1)) % n)) := by
        intro i hi;
        exact frob_mod 2 hn x (i + (m - 1))
      rw [ Finset.sum_congr rfl h_sum, Finset.sum_Ico_eq_sum_range ];
      rw [ show n + 1 - ( n - m + 1 ) = m by omega ];
    have h_exp : ∀ i ∈ Finset.range m, (n - m + 1 + i + (m - 1)) % n = i := by
      intro i hi; rw [ Nat.mod_eq_sub_mod ] ;
      · rw [ Nat.mod_eq_of_lt ] <;> norm_num at * <;> omega;
      · linarith [ Nat.sub_add_cancel ‹m ≤ n›, Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hm ), Finset.mem_range.mp hi ];
    rw [ h_frob, h_sum, Finset.sum_congr rfl fun i hi => by rw [ h_exp i hi ] ] ; rfl

/-- L(x)·x^{k'} is a permutation polynomial. -/
lemma LxXk'_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) (k' : ℕ)
    (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
            2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by
  apply adjoint_swap_bij;
  exact hn;
  grind +suggestions;
  rotate_left;
  exact fun a b => truncTrace_add m a b;
  case L₁ => exact fun x => ∑ i ∈ Finset.Ico ( n - m + 1 ) ( n + 1 ), x ^ ( 2 ^ i );
  case e => exact ( 2 ^ ( n - 1 ) - 2 ^ ( m - 1 ) - 1 ) * 2 ^ ( n - m + 1 );
  · intro w z; exact (by
    convert frobSum_adjoint_Ico _ _ _ _ _ using 1;
    rotate_left;
    exact F;
    all_goals try infer_instance;
    exact ⟨ Nat.prime_two ⟩;
    exact n;
    exact hn;
    exact m;
    exact le_of_lt hm_lt;
    bv_omega;
    constructor <;> intro h;
    · convert frobSum_adjoint_Ico _ _ _ _ _ using 1;
      all_goals try infer_instance;
      · exact hn;
      · grobner;
    · convert h w |> Eq.symm using 1;
      · rw [ mul_comm ];
      · simp +decide [ mul_comm, frobSum, truncTrace ]);
  · apply trace_nondegenerate;
    · exact hn;
    · grind;
  · rw [ hn ];
    rw [ mul_right_comm, Nat.ModEq.mul_right _ hk' ];
    rw [ ← pow_add, show m - 1 + ( n - m + 1 ) = n by omega ];
    exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by simp );
  · have h_bijective : Function.Bijective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
      apply LxXk_bijective hn m hm_pos hm_odd hm_lt hcop;
    have h_bijective : Function.Bijective (fun x : F => (truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ (2 ^ (n - m + 1))) := by
      convert frob_comp_bijective_right ( p := 2 ) h_bijective ( n - m + 1 ) using 1;
    convert h_bijective using 2;
    rw [ mul_pow, ← pow_mul, ← truncTrace_adj_frob hn m ( by linarith ) ];
    rw [ ← pow_mul, ← pow_add, add_comm ];
    have h_frob : ∀ x : F, x ^ (2 ^ n) = x := by
      exact fun x => by rw [ ← hn, FiniteField.pow_card ] ;
    grind +locals;
  · simp +decide [ ← Finset.sum_add_distrib, add_pow_char_pow ]

-- ═══════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════

/-- **Theorem 3.2** (Dempwolff–Müller). L(X)·X^k is a permutation polynomial on GF(2ⁿ). -/
theorem theorem_3_2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :=
  LxXk_bijective hn m hm_pos hm_odd hm_lt hcop

end DempwolffMueller
