import Mathlib
import RequestProject.Thm32
import RequestProject.Lemma31
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg
import RequestProject.AdjointBij

/-!
# Theorem 3.2 (k' part) — Dempwolff & Müller

Proof that `L(X)·X^{k'}` is a permutation polynomial.
-/

namespace DempwolffMueller

open Finset BigOperators

/-
═══════════════════════════════════════════
Layer A : Frobenius–trace interaction (char 2)
═══════════════════════════════════════════

**A1.** The truncated trace commutes with Frobenius.
-/
lemma truncTrace_frob_comm {F : Type*} [CommSemiring F] [CharP F 2]
    (m j : ℕ) (x : F) :
    truncTrace m (x ^ (2 ^ j)) = (truncTrace m x) ^ (2 ^ j) := by
      induction' m with m ih generalizing x;
      · simp +decide [ truncTrace ];
      · simp +decide only [truncTrace, sum_range_succ];
        simp_all +decide [ add_pow_char_pow, pow_mul ];
        simp_all +decide [ ← pow_mul, mul_comm, truncTrace ]

/-
**A2.** The adjoint truncated trace equals a Frobenius shift of L.
-/
lemma truncTraceAdj_eq_frob_L {F : Type*} [CommSemiring F] [CharP F 2]
    {n : ℕ} (m : ℕ) (hm : m ≤ n) (x : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) =
    (truncTrace m x) ^ (2 ^ (n - m + 1)) := by
      have h_frob_comm : truncTrace m (x ^ (2 ^ (n - m + 1))) = (truncTrace m x) ^ (2 ^ (n - m + 1)) := by
        convert truncTrace_frob_comm m ( n - m + 1 ) x using 1;
      rw [ ← h_frob_comm, truncTrace ];
      rw [ Finset.sum_Ico_eq_sum_range ];
      simp +decide [ pow_add, pow_mul, Nat.sub_add_comm hm ];
      rw [ Nat.sub_sub_self hm ]

-- ═══════════════════════════════════════════
-- Layer B : Full-trace adjoint identity
-- ═══════════════════════════════════════════

/-- **B3.** Adjoint property: `Tr(L(w)·z) = Tr(w·L*(z))`. -/
lemma truncTrace_adj_trace_prop {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ) (hm : m ≤ n) (w z : F) :
    truncTrace n (truncTrace m w * z) =
    truncTrace n (w * (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (2 ^ i))) :=
  frobSum_adjoint_Ico 2 hn m hm w z

/-
═══════════════════════════════════════════
Layer D : Power-map arithmetic (pure ℕ)
═══════════════════════════════════════════

**D1.** `gcd(k, 2^n - 1) = 1`.
-/
lemma k_coprime_order' {n : ℕ} (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) :
    Nat.Coprime (2 ^ (n - 1) - 2 ^ (m - 1) - 1) (2 ^ n - 1) := by
      -- Since $d$ divides both $2^{n-1} - 2^{m-1} - 1$ and $2^n - 1$, it must also divide $2^m + 1$.
      suffices h_div : ∀ d, d ∣ 2 ^ (n - 1) - 2 ^ (m - 1) - 1 → d ∣ 2 ^ n - 1 → d ∣ 2 ^ m + 1 by
        refine' Nat.coprime_of_dvd' _;
        intro k hk hk₁ hk₂; specialize h_div k hk₁ hk₂; have := Nat.dvd_gcd ( h_div ) hk₂; simp_all +decide [ Nat.one_le_iff_ne_zero, parity_simps ] ;
        -- Since $k$ divides both $2^m + 1$ and $2^n - 1$, it must also divide $2^{2m} - 1$.
        have h_div_2m : k ∣ 2 ^ (2 * m) - 1 := by
          convert h_div.mul_right ( 2 ^ m - 1 ) using 1 ; rw [ ← Nat.sq_sub_sq ] ; ring;
        -- Since $k$ divides both $2^{2m} - 1$ and $2^n - 1$, it must also divide $2^{\gcd(2m, n)} - 1$.
        have h_div_gcd : k ∣ 2 ^ Nat.gcd (2 * m) n - 1 := by
          simp_all +decide [ ← ZMod.natCast_eq_zero_iff, sub_eq_iff_eq_add ];
        -- Since $\gcd(2m, n) = \gcd(2, n) \cdot \gcd(m, n)$ and $\gcd(m, n) = 1$, we have $\gcd(2m, n) = \gcd(2, n)$.
        have h_gcd_2m_n : Nat.gcd (2 * m) n = Nat.gcd 2 n := by
          exact Nat.Coprime.gcd_mul_right_cancel _ hcop;
        cases hn_odd ; simp_all +decide [ Nat.Coprime ];
      intro d hd₁ hd₂
      have h_div : d ∣ 2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) := by
        convert hd₂ using 1;
        rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> simp_all +decide [ pow_succ' ];
        exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show 2 * 2 ^ n ≥ 2 * 2 ^ m from Nat.mul_le_mul_left _ ( pow_le_pow_right₀ ( by decide ) hm_lt.le ) ), Nat.sub_add_cancel ( show 2 * 2 ^ n - 2 * 2 ^ m ≥ 1 from Nat.sub_pos_of_lt ( by exact mul_lt_mul_of_pos_left ( pow_lt_pow_right₀ ( by decide ) hm_lt ) zero_lt_two ) ) ] );
      have h_simp : 2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) = 2 ^ n - 1 := by
        convert two_k_add_eq ( by linarith : 1 ≤ n ) ( by linarith : 1 ≤ m ) ( by linarith : m < n ) using 1;
      convert Nat.dvd_sub h_div ( hd₁.mul_left 2 ) using 1 ; rw [ h_simp ] ; rw [ Nat.sub_eq_of_eq_add ] ; ring;
      grind

/-- **D2.** Existence of multiplicative inverse of `k` mod `2^n - 1`. -/
lemma exists_pow_inverse' {n : ℕ} (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) :
    ∃ l, (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * l % (2 ^ n - 1) = 1 % (2 ^ n - 1) := by
  have h_inv := k_coprime_order' m hm_pos hm_lt hn_odd hcop
  have hge2 : 1 < 2 ^ n - 1 := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨b, _, hb2⟩ := Nat.exists_mul_mod_eq_one_of_coprime h_inv hge2
  refine ⟨b, ?_⟩
  simp only [hb2, Nat.mod_eq_of_lt hge2]

-- ═══════════════════════════════════════════
-- Layer E : Frobenius shift gives L*-bijection
-- ═══════════════════════════════════════════

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {n : ℕ} (hn : Fintype.card F = 2 ^ n)

/-- **E1.** From `L(x)·x^k` bijective, `L*(x) · x^{k·2^{n-m+1}}` bijective. -/
lemma LadjXe_bijective (m : ℕ) (hm : m ≤ n)
    (hbij : Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1))) :
    Function.Bijective (fun x : F =>
      (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) *
      x ^ ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1))) := by
  have hfrob : Function.Bijective (fun x : F =>
      (truncTrace m x) ^ (2 ^ (n - m + 1)) *
      x ^ ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1))) := by
    have hbij2 : Function.Bijective (fun x : F =>
        (truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ (2 ^ (n - m + 1))) :=
      frob_comp_bijective_right 2 hbij (n - m + 1)
    convert hbij2 using 1
    funext x
    rw [mul_pow, ← pow_mul]
  have heq : (fun x : F =>
      (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) *
      x ^ ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1))) =
    (fun x : F =>
      (truncTrace m x) ^ (2 ^ (n - m + 1)) *
      x ^ ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1))) := by
    funext x
    rw [truncTraceAdj_eq_frob_L m hm x]
  rw [heq]
  exact hfrob

-- ═══════════════════════════════════════════
-- Layer F : Adjoint swap (specialized Lemma 3.1)
-- ═══════════════════════════════════════════

include hn in
/-- **F1.** Adjoint swap via Lemma 3.1. -/
lemma adjoint_swap_bijective
    (L₁ L₂ : F → F) (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, truncTrace n (L₁ w * z) = truncTrace n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, truncTrace n (x * y) ≠ 0)
    (e l : ℕ) (hel : e * l % (2 ^ n - 1) = 1 % (2 ^ n - 1))
    (hbij : Function.Bijective (fun x : F => L₁ x * x ^ e)) :
    Function.Bijective (fun x : F => L₂ x * x ^ l) := by
  have htt : ∀ (f : F), truncTrace n f = frobSum 2 n f := fun f => by simp [truncTrace, frobSum]
  have hAdj' : ∀ w z, frobSum 2 n (L₁ w * z) = frobSum 2 n (w * L₂ z) := by
    intro w z; simp only [← htt]; exact hAdj w z
  have hTnd' : ∀ x : F, x ≠ 0 → ∃ y, frobSum 2 n (x * y) ≠ 0 := by
    intro x hx; obtain ⟨y, hy⟩ := hTnd x hx; exact ⟨y, by simp only [← htt]; exact hy⟩
  have hn1 : 1 ≤ n := by
    by_contra h; push_neg at h; interval_cases n
    simp at hn; have : 1 < Fintype.card F := Fintype.one_lt_card; omega
  exact adjoint_swap_bij 2 hn hn1 L₁ L₂ hL₁_add hL₂_add hAdj' hTnd' e l (by rwa [hn]) hbij

/-
═══════════════════════════════════════════
Layer G : Exponent identification
═══════════════════════════════════════════

Helper: coprimality of k with 2^n - 1 from modular inverse existence.
-/
lemma coprime_of_mul_mod_one {k l N : ℕ} (hN : 2 ≤ N)
    (hkl : k * l % N = 1 % N) : Nat.Coprime k N := by
      exact Nat.Coprime.symm ( Nat.Coprime.coprime_dvd_right ( dvd_mul_right _ _ ) <| by rw [ ← Nat.mod_add_div ( k * l ) N, hkl ] ; norm_num [ Nat.mod_eq_of_lt hN ] )

/-
Helper: k * (k' * 2^{n-m+1}) ≡ 2^{m-1} * 2^{n-m+1} = 2^n ≡ 1 mod (2^n - 1).
-/
lemma exp_mod_chain {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (k k' : ℕ)
    (hkk' : k * k' % (2 ^ n - 1) = 2 ^ (m - 1) % (2 ^ n - 1)) :
    k * (k' * 2 ^ (n - m + 1)) % (2 ^ n - 1) = 1 % (2 ^ n - 1) := by
      rw [ ← mul_assoc, Nat.ModEq.mul_right _ hkk' ];
      convert pow_two_mod_mersenne ( show 1 ≤ n by linarith ) using 1;
      rw [ ← pow_add, show m - 1 + ( n - m + 1 ) = n by omega ]

include hn in
/-- **G1.** Exponent congruence: x^l = x^{k'·2^{n-m+1}} on units. -/
lemma exp_k'_eq_on_units
    (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n) (hn1 : 1 ≤ n)
    (k' l : ℕ)
    (hkl : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * l % (2 ^ n - 1) = 1 % (2 ^ n - 1))
    (hkk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) = 2 ^ (m - 1) % (2 ^ n - 1))
    {x : F} (hx : x ≠ 0) :
    x ^ l = x ^ (k' * (2 ^ (n - m + 1))) := by
  set k := 2 ^ (n - 1) - 2 ^ (m - 1) - 1 with hk_def
  have hcard : Fintype.card F - 1 = 2 ^ n - 1 := by rw [hn]
  apply pow_eq_pow_of_mod_eq hx
  rw [hcard]
  have hN : 2 ≤ 2 ^ n - 1 := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcop : Nat.Coprime k (2 ^ n - 1) :=
    coprime_of_mul_mod_one hN hkl
  have hrhs : k * (k' * 2 ^ (n - m + 1)) % (2 ^ n - 1) = 1 % (2 ^ n - 1) :=
    exp_mod_chain (by omega) (by omega) k k' hkk'
  exact mul_mod_cancel_left hcop (hkl.trans hrhs.symm)

-- ═══════════════════════════════════════════
-- Layer H : Main conclusion
-- ═══════════════════════════════════════════

-- Helper: L* is additive
private lemma Ladj_add' (m : ℕ) (a b : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), (a + b) ^ (2 ^ i)) =
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), a ^ (2 ^ i)) +
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), b ^ (2 ^ i)) := by
  simp [← Finset.sum_add_distrib, add_pow_char_pow]

-- Helper: the adjoint identity in the right form for adjoint_swap_bijective
-- truncTrace_adj_trace_prop says: Tr(L(w)*z) = Tr(w*L*(z))
-- We need: Tr(L*(w)*z) = Tr(w*L(z))
-- This follows from: Tr(L*(w)*z) = Tr(z*L*(w)) [commutativity of mul]
--                                = Tr(truncTrace m z * w) [truncTrace_adj_trace_prop with w↔z]
--                                = Tr(w * truncTrace m z) [commutativity]
include hn in
private lemma adj_identity_reversed
    (m : ℕ) (hm : m ≤ n) (w z : F) :
    truncTrace n ((∑ i ∈ Finset.Ico (n - m + 1) (n + 1), w ^ (2 ^ i)) * z) =
    truncTrace n (w * truncTrace m z) := by
  have h1 := truncTrace_adj_trace_prop hn m hm z w
  -- h1 : Tr(L(z) * w) = Tr(z * L*(w))
  -- i.e. Tr(truncTrace m z * w) = Tr(z * ∑_{Ico} w^{2^i})
  rw [mul_comm (truncTrace m z) w] at h1
  rw [mul_comm z] at h1
  -- h1 : Tr(w * truncTrace m z) = Tr(L*(w) * z)
  exact h1.symm

include hn in
/-- **H1.** `L(X)·X^{k'}` is a permutation polynomial. -/
theorem LxXk'_bijective_v2
    (m : ℕ) (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    (k' : ℕ) (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) = 2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by
  -- Step 1: L(X)·X^k is bijective (Theorem 3.2)
  have h_LXk : Function.Bijective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :=
    theorem_3_2 hn m hm_pos hm_odd hm_lt hn_odd hcop
  -- Step 2: L*(X)·X^{k·2^{n-m+1}} is bijective
  have h_Ladj := LadjXe_bijective m (le_of_lt hm_lt) h_LXk
  -- Step 3: (k*2^{n-m+1}) * k' ≡ 1 mod (2^n-1)
  have h_el : ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1)) * k' % (2 ^ n - 1) = 1 % (2 ^ n - 1) := by
    have h := exp_mod_chain (by omega : 1 ≤ m) (by omega : m ≤ n) (2 ^ (n - 1) - 2 ^ (m - 1) - 1) k' hk'
    -- h : (2^..-1) * (k' * 2^(n-m+1)) % .. = 1 % ..
    -- Need: ((2^..-1) * 2^(n-m+1)) * k' % .. = 1 % ..
    convert h using 2; ring
  -- Step 4: Apply adjoint swap with l = k' directly
  have h_trL_add : ∀ a b : F, truncTrace m (a + b) = truncTrace m a + truncTrace m b := by
    intro a b; simp [truncTrace, ← Finset.sum_add_distrib, add_pow_char_pow]
  have hm_le : m ≤ n := le_of_lt hm_lt
  have hn1 : 1 ≤ n := by omega
  have h_tnd : ∀ x : F, x ≠ 0 → ∃ y, truncTrace n (x * y) ≠ 0 := by
    intro x hx
    have := @trace_nondegenerate F _ _ 2 _ _ n hn hn1 x hx
    simp [truncTrace, frobSum] at this ⊢; exact this
  exact adjoint_swap_bijective hn
    (fun x => ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i))
    (fun x => truncTrace m x)
    (Ladj_add' m)
    h_trL_add
    (fun w z => adj_identity_reversed hn m hm_le w z)
    h_tnd
    ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1)) k'
    h_el
    h_Ladj

end DempwolffMueller