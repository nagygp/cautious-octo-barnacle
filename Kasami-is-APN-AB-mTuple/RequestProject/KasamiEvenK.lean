import Mathlib
import RequestProject.KasamiAPN
import RequestProject.ExpArith

/-!
# Kasami APN for Even k — Frobenius Twist Extension

The main theorem `kasami_is_apn` requires `Odd k`. This file removes that
restriction via a Frobenius twist argument:

When k is even and n is odd, n - k is odd with the same coprimality.
The Kasami exponents satisfy d_k ≡ d_{n-k} · 2^{2k} (mod 2^n - 1), so on
GF(2ⁿ) the power function x^{d_k} equals Frob_{2k}(x^{d_{n-k}}).
Since Frobenius is an additive bijection, APN is preserved.

For the edge case k = n - 1, the companion parameter n - k = 1 gives the
Gold exponent d₁ = 3 = 2^1 + 1, and Gold APN is proved directly.

## Main result

`kasami_is_apn_general`: x^{d_k} is APN on GF(2ⁿ) for ALL k with
1 < k < n, n odd, gcd(k,n) = 1 — no parity restriction on k.
-/

namespace KasamiEvenK

open KasamiAPN DempwolffMueller Finset BigOperators

set_option maxHeartbeats 800000

/-
═══════════════════════════════════════════
APN preserved under additive bijection
═══════════════════════════════════════════
-/
lemma apn_comp_additive_bijective {F : Type*} [Field F] [CharP F 2]
    {f : F → F} (hf : IsAPN f)
    {σ : F → F} (hσ_bij : Function.Bijective σ)
    (hσ_add : ∀ x y, σ (x + y) = σ x + σ y) :
    IsAPN (σ ∘ f) := by
  intro a ha x y hxy;
  convert hf a ha x y _ using 1;
  exact hσ_bij.injective ( by aesop )

-- ═══════════════════════════════════════════
-- Frobenius properties
-- ═══════════════════════════════════════════

lemma frob_additive {F : Type*} [CommSemiring F] [CharP F 2]
    (j : ℕ) (x y : F) :
    (x + y) ^ (2 ^ j) = x ^ (2 ^ j) + y ^ (2 ^ j) :=
  add_pow_char_pow (p := 2) (n := j) x y

lemma frob_bijective_field {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (j : ℕ) : Function.Bijective (fun x : F => x ^ (2 ^ j)) := by
  have : (fun x : F => x ^ (2 ^ j)) = iterateFrobenius F 2 j := by
    ext x; simp [iterateFrobenius_def]
  rw [this]
  exact Finite.injective_iff_bijective.mp (iterateFrobenius F 2 j).injective

lemma frob_pow_card {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ n) = x := by
  rw [← hn, FiniteField.pow_card]

/-- APN is preserved under Frobenius twist. -/
lemma apn_frob_twist {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {d : ℕ} (hd : IsAPN (fun x : F => x ^ d))
    (j : ℕ) :
    IsAPN (fun x : F => x ^ (d * 2 ^ j)) := by
  have heq : (fun x : F => x ^ (d * 2 ^ j)) =
      (fun x => x ^ (2 ^ j)) ∘ (fun x => x ^ d) := by
    ext x; simp [pow_mul]
  rw [heq]
  exact apn_comp_additive_bijective hd (frob_bijective_field j) (frob_additive j)

/-
═══════════════════════════════════════════
Kasami exponent congruence
═══════════════════════════════════════════
-/
lemma kasami_exp_congr_mod {k n : ℕ} (hk : 0 < k) (hkn : k < n) :
    kasamiExp k % (2 ^ n - 1) =
    (kasamiExp (n - k) * 2 ^ (2 * k)) % (2 ^ n - 1) := by
  rw [ Nat.modEq_of_dvd ];
  unfold kasamiExp;
  norm_num [ Nat.cast_sub ( show 2 ^ ( 2 * ( n - k ) ) ≥ 2 ^ ( n - k ) by gcongr <;> omega ), Nat.cast_sub ( show 2 ^ ( 2 * k ) ≥ 2 ^ k by gcongr <;> omega ) ] ; ring_nf;
  rw [ show n = n - k + k by rw [ Nat.sub_add_cancel hkn.le ] ] ; ring_nf ;
  norm_num [ pow_mul ];
  exact ⟨ 1 - 2 ^ k + 2 ^ k * 2 ^ ( n - k ), by ring ⟩

-- ═══════════════════════════════════════════
-- Power function identity on GF(2ⁿ)
-- ═══════════════════════════════════════════

lemma kasami_pow_frob_identity {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hkn : k < n) (x : F) :
    x ^ kasamiExp k = (x ^ kasamiExp (n - k)) ^ (2 ^ (2 * k)) := by
  by_cases hx : x = 0
  · simp +decide [hx, kasamiExp]
  · rw [← pow_mul]
    have h := kasami_exp_congr_mod hk hkn
    rw [← hn] at h
    exact pow_eq_pow_of_mod_eq hx h

/-- APN for one parameter implies APN for the complement. -/
lemma kasami_apn_of_complement {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hkn : k < n)
    (hapn : IsAPN (fun x : F => x ^ kasamiExp (n - k))) :
    IsAPN (fun x : F => x ^ kasamiExp k) := by
  have heq : (fun x : F => x ^ kasamiExp k) =
      (fun x : F => x ^ (kasamiExp (n - k) * 2 ^ (2 * k))) := by
    ext x; rw [pow_mul]; exact kasami_pow_frob_identity hn k hk hkn x
  rw [heq]
  exact apn_frob_twist hapn (2 * k)

/-
═══════════════════════════════════════════
Gold APN (for edge case k = n - 1)
═══════════════════════════════════════════
-/
lemma frob_fixed_implies_GF2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    {k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime k n)
    {x : F} (hfixed : x ^ (2 ^ k) = x) :
    x = 0 ∨ x = 1 := by
  -- If $x \neq 0$, then $x^{2^k - 1} = 1$.
  by_cases hx0 : x = 0;
  · exact Or.inl hx0;
  · have h_order : x ^ (2 ^ n - 1) = 1 := by
      rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx0 ];
    have h_order : x ^ (Nat.gcd (2 ^ k - 1) (2 ^ n - 1)) = 1 := by
      cases h : 2 ^ k <;> simp_all +decide [ pow_succ, pow_mul ];
    simp_all +decide [ Nat.Coprime, Nat.Coprime.pow ]

lemma gold_differential {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) (a x : F) :
    (x + a) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) =
    a ^ (2 ^ k) * x + a * x ^ (2 ^ k) + a ^ (2 ^ k + 1) := by
  -- By the properties of exponents in characteristic 2, we have $(x + y)^{2^k} = x^{2^k} + y^{2^k}$.
  have h_exp : ∀ (x y : F), (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) := by
    exact?;
  grind

lemma gold_kernel_eq {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) {a : F} (ha : a ≠ 0) (x : F) :
    a ^ (2 ^ k) * x + a * x ^ (2 ^ k) = 0 ↔
    (x * a⁻¹) ^ (2 ^ k) = x * a⁻¹ := by
  simp +decide [ ha, mul_pow, add_comm, eq_inv_mul_iff_mul_eq₀];
  field_simp;
  grind +ring

/-
**Gold APN Theorem.** x^{2^k+1} is APN on GF(2ⁿ) when gcd(k,n) = 1.
-/
theorem gold_is_apn {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hcop : Nat.Coprime k n) :
    IsAPN (fun x : F => x ^ (2 ^ k + 1)) := by
  intro a ha x y hxy
  have h_diff : a ^ (2 ^ k) * (x + y) + a * (x + y) ^ (2 ^ k) = 0 := by
    grind +suggestions;
  -- By gold_kernel_eq, (x + y) * a⁻¹ ∈ {0, 1}.
  have h_kernel : (x + y) * a⁻¹ = 0 ∨ (x + y) * a⁻¹ = 1 := by
    apply frob_fixed_implies_GF2 hn hk hcop;
    grind +suggestions;
  grind

lemma kasamiExp_one : kasamiExp 1 = 3 := by simp [kasamiExp]

lemma kasami_one_is_apn {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime 1 n) :
    IsAPN (fun x : F => x ^ kasamiExp 1) := by
  rw [kasamiExp_one]
  exact gold_is_apn hn 1 one_pos hcop

-- ═══════════════════════════════════════════
-- Parity & coprimality transfer
-- ═══════════════════════════════════════════

lemma odd_sub_even {n k : ℕ} (hn : Odd n) (hk : Even k) (hkn : k ≤ n) :
    Odd (n - k) :=
  Nat.Odd.sub_even hkn hn hk

lemma coprime_sub_self {k n : ℕ} (hkn : k ≤ n) (hcop : Nat.Coprime k n) :
    Nat.Coprime (n - k) n := by
  simpa [ hkn ] using hcop

-- ═══════════════════════════════════════════
-- Even k theorems
-- ═══════════════════════════════════════════

theorem kasami_is_apn_even_k {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_even : Even k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    (hnk : n - k ≥ 2) :
    IsAPN (fun (x : F) => x ^ kasamiExp k) := by
  apply kasami_apn_of_complement hn k (by omega) hkn
  have hcop' : Nat.Coprime (n - k) n := coprime_sub_self (le_of_lt hkn) hcop
  have hodd' : Odd (n - k) := odd_sub_even hn_odd hk_even (le_of_lt hkn)
  exact kasami_is_apn hn (n - k) hnk hodd' (by omega) hn_odd hcop'

theorem kasami_is_apn_even_k_edge {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (_hk_even : Even k) (hkn : k < n)
    (_hn_odd : Odd n) (hcop : Nat.Coprime k n)
    (hnk : n - k = 1) :
    IsAPN (fun (x : F) => x ^ kasamiExp k) := by
  apply kasami_apn_of_complement hn k (by linarith) hkn
  rw [hnk]
  have hcop' : Nat.Coprime (n - k) n := coprime_sub_self (le_of_lt hkn) hcop
  rw [hnk] at hcop'
  exact kasami_one_is_apn hn hcop'

-- ═══════════════════════════════════════════
-- General theorem (unified)
-- ═══════════════════════════════════════════

/-- **Kasami APN — General Form.** The Kasami power function x^d on GF(2ⁿ),
where d = 2^{2k} - 2^k + 1, is APN when n is odd, 1 < k < n, and gcd(k,n) = 1.
No parity restriction on k. -/
theorem kasami_is_apn_general {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ kasamiExp k) := by
  by_cases hk_odd : Odd k
  · exact kasami_is_apn hn k hk hk_odd hkn hn_odd hcop
  · have hk_even : Even k := Nat.not_odd_iff_even.mp hk_odd
    by_cases hnk : n - k ≥ 2
    · exact kasami_is_apn_even_k hn k hk hk_even hkn hn_odd hcop hnk
    · have hnk1 : n - k = 1 := by omega
      exact kasami_is_apn_even_k_edge hn k hk hk_even hkn hn_odd hcop hnk1

end KasamiEvenK