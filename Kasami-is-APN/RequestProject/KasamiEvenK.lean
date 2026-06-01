import Mathlib
import RequestProject.KasamiAPN
import RequestProject.ExpArith

/-!
# Kasami APN for Even k — DAG Extension

The main theorem `kasami_is_apn` in `KasamiAPN.lean` requires `Odd k`. This file
removes that restriction by a **Frobenius twist** argument:

When `k` is even and `n` is odd, `n - k` is odd with the same coprimality.
The Kasami exponents satisfy `d_k ≡ d_{n-k} · 2^{2k} (mod 2^n - 1)`, so on
GF(2ⁿ) the power function `x^{d_k}` equals `Frob_{2k}(x^{d_{n-k}})`.
Since Frobenius is an additive bijection, APN is preserved.

For the edge case `k = n - 1`, the companion parameter `n - k = 1` gives the
Gold exponent `d₁ = 3`, and Gold APN is proved directly from kernel triviality.

## DAG structure

```
Layer A: APN under additive bijection (apn_comp_additive_bijective)
   │
Layer B: Frobenius properties
   ├── frob_additive:  (x+y)^{2^j} = x^{2^j} + y^{2^j}
   ├── frob_bijective: x ↦ x^{2^j} is bijective on GF(2ⁿ)
   └── frob_pow_card:  x^{2^n} = x on GF(2ⁿ)
   │
Layer C: Kasami exponent congruence (kasami_exp_congr_mod)
   │     d_k ≡ d_{n-k} · 2^{2k}  (mod 2ⁿ-1)
   │
Layer D: Power function identity (kasami_pow_frob_identity)
   │     x^{d_k} = (x^{d_{n-k}})^{2^{2k}}  on GF(2ⁿ)
   │
Layer E: Gold APN (gold_is_apn) — for edge case k = n-1
   │     x^3 is APN on GF(2ⁿ)
   │
Layer F: Parity & coprimality transfer
   │     n odd, k even ⟹ n-k odd, gcd(n-k,n) = 1
   │
Layer G: Main theorem (kasami_is_apn_general)
         Kasami APN for ALL k with gcd(k,n) = 1
```
-/

namespace KasamiEvenK

open KasamiAPN DempwolffMueller Finset BigOperators

set_option maxHeartbeats 800000

/-
═══════════════════════════════════════════════════════
Layer A : APN preserved under additive bijection
═══════════════════════════════════════════════════════

Composing an APN function with an additive bijection yields an APN function.
This is the abstract "Morita equivalence" for APN: the APN property is invariant
under the automorphism group of (F, +).
-/
lemma apn_comp_additive_bijective {F : Type*} [Field F] [CharP F 2]
    {f : F → F} (hf : IsAPN f)
    {σ : F → F} (hσ_bij : Function.Bijective σ)
    (hσ_add : ∀ x y, σ (x + y) = σ x + σ y) :
    IsAPN (σ ∘ f) := by
      intro a ha x y hxy; have := hσ_add; simp_all +decide [ IsAPN ] ; (
      convert hf a ha x y _ using 1;
      exact hσ_bij.injective ( by aesop ));

-- ═══════════════════════════════════════════════════════
-- Layer B : Frobenius properties in characteristic 2
-- ═══════════════════════════════════════════════════════

/-- Frobenius is additive in characteristic 2. -/
lemma frob_additive {F : Type*} [CommSemiring F] [CharP F 2]
    (j : ℕ) (x y : F) :
    (x + y) ^ (2 ^ j) = x ^ (2 ^ j) + y ^ (2 ^ j) :=
  add_pow_char_pow (p := 2) (n := j) x y

/-
Frobenius x ↦ x^{2^j} is bijective on a finite field.
-/
lemma frob_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (j : ℕ) : Function.Bijective (fun x : F => x ^ (2 ^ j)) := by
      -- iterateFrobenius is a RingHom, hence injective on a field
      have : (fun x : F => x ^ (2 ^ j)) = iterateFrobenius F 2 j := by
        ext x; simp [iterateFrobenius_def]
      rw [this]
      exact Finite.injective_iff_bijective.mp (iterateFrobenius F 2 j).injective

/-
The Frobenius identity x^{2^n} = x on GF(2ⁿ).
-/
lemma frob_pow_card {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ n) = x := by
      rw [ ← hn, FiniteField.pow_card ]

/-- APN is preserved under Frobenius twist: if x^d is APN then x^{d·2^j} is APN. -/
lemma apn_frob_twist {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {d : ℕ} (hd : IsAPN (fun x : F => x ^ d))
    (j : ℕ) :
    IsAPN (fun x : F => x ^ (d * 2 ^ j)) := by
  have heq : (fun x : F => x ^ (d * 2 ^ j)) = (fun x => x ^ (2 ^ j)) ∘ (fun x => x ^ d) := by
    ext x; simp [pow_mul]
  rw [heq]
  exact apn_comp_additive_bijective hd (frob_bijective j) (frob_additive j)

/-
═══════════════════════════════════════════════════════
Layer C : Kasami exponent congruence
═══════════════════════════════════════════════════════

The key arithmetic identity: d_k ≡ d_{n-k} · 2^{2k} (mod 2ⁿ - 1).
This is the "bridge" connecting Kasami parameters via Frobenius twist.
-/
lemma kasami_exp_congr_mod {k n : ℕ} (hk : 0 < k) (hkn : k < n) :
    kasamiExp k % (2 ^ n - 1) =
    (kasamiExp (n - k) * 2 ^ (2 * k)) % (2 ^ n - 1) := by
      refine Nat.modEq_of_dvd ?_;
      simp +decide [ kasamiExp ];
      rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ pow_mul', pow_add ];
      · rw [ ← Nat.sub_add_cancel hkn.le ] ; ring_nf ;
        norm_num [ pow_mul ];
        exact ⟨ 1 + 2 ^ k * 2 ^ ( n - k ) - 2 ^ k, by ring ⟩;
      · exact Nat.le_self_pow ( by norm_num ) _;
      · exact Nat.le_self_pow ( by norm_num ) _

/-
═══════════════════════════════════════════════════════
Layer D : Power function identity on GF(2ⁿ)
═══════════════════════════════════════════════════════

On GF(2ⁿ), x^{d_k} = (x^{d_{n-k}})^{2^{2k}} for all x.
This follows from the exponent congruence modulo 2ⁿ - 1.
-/
lemma kasami_pow_frob_identity {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hkn : k < n) (x : F) :
    x ^ kasamiExp k = (x ^ kasamiExp (n - k)) ^ (2 ^ (2 * k)) := by
      by_cases hx : x = 0;
      · simp +decide [ hx, kasamiExp ];
      · rw [ ← pow_mul ];
        convert pow_eq_pow_of_mod_eq hx _ using 1;
        rw [ hn, kasami_exp_congr_mod hk hkn ]

/-- APN for one Kasami parameter implies APN for the complementary parameter. -/
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
═══════════════════════════════════════════════════════
Layer E : Gold APN (for edge case k = n - 1)
═══════════════════════════════════════════════════════

In GF(2ⁿ), x^{2^k} = x implies x ∈ {0, 1} when gcd(k,n) = 1.
This is the finite field intersection: GF(2^k) ∩ GF(2^n) = GF(2^gcd(k,n)) = GF(2).
-/
lemma frob_fixed_implies_GF2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    {k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime k n)
    {x : F} (hfixed : x ^ (2 ^ k) = x) :
    x = 0 ∨ x = 1 := by
      by_contra h_contra;
      -- Since $x$ is a root of unity of � order� $2^k � -� 1$, we have $x^{2^k - 1} = 1$.
      have h_root : x ^ (2 ^ k - 1) = 1 := by
        cases h : 2 ^ k <;> simp_all +decide [ pow_succ, pow_mul ];
      -- Since $x$ is a root of unity of order $2^k - 1$, we have $x^{2^n - 1} = 1$.
      have h_root_n : x ^ (2 ^ n - 1) = 1 := by
        rw [ ← hn, FiniteField.pow_card_sub_one_eq_one ] ; aesop;
      -- Since $x$ is a root of unity of order $2^k - 1$ and $2^n - 1$, we have $x^{\gcd(2^k - 1, 2^n - 1)} = 1$.
      have h_root_gcd : x ^ Nat.gcd (2 ^ k - 1) (2 ^ n - 1) = 1 := by
        rw [ Nat.gcd_comm, pow_gcd_eq_one ] ; aesop;
      simp_all +decide [ Nat.Coprime, Nat.Coprime.pow ]

/-
The Gold differential D_a(x) = (x+a)^{2^k+1} + x^{2^k+1} satisfies
D_a(x) = a^{2^k}·x + a·x^{2^k} + a^{2^k+1}, which is GF(2)-affine in x.
-/
lemma gold_differential {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) (a x : F) :
    (x + a) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) =
    a ^ (2 ^ k) * x + a * x ^ (2 ^ k) + a ^ (2 ^ k + 1) := by
      have := @frob_additive F;
      grind

/-
The Gold kernel equation: a^{2^k}·x + a·x^{2^k} = 0 iff (x/a)^{2^k} = x/a,
when a ≠ 0. Combined with frob_fixed_implies_GF2, this gives x/a ∈ {0,1}.
-/
lemma gold_kernel_eq {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) {a : F} (ha : a ≠ 0) (x : F) :
    a ^ (2 ^ k) * x + a * x ^ (2 ^ k) = 0 ↔
    (x * a⁻¹) ^ (2 ^ k) = x * a⁻¹ := by
      by_cases hx : x = 0 <;> simp +decide [ hx, ha, mul_pow, mul_assoc, mul_comm, mul_left_comm ];
      field_simp;
      grind

/-
**Gold APN Theorem.** x^{2^k+1} is APN on GF(2ⁿ) when gcd(k,n) = 1.
This is the "Gold function" case, simpler than Kasami because the
differential is GF(2)-linear.
-/
theorem gold_is_apn {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hcop : Nat.Coprime k n) :
    IsAPN (fun x : F => x ^ (2 ^ k + 1)) := by
      intro a ha x y hxy;
      -- By gold_kernel_eq with (x+y) in place of x: ((x+y)·a⁻¹)^{2^k} = (x+y)·a⁻¹.
      have h_kernel : ((x + y) * a⁻¹) ^ (2 ^ k) = (x + y) * a⁻¹ := by
        convert gold_kernel_eq k ha ( x + y ) |>.1 _ using 1;
        convert sub_eq_zero.mpr hxy using 1 ; ring;
        simp +decide [ add_pow_char_pow, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ] ; ring;
        grind +ring;
      have := frob_fixed_implies_GF2 hn hk hcop h_kernel;
      grind +splitImp

/-- The Kasami exponent for k = 1 equals the Gold exponent 3 = 2^1 + 1. -/
lemma kasamiExp_one : kasamiExp 1 = 3 := by
  simp [kasamiExp]

/-- Gold APN stated in Kasami exponent form: x^{d₁} is APN. -/
lemma kasami_one_is_apn {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime 1 n) :
    IsAPN (fun x : F => x ^ kasamiExp 1) := by
  rw [kasamiExp_one]
  exact gold_is_apn hn 1 one_pos hcop

/-
═══════════════════════════════════════════════════════
Layer F : Parity & coprimality transfer
═══════════════════════════════════════════════════════

n odd, k even ⟹ n - k odd.
-/
lemma odd_sub_even {n k : ℕ} (hn : Odd n) (hk : Even k) (hkn : k ≤ n) :
    Odd (n - k) := by
      exact Nat.Odd.sub_even hkn hn hk

/-
gcd(k, n) = 1 ⟹ gcd(n - k, n) = 1.
-/
lemma coprime_sub_self {k n : ℕ} (hkn : k ≤ n) (hcop : Nat.Coprime k n) :
    Nat.Coprime (n - k) n := by
      simpa [ hkn ] using hcop

-- ═══════════════════════════════════════════════════════
-- Layer G : Kasami APN for even k
-- ═══════════════════════════════════════════════════════

/-- Kasami APN for even k with n - k ≥ 2.
Uses the Frobenius twist: d_k ≡ d_{n-k} · 2^{2k} (mod 2ⁿ-1),
and applies kasami_is_apn with the odd parameter n - k. -/
theorem kasami_is_apn_even_k {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_even : Even k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    (hnk : n - k ≥ 2) :
    IsAPN (fun (x : F) => x ^ kasamiExp k) := by
  have hk_pos : 0 < k := by omega
  apply kasami_apn_of_complement hn k hk_pos hkn
  have hcop' : Nat.Coprime (n - k) n := coprime_sub_self (le_of_lt hkn) hcop
  have hodd' : Odd (n - k) := odd_sub_even hn_odd hk_even (le_of_lt hkn)
  exact kasami_is_apn hn (n - k) hnk hodd' (by omega) hn_odd hcop'

/-- Kasami APN for even k with n - k = 1 (Gold edge case).
When k = n - 1 is even, d_k ≡ d₁ · 2^{2k} (mod 2ⁿ-1), and d₁ = 3 is Gold. -/
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

-- ═══════════════════════════════════════════════════════
-- Layer H : Unified general theorem
-- ═══════════════════════════════════════════════════════

/-- **Kasami APN — General Form.** The Kasami power function x^d on GF(2ⁿ),
where d = 2^{2k} - 2^k + 1, is APN when n is odd, 1 < k < n, and gcd(k,n) = 1.

No parity restriction on k. This unifies:
- `kasami_is_apn` (odd k, via Theorem 3.2 directly)
- `kasami_is_apn_even_k` (even k, via Frobenius twist to odd n-k ≥ 2)
- `kasami_is_apn_even_k_edge` (even k = n-1, via Gold APN)

The proof decomposes as:
```
                    kasami_is_apn_general
                     /        |        \
              (k odd)    (k even,     (k even,
                |         n-k ≥ 2)    n-k = 1)
                |            |            |
          kasami_is_apn  kasami_is_apn  gold_is_apn
              |           _even_k       _even_k_edge
          [Thm 3.2]         |              |
                     kasami_apn_of    kasami_one_is_apn
                      _complement          |
                          |            gold_is_apn
                   apn_frob_twist
                          |
               apn_comp_additive_bijective
``` -/
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