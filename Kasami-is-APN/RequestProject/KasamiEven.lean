import Mathlib
import RequestProject.KasamiAPNNew
import RequestProject.FrobAlg
import RequestProject.ExpArith

/-!
# Kasami APN for Even k — DAG Layers

Extension of the Kasami APN theorem from odd k to all k with gcd(k,n) = 1.

## Mathematical Background

The Kasami function x^d on GF(2ⁿ), d = 2^{2k} - 2^k + 1, is known to be APN
whenever gcd(k,n) = 1 (Kasami 1971, Dempwolff–Müller 2013). The file
`KasamiAPNNew.lean` proves this for **odd k**. This file extends the result
to **even k** via the *Frobenius complement trick*:

    d_k · 2^{2(n-k)} ≡ d_{n-k} (mod 2ⁿ - 1)

Since n is necessarily odd (forced by gcd(k,n) = 1 with k even) and n-k is odd,
the odd-k theorem applies to the complementary parameter n-k.

## DAG Structure

    Layer A: APN invariance under additive bijections (abstract)
        ↓
    Layer B: Frobenius twist for power functions
        ↓
    Layer C: Gold APN (x³ is APN — handles the n-k = 1 boundary)
        ↓
    Layer D: Kasami exponent complement arithmetic
        ↓
    Layer E: Even-k reduction and general theorem
-/

namespace KasamiAPN

open DempwolffMueller Finset BigOperators

set_option maxHeartbeats 800000

-- ═══════════════════════════════════════════
-- Layer A: APN invariance under additive bijections
--
-- This captures the "functorial" property: APN is defined via
-- differentials, and additive maps preserve differentials.
-- Cf. Morita equivalence: equivalent presentations of the
-- same algebraic structure preserve all "invariant" properties.
-- ═══════════════════════════════════════════

section LayerA

variable {F : Type*} [Field F] [CharP F 2]

/-
Post-composing an APN function with an additive injection yields APN.
This is the key abstract transfer principle.

*Proof*: φ(f(x+a) + f(x)) = φ(f(y+a) + f(y)) by additivity of φ,
so f(x+a) + f(x) = f(y+a) + f(y) by injectivity of φ,
and APN of f concludes.
-/
lemma apn_comp_additive_inj (f : F → F) (φ : F → F)
    (hφ_add : ∀ a b, φ (a + b) = φ a + φ b)
    (hφ_inj : Function.Injective φ)
    (hf : IsAPN f) :
    IsAPN (fun x => φ (f x)) := by
  intro a ha x y hxy;
  exact hf a ha x y ( by simpa [ ← hφ_add ] using hφ_inj ( by simpa [ ← hφ_add ] using hxy ) )

/-
Converse: if φ ∘ f is APN and φ is an additive bijection, then f is APN.
This is the "Morita dual" direction — the equivalence is symmetric.
-/
lemma apn_of_comp_additive_bij (f : F → F) (φ : F → F)
    (hφ_add : ∀ a b, φ (a + b) = φ a + φ b)
    (hφ_bij : Function.Bijective φ)
    (h : IsAPN (fun x => φ (f x))) :
    IsAPN f := by
  intro a ha x y hxy;
  exact h a ha x y ( by simpa [ ← hφ_add ] using congr_arg φ hxy )

/-- APN is an invariant of the "additive bijection equivalence class".
This is the analogue of a Morita-invariant property: two functions
related by an additive automorphism have the same APN status. -/
lemma apn_iff_comp_additive_bij (f : F → F) (φ : F → F)
    (hφ_add : ∀ a b, φ (a + b) = φ a + φ b)
    (hφ_bij : Function.Bijective φ) :
    IsAPN f ↔ IsAPN (fun x => φ (f x)) := by
  exact ⟨apn_comp_additive_inj f φ hφ_add hφ_bij.injective,
         apn_of_comp_additive_bij f φ hφ_add hφ_bij⟩

end LayerA

-- ═══════════════════════════════════════════
-- Layer B: Frobenius twist for power functions
--
-- The Frobenius x ↦ x^{2^s} is an additive bijection on GF(2ⁿ).
-- Combined with Layer A, this gives: x^d is APN iff x^{d·2^s} is APN.
-- ═══════════════════════════════════════════

section LayerB

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-
APN of x^d implies APN of x^{d·2^s} (forward Frobenius twist).
-/
lemma apn_pow_of_frobenius_mul (d s : ℕ)
    (hf : IsAPN (fun (x : F) => x ^ d)) :
    IsAPN (fun (x : F) => x ^ (d * 2 ^ s)) := by
  simp_all +decide [ IsAPN ];
  intro a ha x y h; contrapose! h; simp_all +decide [ pow_mul ] ;
  have h_frobenius : ∀ x y : F, (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
    grobner;
  induction' s with s ih generalizing x y <;> simp_all +decide [ pow_succ, pow_mul ];
  · exact fun h' => h.2 ( hf a ha x y h' |> Or.resolve_left <| by tauto );
  · grind +ring

/-
APN of x^{d·2^s} implies APN of x^d (reverse Frobenius twist).
-/
lemma apn_pow_of_frobenius_mul_rev (d s : ℕ)
    (hf : IsAPN (fun (x : F) => x ^ (d * 2 ^ s))) :
    IsAPN (fun (x : F) => x ^ d) := by
  convert apn_of_comp_additive_bij _ _ _ _ _ using 1;
  exact fun x => x ^ ( 2 ^ s );
  · exact?;
  · exact?;
  · simpa only [ ← pow_mul, mul_comm ] using hf

/-- **Frobenius APN equivalence** for power functions:
x^d is APN iff x^{d·2^s} is APN. -/
theorem apn_pow_frobenius_iff (d s : ℕ) :
    IsAPN (fun (x : F) => x ^ d) ↔ IsAPN (fun (x : F) => x ^ (d * 2 ^ s)) :=
  ⟨apn_pow_of_frobenius_mul d s, apn_pow_of_frobenius_mul_rev d s⟩

end LayerB

-- ═══════════════════════════════════════════
-- Layer C: Gold APN — x³ is APN in characteristic 2
--
-- This handles the boundary case n-k = 1 in the complement reduction.
-- The proof is entirely elementary: the collision equation factors as
-- a·(x+y)·(x+y+a) = 0 in characteristic 2.
-- ═══════════════════════════════════════════

section LayerC

variable {F : Type*} [Field F] [CharP F 2]

/-
Cube differential identity in characteristic 2:
(x+a)³ + x³ = a·x² + a²·x + a³.
Uses the fact that 3 ≡ 1 (mod 2) and (x+a)² = x² + a² in char 2.
-/
lemma cube_differential (x a : F) :
    (x + a) ^ 3 + x ^ 3 = a * x ^ 2 + a ^ 2 * x + a ^ 3 := by
  grind +ring

/-
The cube collision equation factors in characteristic 2:
if (x+a)³ + x³ = (y+a)³ + y³ then a·(x+y)·(x+y+a) = 0.
This is the characteristic-2 analogue of the general factorization
for monomial differentials.
-/
lemma cube_collision_factor (x y a : F)
    (h : (x + a) ^ 3 + x ^ 3 = (y + a) ^ 3 + y ^ 3) :
    a * (x + y) * (x + y + a) = 0 := by
  grind +ring

/-
**Gold APN Theorem (k=1)**: x³ is APN on any field of characteristic 2.

*Proof*: The differential collision factors as a·(x+y)·(x+y+a) = 0.
Since a ≠ 0, we get (x+y)·(x+y+a) = 0, hence x+y = 0 or x+y = a,
i.e., y = x or y = x+a.
-/
theorem gold_cube_is_apn : IsAPN (fun (x : F) => x ^ 3) := by
  intro a ha x y hxy;
  grind

/-- The Kasami exponent at k=1 equals 3 (the Gold/cube exponent). -/
@[simp] lemma kasami_exp_one : kasamiExp 1 = 3 := by
  unfold kasamiExp; norm_num

end LayerC

-- ═══════════════════════════════════════════
-- Layer D: Kasami exponent complement arithmetic
--
-- The key congruence: d_k · 2^{2(n-k)} ≡ d_{n-k} (mod 2ⁿ-1).
-- This follows from the factorization:
--   d_k · 2^{2(n-k)} - d_{n-k} = (2ⁿ - 1)·(2ⁿ + 1 - 2^{n-k})
-- ═══════════════════════════════════════════

section LayerD

/-
gcd(n-k, n) = gcd(k, n) for k ≤ n.
Follows from the Euclidean algorithm: gcd(n-k, n) = gcd(n-k, k) = gcd(k, n).
-/
lemma gcd_complement {k n : ℕ} (hkn : k ≤ n) :
    Nat.gcd (n - k) n = Nat.gcd k n := by
  simp +decide [ hkn, Nat.gcd_comm ]

/-
If n is odd and k is even with k ≤ n, then n - k is odd.
-/
lemma complement_odd_of_even {k n : ℕ} (hn : Odd n) (hk : Even k) (hkn : k ≤ n) :
    Odd (n - k) := by
  grind +qlia

/-
The Kasami exponent complement congruence:
d_k · 2^{2(n-k)} ≡ d_{n-k} (mod 2ⁿ - 1).

*Proof*: Direct calculation shows
  d_k · 2^{2(n-k)} - d_{n-k} = (2ⁿ - 1)·(2ⁿ + 1 - 2^{n-k}).
-/
lemma kasami_exp_complement_congr {k n : ℕ} (hk : 0 < k) (hn : 1 < n) (hkn : k < n) :
    (kasamiExp k * 2 ^ (2 * (n - k))) % (2 ^ n - 1) =
    kasamiExp (n - k) % (2 ^ n - 1) := by
  unfold kasamiExp; zify; norm_num; ring;
  rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ pow_mul ] <;> ring;
  · rw [ ← pow_add, ← pow_add ] ; rw [ show n = k + ( n - k ) by rw [ Nat.add_sub_cancel' hkn.le ] ] ; ring; norm_num [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ; ring;
    exact ⟨ 2 ^ k * 2 ^ ( n - k ) + 1 - 2 ^ ( n - k ), by ring ⟩;
  · exact pow_le_pow_right₀ ( by decide ) ( by linarith );
  · gcongr <;> linarith

/-
Two functions that agree pointwise have the same APN status.
-/
lemma apn_congr {F : Type*} [Field F] [CharP F 2] {f g : F → F}
    (h : ∀ x, f x = g x) : IsAPN f ↔ IsAPN g := by
  unfold IsAPN; aesop;

/-
Power functions with congruent exponents agree on GF(2ⁿ),
using Fermat's little theorem: x^{|F|-1} = 1 for x ≠ 0.
-/
lemma pow_congr_on_field {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) {d₁ d₂ : ℕ}
    (hd : d₁ % (2 ^ n - 1) = d₂ % (2 ^ n - 1))
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (x : F) :
    x ^ d₁ = x ^ d₂ := by
  by_cases hx : x = 0;
  · rw [ hx, zero_pow hd₁.ne', zero_pow hd₂.ne' ];
  · exact pow_eq_pow_of_mod_eq hx ( by simpa [ hn ] using hd )

/-
kasamiExp k > 0 for all k.
-/
lemma kasami_exp_pos (k : ℕ) : 0 < kasamiExp k := by
  exact Nat.succ_pos _

/-
On GF(2ⁿ), x^{d_k} and x^{d_{n-k}} are APN-equivalent via Frobenius.
The proof chains: x^{d_k} APN ↔ x^{d_k · 2^{2(n-k)}} APN (Frobenius twist)
                                ↔ x^{d_{n-k}} APN (congruent exponents).
-/
lemma kasami_apn_complement_equiv {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn1 : 1 < n)
    {k : ℕ} (hk : 0 < k) (hkn : k < n) :
    IsAPN (fun (x : F) => x ^ kasamiExp k) ↔
    IsAPN (fun (x : F) => x ^ kasamiExp (n - k)) := by
  -- By the properties of the Frobenius map, we can rewrite the APN condition for $x^{d_k}$ in terms of $x^{d_{n-k}}$.
  have h_frob : IsAPN (fun x : F => x ^ (kasamiExp k)) ↔ IsAPN (fun x : F => x ^ (kasamiExp k * 2 ^ (2 * (n - k)))) := by
    exact?;
  convert h_frob using 2;
  ext x;
  convert pow_congr_on_field hn _ _ _ _ using 1;
  · exact Eq.symm ( kasami_exp_complement_congr hk hn1 hkn );
  · exact kasami_exp_pos _;
  · exact mul_pos ( kasami_exp_pos k ) ( pow_pos ( by decide ) _ )

end LayerD

-- ═══════════════════════════════════════════
-- Layer E: Even-k reduction and general theorem
-- ═══════════════════════════════════════════

section LayerE

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- Kasami APN for even k with k < n-1: reduces to odd n-k via complement. -/
theorem kasami_is_apn_even_interior
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_even : Even k) (hkn : k < n) (hkn' : k < n - 1)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp k)) := by
  rw [kasami_apn_complement_equiv hn (by linarith) (by linarith) hkn]
  apply kasami_is_apn hn (n - k)
  · omega
  · exact complement_odd_of_even hn_odd hk_even hkn.le
  · omega
  · exact hn_odd
  · unfold Nat.Coprime at *
    rw [gcd_complement hkn.le]
    exact hcop

/-- Kasami APN for k = n-1 (the boundary even case):
d_{n-1} is Frobenius-equivalent to d₁ = 3, which is Gold APN. -/
theorem kasami_is_apn_boundary
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 1 < n)
    (hn_odd : Odd n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp (n - 1))) := by
  rw [kasami_apn_complement_equiv hn hn_pos (by omega) (by omega)]
  have h1 : n - (n - 1) = 1 := by omega
  rw [h1, kasami_exp_one]
  exact gold_cube_is_apn

/-- **General Kasami APN Theorem.** For any k with 1 < k < n, gcd(k,n) = 1,
and n odd, x^{d_k} is APN on GF(2ⁿ), regardless of the parity of k.

This unifies the odd-k case (from `kasami_is_apn`) with the even-k case
(via Frobenius complement reduction). -/
theorem kasami_is_apn_general
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp k)) := by
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · -- Even k: use complement reduction
    by_cases hkn' : k < n - 1
    · exact kasami_is_apn_even_interior hn k hk hk_even hkn hkn' hn_odd hcop
    · -- k = n - 1
      have hk_eq : k = n - 1 := by omega
      subst hk_eq
      exact kasami_is_apn_boundary hn (by linarith) hn_odd
  · -- Odd k: directly from kasami_is_apn
    exact kasami_is_apn hn k hk hk_odd hkn hn_odd hcop

end LayerE

end KasamiAPN