/-
  KasamiAPN.lean

  Proof infrastructure for the Kasami APN theorem and the spectral
  uniformity that yields the triple count.

  This file provides:
  1. Frobenius properties in characteristic 2
  2. The linearized polynomial L(y) = y^(2^(2k)) + y^(2^k) + y and its additivity
  3. The Kasami APN theorem (sorry — deep finite field result)
  4. The spectral uniformity lemma (sorry — requires AB property)
  5. Arithmetic: |Δ|³/|F| = 2^(2n-3)
-/
import Mathlib
import KasamiConjecture

noncomputable section

open Finset BigOperators

set_option maxHeartbeats 800000

namespace KasamiAPN

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Characteristic 2 Frobenius properties -/

/-- In characteristic 2, `x + x = 0`. -/
lemma char2_add_self (x : F) : x + x = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  calc x + x = 2 * x := by ring
    _ = 0 * x := by rw [h2]
    _ = 0 := by ring

/-- In char 2, (a+b)^(2^j) = a^(2^j) + b^(2^j) (Frobenius additivity). -/
lemma frobenius_add (a b : F) (j : ℕ) :
    (a + b) ^ (2 ^ j) = a ^ (2 ^ j) + b ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih]
    have : ∀ x y : F, (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
      intro x y
      have : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring
      rw [this, h2]; ring
    exact this _ _

/-! ## The linearized polynomial -/

/-- The linearized polynomial L(y) = y^(2^(2k)) + y^(2^k) + y. -/
def linearizedL (k : ℕ) (y : F) : F := y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + y

/-- L is additive (GF(2)-linear). -/
lemma linearizedL_add (k : ℕ) (a b : F) :
    linearizedL F k (a + b) = linearizedL F k a + linearizedL F k b := by
  unfold linearizedL
  rw [frobenius_add F a b (2 * k), frobenius_add F a b k]
  ring

/-! ## Core results (sorry'd — deep finite field theory) -/

/-- **The Kasami function is APN when gcd(k,n) = 1.**
    Reference: Kasami (1971), Dillon-Dobbertin (2004).

    Proof outline: The derivative equation reduces to a linearized polynomial
    L(y) = y^(2^(2k)) + y^(2^k) + y whose kernel over GF(2^n) has
    GF(2)-dimension gcd(2k,n). When gcd(k,n)=1, this equals 1 (since n is
    odd for AB functions), giving at most 2 solutions. -/
theorem kasami_is_apn (n k : ℕ)
    (hn : 3 ≤ n) (hcard : Fintype.card F = 2 ^ n) (hcoprime : Nat.Coprime k n) :
    ∀ a : F, a ≠ 0 → ∀ v : F,
      (Finset.univ.filter fun x => kasamiFun F k (x + a) + kasamiFun F k x = v).card ≤ 2 := by
  sorry

/-- **Spectral uniformity for Kasami Delta.**

    For the Kasami function (which is Almost Bent when n is odd and gcd(k,n)=1),
    the set Δ has "flat spectrum": the three-fold convolution count equals |Δ|³/|F|.

    Formally: for any distinct nonzero v₁, v₂,
    |{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}| = |Δ|³ / |F|

    This follows from:
    1. Writing the count as (1/|F|) ∑_a 1̂_Δ(v₁a)·1̂_Δ(v₂a)·1̂_Δ((v₁+v₂)a)
    2. Using the AB property: |1̂_Δ(b)|² ∈ {0, 2^(n-1)} for b ≠ 0
    3. Evaluating the resulting sum -/
theorem spectral_uniformity (n k : ℕ)
    (hn : 3 ≤ n) (hcard : Fintype.card F = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (tripleSet F k v₁ v₂).card = (kasamiDelta F k).card ^ 3 / Fintype.card F := by
  sorry

/-! ## Arithmetic bridge -/

/-
**Arithmetic: (2^(n-1))³ / 2^n = 2^(2n-3) for n ≥ 3.**
-/
theorem delta_cube_div_field (n : ℕ) (hn : 3 ≤ n) :
    (2 ^ (n - 1)) ^ 3 / 2 ^ n = 2 ^ (2 * n - 3) := by
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
  exact Nat.div_eq_of_eq_mul_left ( by positivity ) ( by ring )

/-- **Main theorem: connecting spectral uniformity to the conjecture.**
    Uses `spectral_uniformity` + `kasamiDelta_card` + `delta_cube_div_field`. -/
theorem kasami_triple_from_spectral (n k : ℕ)
    (hn : 3 ≤ n) (hcard : Fintype.card F = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂)
    (h_delta : (kasamiDelta F k).card = 2 ^ (n - 1)) :
    (tripleSet F k v₁ v₂).card = 2 ^ (2 * n - 3) := by
  rw [spectral_uniformity F n k hn hcard hcoprime v₁ v₂ hv₁ hv₂ hne]
  rw [h_delta, hcard]
  exact delta_cube_div_field n hn

end KasamiAPN

end