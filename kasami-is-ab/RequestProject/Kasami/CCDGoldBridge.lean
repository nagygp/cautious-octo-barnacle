/-
# CCD-Gold Bridge

Algebraic identities connecting the Kasami function to the Gold function
via the CCD identity d·(2^k+1) = 2^{3k}+1.

## Main results

* `ccd_norm_eq` : G(x)^{2^k+1} = x^{2^{3k}+1}
* `linPolyM_3k_eq_comp` : M_{3k}(z) = M_k(L_k(z))
* `frobenius_3k_in_GF2` : z^{2^{3k}} = z and 3∤n implies z ∈ {0,1}

## References

* Canteaut, Charpin, Dobbertin (2000), §3
-/
import Mathlib
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### §1 CCD Norm Identity -/

/-- The CCD exponent identity: (4^k - 2^k + 1)·(2^k + 1) = 2^{3k} + 1. -/
theorem ccd_exponent_identity (k : ℕ) :
    (4 ^ k - 2 ^ k + 1) * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  have h4 : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]; ring_nf
  have h3k : (2 : ℕ) ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; ring_nf
  have h2k : 2 ^ k ≤ 4 ^ k := by nlinarith [Nat.one_le_pow k 2 (by omega)]
  rw [h4] at h2k ⊢; rw [h3k]; zify [h2k]; ring

/-- Field version: G(x)^{2^k+1} = x^{2^{3k}+1}. -/
theorem ccd_norm_eq (x : F) (k : ℕ) :
    (x ^ (4 ^ k - 2 ^ k + 1)) ^ (2 ^ k + 1) = x ^ (2 ^ (3 * k) + 1) := by
  rw [← pow_mul, ccd_exponent_identity]

/-! ### §2 M_{3k} Factorization -/

/-
The key factorization: M_{3k}(z) = M_k(L_k(z)).
    Proof: L_k(z)^{2^k} + L_k(z) = (z^{2^{2k}}+z^{2^k}+z)^{2^k} + z^{2^{2k}}+z^{2^k}+z
    = z^{2^{3k}} + z^{2^{2k}} + z^{2^k} + z^{2^{2k}} + z^{2^k} + z = z^{2^{3k}} + z.
-/
theorem linPolyM_3k_eq_comp (z : F) (k : ℕ) :
    linPolyM (3 * k) z = linPolyM k (linPolyL k z) := by
  unfold linPolyM linPolyL;
  simp +decide [ ← pow_mul, mul_assoc, add_pow_char_pow ];
  ring;
  grind

/-! ### §3 Frobenius Fixed Points -/

/-
When gcd(k,n)=1 and 3 ∤ n, z^{2^{3k}} = z implies z ∈ {0,1}.
-/
theorem frobenius_3k_in_GF2 (n k : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n)
    (h3 : ¬ 3 ∣ n) (z : F) (hz : z ^ (2 ^ (3 * k)) = z) :
    z = 0 ∨ z = 1 := by
  -- Since $z^{2^{3k}} = z$, we have $z^{2^{gcd(3k,n)}} = z$ by the properties of the Frobenius map.
  have h_frob : z ^ (2 ^ Nat.gcd (3 * k) n) = z := by
    exact?;
  have h_gcd : Nat.gcd (3 * k) n = 1 := by
    exact Nat.Coprime.mul_left ( Nat.prime_three.coprime_iff_not_dvd.mpr h3 ) hgcd;
  simp_all +decide [ pow_succ' ];
  exact or_iff_not_imp_left.mpr fun h => mul_left_cancel₀ h <| by linear_combination h_frob;

end