/-
# General Kasami Framework

This module sets up the framework for proving P₃ for general Kasami exponents
e(k) = 4^k - 2^k + 1 with gcd(k, n) = 1.

## Structure
The proof of general P₃ reduces to proving `AlmostBentVanishing` for the
Kasami derivative set. The AB vanishing property for general k is equivalent
to the 3-valued Walsh spectrum theorem of Kasami (1971).

## What is proved here
* The reduction: P₃ follows from the spectral identity + AB vanishing
* The full Kasami AB vanishing via the Walsh spectrum theorem
* The complete P₃ theorem for general Kasami exponents

## References
* Kasami, "The Weight Enumerators for Several Classes of Subcodes of the
  2nd Order Binary Reed-Muller Codes" (1971)
* Canteaut, Charpin, Dobbertin, "Weight Divisibility of Cyclic Codes,
  Highly Nonlinear Functions on GF(2^m), and Crosscorrelation of
  Maximum-Length Sequences" (2000)
-/
import Mathlib
import RequestProject.TraceChar
import RequestProject.WalshHadamard
import RequestProject.SpectralIdentity
import RequestProject.APNTheory
import RequestProject.KasamiWalshSpectrum
open Finset BigOperators
noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-! ### General P₃ Statement -/

/-- **General P₃** for any set S satisfying AlmostBentVanishing.
    Given S ⊆ F with AlmostBentVanishing, for all c ≠ 0, 1:
    |F| · N(c) = |S|³ -/
theorem general_P3 (S : Finset F) (hAB : AlmostBentVanishing F S)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (Fintype.card F : ℤ) * tripleCount F S c = (S.card : ℤ) ^ 3 := by
  convert P3_from_AB F S hAB (fun _ _ _ => trivial) c hc0 hc1 using 1

/-! ### Kasami Derivative Set -/

/-- The Kasami power function G(x) = x^{e(k)}. -/
def kasamiPower (k : ℕ) (x : F) : F := x ^ (kasamiExponent k)

/-- The Kasami derivative set Δ_k = {G(b) + G(b+1) + 1 : b ∈ F}. -/
def kasamiDeltaK (k : ℕ) : Finset F :=
  Finset.univ.image (fun b : F => kasamiPower F k b + kasamiPower F k (b + 1) + 1)

/-- kasamiDeltaK equals kasamiDeltaSet from the spectrum module. -/
lemma kasamiDeltaK_eq_kasamiDeltaSet (k : ℕ) :
    kasamiDeltaK F k = kasamiDeltaSet F k := by
  unfold kasamiDeltaK kasamiDeltaSet kasamiDeltaFn kasamiPower kasamiPowerFn; rfl

/-! ### Kasami AB Vanishing -/

/-- **Kasami Walsh Spectrum Theorem** implies AlmostBentVanishing for Δ_k. -/
theorem kasami_AB_vanishing (k n : ℕ) (hn : n ≥ 3) (hk : Nat.Coprime k n)
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) :
    AlmostBentVanishing F (kasamiDeltaK F k) := by
  rw [kasamiDeltaK_eq_kasamiDeltaSet]
  exact kasami_AB_vanishing_proof F k n hn hk hcard hodd

/-- **General Kasami P₃**: Combining AB vanishing with the spectral identity.
    This is the full statement of P₃ for general Kasami exponents. -/
theorem kasami_P3 (k n : ℕ) (hn : n ≥ 3) (hk : Nat.Coprime k n)
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (Fintype.card F : ℤ) * tripleCount F (kasamiDeltaK F k) c =
    ((kasamiDeltaK F k).card : ℤ) ^ 3 := by
  exact general_P3 F (kasamiDeltaK F k) (kasami_AB_vanishing F k n hn hk hcard hodd) c hc0 hc1

end
