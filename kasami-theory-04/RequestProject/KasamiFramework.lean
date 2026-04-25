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
* The statement of what remains (AlmostBentVanishing for general k)

## What would need to be formalized for the full general proof

1. Linearized polynomial factorization of the Kasami derivative
2. Quadratic form analysis over GF(2)
3. Rank computation for the associated bilinear form
4. The 3-valued Walsh spectrum theorem

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

open Finset BigOperators

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

attribute [local instance] ZMod.algebra

/-! ### General P₃ Statement -/

/-
**General P₃** for any set S satisfying AlmostBentVanishing.

    Given:
    * S ⊆ F with AlmostBentVanishing
    * v₁, v₂ ∈ F \ {0} with v₁ ≠ v₂

    Then: |{(x,y,z) ∈ S³ : v₁·x + v₂·y + (v₁+v₂)·z = 0}| = |S|³/|F|

    The proof structure:
    1. Reduce to c = v₂/v₁ ≠ 0, 1 via ratio_reduction
    2. Apply spectral_identity to get |F|·N(c) = ∑_b Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c))
    3. Split: b=0 contributes |S|³, b≠0 contributes 0 by AB vanishing
    4. Conclude: N(c) = |S|³/|F|
-/
theorem general_P3 (S : Finset F) (hAB : AlmostBentVanishing F S)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (Fintype.card F : ℤ) * tripleCount F S c = (S.card : ℤ) ^ 3 := by
  convert P3_from_AB F S hAB _ c hc0 hc1 using 1;
  exact fun _ _ _ => trivial

/-! ### Kasami Derivative Set -/

/-- The Kasami power function G(x) = x^{e(k)} where e(k) = 4^k - 2^k + 1. -/
def kasamiPower (k : ℕ) (x : F) : F := x ^ (kasamiExponent k)

/-- The Kasami derivative set Δ_k = {G(b) + G(b+1) + 1 : b ∈ F}. -/
def kasamiDeltaK (k : ℕ) : Finset F :=
  Finset.univ.image (fun b : F => kasamiPower F k b + kasamiPower F k (b + 1) + 1)

/-! ### What remains for the general proof -/

/-- **Kasami Walsh Spectrum Theorem** (Kasami 1971):
    When gcd(k, n) = 1 and n is odd, the Walsh spectrum of the Kasami
    derivative set Δ_k is 3-valued: {0, ±2^{(n+1)/2}}.

    This implies AlmostBentVanishing for Δ_k.

    The proof requires:
    1. Express the Walsh coefficient as a sum involving a quadratic form
    2. Analyze the rank of the quadratic form Q_b(x₁,...,xₙ) over GF(2)
    3. Show the rank is n, n-1, or n-2 depending on b
    4. Apply the quadratic Gauss sum formula

    This is the deepest result needed for the full general Kasami proof. -/
theorem kasami_AB_vanishing (k n : ℕ) (hn : n ≥ 3) (hk : Nat.Coprime k n)
    (hcard : Fintype.card F = 2 ^ n) :
    AlmostBentVanishing F (kasamiDeltaK F k) := by
  sorry

/-- **General Kasami P₃**: Combining AB vanishing with the spectral identity.
    This is the full statement of P₃ for general Kasami exponents. -/
theorem kasami_P3 (k n : ℕ) (hn : n ≥ 3) (hk : Nat.Coprime k n)
    (hcard : Fintype.card F = 2 ^ n)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (Fintype.card F : ℤ) * tripleCount F (kasamiDeltaK F k) c =
    ((kasamiDeltaK F k).card : ℤ) ^ 3 := by
  exact general_P3 F (kasamiDeltaK F k) (kasami_AB_vanishing F k n hn hk hcard) c hc0 hc1

/-! ### Duality Discussion -/

/-
## Categorical Duality — The Dual of P₃

The proof of P₃ operates in two dual worlds connected by the Fourier transform:

**Spatial (Primal) side**: The finite field (F, +) as an abelian group.
  The indicator function 1_S, the triple intersection count N(c).

**Spectral (Dual) side**: The character group F̂ ≅ F (self-dual via trace pairing).
  The Walsh–Hadamard transform Ŝ(b), the triple product sum.

The `spectral_identity` is precisely the bridge:
  ∑_b Ŝ(b) · Ŝ(bc) · Ŝ(b(1+c)) = |F| · N(c)

The "dual statement" of P₃ is:
  ∀ c ∈ F \ {0,1}: ∑_{b≠0} Ŝ(b) · Ŝ(bc) · Ŝ(b(1+c)) = 0

This is exactly `AlmostBentVanishing`. The proof of P₃ *reduces* the spatial
counting problem to this spectral vanishing property.

### Why is this remarkable?

1. The Fourier transform converts a combinatorial counting problem into
   an algebraic vanishing problem.

2. The duality is essential: there is no known purely combinatorial proof
   of P₃ for general Kasami exponents.

3. The self-duality of F_{2^n} (as an elementary abelian 2-group) means
   the "dual theorem" lives in the same field.
-/

end