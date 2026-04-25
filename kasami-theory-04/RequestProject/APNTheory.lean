/-
# Almost Perfect Nonlinear (APN) and Almost Bent (AB) Function Theory

This module defines the key concepts from the theory of APN and AB functions
over finite fields of characteristic 2.

## Main definitions

* `differentialUniformity` : δ(F) = max_a max_b |{x : F(x+a) + F(x) = b}|
* `isAPN` : F has differential uniformity ≤ 2
* `AlmostBentVanishing` : The off-diagonal triple product of Walsh coefficients vanishes
* `kasamiExponent` : e(k) = 4^k - 2^k + 1

## Main results

* `P3_from_AB` : AlmostBentVanishing implies P₃

## References

* Nyberg, "Differentially uniform mappings for cryptography" (1994)
* Carlet, "Boolean Functions for Cryptography and Coding Theory" (2021)
* Kasami, "The Weight Enumerators for Several Classes of Subcodes..." (1971)
-/

import Mathlib
import RequestProject.TraceChar
import RequestProject.WalshHadamard
import RequestProject.SpectralIdentity

open Finset BigOperators

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

attribute [local instance] ZMod.algebra

/-! ### Kasami Exponent -/

/-- The Kasami exponent e(k) = 4^k - 2^k + 1.
    For k = 1: e(1) = 4 - 2 + 1 = 3 (the Gold/cubing exponent).
    The corresponding power function x^{e(k)} has special cryptographic properties
    when gcd(k, n) = 1 (where |F| = 2^n). -/
def kasamiExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- For k = 1, the Kasami exponent is 3. -/
lemma kasamiExponent_one : kasamiExponent 1 = 3 := by norm_num [kasamiExponent]

/-! ### Differential Uniformity -/

/-- The derivative of a function G at point a:
    D_a G(x) = G(x + a) + G(x)
    In characteristic 2, this is also G(x + a) - G(x). -/
def derivative (G : F → F) (a x : F) : F := G (x + a) + G x

/-- A function G : F → F is Almost Perfect Nonlinear (APN) if for every
    nonzero a, the equation G(x+a) + G(x) = b has at most 2 solutions
    for any b. Equivalently, the differential uniformity is ≤ 2. -/
def isAPN (G : F → F) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (b : F),
    (Finset.univ.filter (fun x => derivative F G a x = b)).card ≤ 2

/-! ### Almost Bent Vanishing -/

/-- **AlmostBentVanishing**: The key spectral condition that makes P₃ work.

    For a set S ⊆ F, this says that the off-diagonal triple product of
    Walsh coefficients vanishes for all c ≠ 0, 1:

    ∑_{b ≠ 0} Ŝ(b) · Ŝ(b·c) · Ŝ(b·(1+c)) = 0

    This is equivalent to the Almost Bent property when the Walsh spectrum
    is 3-valued {0, ±2^{(n+1)/2}}.

    For the Gold case (k=1, S = ker(Tr)), this is trivially true because
    Ŝ(b) is nonzero only for b ∈ {0, 1}.

    For general Kasami exponents, this follows from the 3-valued Walsh
    spectrum theorem of Kasami (1971). -/
def nonzeroElems : Finset F := Finset.univ.filter (fun (b : F) => b ≠ 0)

def AlmostBentVanishing (S : Finset F) : Prop :=
  ∀ (c : F), c ≠ 0 → c ≠ 1 →
    (nonzeroElems F).sum (fun b =>
      walshCoeff F (indicator F S) b *
      walshCoeff F (indicator F S) (b * c) *
      walshCoeff F (indicator F S) (b * (1 + c))) = 0

/-! ### P₃ from Almost Bent Vanishing -/

/-- The Kasami derivative set Δ:
    Δ = {x ∈ F : ∃ b ∈ F, x = G(b) + G(b+1) + 1}
    where G(b) = b^{e(k)}. -/
def kasamiDelta (e : ℕ) : Finset F :=
  Finset.univ.image (fun b : F => b ^ e + (b + 1) ^ e + 1)

/-
**Main Theorem (P₃)**: If S satisfies AlmostBentVanishing and has
    cardinality 2^{n-1} (half the field), then the triple intersection
    count N(c) = |S|³/|F| = 2^{2n-3} for all c ≠ 0, 1.

    The proof reduces to the spectral identity + AB vanishing:
    1. By spectral_identity: |F|·N(c) = ∑_b Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c))
    2. Split sum: b=0 contributes Ŝ(0)³ = |S|³
    3. b≠0 contributes 0 by AlmostBentVanishing
    4. Therefore N(c) = |S|³/|F|
-/
theorem P3_from_AB (S : Finset F) (hAB : AlmostBentVanishing F S)
    (hc : ∀ c : F, c ≠ 0 → c ≠ 1 → True) :
    ∀ (c : F), c ≠ 0 → c ≠ 1 →
      (Fintype.card F : ℤ) * tripleCount F S c = (S.card : ℤ) ^ 3 := by
  intro c hc0 hc1;
  have := hAB c hc0 hc1;
  unfold nonzeroElems at this;
  simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ];
  rw [ sub_eq_zero ] at this;
  rw [ ← spectral_identity F S c, this, walshCoeff_indicator_zero ] ; ring

end