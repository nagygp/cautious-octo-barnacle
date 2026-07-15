import Mathlib
import RequestProject.KasamiPermutation.Core.KasamiAPN

/-!
# The Artin–Schreier telescoping invariant, in every characteristic

## A small elegant invariant that propagates to the headlines

The finite-field engine of this development rests on one small but load-bearing
identity (`KasamiAPN.truncTrace_artin_schreier`):

> in characteristic `2`, the linearized trace `L_k(y) = ∑_{i<k} y^{2ⁱ}` sends the
> Artin–Schreier element `x² + x` to the Frobenius difference `x^{2ᵏ} + x`.

That lemma feeds the MCM → APN chain (it is the reason the Kasami derivative
factors through the two-to-one map `x ↦ x² + x`), so it propagates all the way to
the APN headline `KasamiPerm.MCMtoAPN.kasami_collision_forces_equal_u`.

This module isolates the *mechanism* and shows it is not special to
characteristic `2` at all: it is a pure **telescoping invariant** valid over any
commutative ring, for every exponential characteristic `p`.  We then close the
loop by re-deriving the exact char-2 lemma the development consumes from the
characteristic-free statement — a structural alternative to the bespoke proof in
`Core/KasamiAPN.lean`.

## The invariant

For a commutative ring `R` of exponential characteristic `p`, the `p`-linearized
trace `linTrace p k y = ∑_{i<k} y^{pⁱ}` satisfies, for all `x`,
```
   linTrace p k (xᵖ − x)  =  x^{pᵏ} − x.                               (⋆)
```
Writing `φ` for the Frobenius `y ↦ yᵖ`, the summand
`(xᵖ − x)^{pⁱ} = x^{p^{i+1}} − x^{pⁱ}` is the gap between consecutive Frobenius
powers, so `(⋆)` is `∑_{i<k}(x^{p^{i+1}} − x^{pⁱ})`, a telescoping sum.  The
one-line engine is Mathlib's freshman's dream `sub_pow_expChar_pow`.

## Contents

* `linTrace` and its three defining invariants: `linTrace_add` (additivity),
  `linTrace_frobenius` (Frobenius-equivariance), and `linTrace_artin_schreier`
  (the telescoping glue `(⋆)`).
* `truncTrace_artin_schreier_via_invariant` — the char-2 library lemma
  `KasamiAPN.truncTrace_artin_schreier`, re-derived from `(⋆)`.
-/

namespace KasamiPerm.FieldBridge

open Finset

/-- The `p`-**linearized trace** `L_{p,k}(y) = ∑_{i<k} y^{pⁱ}`.  For `p = 2` it is
`FiniteFieldCharTwo.truncTrace`, the numerator building block of the MCM polynomial. -/
def linTrace {R : Type*} [CommRing R] (p k : ℕ) (y : R) : R :=
  ∑ i ∈ Finset.range k, y ^ (p ^ i)

@[simp] lemma linTrace_zero_len {R : Type*} [CommRing R] (p : ℕ) (y : R) :
    linTrace p 0 y = 0 := by simp [linTrace]

lemma linTrace_succ {R : Type*} [CommRing R] (p k : ℕ) (y : R) :
    linTrace p (k + 1) y = linTrace p k y + y ^ (p ^ k) := by
  simp [linTrace, Finset.sum_range_succ]

/-- **L is additive.**  In exponential characteristic `p`, `linTrace p k` is a
linearized (additive) map, by the freshman's dream `(x+y)^{pⁱ} = x^{pⁱ} + y^{pⁱ}`. -/
lemma linTrace_add {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (k : ℕ) (x y : R) :
    linTrace p k (x + y) = linTrace p k x + linTrace p k y := by
  simp only [linTrace, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_expChar_pow x y p i

/-- **L is Frobenius-equivariant.**  `linTrace p k (xᵖ) = (linTrace p k x)ᵖ`. -/
lemma linTrace_frobenius {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (k : ℕ)
    (x : R) : linTrace p k (x ^ p) = (linTrace p k x) ^ p := by
  simp only [linTrace, sum_pow_char p]
  congr 1; ext i; rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **The telescoping invariant (⋆).**  The linearized trace sends the
Artin–Schreier element `xᵖ − x` to the Frobenius difference `x^{pᵏ} − x`:
```
   ∑_{i<k} (xᵖ − x)^{pⁱ}  =  x^{pᵏ} − x.
```
Each summand `(xᵖ − x)^{pⁱ} = x^{p^{i+1}} − x^{pⁱ}` is the gap between consecutive
Frobenius powers, so the whole sum telescopes. -/
theorem linTrace_artin_schreier {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]
    (k : ℕ) (x : R) :
    linTrace p k (x ^ p - x) = x ^ (p ^ k) - x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [linTrace_succ, ih]
      have hstep : (x ^ p - x) ^ (p ^ k) = x ^ (p ^ (k + 1)) - x ^ (p ^ k) := by
        rw [sub_pow_expChar_pow, ← pow_mul, ← pow_succ']
      rw [hstep]; ring

/-- **The char-2 library lemma, re-derived from the invariant.**

`KasamiAPN.truncTrace_artin_schreier` states `L_k(x² + x) = x^{2ᵏ} + x` in
characteristic `2`.  In characteristic `2`, `x^p − x = x² + x` and
`linTrace 2 = FiniteFieldCharTwo.truncTrace`, so the characteristic-free invariant
`(⋆)` specializes back to exactly the identity the Dobbertin development consumes.

This is a structural alternative to the bespoke proof in `Core/KasamiAPN.lean`. -/
theorem truncTrace_artin_schreier_via_invariant {F : Type*} [CommRing F] [CharP F 2]
    (k : ℕ) (x : F) :
    FiniteFieldCharTwo.truncTrace k (x ^ 2 + x) = x ^ (2 ^ k) + x := by
  haveI hp : ExpChar F 2 := ExpChar.prime Nat.prime_two
  have hsub : x ^ 2 - x = x ^ 2 + x := by rw [CharTwo.sub_eq_add]
  have hadd : x ^ (2 ^ k) - x = x ^ (2 ^ k) + x := by rw [CharTwo.sub_eq_add]
  have h := linTrace_artin_schreier (R := F) 2 k x
  rw [hsub, hadd] at h
  simpa [linTrace, FiniteFieldCharTwo.truncTrace] using h

/-- A finite sanity check of the invariant in `𝔽₅` (`p = 5`, `k = 3`): the
length-3 Artin–Schreier sum collapses to a single Frobenius difference. -/
example (x : ZMod 5) :
    ∑ i ∈ Finset.range 3, (x ^ 5 - x) ^ (5 ^ i) = x ^ (5 ^ 3) - x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact linTrace_artin_schreier 5 3 x

end KasamiPerm.FieldBridge
