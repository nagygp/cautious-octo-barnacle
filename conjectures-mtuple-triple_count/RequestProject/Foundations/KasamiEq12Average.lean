import RequestProject.Foundations.KasamiEvenMCubing
import Mathlib

/-!
# Foundations — Dillon–Dobbertin equation (12): the literal GF(4)-coset averaging

This module **implements the character-sum averaging of Dillon–Dobbertin's
equation (12)** on top of the even-`m` GF(4) / cubing substrate of
`KasamiEvenMCubing.lean`:

```
   Ŝ_d^λ(a) = (1/3) · ∑_{μ ∈ GF(4)*} Q̂^λ_{aμ}(0),
   q^λ_{aμ}(x) = Tr(λ x^{2^{3k}+1} + aμ x^{2^k+1}).
```

The factor `1/3` and the three scalars `μ ∈ GF(4)*` are produced by two literal,
sorry-free summation identities — the two mechanisms named in the derivation:

* **the cubing 3-to-1 map** (`cube_sum_threeToOne`):
  `∑_{x∈GF(2ⁿ)*} φ(x³) = 3 · ∑_{y ∈ cubes} φ(y)`, the precise summation form of the
  3-to-1 fiber structure `cube_fiber_card`; and
* **the GF(4)\* scalar action** (`gf4_scalar_action_sum`):
  `∑_{μ ∈ GF(4)*} ∑_{x∈GF(2ⁿ)*} φ(μ·x) = 3 · ∑_{x∈GF(2ⁿ)*} φ(x)`, the three-fold
  averaging from the order-3 group `GF(4)*` acting by multiplication
  (`card_cubeRootsOne`).

The right-hand terms `Q̂^λ_{aμ}(0)` are then **evaluated through the quadratic-form
Gauss-sum / rank substrate**: each is the Gauss sum of the Appendix-A.4 auxiliary
form `λ x^{2^{3k}+1} + aμ x^{2^k+1}`, which is a genuine quadratic form
(`kasamiAux_isQuadraticForm`), so it lies in `{0, ±2^{(n+r)/2}}`
(`eq12_term_spectrum`, a specialization of `kasamiAux_gaussSum_spectrum`).
Consequently, once the field substitution `x = u^{2^k+1}` that realizes (12) is
supplied (carried as a named hypothesis `h12`, the irreducible finite-field
substitution core), the Kasami Walsh value `3·W` is exhibited as a sum of three
quadratic-form Gauss sums each in the spectrum set
(`three_mul_kasamiWalsh_terms_spectrum`).

## Scope

The two averaging mechanisms and the term evaluation are sorry-free.  The literal
substitution `x = u^{2^k+1}` linking the (non-quadratic) Kasami exponent to the
Gold exponents `2^{3k}+1`, `2^k+1` of the auxiliary forms — i.e. equation (12)
itself — is the remaining finite-field-algebra core, carried as a named hypothesis
rather than an axiom or `sorry`.

## Sources

Dillon–Dobbertin (FFA 2004), §7 (eq. (12)) and Appendix A.4; Lidl–Niederreiter,
*Finite Fields*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The cubing 3-to-1 summation identity (the literal `1/3`) -/

/-
**The cubing 3-to-1 summation identity.**  For `n` even (so cubing is 3-to-1
on `GF(2ⁿ)*`, `cube_fiber_card`), every cube has exactly three cube roots, so
summing `φ ∘ (·³)` over `GF(2ⁿ)*` triple-counts the cubes:
`∑_{x} φ(x³) = 3 · ∑_{y ∈ cubes} φ(y)`.  This is the summation form behind the
factor `1/3` in equation (12).
-/
theorem cube_sum_threeToOne {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n)
    (φ : Fˣ → ℤ) :
    ∑ x : Fˣ, φ (x ^ 3)
      = 3 * ∑ y ∈ Finset.image (fun x : Fˣ => x ^ 3) univ, φ y := by
  have h_sum_eq : ∀ y ∈ Finset.image (fun x : Fˣ => x ^ 3) Finset.univ, (Finset.filter (fun x : Fˣ => x ^ 3 = y) Finset.univ).card = 3 := by
    exact fun y hy => Vanish.Foundations.cube_fiber_card hcard hn y <| Finset.mem_image.mp hy |> fun ⟨ x, _, hx ⟩ => ⟨ x, hx ⟩;
  rw [ Finset.mul_sum, Finset.sum_image' ];
  intro x hx; rw [ Finset.sum_congr rfl fun y hy => by rw [ show y ^ 3 = x ^ 3 from Finset.mem_filter.mp hy |>.2 ] ] ; simp +decide [ h_sum_eq ] ;

/-! ## 2. The GF(4)* scalar action (the three terms) -/

/-
**The GF(4)\* scalar averaging.**  `GF(4)*` (the order-3 group of cube roots
of unity, `card_cubeRootsOne`) acts on `GF(2ⁿ)*` by multiplication; each
`x ↦ μ·x` is a bijection, so summing over the three scalars triple-counts:
`∑_{μ ∈ GF(4)*} ∑_x φ(μ·x) = 3 · ∑_x φ(x)`.  This produces the three terms
`μ ∈ GF(4)*` of equation (12).
-/
theorem gf4_scalar_action_sum {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n)
    (φ : Fˣ → ℤ) :
    ∑ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1), ∑ x : Fˣ, φ (μ * x)
      = 3 * ∑ x : Fˣ, φ x := by
  -- By definition of $GF$, we know that $GFcodingTime* adalah grup berhingga dengan 3 anggota.
  have h_card : (Finset.univ.filter (fun g : Fˣ => g ^ 3 = 1)).card = 3 := by
    convert Vanish.Foundations.card_cubeRootsOne hcard hn using 1;
  rw [ Finset.sum_congr rfl fun μ hμ => show ∑ x : Fˣ, φ ( μ * x ) = ∑ x : Fˣ, φ x from ?_ ];
  · simp +decide [ h_card ];
  · exact Equiv.sum_comp ( Equiv.mulLeft μ ) _

section CharTwo

variable [CharP F 2]

/-! ## 3. Evaluating the equation-(12) terms via the rank substrate -/

/-- **Each equation-(12) term lies in the quadratic-form spectrum.**  The
right-hand term `Q̂^λ_{aμ}(0)` is the Gauss sum of the Appendix-A.4 auxiliary form
`λ x^{2^{3k}+1} + (a·μ) x^{2^k+1}`, a genuine quadratic form, so by rank ⇒ spectrum
it is `0` or `±2^{(n+r)/2}`.  This is `kasamiAux_gaussSum_spectrum` with the
linear coefficient `a·μ`. -/
theorem eq12_term_spectrum {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (lam a μ : F) :
    ∃ r : ℕ, r ≤ n ∧
      (quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + (a * μ) * x ^ (2 ^ k + 1)) = 0
        ∨ ∃ m : ℕ, 2 * m = n + r
            ∧ (quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + (a * μ) * x ^ (2 ^ k + 1))
                  = 2 ^ m
              ∨ quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + (a * μ) * x ^ (2 ^ k + 1))
                  = -(2 ^ m))) :=
  kasamiAux_gaussSum_spectrum hcard k lam (a * μ)

/-- **Assembling equation (12): the Kasami value as three quadratic Gauss sums.**
Given the field-substitution realization of equation (12) (the named hypothesis
`h12`: `3·W = ∑_{μ ∈ GF(4)*} Q̂^λ_{aμ}(0)`), the Kasami Walsh value `3·W` is a sum
of equation-(12) terms each of which is `0` or `±2^{(n+r)/2}` (`eq12_term_spectrum`).
This is the form consumed by the value-set / divisibility input (A). -/
theorem three_mul_kasamiWalsh_terms_spectrum {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (lam a : F) (W : ℤ)
    (h12 : 3 * W = ∑ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1),
      quadGaussSum (fun x : F =>
        lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))) :
    3 * W = ∑ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1),
      quadGaussSum (fun x : F =>
        lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))
    ∧ ∀ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1), ∃ r : ℕ, r ≤ n ∧
        (quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1)) = 0
          ∨ ∃ m : ℕ, 2 * m = n + r
              ∧ (quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1)) = 2 ^ m
                ∨ quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1)) = -(2 ^ m))) :=
  ⟨h12, fun μ _ => eq12_term_spectrum hcard k lam a (μ : F)⟩

end CharTwo

end Vanish.Foundations