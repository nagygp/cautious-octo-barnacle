import Mathlib
import RequestProject.Steiner.Foundations

/-!
# Preliminaries

This file transcribes the notational and foundational material of Section 2 of

  M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
  Designs, Codes and Cryptography (2025) 93:2245–2262,
  https://doi.org/10.1007/s10623-025-01589-w

The paper works over a finite field `Fq` of characteristic `p`.  In this
formalisation a finite field is modelled by the typeclass assumptions
`[Field Fq] [Fintype Fq]`.

Throughout we follow the paper's convention of identifying *functions*
`Fq → Fq` with *polynomials* in `Fq[x]/(x^q - x)` (a consequence of Lagrange
interpolation, [Lidl–Niederreiter, 1.71]).

The genuinely deep mathematical inputs (scheme theory, smoothness, the
character–sum bounds of Weil, Deligne and Rojas–León) are isolated into their
own modules.  See `FORMALIZATION_NOTES.md` for the road-map of what must be
established from first principles.
-/

open scoped BigOperators

namespace Flystel

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-! ## The standard inner product (Eq. (3))

For two vectors `a, b ∈ k^n` the standard inner product `⟨a, b⟩ = aᵀ b`.
In Mathlib this is `Matrix.dotProduct`, abbreviated `dotProduct` / `a ⬝ᵥ b`. -/

/-- The inner product of Eq. (3), spelled out for reference. -/
noncomputable def inner' {n : ℕ} (a b : Fin n → Fq) : Fq := dotProduct a b

omit [Fintype Fq] in
@[simp] theorem inner'_def {n : ℕ} (a b : Fin n → Fq) :
    inner' a b = ∑ i, a i * b i := rfl

/-! ## Additive characters (Eq. (2))

For a finite field `Fq` of characteristic `p`, the *fundamental additive
character* is
`ψ₁(x) = exp (2·π·i·Tr_{Fq/Fp}(x) / p)`,
and every non-trivial additive character is of the form `ψ(x) = ψ₁(b·x)` for
some `b ∈ Fq×` ([Lidl–Niederreiter, 5.7]).

In this formalisation additive characters are modelled by `AddChar Fq ℂ`. -/

/-- Every non-trivial additive character of `Fq` is `x ↦ ψ₁ (b * x)` for some
`b ≠ 0`, where `ψ₁` is the fundamental additive character
([Lidl–Niederreiter, 5.7]).

**Proved** in the foundational layer `Foundations.CharacterDuality`. -/
theorem exists_eq_fundamental_smul
    (ψ : AddChar Fq ℂ) (hψ : ψ ≠ 1) :
    ∃ (ψ₁ : AddChar Fq ℂ) (b : Fq), b ≠ 0 ∧
      ∀ x : Fq, ψ x = ψ₁ (b * x) :=
  Foundations.exists_eq_fundamental_smul ψ hψ

/-! ## Power permutations ([Lidl–Niederreiter, 7.8])

For an integer `d ≥ 1` the power map `x ↦ x^d` is a permutation of `Fq` iff
`gcd (d, q - 1) = 1`. -/

/-- The power map `x ↦ x ^ d` is a permutation of `Fq` iff `gcd (d, q-1) = 1`.
([Lidl–Niederreiter, 7.8].)

The `0 < d` hypothesis (implicit in the paper, where `d ≥ 1`) is genuinely
required: for `d = 0`, `#Fq = 2` the map is constant yet `gcd(0,1) = 1`.

**Proved** in the foundational layer `Foundations.PowerPermutation`. -/
theorem powMap_bijective_iff (d : ℕ) (hd : 0 < d) :
    Function.Bijective (fun x : Fq => x ^ d) ↔ Nat.Coprime d (Fintype.card Fq - 1) :=
  Foundations.powMap_bijective_iff d hd

end Flystel
