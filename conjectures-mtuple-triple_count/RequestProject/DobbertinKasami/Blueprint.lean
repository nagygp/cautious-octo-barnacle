/-
  Blueprint / interface layer for the formalisation of

    Hans Dobbertin,
    "Kasami Power Functions, Permutation Polynomials and Cyclic Difference Sets"
    (Difference Sets, Sequences and their Correlation Properties, 133-158, Kluwer 1999).

  This file records the *interfaces* (definitions we can already state faithfully
  against Mathlib) that Theorem 1, its Case 1 / Case 2, and Corollary 2 depend on.

  It is the integration into the buildable `RequestProject` library of the
  reference blueprint shipped in `dobbertin-kasami-power.zip`.  The namespace is
  `DobbertinKasami` (to avoid collision with the existing `Kasami.*` development).
-/
import Mathlib

open scoped BigOperators

namespace DobbertinKasami

/-! ## Layer A — foundations that already exist in Mathlib -/

/-- The ambient field `L = 𝔽_{2ⁿ}`. -/
abbrev Lfield (n : ℕ) := GaloisField 2 n

/-- The absolute trace `Tr : 𝔽_{2ⁿ} → 𝔽₂`. -/
noncomputable abbrev Tr (n : ℕ) : Lfield n → ZMod 2 :=
  Algebra.trace (ZMod 2) (Lfield n)

/-- The Kasami exponent `d = 2^{2k} − 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- Hypothesis package for a Kasami exponent: `k < n` and `gcd(k,n) = 1`. -/
structure KasamiParams (n : ℕ) where
  k : ℕ
  hk_lt : k < n
  hk_coprime : Nat.Coprime k n

/-! ## Layer B — notions to be built (stated here at interface level) -/

/-- A map on a finite field is a *permutation polynomial* iff the induced map
is a bijection.  (Over a finite field, injective ↔ surjective ↔ bijective, cf.
`Finite.injective_iff_bijective`.) -/
def IsPermutation {F : Type*} (f : F → F) : Prop := Function.Bijective f

/-- `f` is *almost perfect nonlinear* (APN): for every nonzero `a` and every `b`,
the equation `f(x+a) + f(x) = b` has at most two solutions.  In characteristic 2,
solutions come in pairs `{x, x+a}`, so "at most two" is equivalent to Dobbertin's
"either no or precisely two". -/
def IsAPN {F : Type*} [Field F] (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F, {x : F | f (x + a) + f x = b}.ncard ≤ 2

end DobbertinKasami
