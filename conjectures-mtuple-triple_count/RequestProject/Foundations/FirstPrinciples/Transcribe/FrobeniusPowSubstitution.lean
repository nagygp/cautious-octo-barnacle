import Mathlib

/-!
# Transcription — Leaf L1, module 4 (support): the Frobenius power substitution

This module records the elementary **Frobenius power** facts that sit exactly one
edge below the Kasami trace → monomial collapse leaf
(`TraceMonomial.kasami_monomial_collapse_one`) in the `MissingModulesDAG.md` graph.
They are all **real, `sorry`-free, axiom-clean** proofs rooted only in Mathlib's
`frobenius` API and finite-field cardinality, over an *arbitrary* finite field of
characteristic `2` (nothing Kasami-specific).

The Kasami substitution repeatedly needs three facts about the map `y ↦ y^{2^k}`
(the `k`-th iterate of the Frobenius endomorphism `x ↦ x²` in characteristic `2`):

* `frobPow_add` — it is additive: `(x + y)^{2^k} = x^{2^k} + y^{2^k}`
  (Freshman's dream, `add_pow_char_pow`).
* `frobPow_bijective` — it is a bijection of the finite field (an iterate of the
  Frobenius automorphism).
* `sum_comp_frobPow` — hence it reindexes any finite sum over the field:
  `∑_y g(y^{2^k}) = ∑_y g(y)`.

These are the change-of-variable atoms behind Kasami's classical substitution
(Lidl–Niederreiter, *Finite Fields*, Ch. 5), which turns the second-derivative
character sum of the Kasami power map into a single monomial character sum.

## Sources

* Lidl–Niederreiter, *Finite Fields*, Ch. 2 (Frobenius), Ch. 5 (character sums).
* Mathlib: `frobenius`, `add_pow_char_pow`, `Finite.injective_iff_bijective`,
  `Fintype.sum_bijective`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open Finset

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

omit [Fintype F] in
/-- **Additivity of the Frobenius power (Freshman's dream).**  In characteristic
`2`, the map `y ↦ y^{2^k}` is additive: `(x + y)^{2^k} = x^{2^k} + y^{2^k}`.  A
direct specialization of Mathlib's `add_pow_char_pow`. -/
theorem frobPow_add (k : ℕ) (x y : F) :
    (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) := by
  simpa using add_pow_char_pow (R := F) (p := 2) (n := k) x y

/-- **The Frobenius power is a bijection.**  On a finite field of characteristic `2`
the map `y ↦ y^{2^k}` is the `k`-th iterate of the Frobenius automorphism
`x ↦ x²`, hence a bijection. -/
theorem frobPow_bijective (k : ℕ) :
    Function.Bijective (fun y : F => y ^ (2 ^ k)) := by
  have hb : Function.Bijective (frobenius F 2) :=
    Finite.injective_iff_bijective.mp (frobenius F 2).injective
  have hfun : (fun y : F => y ^ (2 ^ k)) = (fun y : F => (frobenius F 2)^[k] y) := by
    funext y
    induction k with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply', ← ih]
        simp [frobenius_def, pow_succ, pow_mul]
  rw [hfun]
  exact hb.iterate k

/-- **Reindexing a field sum by the Frobenius power.**  Since `y ↦ y^{2^k}` is a
bijection of the finite field, it reparametrizes any finite sum over the field:
`∑_y g(y^{2^k}) = ∑_y g(y)`.  This is the change-of-variable step used by Kasami's
substitution. -/
theorem sum_comp_frobPow {M : Type*} [AddCommMonoid M] (k : ℕ) (g : F → M) :
    (∑ y : F, g (y ^ (2 ^ k))) = ∑ y : F, g y :=
  Fintype.sum_bijective _ (frobPow_bijective k) _ _ (fun _ => rfl)

end Vanish.Foundations.FirstPrinciples.Transcribe
