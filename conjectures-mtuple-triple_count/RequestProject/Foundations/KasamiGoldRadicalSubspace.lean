import RequestProject.Foundations.RankSpectrum
import RequestProject.Foundations.GoldQuadratic
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-4b: the radical is an `𝔽₂`-subspace

This module is a **further from-scratch foundational rung of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), refining DD-fp-4 (`KasamiGoldRadical.lean`)
and DD-fp-4a (`KasamiGoldPolar.lean`).

`KasamiGoldRadical.lean` feeds `|radical Q| = 2 = 2¹` into the rank ⇒ spectrum
principle.  The hypothesis there — that the radical has size *exactly* `2` — is the
output of a gcd-of-exponents computation.  Underneath it lies the deepest/simplest
structural fact, the one closest to Mathlib: the radical is an **`𝔽₂`-subspace** of
`GF(2ⁿ)`, so its cardinality is automatically a **power of two** `2^r` with
`r ≤ n` (rank `n − r`).  Indeed `radical Q` contains `0` (`zero_mem_radical`) and
is closed under addition (`add_mem_radical`); in characteristic `2` it is therefore
an additive subgroup, and by Lagrange its size divides `|F| = 2ⁿ`, hence equals
`2^r` for a unique `r ≤ n`.

This is exactly what makes the `(radical Q).card = 2^r` shape of `rank_spectrum`
(`RankSpectrum.lean`) legitimate in general: the radical can only ever have a
power-of-two size.  The remaining DD-fp-4 content — pinning `r = 1` for the
auxiliary Gold form via the linearized-polynomial gcd computation — is the carried
core.

## Results

* `radicalSubgroup` — the radical of a quadratic form as an `AddSubgroup F`.
* `radical_card_dvd_card` — `|radical Q| ∣ |F|`.
* `radical_card_eq_two_pow` — for `|F| = 2ⁿ`, `∃ r ≤ n, |radical Q| = 2^r`.
* `kasamiAux_radical_card_eq_two_pow` — its specialization to the auxiliary Gold
  form `λ x^{2^{3k}+1} + a x^{2^k+1}`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite-group structure
(Lagrange's theorem for an additive subgroup of `GF(2ⁿ)`); it introduces no new
hypotheses.  The remaining DD-fp-4 content — that this power-of-two is `2¹` for the
relevant parameters (the gcd-of-exponents computation) — is the carried core.

## Sources

Dillon–Dobbertin (FFA 2004), Appendix A.4; Lidl–Niederreiter, *Finite Fields*,
Ch. 6 (quadratic forms, radicals).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The radical of a quadratic form as an additive subgroup.**  In characteristic
`2`, the radical `{u | ∀ x, Tr(polar Q x u) = 0}` is an additive subgroup of `F`:
it contains `0` (`zero_mem_radical`), is closed under addition
(`add_mem_radical`), and (since `-u = u`) under negation. -/
noncomputable def radicalSubgroup {Q : F → F} (hQ : IsQuadraticForm Q) : AddSubgroup F where
  carrier := {u | u ∈ radical Q}
  zero_mem' := zero_mem_radical hQ
  add_mem' := fun hu hv => add_mem_radical hQ hu hv
  neg_mem' := by
    intro u hu
    simpa [CharTwo.neg_eq] using hu

/-
**The radical size divides the field size.**  By Lagrange's theorem for the
additive subgroup `radicalSubgroup`.
-/
omit [DecidableEq F] in
theorem radical_card_dvd_card {Q : F → F} (hQ : IsQuadraticForm Q) :
    (radical Q).card ∣ Fintype.card F := by
  -- Let K = radicalSubgroup hQ : AddSubgroup F
  set K : AddSubgroup F := radicalSubgroup hQ;
  convert AddSubgroup.card_addSubgroup_dvd_card K;
  · convert Fintype.card_coe ( radical Q );
    · rw [ Fintype.card_of_subtype ] ; aesop;
    · convert Nat.card_eq_finsetCard ( radical Q );
  · rw [ Nat.card_eq_fintype_card ]

omit [DecidableEq F] in
/-- **The radical has power-of-two size.**  For `|F| = 2ⁿ`, the radical of any
quadratic form `Q` is an `𝔽₂`-subspace, so its cardinality is `2^r` for some
`r ≤ n`. -/
theorem radical_card_eq_two_pow {n : ℕ} {Q : F → F} (hQ : IsQuadraticForm Q)
    (hcard : Fintype.card F = 2 ^ n) :
    ∃ r ≤ n, (radical Q).card = 2 ^ r := by
  have hdvd : (radical Q).card ∣ 2 ^ n := hcard ▸ radical_card_dvd_card hQ
  exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd

/-- **The auxiliary Gold form has power-of-two radical size.**  Specializing
`radical_card_eq_two_pow` to the Appendix-A.4 auxiliary Gold form
`q^λ_{a}(x) = λ x^{2^{3k}+1} + a x^{2^k+1}` (`kasamiAux_isQuadraticForm`). -/
theorem kasamiAux_radical_card_eq_two_pow {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (lam a : F) :
    ∃ r ≤ n,
      (radical (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))).card = 2 ^ r :=
  radical_card_eq_two_pow (kasamiAux_isQuadraticForm k lam a) hcard

end Vanish.Foundations