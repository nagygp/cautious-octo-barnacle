import RequestProject.Foundations.QuadraticGaussSum

/-!
# Foundations — Proposition A.3: "rank ⇒ spectrum"

This module transcribes **Proposition A.3** of Dillon–Dobbertin (*New cyclic
difference sets with Singer parameters*, FFA 2004, Appendix A) — the
**rank ⇒ spectrum** principle:

> For a quadratic form `Q` over `GF(2ⁿ)`, the Hadamard/Walsh spectrum value at `0`
> of the sign function `F(x) = (−1)^{Tr(Q x)}` is *completely determined by the
> rank of `Q`*: it is either `0` (if `F` is balanced) or `±2^{(n+r)/2}`, where
> `2^r = |radical Q|` is the size of the radical of the polar (bilinear) form
> (`2R = n − r` the rank).

In the project's `ℤ`-valued sign-character packaging (`WalshAB.χ`), the Hadamard
transform at `0` of `χ ∘ Q` is *literally* the quadratic-form Gauss sum
`quadGaussSum Q = ∑_x χ(Q x)` already evaluated in
`Foundations/QuadraticGaussSum.lean`.  Consequently Proposition A.3 is a **thin
corollary** of `quadGaussSum_value`: this file states it in the explicit
radical/rank form (the magnitude `2^{(n+r)/2}` pinned to the *actual* radical
cardinality `2^r`, rather than the existential `∃ r` of `quadGaussSum_value`),
which is the form the equation-(12) average of three quadratic-form Gauss sums
consumes downstream (`Foundations/GoldQuadratic.lean`).

## Results

* `quadGaussSum_eq_hadamard_zero` — the Gauss sum *is* the Hadamard transform at
  `0` (`∑_x χ(Q x)`).
* `rank_spectrum` — Prop A.3: with `|radical Q| = 2^r`, the Gauss sum is `0` or
  `±2^m` with `2m = n + r`.
* `rank_spectrum_natAbs` — the magnitude form `|S(Q)| ∈ {0, 2^{(n+r)/2}}`.
* `rank_determines_natAbs` — *the spectrum is determined by the rank*: two
  quadratic forms with radicals of equal size have the same magnitude options.

## Sources

Dillon–Dobbertin (FFA 2004), Appendix A, Propositions A.2/A.3; Lidl–Niederreiter,
*Finite Fields*, Ch. 6; Carlet, *Boolean Functions for Cryptography and Coding
Theory*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [DecidableEq F] in
/-- The quadratic-form Gauss sum is exactly the Hadamard/Walsh transform at the
zero frequency of the sign function `χ ∘ Q`: `S(Q) = F̂(0) = ∑_x χ(Q x)`. -/
theorem quadGaussSum_eq_hadamard_zero (Q : F → F) :
    quadGaussSum Q = ∑ x : F, χ (Q x) := rfl

/-
**Proposition A.3 (rank ⇒ spectrum), explicit radical form.**  For a quadratic
form `Q` over `GF(2ⁿ)` whose radical has size `2^r`, the Gauss sum
`S(Q) = ∑_x χ(Q x)` is either `0` or `±2^m` with `2m = n + r`.  This is the
content of `quadGaussSum_value` with the magnitude pinned to the *actual* radical
cardinality.
-/
theorem rank_spectrum {n : ℕ} {Q : F → F} (hQ : IsQuadraticForm Q)
    (hcard : Fintype.card F = 2 ^ n) {r : ℕ} (hr : (radical Q).card = 2 ^ r) :
    quadGaussSum Q = 0
      ∨ ∃ m : ℕ, 2 * m = n + r
          ∧ (quadGaussSum Q = 2 ^ m ∨ quadGaussSum Q = -(2 ^ m)) := by
  obtain h | h := ( Vanish.Foundations.quadGaussSum_sq_eq_or hQ );
  · exact Or.inl <| sq_eq_zero_iff.mp h;
  · simp_all +decide [ ← pow_add ];
    have h_even : Even (n + r) := by
      replace h := congr_arg ( fun x => x.natAbs.factorization 2 ) h ; simp_all +decide [ Int.natAbs_pow ];
      exact h ▸ even_two_mul _;
    obtain ⟨ m, hm ⟩ := h_even;
    exact Or.inr ⟨ m, by linarith, eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [ h, hm ] ; ring ⟩

/-
**Proposition A.3 (magnitude form).**  `|S(Q)| ∈ {0, 2^{(n+r)/2}}`: the Gauss
sum is `0`, or its absolute value is `2^m` with `2m = n + r`.
-/
theorem rank_spectrum_natAbs {n : ℕ} {Q : F → F} (hQ : IsQuadraticForm Q)
    (hcard : Fintype.card F = 2 ^ n) {r : ℕ} (hr : (radical Q).card = 2 ^ r) :
    (quadGaussSum Q).natAbs = 0
      ∨ ∃ m : ℕ, 2 * m = n + r ∧ (quadGaussSum Q).natAbs = 2 ^ m := by
  convert rank_spectrum hQ hcard hr using 1;
  · simp +decide [ Int.natAbs_eq_zero ];
  · constructor <;> rintro ⟨ m, hm₁, hm₂ ⟩ <;> use m <;> simp_all +decide [ Int.natAbs_eq_iff ]

/-- **The spectrum is determined by the rank.**  Two quadratic forms over `GF(2ⁿ)`
whose polar forms have radicals of the *same* size `2^r` have Gauss sums with the
*same* magnitude options: each is `0` or `2^m` with `2m = n + r`.  This is the
precise sense of Dillon–Dobbertin's "the Fourier spectrum of `F` is completely
determined by the rank of `f`". -/
theorem rank_determines_natAbs {n : ℕ} {Q R : F → F}
    (hQ : IsQuadraticForm Q) (hR : IsQuadraticForm R)
    (hcard : Fintype.card F = 2 ^ n) {r : ℕ}
    (hrQ : (radical Q).card = 2 ^ r) (hrR : (radical R).card = 2 ^ r) :
    ((quadGaussSum Q).natAbs = 0
        ∨ ∃ m : ℕ, 2 * m = n + r ∧ (quadGaussSum Q).natAbs = 2 ^ m)
    ∧ ((quadGaussSum R).natAbs = 0
        ∨ ∃ m : ℕ, 2 * m = n + r ∧ (quadGaussSum R).natAbs = 2 ^ m) :=
  ⟨rank_spectrum_natAbs hQ hcard hrQ, rank_spectrum_natAbs hR hcard hrR⟩

end Vanish.Foundations