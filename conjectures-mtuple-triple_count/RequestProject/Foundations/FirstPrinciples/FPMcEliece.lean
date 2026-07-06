import RequestProject.Foundations.FirstPrinciples.FPGaussSumSetup
import RequestProject.Foundations.FirstPrinciples.Decomp.AxKatzDecomp
import RequestProject.Foundations.KasamiDigitSumBound
import Mathlib

/-!
# First-principles tower, Core (A) — module A·fp·s4: Ax–Katz / McEliece factorial bound (`hfact`, `hle`)

This module supplies the **McEliece weight-congruence** half of input (A): the
factorial-valuation bound that `KasamiDigitSumBound.hbound_of_factorial_bound`
turns into the digit-sum lower bound `hbound`.  It rests on the iterated
Ax–Katz `p^μ`-divisibility of the number of common zeros of a polynomial system —
the strengthening of the project's already-proved characteristic-2
Chevalley–Warning base case `charTwo_two_dvd_card_solutions` (`μ = 1`).

## The chain

* **Ax–Katz** (`axKatz_two_pow_dvd`).  The genuinely missing number-theoretic
  input absent from Mathlib: for a finite system of polynomials over a char-2
  finite field with `μ·d + ∑ deg fᵢ ≤ (#variables)` (a sufficient form of the
  Ax–Katz inequality, `d = max deg`), the number of common zeros is divisible by
  `2^μ`.  Carried as `sorry`.
* **McEliece factorial bound** (`kasami_exp_factorial_bound`).  Specializing
  Ax–Katz to the system cutting out `R(s)` (the dual Kasami/BCH code), the
  Teichmüller exponent `e(s)` satisfies the factorial-valuation bound
  `v₂((e s)!) ≤ e s − (n+1)/2`.  This is `hfact`.
* **Size condition** (`kasami_exp_ge`).  The exponent is large enough,
  `(n+1)/2 ≤ e s`, so the `KasamiDigitSumBound` translation applies.  This is
  `hle`.

## Sources

Ax, *Zeroes of polynomials over finite fields* (1964); Katz (1971); McEliece,
*Weight congruences for p-ary cyclic codes* (1972); Canteaut–Charpin–Dobbertin
(IEEE-IT 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

/-- **Iterated Ax–Katz `p^μ`-divisibility (char 2).**  For a finite system of
multivariate polynomials `f : ι → K[Xₛ]` over a char-2 finite field `K`, with
`d` an upper bound on the total degrees and `μ·d + ∑ deg fᵢ ≤ (#variables)`
(a sufficient form of the Ax–Katz inequality), the number of common zeros in
`σ → K` is divisible by `2^μ`.  The `μ = 1` case is the project's proved
`charTwo_two_dvd_card_solutions`; the iterated statement is the deep Ax–Katz
theorem absent from Mathlib. -/
theorem axKatz_two_pow_dvd {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {σ : Type*} [Fintype σ] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) (d μ : ℕ) (hd1 : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    (hμ : μ * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ) :
    (2 : ℕ) ^ μ ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} :=
  Decomp.axKatz_two_pow_dvd f d μ hd1 hd hμ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The McEliece factorial-valuation bound (`hfact`).**  Specializing Ax–Katz to
the dual Kasami/BCH code system, the Teichmüller exponent satisfies
`v₂((e s)!) ≤ e s − (n+1)/2` for every non-zero frequency — the McEliece
weight-congruence input consumed by `hbound_of_factorial_bound`. -/
theorem kasami_exp_factorial_bound {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      padicValNat 2 (Nat.factorial (kasamiExp k a s)) ≤ kasamiExp k a s - (n + 1) / 2 :=
  Decomp.kasami_exp_factorial_bound hcard hk hkn hcop hnodd a ha

/-- **The exponent size condition (`hle`).**  The Teichmüller exponent of a
non-trivial frequency is at least `(n+1)/2`, so the digit-sum/factorial
translation `digitSum_bound_iff_factorial` applies. -/
theorem kasami_exp_ge {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ kasamiExp k a s :=
  Decomp.kasami_exp_ge hcard hk hkn hcop hnodd a ha

end Vanish.Foundations.FirstPrinciples
