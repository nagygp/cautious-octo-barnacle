import RequestProject.Foundations.KasamiGoldRadical
import RequestProject.Foundations.KasamiEq12ValueSet
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-5: the rank evaluation (`hrank`)

This module is the **fifth from-scratch foundational module of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), building on DD-fp-4
(`KasamiGoldRadical.lean`) and the coset-average value-set assembly
(`KasamiEq12ValueSet.lean`).

This is the core **DD-fp-5**: the *rank evaluation* pinning each equation-(12)
term to `{0, ±2^{(n+1)/2}}`, which discharges the named hypothesis `hrank` of
`eq12_three_mul_value`.

Given that each auxiliary Gold form `q^λ_{aμ}(x) = λ x^{2^{3k}+1} + (aμ) x^{2^k+1}`
(for the three scalars `μ ∈ GF(4)*`) has a **one-dimensional radical**
(`|radical| = 2`, the rank-`n−1` computation of DD-fp-4 — carried here as the
hypothesis `hrad`), the rank ⇒ spectrum reduction
`kasamiAux_radical_two_spectrum` pins each term to `{0, ±2^{(n+1)/2}}`.  This is
exactly the `hrank` premise consumed by `eq12_three_mul_value`.

* `eq12_hrank_of_radical` — the assembly: per-term `|radical| = 2` ⟹ the `hrank`
  premise in the precise form `eq12_three_mul_value` expects.

## Regime note (honest)

The AB magnitude `2^{(n+1)/2}` lives in the **`n` odd** regime (the Kasami
almost-bent regime), where `2m = n + 1` has the integer solution `m = (n+1)/2`;
DD-fp-4's spectrum reduction is therefore stated for `n` odd.  Equation (12)'s
GF(4)-coset average (`card_cubeRootsOne`, `eq12_three_mul_value`) is by contrast an
**`n` even** device (it needs `GF(4) ⊆ GF(2ⁿ)`).  This module delivers the rank
evaluation `hrank` in the exact form `eq12_three_mul_value` consumes; the two
parities not coinciding is the documented regime caveat of
`GoldQuadratic.lean`, not a defect of this reduction.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  The linearized-polynomial gcd
computation that each radical *is* one-dimensional is carried as the hypothesis
`hrad`; what this module proves is the rank ⇒ `hrank` assembly.

## Sources

Dillon–Dobbertin (FFA 2004), Appendix A.4 (Theorem A.5, Corollary A.6).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The rank evaluation `hrank`, from one-dimensional radicals.**  If each
equation-(12) auxiliary Gold form `q^λ_{aμ}(x) = λ x^{2^{3k}+1} + (aμ) x^{2^k+1}`
(over the three scalars `μ ∈ GF(4)*`) has a one-dimensional radical
(`|radical| = 2`, the hypothesis `hrad` — the DD-fp-4 rank computation), then each
term lies in `{0, ±2^{(n+1)/2}}`.  This is the precise `hrank` premise consumed by
`eq12_three_mul_value`. -/
theorem eq12_hrank_of_radical {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Odd n)
    (k : ℕ) (lam a : F)
    (hrad : ∀ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1),
        (radical (fun x : F =>
            lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))).card = 2) :
    ∀ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1),
        quadGaussSum (fun x : F =>
            lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1)) = 0
        ∨ quadGaussSum (fun x : F =>
            lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))
              = 2 ^ ((n + 1) / 2)
        ∨ quadGaussSum (fun x : F =>
            lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))
              = -2 ^ ((n + 1) / 2) :=
  fun μ hμ => kasamiAux_radical_two_spectrum hcard hn k lam (a * (μ : F)) (hrad μ hμ)

end Vanish.Foundations
