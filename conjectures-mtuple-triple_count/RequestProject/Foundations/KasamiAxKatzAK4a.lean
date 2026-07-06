import RequestProject.Foundations.KasamiAxKatzAK3d
import RequestProject.APN.Defs
import Mathlib

/-!
# Foundations, Layer AK4.0 — the orbit-invariant digit sum as McEliece coset arithmetic

This module formalizes the **first layer of the open deep core AK4** of
`Docs/VanishFutureDirections.md` §8.2: packaging the orbit-invariant binary
digit sum (AK3.3.0, `KasamiAxKatzAK3d.lean`) as the **McEliece / cyclotomic-coset
arithmetic** for the Kasami exponent `d k = 2^{2k} − 2^k + 1`.

## The mathematical content

McEliece's weight congruence for `2`-ary cyclic codes reads the `2`-adic
divisibility of a weight off the binary digit sums `s₂` of the exponents grouped
into their **`2`-cyclotomic cosets** `{s, 2s, 4s, … (mod 2ⁿ − 1)}` (the Frobenius
orbits).  AK3.3.0 established the combinatorial heart of this — that `s₂` is
*constant along such an orbit*:

  `s₂((2^j·s) mod (2ⁿ − 1)) = s₂(s mod (2ⁿ − 1))`   (`binDigitSum_two_pow_mul_mod`),

i.e. doubling modulo `2ⁿ − 1` is a cyclic bit-rotation.  This module *packages*
that invariance for the **Kasami exponent**: the entire `2`-cyclotomic coset of
`d k` shares one digit sum, and (when `d k` is already reduced modulo `2ⁿ − 1`)
that common value is the AK2 input `s₂(d k) = k + 1`
(`binDigitSum_kasami_exponent`).

## What is established (sorry-free)

* `kasami_coset_digitSum_invariant` — the digit sum is **constant along the
  `2`-cyclotomic coset** of `d k`:
  `s₂((2^j·d k) mod (2ⁿ − 1)) = s₂((d k) mod (2ⁿ − 1))` for `1 ≤ n`, all `j`.
* `kasami_coset_digitSum_eq` — when `d k` is reduced (`d k < 2ⁿ − 1`), the
  common coset digit sum is `k + 1`:
  `s₂((2^j·d k) mod (2ⁿ − 1)) = k + 1` for `1 ≤ n`, all `j`.
* `kasami_coset_digitSum_const` — the two-point form making the *constancy*
  explicit: any two members `2^i·d k` and `2^j·d k` of the coset have equal
  digit sums modulo `2ⁿ − 1`.

## Scope

This layer is sorry-free and is **pure `Nat` arithmetic**, built on AK3.3.0
(`binDigitSum_two_pow_mul_mod`) and AK2 (`binDigitSum_kasami_exponent`).  It is
crypto-free and upstreamable.  The deep input it *feeds* — the McEliece weight
congruence proper, turning these coset digit sums into the CCD `2`-adic
cross-correlation bound `v₂(R(s)) ≥ (n+1)/2` (AK4.2, discharging the named
hypothesis `hval` of `kasami_crossCorr_hdiv_of_valuation`) — needs the Ax–Katz /
McEliece estimate absent from Mathlib, and is deliberately neither axiomatized
nor `sorry`-ed.

## Sources

McEliece, *Weight congruences for `p`-ary cyclic codes* (Discrete Math., 1972);
Canteaut–Charpin–Dobbertin (SIAM J. Discrete Math., 2000); Lidl–Niederreiter,
*Finite Fields*, Ch. 6.
-/

namespace Vanish.Foundations

/-! ## 1. The coset digit sum is constant along the Frobenius orbit -/

/--
**Constancy along the `2`-cyclotomic coset of the Kasami exponent.**  For
`1 ≤ n`, every member `2^j·d k` of the Frobenius orbit of the Kasami exponent
shares the digit sum of the orbit representative, modulo `2ⁿ − 1`:

  `s₂((2^j·d k) mod (2ⁿ − 1)) = s₂((d k) mod (2ⁿ − 1))`.

This is `binDigitSum_two_pow_mul_mod` (AK3.3.0) specialized to `s = d k`.
-/
theorem kasami_coset_digitSum_invariant {n : ℕ} (hn : 1 ≤ n) (j k : ℕ) :
    binDigitSum ((2 ^ j * CollisionAnalysis.d k) % (2 ^ n - 1))
      = binDigitSum ((CollisionAnalysis.d k) % (2 ^ n - 1)) :=
  binDigitSum_two_pow_mul_mod hn j (CollisionAnalysis.d k)

/--
**Two-point constancy.**  Any two members `2^i·d k` and `2^j·d k` of the
`2`-cyclotomic coset of the Kasami exponent have equal digit sums modulo
`2ⁿ − 1`.
-/
theorem kasami_coset_digitSum_const {n : ℕ} (hn : 1 ≤ n) (i j k : ℕ) :
    binDigitSum ((2 ^ i * CollisionAnalysis.d k) % (2 ^ n - 1))
      = binDigitSum ((2 ^ j * CollisionAnalysis.d k) % (2 ^ n - 1)) := by
  rw [kasami_coset_digitSum_invariant hn, kasami_coset_digitSum_invariant hn]

/-! ## 2. The common coset value for the reduced Kasami exponent -/

/--
**The common coset digit sum is `k + 1`.**  When the Kasami exponent is already
reduced modulo `2ⁿ − 1` (`d k < 2ⁿ − 1`), the digit sum shared by every member of
its `2`-cyclotomic coset is the AK2 value `s₂(d k) = k + 1`:

  `s₂((2^j·d k) mod (2ⁿ − 1)) = k + 1`.
-/
theorem kasami_coset_digitSum_eq {n : ℕ} (hn : 1 ≤ n) (j k : ℕ)
    (hlt : CollisionAnalysis.d k < 2 ^ n - 1) :
    binDigitSum ((2 ^ j * CollisionAnalysis.d k) % (2 ^ n - 1)) = k + 1 := by
  rw [kasami_coset_digitSum_invariant hn, Nat.mod_eq_of_lt hlt,
    binDigitSum_kasami_exponent]

end Vanish.Foundations
