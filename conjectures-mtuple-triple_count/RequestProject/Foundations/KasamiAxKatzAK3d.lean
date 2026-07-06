import RequestProject.Foundations.KasamiAxKatzAK3
import Mathlib

/-!
# Foundations, Layer AK3.3 (first layer) — the Stickelberger combinatorial core

This module supplies the **most foundational, fully Mathlib-rooted first layer**
of the open deep core AK3.3 of `Docs/VanishFutureDirections.md` §7: the
Stickelberger / Gross–Koblitz factorization

  `v(g(ω^{-s})) = s₂(s)`

(the `2`-adic valuation of a Gauss sum equals the binary digit sum of the
exponent of the multiplicative character).  The full factorization needs the
`p`-adic Gamma function / Gross–Koblitz machinery, which is absent from Mathlib.
But one of its two halves — the **invariance of the valuation along a Frobenius
orbit** — has a purely combinatorial shadow that is provable from pure `Nat`
arithmetic, and that is what this module establishes.

## The mathematical content

Over `GF(2ⁿ)` the Frobenius automorphism `x ↦ x²` acts on the multiplicative
characters by `χ ↦ χ²`, hence on the Stickelberger exponent by `s ↦ 2s`
(modulo `q − 1 = 2ⁿ − 1`).  The Gauss-sum `p`-power law
`g(χ)^p = g(χ^p, ψ^p)` (already transcribed as
`Vanish.Foundations.gaussSum_pow_char` in `KasamiAxKatzAK3.lean`) shows
`g(ω^{-2s})` is, up to a unit (a root of unity), a Galois conjugate of
`g(ω^{-s})`.  Galois conjugation preserves the `2`-adic valuation, so the
Stickelberger valuation must be **constant on the orbit**
`s, 2s, 4s, … (mod 2ⁿ − 1)`.

If the Stickelberger formula `v(g(ω^{-s})) = s₂(s)` is to be self-consistent with
this Frobenius invariance, the binary digit sum **must itself** be invariant
under doubling modulo `2ⁿ − 1`:

  `s₂((2·s) mod (2ⁿ − 1)) = s₂(s mod (2ⁿ − 1))`.

This is true, and it is exactly the statement that *multiplication by `2`
modulo `2ⁿ − 1` is a cyclic rotation of the `n`-bit word* — the combinatorial
heart of the McEliece weight congruence and of why the Stickelberger valuation is
constant on `2`-cyclotomic cosets.  This module proves it, sorry-free, from the
digit-sum engine of AK1–AK3 (in particular the block-additivity law
`binDigitSum_block_add`), rooting the AK3.3 deep core's invariance half in
Mathlib `Nat` arithmetic.

## What is established (sorry-free)

* `binDigitSum_two_mul_mod_of_lt` — the reduced doubling law: for `1 ≤ n` and a
  representative `r < 2ⁿ − 1`, `s₂((2·r) mod (2ⁿ − 1)) = s₂(r)`.
* `binDigitSum_two_mul_mod` — the general doubling law:
  `s₂((2·s) mod (2ⁿ − 1)) = s₂(s mod (2ⁿ − 1))` for `1 ≤ n`.
* `binDigitSum_two_pow_mul_mod` — the iterated / orbit form:
  `s₂((2^j·s) mod (2ⁿ − 1)) = s₂(s mod (2ⁿ − 1))`, i.e. the digit sum is constant
  along the whole Frobenius orbit `s, 2s, 4s, … (mod 2ⁿ − 1)`.

## Scope

This layer is sorry-free.  It supplies the **invariance half** of the
Stickelberger valuation AK3.3 — the part forced by the Frobenius `p`-power law and
expressible in pure `Nat` arithmetic.  The remaining content of AK3.3 — the
*value* `v(g(ω^{-s})) = s₂(s)` itself (which representative in the orbit the
common valuation equals), needing the Gross–Koblitz / `p`-adic Gamma machinery
absent from Mathlib — stays the open deep core, deliberately neither axiomatized
nor `sorry`-ed.

This doubling-invariance is **crypto-free and upstreamable**: "the binary digit
sum is invariant under doubling modulo `2ⁿ − 1`" is a clean standalone `Nat`
lemma, the combinatorial core of the McEliece/Stickelberger weight congruence in
characteristic `2`.

## Sources

McEliece, *Weight congruences for `p`-ary cyclic codes* (Discrete Math., 1972);
Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 14
(Stickelberger's relation); Washington, *Introduction to Cyclotomic Fields*,
Ch. 6 (Gross–Koblitz); Lidl–Niederreiter, *Finite Fields*, Ch. 6 (digit sums and
Gauss-sum valuations).
-/

namespace Vanish.Foundations

/-! ## 1. The reduced doubling law (for a representative `r < 2ⁿ − 1`) -/

/-
**Reduced doubling law.**  For `1 ≤ n` and a representative `r < 2ⁿ − 1`, doubling
modulo `2ⁿ − 1` preserves the binary digit sum:
`s₂((2·r) mod (2ⁿ − 1)) = s₂(r)`.

This is the statement that doubling mod `2ⁿ − 1` is a cyclic left-rotation of the
`n`-bit word: if the top bit is `0` (`r < 2^{n-1}`) it is a plain left shift
(`(2·r) mod (2ⁿ−1) = 2·r`, no carry, same digit sum); if the top bit is `1`
(`r ≥ 2^{n-1}`) the top bit wraps around to the bottom
(`(2·r) mod (2ⁿ−1) = 2·(r − 2^{n-1}) + 1`), again with the same digit sum by
block additivity.
-/
theorem binDigitSum_two_mul_mod_of_lt {n : ℕ} (hn : 1 ≤ n) {r : ℕ}
    (hr : r < 2 ^ n - 1) :
    binDigitSum ((2 * r) % (2 ^ n - 1)) = binDigitSum r := by
  by_cases h₂ : 2 * r < 2 ^ n - 1;
  · rw [ Nat.mod_eq_of_lt h₂, binDigitSum_two_mul ];
  · -- Since $2 * r \geq 2^n - 1$, we have $2 * r - (2^n - 1) < 2^n - 1$.
    have h₃ : 2 * r - (2 ^ n - 1) < 2 ^ n - 1 := by
      omega;
    convert Vanish.Foundations.binDigitSum_two_mul_add_one ( r - 2 ^ ( n - 1 ) ) using 1;
    · rcases n <;> simp_all +decide [ Nat.pow_succ' ];
      rw [ Nat.mod_eq_sub_mod ];
      · rw [ Nat.mod_eq_of_lt h₃ ];
        exact congr_arg _ ( by omega );
      · omega;
    · convert Vanish.Foundations.binDigitSum_block_add ( n - 1 ) 1 ( r - 2 ^ ( n - 1 ) ) _ using 1;
      · rw [ Nat.mul_one, add_tsub_cancel_of_le ];
        cases n <;> simp_all +decide [ pow_succ' ] ; omega;
      · simp +arith +decide [ add_comm ];
      · cases n <;> simp_all +decide [ pow_succ' ] ; omega

/-! ## 2. The general doubling law -/

/-
**General doubling law.**  For `1 ≤ n` and any `s`, doubling modulo `2ⁿ − 1`
preserves the binary digit sum of the reduced residue:
`s₂((2·s) mod (2ⁿ − 1)) = s₂(s mod (2ⁿ − 1))`.

This is the combinatorial shadow of the Frobenius invariance of the Stickelberger
valuation `v(g(ω^{-s}))` (the Frobenius `x ↦ x²` sends the exponent `s ↦ 2s mod
(2ⁿ − 1)` and preserves the `2`-adic valuation).
-/
theorem binDigitSum_two_mul_mod {n : ℕ} (hn : 1 ≤ n) (s : ℕ) :
    binDigitSum ((2 * s) % (2 ^ n - 1)) = binDigitSum (s % (2 ^ n - 1)) := by
  convert binDigitSum_two_mul_mod_of_lt hn ( show s % ( 2 ^ n - 1 ) < 2 ^ n - 1 from Nat.mod_lt _ <| Nat.sub_pos_of_lt <| one_lt_pow₀ one_lt_two <| by linarith ) using 1;
  simp +decide [ Nat.mul_mod ]

/-! ## 3. The iterated / Frobenius-orbit form -/

/-
**Frobenius-orbit invariance.**  Iterating the doubling law: for `1 ≤ n`, the
binary digit sum is constant along the whole Frobenius orbit
`s, 2s, 4s, … (mod 2ⁿ − 1)`:
`s₂((2^j·s) mod (2ⁿ − 1)) = s₂(s mod (2ⁿ − 1))`.

This is exactly the invariance the Stickelberger valuation `v(g(ω^{-s})) = s₂(s)`
must satisfy because Galois conjugation (the Frobenius `p`-power law
`gaussSum_pow_char`) preserves the `2`-adic valuation: the valuation is constant
on `2`-cyclotomic cosets, and so the digit sum that computes it.
-/
theorem binDigitSum_two_pow_mul_mod {n : ℕ} (hn : 1 ≤ n) (j s : ℕ) :
    binDigitSum ((2 ^ j * s) % (2 ^ n - 1)) = binDigitSum (s % (2 ^ n - 1)) := by
  induction' j with j ih;
  · grind;
  · rw [ ← ih, pow_succ', mul_assoc, binDigitSum_two_mul_mod hn ]

end Vanish.Foundations