import Mathlib
import RequestProject.Foundations.FirstPrinciples.Decomp.StickelbergerDecomp
import RequestProject.Foundations.FirstPrinciples.Decomp.AxKatzDecomp

/-!
# Transcription — Leaf L5, module 1: the McEliece weight-congruence divisibility

This is the **first rung** of the McEliece digit-sum bound (leaf **L5** in
`FirstPrinciplesTranscriptionRoadmap.md`).  Its goal (with module 2,
`KasamiCosetDigitSum`) is the `Decomp` leaf
`AxKatzDecomp.kasami_exp_digitSum_lower_bound`: for a non-trivial Kasami frequency,
`s₂(e(s)) ≥ (n+1)/2`.

Classically the digit-sum lower bound is the **McEliece weight congruence** read
through Ax–Katz (leaf L4): the `2`-adic divisibility of the dual Kasami/BCH code
weights forces a valuation lower bound on the associated Gauss sum, which
Stickelberger (leaf L3) converts to the digit sum.  This module carries the two
ingredients of that reading:

* `padicValInt_ge_of_two_pow_dvd` — the elementary bridge `2^m ∣ x → m ≤ v₂(x)`
  (for `x ≠ 0`), a **real proof**;
* `kasami_gaussInt_two_pow_dvd` — the McEliece / Ax–Katz weight congruence in
  Gauss-sum form: `2^{(n+1)/2} ∣ g(s)` for a non-trivial frequency (the single
  classical leaf, the output of L4 applied to the Kasami/BCH defining system).

Module 2 then combines these with Stickelberger's valuation formula
(`StickelbergerDecomp.gaussSum_grossKoblitz_factor`, `v₂(g) = s₂(e)`) to conclude
`s₂(e(s)) ≥ (n+1)/2`, discharging the digit-sum leaf.

## Sources

* R. J. McEliece, *Weight congruences for p-ary cyclic codes*, Discrete Math. 3
  (1972).
* A. Canteaut, P. Charpin, H. Dobbertin, *Weight divisibility of cyclic codes …*,
  SIAM J. Discrete Math. 13 (2000).
* Project: `AxKatzDecomp.axKatz_two_pow_dvd`,
  `StickelbergerDecomp.gaussSum_grossKoblitz_factor`.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations
open Vanish.Foundations.FirstPrinciples Vanish.Foundations.FirstPrinciples.Decomp

/-
**Divisibility gives a valuation lower bound (real proof).**  For a non-zero
integer `x`, if `2^m ∣ x` then the `2`-adic valuation `v₂(x)` is at least `m`.  This
is the elementary bridge that turns the McEliece/Ax–Katz weight divisibility into a
valuation lower bound.
-/
theorem padicValInt_ge_of_two_pow_dvd (x : ℤ) (m : ℕ) (hx : x ≠ 0)
    (h : (2 : ℤ) ^ m ∣ x) : m ≤ padicValInt 2 x := by
  obtain ⟨ k, hk ⟩ := h;
  simp_all +decide [ padicValInt ];
  rw [ Int.natAbs_mul, Int.natAbs_pow, padicValNat.mul ] <;> norm_num [ hx ]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The McEliece / Ax–Katz weight congruence in Gauss-sum form (the L5 leaf).**  For
a non-trivial Kasami frequency (`kasamiGaussInt ≠ 0`), the integer Teichmüller Gauss
sum `g(s)` is divisible by `2^{(n+1)/2}`.  Classically this is the McEliece weight
congruence for the dual Kasami/BCH code — the output of the iterated Ax–Katz
`2^μ`-divisibility (leaf L4, `AxKatzDecomp.axKatz_two_pow_dvd`) applied to the code's
defining polynomial system.  Combined with Stickelberger's valuation formula it
yields the digit-sum bound (module 2). -/
theorem kasami_gaussInt_two_pow_dvd {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) (s : F)
    (hne : kasamiGaussInt k a s ≠ 0) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ kasamiGaussInt k a s := by
  sorry

end Vanish.Foundations.FirstPrinciples.Transcribe