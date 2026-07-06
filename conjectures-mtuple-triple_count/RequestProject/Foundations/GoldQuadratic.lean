import RequestProject.Foundations.RankSpectrum
import RequestProject.APN.CharTwoBasics

/-!
# Foundations — Appendix A.4 / equation (12): the Gold building blocks are quadratic

This module transcribes the **Appendix A.4** ingredient of Dillon–Dobbertin's
equation (12): the auxiliary forms appearing in the average

```
   Ŝ_d^λ(a) = (1/3) · ∑_{μ ∈ K*}  Q̂^λ_{aμ}(0),
   where  q^λ_{aμ}(x) = Tr(λ x^{2^{3k}+1} + aμ x^{2^k+1})     (K = GF(4))
```

are **genuine quadratic forms**, so each `Q̂^λ_{aμ}(0)` is evaluated by the
rank ⇒ spectrum principle (`Foundations/RankSpectrum.lean`) via the existing
`quadGaussSum_value`.  Concretely, both exponents `2^j + 1` are *Gold* (quadratic)
exponents, and the trace of a Gold monomial `λ x^{2^j+1}` has an `F₂`-biadditive
polar form, hence is a quadratic form in the project's sense
(`Vanish.Foundations.IsQuadraticForm`).  Sums of quadratic forms are quadratic, so
`q^λ_{aμ}` is quadratic; feeding it to `quadGaussSum_value` gives
`Q̂^λ_{aμ}(0) ∈ {0, ±2^{(n+r)/2}}`.

The accompanying **exponent identity** `d · (2^k + 1) = 2^{3k} + 1` (with
`d = 2^{2k} − 2^k + 1` the Kasami exponent) is the algebraic backbone that turns
the non-quadratic Kasami exponent into the Gold exponents `2^{3k}+1`, `2^k+1` of
the auxiliary forms.

## Regime caveat (honest)

Equation (12)'s **GF(4)-coset average** is intrinsically an **`m`-even** device:
its factor `1/3` and the scalars `μ ∈ GF(4)*` rely on `GF(4) ⊆ GF(2^m)`, i.e.
`2 ∣ m`, and on the cubing map having nontrivial fibers.  For the project's
**`n` odd** regime neither holds — indeed `x ↦ x³` is a *bijection* of `GF(2ⁿ)*`
when `n` is odd (`three_not_dvd_two_pow_sub_one_of_odd` below: `3 ∤ 2ⁿ − 1`), so
the three-term coset average *degenerates*.  Thus the odd-`n` Kasami value set —
and with it the cross-correlation inputs **(A)** divisibility and **(B)** the
fourth moment — is *not* delivered by transcribing (12) literally; it is the
classical odd-`n` almost-bent cross-correlation theorem, carried as named
hypotheses elsewhere in the development (`KasamiCrossCorrelationValueSet.lean`).
What *does* transfer parity-agnostically, and is delivered here sorry-free, is the
**quadratic-form substrate** on which both the even-`n` equation (12) and the
odd-`n` Gold case (Prop. A.4) rest.

## Results

* `goldForm_isQuadraticForm` — `Q(x) = λ x^{2^j+1}` is a quadratic form.
* `IsQuadraticForm.add` — sums of quadratic forms are quadratic.
* `kasamiAux_isQuadraticForm` — the Appendix-A.4 form
  `λ x^{2^{3k}+1} + a x^{2^k+1}` is a quadratic form.
* `kasamiAux_gaussSum_spectrum` — its Gauss sum lies in `{0, ±2^{(n+r)/2}}`
  (rank ⇒ spectrum applied to the auxiliary form).
* `kasami_exponent_factor` — `d · (2^k + 1) = 2^{3k} + 1`.
* `three_not_dvd_two_pow_sub_one_of_odd` — the degeneracy witness: `3 ∤ 2ⁿ − 1`
  for `n` odd.

## Sources

Dillon–Dobbertin (FFA 2004), §7 (eq. (12)) and Appendix A.4 (Theorem A.5,
Corollary A.6); Lidl–Niederreiter Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**Sums of quadratic forms are quadratic.**  The polar form is additive, so if
`Q` and `R` are quadratic forms then so is `x ↦ Q x + R x`.
-/
omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem IsQuadraticForm.add {Q R : F → F} (hQ : IsQuadraticForm Q)
    (hR : IsQuadraticForm R) : IsQuadraticForm (fun x => Q x + R x) := by
  have hsplit : ∀ x y : F, polar (fun x => Q x + R x) x y
      = polar Q x y + polar R x y := by
    intro x y; simp only [polar]; ring
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ y
    rw [hsplit, hsplit, hsplit, hQ.polar_add_left, hR.polar_add_left]; ring
  · intro x y₁ y₂
    rw [hsplit, hsplit, hsplit, hQ.polar_add_right, hR.polar_add_right]; ring

/-
**The Gold monomial form is quadratic.**  For a Gold (quadratic) exponent
`2^j + 1`, the monomial `Q(x) = λ · x^{2^j+1}` is a quadratic form: its polar form
`B(x,y) = λ (x · y^{2^j} + x^{2^j} · y)` is `F₂`-biadditive (Freshman's dream
makes `y ↦ y^{2^j}` additive).
-/
theorem goldForm_isQuadraticForm (j : ℕ) (lam : F) :
    IsQuadraticForm (fun x => lam * x ^ (2 ^ j + 1)) := by
  constructor
  · intro x₁ x₂ y; simp only [polar, pow_add, pow_one, mul_add]; grind +suggestions
  · unfold polar; grind +suggestions

/-- **The Appendix-A.4 auxiliary form is quadratic.**  The form
`q(x) = λ x^{2^{3k}+1} + a x^{2^k+1}` (a sum of two Gold monomial forms) is a
quadratic form. -/
theorem kasamiAux_isQuadraticForm (k : ℕ) (lam a : F) :
    IsQuadraticForm (fun x => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1)) :=
  (goldForm_isQuadraticForm (3 * k) lam).add (goldForm_isQuadraticForm k a)

/-- **Each equation-(12) term obeys rank ⇒ spectrum.**  The Gauss sum of the
Appendix-A.4 auxiliary form `q^λ_{a}(x) = λ x^{2^{3k}+1} + a x^{2^k+1}` over
`GF(2ⁿ)` lies in `{0, ±2^{(n+r)/2}}`: it is `0`, or `±2^m` with `2m = n + r` for
some radical exponent `r ≤ n`.  This is `quadGaussSum_value` applied to
`kasamiAux_isQuadraticForm`. -/
theorem kasamiAux_gaussSum_spectrum {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (lam a : F) :
    ∃ r : ℕ, r ≤ n ∧
      (quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1)) = 0
        ∨ ∃ m : ℕ, 2 * m = n + r
            ∧ (quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))
                  = 2 ^ m
              ∨ quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))
                  = -(2 ^ m))) :=
  quadGaussSum_value (kasamiAux_isQuadraticForm k lam a) hcard

/-
**The Kasami exponent identity** `d · (2^k + 1) = 2^{3k} + 1`, with
`d = 2^{2k} − 2^k + 1` the Kasami exponent.  This is the algebraic backbone of
equation (12): it turns the non-quadratic Kasami exponent into the Gold exponents
`2^{3k}+1` and `2^k+1` of the auxiliary forms.
-/
theorem kasami_exponent_factor (k : ℕ) :
    (2 ^ (2 * k) - 2 ^ k + 1) * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  have h : 2 ^ k ≤ 2 ^ (2 * k) := by apply Nat.pow_le_pow_right <;> omega
  have e2 : (2 : ℤ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
  have e3 : (2 : ℤ) ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; ring_nf
  zify [h]; rw [e2, e3]; ring

/-
**Degeneracy witness for odd `n`.**  When `n` is odd, `3 ∤ 2ⁿ − 1` (since
`2ⁿ ≡ 2 (mod 3)`), so the cubing map `x ↦ x³` is a bijection of `GF(2ⁿ)*` and the
GF(4)-coset average of equation (12) degenerates — the reason the odd-`n` Kasami
value set is the classical almost-bent cross-correlation theorem rather than a
consequence of (12).
-/
theorem three_not_dvd_two_pow_sub_one_of_odd {n : ℕ} (hn : Odd n) :
    ¬ (3 ∣ 2 ^ n - 1) := by
  obtain ⟨ k, rfl ⟩ := hn;
  rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * k + 1 ) ) 3, Nat.pow_add, Nat.pow_mul ] ; norm_num [ Nat.mul_mod, Nat.pow_mod, Nat.dvd_iff_mod_eq_zero ]

end Vanish.Foundations