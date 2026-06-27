import ConjecturesMTupleTripleCount.Foundations.QuadraticGaussSum
import ConjecturesMTupleTripleCount.Foundations.KasamiCrossCorrelationValueSet
import ConjecturesMTupleTripleCount.Support.AutocorrQuadratic
import Mathlib

/-!
# Foundations, Layer A2 — the 2-adic valuation bound ⟹ input (A)

This module transcribes **Layer A2** of the value-set dependency chain in
`Docs/VanishFutureDirections.md` §6.  Layer A1
(`Foundations/QuadraticGaussSum.lean`) evaluated the quadratic-form Gauss sum
`S(Q) = ∑_x χ(Q x)` over `GF(2ⁿ)` as `S(Q) ∈ {0, ±2^{(n+r)/2}}`, where `2^r` is
the size of the radical of the polar form.  Layer A2 reads the **2-adic valuation
bound** off that evaluation:

```
  n odd  ⟹  2^{(n+1)/2} ∣ S(Q)            (quadGaussSum_two_adic_div)
```

The point is the *parity* of the exponent.  For a nonzero `S(Q) = ±2^m` with
`2m = n + r`, oddness of `n` forces `r` to be **odd**, hence `r ≥ 1`, hence
`2m = n + r ≥ n + 1`, i.e. `m ≥ (n+1)/2`.  This is exactly the
Stickelberger / McEliece "valuation `≥ (n+1)/2`" bound, here obtained
elementarily from the radical dimension supplied by Layer A1 (no Gauss-sum
2-adic / Ax–Katz machinery is needed once the value set is in hand).

## From the valuation bound to input (A)

The Kasami cross-correlation `R(s) = autocorrScaled f s a = ∑_x χ(s·Δf_a x)` is
**literally** a quadratic-form Gauss sum of the derivative form
`Q_s(x) = s·Δf_a(x)` (`autocorrScaled_eq_quadGaussSum`).  Whenever that form is a
quadratic form (`IsQuadraticForm`, equivalently its third discrete derivative
vanishes — `isQuadraticForm_of_third_deriv_zero`), the valuation bound applies and
gives input **(A)**'s divisibility `hdiv`:

```
  2^{(n+1)/2} ∣ autocorrScaled f s a       (autocorrScaled_two_adic_div_of_isQuadraticForm)
```

`crossCorr_hdiv_of_isQuadraticForm` packages this as the exact `hdiv` hypothesis
of `kasami_crossCorr_value_set`, under the structural assumption that every
derivative form `x ↦ s·Δf_a x` is quadratic.

## Scope: which Kasami exponents are covered unconditionally

The derivative form `x ↦ s·((x+a)^{d k} + x^{d k})` has algebraic degree `≤ 2`
(its third derivative vanishes for **all** `s, a`) exactly when the Kasami
derivative is quadratic — which holds for the low Kasami exponents
`k ≤ 2` (`d 1 = 3`, `d 2 = 13`); for those, `hdiv` is discharged here
**unconditionally** (`kasami_one_crossCorr_hdiv`, `kasami_two_crossCorr_hdiv`).

For the genuinely non-quadratic Kasami exponents (`k ≥ 3`, large `n`) the
derivative form is **not** quadratic, so the radical/valuation route of A1–A2 no
longer applies directly; the classical divisibility there is the
Canteaut–Charpin–Dobbertin / McEliece weight-divisibility theorem (a Frobenius
substitution rewriting `R(s)` as a quadratic Gauss sum, or an Ax–Katz argument),
which is the deeper number-theoretic input flagged in the roadmap and is *not*
present in Mathlib.  This module therefore supplies the full A2 *mechanism* (the
valuation bound and its packaging into `hdiv`) and discharges it unconditionally
on the quadratic-derivative class, isolating the remaining gap to the single
hypothesis "the derivative form is quadratic".

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5–6; Carlet, Ch. 6 (quadratic-form
spectrum); McEliece, *Weight congruences for `p`-ary cyclic codes* (1972);
Canteaut–Charpin–Dobbertin (SIAM J. Discrete Math., 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## A2 core — the 2-adic valuation bound from the radical dimension -/

/-- **Layer A2 (valuation bound).**  For a quadratic form `Q` over `GF(2ⁿ)` with
`n` **odd**, the Gauss sum `S(Q) = ∑_x χ(Q x)` is divisible by `2^{(n+1)/2}`.

This is read off Layer A1's evaluation `S(Q) ∈ {0, ±2^{(n+r)/2}}`: for a nonzero
value `±2^m` with `2m = n + r`, oddness of `n` forces `r` odd, so `r ≥ 1` and
`2m ≥ n + 1`, i.e. `m ≥ (n+1)/2`. -/
theorem quadGaussSum_two_adic_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) {Q : F → F} (hQ : IsQuadraticForm Q) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ quadGaussSum Q := by
  obtain ⟨r, hr, h⟩ := quadGaussSum_value hQ hcard
  rcases h with h | ⟨m, hm, h⟩
  · rw [h]; exact dvd_zero _
  · obtain ⟨j, hj⟩ := hodd
    have hle : (n + 1) / 2 ≤ m := by omega
    rcases h with h | h <;> rw [h]
    · exact pow_dvd_pow 2 hle
    · exact (dvd_neg).mpr (pow_dvd_pow 2 hle)

/-! ## Bridge — vanishing third derivative ⟹ quadratic form -/

omit [Fintype F] [DecidableEq F] in
/-- A function whose third discrete derivative vanishes and which fixes `0` is a
**quadratic form** in the sense of Layer A1 (its polar form is biadditive).  This
bridges the two notions of "quadratic" used in the project: the
third-derivative criterion of `Walsh/WalshDivisibility.lean` and the biadditive
polar form `IsQuadraticForm` of `Foundations/QuadraticGaussSum.lean`. -/
theorem isQuadraticForm_of_third_deriv_zero {Q : F → F} (h0 : Q 0 = 0)
    (h3 : ∀ x y z : F, Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z)
      + Q x + Q y + Q z + Q 0 = 0) :
    IsQuadraticForm Q := by
  constructor
  · intro x1 x2 y
    have := h3 x1 x2 y
    simp only [polar, h0] at *
    abel_nf at *
    grind
  · intro x y1 y2
    have := h3 y1 y2 x
    simp only [polar, h0] at *
    abel_nf at *
    grind

/-! ## The affine valuation bound (Gauss sum of an affine-quadratic form)

The cross-correlation derivative form `Q_s(x) = s·Δf_a(x)` is *affine*-quadratic:
its polar form is biadditive but `Q_s(0) = s·(f a + f 0)` need not be `0`.  Since
`χ(Q x) = χ(Q 0)·χ(Q x + Q 0)` and the shifted form `x ↦ Q x + Q 0` is a genuine
quadratic form (`isQuadraticForm_of_third_deriv_zero`), the valuation bound
transfers up to the unit `χ(Q 0) = ±1`. -/

/-- **Layer A2 (affine valuation bound).**  If `Q : F → F` has vanishing third
discrete derivative (its algebraic degree is `≤ 2`, but `Q 0` may be nonzero),
then over `GF(2ⁿ)` with `n` odd the Gauss sum `∑_x χ(Q x)` is divisible by
`2^{(n+1)/2}`.  Proved by factoring out the constant `χ(Q 0)` and applying
`quadGaussSum_two_adic_div` to the shifted (genuine) quadratic form
`x ↦ Q x + Q 0`. -/
theorem quadGaussSum_two_adic_div_of_third_deriv {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) (Q : F → F)
    (h3 : ∀ x y z : F, Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z)
      + Q x + Q y + Q z + Q 0 = 0) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ quadGaussSum Q := by
  -- The shifted form `Q̃ x = Q x + Q 0` is a genuine quadratic form.
  have hQ' : IsQuadraticForm (fun x => Q x + Q 0) := by
    refine isQuadraticForm_of_third_deriv_zero (by simp [CharTwo.add_self_eq_zero]) ?_
    intro x y z
    have := h3 x y z
    have h8 : (8 : F) = 0 := by
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      rw [show (8 : F) = 2 * 4 from by norm_num, h2, zero_mul]
    linear_combination this + Q 0 * h8
  -- Factor out the unit `χ (Q 0)`.
  have hfact : quadGaussSum Q = χ (Q 0) * quadGaussSum (fun x => Q x + Q 0) := by
    unfold quadGaussSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show χ (Q x) = χ (Q 0) * χ (Q x + Q 0)
    rw [← χ_mul,
      show Q 0 + (Q x + Q 0) = Q x from by
        rw [add_comm (Q x) (Q 0), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]]
  rw [hfact]
  exact Dvd.dvd.mul_left (quadGaussSum_two_adic_div hcard hodd hQ') (χ (Q 0))

/-! ## Bridge — the cross-correlation is a quadratic-form Gauss sum -/

omit [DecidableEq F] in
/-- The scaled cross-correlation `R(s) = autocorrScaled f s a` is the
quadratic-form Gauss sum of the derivative form `x ↦ s·Δf_a(x)`. -/
theorem autocorrScaled_eq_quadGaussSum (f : F → F) (s a : F) :
    autocorrScaled f s a = quadGaussSum (fun x => s * MTuple.deriv f a x) := by
  rfl

/-! ## A2 applied to the cross-correlation -/

/-- **Input (A), third-derivative form.**  If the derivative form
`x ↦ s·Δf_a(x)` has vanishing third discrete derivative, then `R(s)` is divisible
by `2^{(n+1)/2}`. -/
theorem autocorrScaled_two_adic_div_of_third_deriv {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (f : F → F) (s a : F)
    (h3 : ∀ x y z : F,
      (s * MTuple.deriv f a (x + y + z)) + (s * MTuple.deriv f a (x + y))
      + (s * MTuple.deriv f a (x + z)) + (s * MTuple.deriv f a (y + z))
      + (s * MTuple.deriv f a x) + (s * MTuple.deriv f a y) + (s * MTuple.deriv f a z)
      + (s * MTuple.deriv f a 0) = 0) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled f s a := by
  rw [autocorrScaled_eq_quadGaussSum]
  exact quadGaussSum_two_adic_div_of_third_deriv hcard hodd _ h3

/-- **Input (A) as the `hdiv` hypothesis.**  If for every frequency `s` the
derivative form `x ↦ s·Δf_a(x)` has vanishing third derivative, then the
divisibility hypothesis `hdiv` of `kasami_crossCorr_value_set` holds. -/
theorem crossCorr_hdiv_of_third_deriv {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (f : F → F) (a : F)
    (h3 : ∀ s x y z : F,
      (s * MTuple.deriv f a (x + y + z)) + (s * MTuple.deriv f a (x + y))
      + (s * MTuple.deriv f a (x + z)) + (s * MTuple.deriv f a (y + z))
      + (s * MTuple.deriv f a x) + (s * MTuple.deriv f a y) + (s * MTuple.deriv f a z)
      + (s * MTuple.deriv f a 0) = 0) :
    ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled f s a :=
  fun s => autocorrScaled_two_adic_div_of_third_deriv hcard hodd f s a (h3 s)

/-! ## Unconditional discharge for the quadratic Kasami exponents `k ≤ 2` -/

/-- The derivative form of the Kasami map `x ↦ x^{d 1}` (where `d 1 = 3`) has
vanishing third derivative. -/
theorem kasami_one_deriv_third_deriv_zero (s a : F) (x y z : F) :
    (s * MTuple.deriv (fun x : F => x ^ d 1) a (x + y + z))
      + (s * MTuple.deriv (fun x : F => x ^ d 1) a (x + y))
      + (s * MTuple.deriv (fun x : F => x ^ d 1) a (x + z))
      + (s * MTuple.deriv (fun x : F => x ^ d 1) a (y + z))
      + (s * MTuple.deriv (fun x : F => x ^ d 1) a x)
      + (s * MTuple.deriv (fun x : F => x ^ d 1) a y)
      + (s * MTuple.deriv (fun x : F => x ^ d 1) a z)
      + (s * MTuple.deriv (fun x : F => x ^ d 1) a 0) = 0 := by
  have hd : d 1 = 3 := by decide
  simp only [hd, MTuple.deriv]
  have := AutocorrQuadratic.gold_autocorr_third_deriv_zero (F := F) s a x y z
  simp only at this
  linear_combination this

omit [Fintype F] [DecidableEq F] in
/-
The derivative form of the Kasami map `x ↦ x^{d 2}` (where `d 2 = 13`) has
vanishing third derivative.
-/
theorem kasami_two_deriv_third_deriv_zero (s a : F) (x y z : F) :
    (s * MTuple.deriv (fun x : F => x ^ d 2) a (x + y + z))
      + (s * MTuple.deriv (fun x : F => x ^ d 2) a (x + y))
      + (s * MTuple.deriv (fun x : F => x ^ d 2) a (x + z))
      + (s * MTuple.deriv (fun x : F => x ^ d 2) a (y + z))
      + (s * MTuple.deriv (fun x : F => x ^ d 2) a x)
      + (s * MTuple.deriv (fun x : F => x ^ d 2) a y)
      + (s * MTuple.deriv (fun x : F => x ^ d 2) a z)
      + (s * MTuple.deriv (fun x : F => x ^ d 2) a 0) = 0 := by
  push_cast [ show d 2 = 13 by decide ];
  simp +decide [ MTuple.deriv ];
  grind +splitIndPred

/-- **Input (A) for `k = 1`.**  Over `GF(2ⁿ)` with `n` odd, every Kasami `k = 1`
cross-correlation value is divisible by `2^{(n+1)/2}`. -/
theorem kasami_one_crossCorr_hdiv {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) (a : F) :
    ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
      ∣ autocorrScaled (fun x : F => x ^ d 1) s a := by
  intro s
  exact autocorrScaled_two_adic_div_of_third_deriv hcard hodd _ s a
    (kasami_one_deriv_third_deriv_zero s a)

/-- **Input (A) for `k = 2`.**  Over `GF(2ⁿ)` with `n` odd, every Kasami `k = 2`
cross-correlation value is divisible by `2^{(n+1)/2}`. -/
theorem kasami_two_crossCorr_hdiv {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) (a : F) :
    ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
      ∣ autocorrScaled (fun x : F => x ^ d 2) s a := by
  intro s
  exact autocorrScaled_two_adic_div_of_third_deriv hcard hodd _ s a
    (kasami_two_deriv_third_deriv_zero s a)

end Vanish.Foundations