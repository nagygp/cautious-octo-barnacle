import RequestProject.Foundations.QuadraticGaussSum
import RequestProject.Foundations.KasamiTwoAdicValuation
import RequestProject.Foundations.KasamiFourthMomentCanonical
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# Foundations — the quadratic value-set layer for input (B)

This module grows the **green core** of the m-tuple count proof path by one edge on
the input-(B) side, staying strictly on already-green foundations.

## Where this sits

The whole of input (B) (`∑_{s≠0} R(s)⁴ = 2q³`, equivalently the derivative
4-collision count `preCount₄ = q³ + 2q²`) is, in the current tower, reduced to the
single deep leaf `Vanish.Foundations.kasami_a1_preCount4`
(`KasamiFourthMomentCanonical.lean`).  That leaf is the genuine almost-bent content.

For the **quadratic-derivative** Kasami exponents — those `k` for which the
derivative form `x ↦ s·Δf_a(x)` has vanishing third discrete derivative (checked
green for `k = 1, 2` in `KasamiTwoAdicValuation.lean`) — the cross-correlation
`R(s)` is *literally* a quadratic-form Gauss sum, so the whole of input (B) can be
read off the **already-green** quadratic Gauss-sum evaluation
(`QuadraticGaussSum.lean`, `quadGaussSum_sq_eq_or`, `radical_card_pow_two`).  The
only genuinely almost-bent datum that remains is then a clean, elementary geometric
fact: the polar form of the (nonzero) derivative form has a **1-dimensional
radical**, i.e. `#(radical Q̃_s) ≤ 2`.

## What is added here (all directly on green foundations)

* `quadGaussSum_sq_value_of_div` — **green**: for a genuine quadratic form `Q` over
  `GF(2ⁿ)` (`n` odd) with `2^{(n+1)/2} ∣ S(Q)` and `#(radical Q) ≤ 2`, the squared
  Gauss sum is `S(Q)² ∈ {0, 2q}`.  (The divisibility forces the radical dimension
  `r ≥ 1`; the hypothesis `#(radical Q) ≤ 2` forces `r ≤ 1`; hence `r = 1`.)  This
  rests only on `quadGaussSum_sq_eq_or` and `radical_card_pow_two`.
* `crossCorr_sq_value_of_third_deriv_radical` — **green**: transferring the above
  through the affine shift `Q̃_s = Q_s + Q_s 0` (`χ` a `±1` unit), the
  cross-correlation of a third-derivative-vanishing derivative form satisfies
  `R(s)² ∈ {0, 2q}` for every `s` with a `≤ 2`-radical.
* `preCount4_of_third_deriv_radical` — **green**: feeding the value set to the
  already-green `preCount4_of_value_set` gives the derivative 4-collision count
  `preCount₄ = q³ + 2q²` for any APN map with quadratic derivative and everywhere
  `≤ 2`-radical.

## The exposed frontier leaf

`kasami_two_derivForm_radical` isolates exactly the remaining almost-bent geometric
content for `k = 2`: the polar radical of the nonzero derivative form has size `≤ 2`.
It is the only `sorry` here, and it is a genuine, faithful leaf (not vacuous): note
it *fails* for `k = 1` (there the cube derivative is `F₂`-affine, its polar form is
identically `0`, so the radical is the whole field), which is exactly why the `k = 1`
"Kasami" map is two-valued and its `preCount₄ = 2q³ ≠ q³ + 2q²` — see
`MTupleQuadraticValueSetFindings.md`.

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5–6; Carlet, Ch. 6 (quadratic-form
spectrum); Canteaut–Charpin–Dobbertin (SIAM J. Discrete Math., 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The green base lemma: quadratic value set from divisibility + radical bound -/

/-- **Quadratic Gauss-sum value set from divisibility and a small radical.**  For a
genuine quadratic form `Q` over `GF(2ⁿ)` with `n` **odd**, if `2^{(n+1)/2} ∣ S(Q)`
and the polar radical has size `≤ 2`, then `S(Q)² ∈ {0, 2q}`.

Proof: `quadGaussSum_sq_eq_or` gives `S² = 0` or `S² = q·#(radical)`; write
`#(radical) = 2^r` (`radical_card_pow_two`).  Divisibility gives `2^{n+1} ∣ S²`, so
in the nonzero case `2^{n+1} ∣ 2^{n+r}`, i.e. `r ≥ 1`; the radical bound gives
`r ≤ 1`.  Hence `r = 1` and `S² = q·2 = 2q`. -/
theorem quadGaussSum_sq_value_of_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) {Q : F → F} (hQ : IsQuadraticForm Q) (hrad : (radical Q).card ≤ 2)
    (hdiv : (2 : ℤ) ^ ((n + 1) / 2) ∣ quadGaussSum Q) :
    quadGaussSum Q ^ 2 = 0 ∨ quadGaussSum Q ^ 2 = 2 * (Fintype.card F : ℤ) := by
  rcases quadGaussSum_sq_eq_or hQ with h | h
  · exact Or.inl h
  obtain ⟨r, hrn, hrcard⟩ := radical_card_pow_two hQ hcard
  have hsqdvd : (2 : ℤ) ^ (n + 1) ∣ quadGaussSum Q ^ 2 := by
    have hh : ((2 : ℤ) ^ ((n + 1) / 2)) ^ 2 ∣ quadGaussSum Q ^ 2 := pow_dvd_pow_of_dvd hdiv 2
    have hnn : (n + 1) / 2 * 2 = n + 1 := by obtain ⟨t, ht⟩ := hodd; omega
    rwa [← pow_mul, hnn] at hh
  have hval : quadGaussSum Q ^ 2 = 2 ^ (n + r) := by
    rw [h, hcard, hrcard]; push_cast; rw [← pow_add]
  have hr1 : 1 ≤ r := by
    rw [hval] at hsqdvd
    have := (pow_dvd_pow_iff (a := (2 : ℤ)) (by norm_num) (by decide)).mp hsqdvd
    omega
  have hr_le : r ≤ 1 := by
    rw [hrcard] at hrad
    have : (2 : ℕ) ^ r ≤ 2 ^ 1 := by simpa using hrad
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hre : r = 1 := le_antisymm hr_le hr1
  subst hre
  right
  rw [hval, hcard]; push_cast; ring

/-! ## Transfer to the cross-correlation through the affine shift -/

/-
**Cross-correlation value set from a quadratic derivative with small radical.**
If the derivative form `Q_s(x) = s·Δf_a(x)` has vanishing third discrete derivative
and the polar radical of its zero-shift `Q̃_s(x) = s·Δf_a(x) + s·Δf_a(0)` has size
`≤ 2`, then over `GF(2ⁿ)` (`n` odd) the cross-correlation satisfies
`R(s)² ∈ {0, 2q}`.

Proof: `R(s) = S(Q_s) = χ(Q_s 0)·S(Q̃_s)` with `χ(Q_s 0) = ±1`, so `R(s)² = S(Q̃_s)²`
and divisibility transfers between them; then apply `quadGaussSum_sq_value_of_div`
to the genuine quadratic form `Q̃_s` (via `isQuadraticForm_of_third_deriv_zero`)
with divisibility from `quadGaussSum_two_adic_div_of_third_deriv`.
-/
theorem crossCorr_sq_value_of_third_deriv_radical {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) (f : F → F) (a s : F)
    (h3 : ∀ x y z : F,
      (s * MTuple.deriv f a (x + y + z)) + (s * MTuple.deriv f a (x + y))
      + (s * MTuple.deriv f a (x + z)) + (s * MTuple.deriv f a (y + z))
      + (s * MTuple.deriv f a x) + (s * MTuple.deriv f a y) + (s * MTuple.deriv f a z)
      + (s * MTuple.deriv f a 0) = 0)
    (hrad : (radical (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0)).card ≤ 2) :
    autocorrScaled f s a ^ 2 = 0 ∨ autocorrScaled f s a ^ 2 = 2 * (Fintype.card F : ℤ) := by
  have h_quad : IsQuadraticForm (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) := by
    apply isQuadraticForm_of_third_deriv_zero;
    · grind +suggestions;
    · grind +splitImp;
  have h_div : (2 : ℤ) ^ ((n + 1) / 2) ∣ quadGaussSum (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) := by
    convert quadGaussSum_two_adic_div_of_third_deriv hcard hodd ( fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0 ) _ using 1;
    grind +qlia;
  have h_eq : quadGaussSum (fun x => s * MTuple.deriv f a x) = χ (s * MTuple.deriv f a 0) * quadGaussSum (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) := by
    unfold quadGaussSum;
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext x ; rw [ ← WalshAB.χ_mul ] ;
    simp only [] ;
    rw [ add_comm ( s * MTuple.deriv f a x ) ( s * MTuple.deriv f a 0 ), ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add ];
  have h_sq : quadGaussSum (fun x => s * MTuple.deriv f a x) ^ 2 = quadGaussSum (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) ^ 2 := by
    rw [ h_eq, mul_pow, WalshAB.χ_sq ] ; norm_num;
  have := quadGaussSum_sq_value_of_div hcard hodd h_quad hrad h_div; simp_all +decide [ autocorrScaled_eq_quadGaussSum ] ;

/-! ## The derivative 4-collision count for quadratic-derivative APN maps -/

/-
**Green consequence: the derivative 4-collision count.**  For an APN map `f`
over `GF(2ⁿ)` (`n` odd) whose derivative forms all have vanishing third derivative
and everywhere-`≤ 2` radical, the derivative 4-collision count attains the
almost-bent value `preCount₄ = q³ + 2q²`.  Assembled from
`crossCorr_sq_value_of_third_deriv_radical` and the already-green
`preCount4_of_value_set`.
-/
theorem preCount4_of_third_deriv_radical {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) (f : F → F) (hf : IsAPN f)
    (a : F) (ha : a ≠ 0)
    (h3 : ∀ s x y z : F,
      (s * MTuple.deriv f a (x + y + z)) + (s * MTuple.deriv f a (x + y))
      + (s * MTuple.deriv f a (x + z)) + (s * MTuple.deriv f a (y + z))
      + (s * MTuple.deriv f a x) + (s * MTuple.deriv f a y) + (s * MTuple.deriv f a z)
      + (s * MTuple.deriv f a 0) = 0)
    (hrad : ∀ s : F,
      (radical (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0)).card ≤ 2) :
    (MTuple.preCount 4 f a (fun _ => 1) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 := by
  apply Vanish.Foundations.preCount4_of_value_set f hf a ha;
  exact fun s hs => Vanish.Foundations.crossCorr_sq_value_of_third_deriv_radical hcard hodd f a s ( h3 s ) ( hrad s )

/-! ## The exposed frontier leaf (`k = 2`) — DISPROVED, see `KasamiTwoDerivPolar.lean`

The frontier leaf that used to live here,

```
   kasami_two_derivForm_radical :
     ∀ s, (radical (s·Δf_a + s·Δf_a 0)).card ≤ 2,
```

is **false**.  A direct computation over `GF(2⁵)` (the genuine Kasami regime
`n = 5, k = 2, d = 13`) shows the polar radical has **eight** elements at `a = 1,
s = 3`, where `R(3) = 0`.  In general the derivative polar radical is large exactly
when `R(s) = 0`; it is `≤ 2` only when `R(s) ≠ 0`.  So `radical.card ≤ 2` is *not*
the correct (satisfiable) hypothesis, and the derivation of `kasami_two_a1_preCount4`
from it went through a `sorry` of a false statement (unsound).

The correct almost-bent datum is the **upper bound** `R(s)² ≤ 2q`
(`= radical.card ≤ 2 ∨ R(s) = 0`), which *is* true for every `s ≠ 0`.  The corrected
value-set chain and the corrected `kasami_two_a1_preCount4` are rebuilt on that true
leaf in `RequestProject/Foundations/KasamiTwoDerivPolar.lean`
(`kasami_two_crossCorr_sq_ub`, `preCount4_of_third_deriv_ub`, `kasami_two_a1_preCount4`).
The false leaf and its (unsound) consumer are commented out below to keep the tree
free of false `sorry`s.
-/

-- FALSE (disproved over GF(2⁵) at s = 3): kept only as a record; see the note above
-- and `KasamiTwoDerivPolar.lean` for the corrected `R(s)² ≤ 2q` leaf.
-- theorem kasami_two_derivForm_radical {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
--     (hodd : Odd n) (a : F) (s : F) :
--     (radical (fun x => s * MTuple.deriv (fun x : F => x ^ d 2) a x
--         + s * MTuple.deriv (fun x : F => x ^ d 2) a 0)).card ≤ 2 := by
--   sorry

-- Rested on the false leaf above; the corrected proof lives in `KasamiTwoDerivPolar.lean`.
-- theorem kasami_two_a1_preCount4 {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
--     (hkn : 2 < n) (hcop : Nat.Coprime 2 n) (hodd : Odd n) (a : F) (ha : a ≠ 0) :
--     (MTuple.preCount 4 (fun x : F => x ^ d 2) a (fun _ => 1) : ℤ)
--       = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 :=
--   preCount4_of_third_deriv_radical hcard hodd _
--     (KasamiAB.kasami_is_apn_pred hcard 2 (by norm_num) hkn hcop hodd (by omega)) a ha
--     (fun s x y z => kasami_two_deriv_third_deriv_zero s a x y z)
--     (fun s => kasami_two_derivForm_radical hcard hodd a s)

end Vanish.Foundations