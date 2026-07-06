import RequestProject.Foundations.KasamiQuadraticValueSet
import RequestProject.Foundations.KasamiCrossCorrelationValueSet
import RequestProject.Foundations.KasamiAutocorrWalshBridge
import Mathlib

/-!
# Foundations — the explicit `k = 2` Kasami derivative polar form, and the *corrected*
input-(B) value-set reduction

This module does two things, both on already-green foundations.

## 1. It corrects a false frontier leaf

The module `KasamiQuadraticValueSet.lean` reduced input (B) for the `k = 2` Kasami
map to the leaf `kasami_two_derivForm_radical`:

```
   ∀ s,  (radical (s·Δf_a + s·Δf_a 0)).card ≤ 2.
```

**This leaf is false.**  A direct computation over `GF(2⁵)` (the genuine Kasami
regime `n = 5, k = 2, d = 13`) shows that at `a = 1, s = 3` the radical has **eight**
elements — while the cross-correlation `R(3) = 0`.  In general the polar radical of
the derivative form is *large* exactly on the frequencies where `R(s) = 0`; it is
`≤ 2` only when `R(s) ≠ 0`.  So `radical.card ≤ 2` is *not* the right (satisfiable)
hypothesis: the correct almost-bent datum is the **upper bound**

```
   R(s)² ≤ 2q          (equivalently  radical.card ≤ 2 ∨ R(s) = 0),
```

which *is* true for every `s ≠ 0` (checked over `GF(2⁵)`: the value set is
`R(s) ∈ {0, ±8}`, so `R(s)² ∈ {0, 64} = {0, 2q}`).

The old chain "proved" `kasami_two_a1_preCount4` from that false leaf, i.e. through
a `sorry` of a false statement — unsound.  Here we rebuild the reduction on the
*true* upper-bound leaf, so the whole chain is sound and the exposed frontier is a
genuine, satisfiable statement.

## 2. It records the explicit polar form (structural handle)

Mirroring `KasamiGoldPolar.lean` (which wrote the Gold polar form explicitly), we
write the polar (bilinear) form of the `k = 2` Kasami derivative explicitly:

```
   polar Q_s(x, u) = s·(a·(x⁸u⁴+x⁴u⁸) + a⁴·(x⁸u+xu⁸) + a⁸·(x⁴u+xu⁴)),
```

so the radical becomes the trace-trivial kernel of an explicit `F₂`-linear form
(`kasami_two_derivForm_mem_radical`).  This is the concrete object underneath the
remaining upper-bound leaf.

## Results

* `kasami_two_derivForm_polar` — **green**: the explicit polar form.
* `kasami_two_derivForm_mem_radical` — **green**: the radical as a trace-trivial kernel.
* `quadGaussSum_sq_value_of_div_ub` — **green**: value set `S(Q)² ∈ {0, 2q}` from the
  divisibility `2^{(n+1)/2} ∣ S(Q)` **and the AB upper bound** `S(Q)² ≤ 2q`.
* `crossCorr_sq_value_of_third_deriv_ub` — **green**: the same, transferred to the
  cross-correlation through the affine `χ`-shift.
* `preCount4_of_third_deriv_ub` — **green**: the derivative 4-collision count
  `preCount₄ = q³ + 2q²` from the everywhere upper bound.
* `kasami_two_crossCorr_sq_ub` — the *true* frontier leaf (the almost-bent upper
  bound `R(s)² ≤ 2q` for the `k = 2` Kasami derivative, `s ≠ 0`).
* `kasami_two_a1_preCount4` — **green modulo the true leaf**: the `k = 2` count,
  re-derived on the corrected chain (replaces the version that rested on the false
  radical leaf).

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5–6; Carlet, *Boolean Functions…*, Ch. 6;
Canteaut–Charpin–Dobbertin (SIAM J. Discrete Math., 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The explicit polar form of the `k = 2` Kasami derivative -/

/- **The explicit `k = 2` Kasami derivative polar form.**  In characteristic `2`,
the polar (bilinear) form of the zero-shifted derivative form
`Q_s(x) = s·Δf_a(x) + s·Δf_a(0)` for the Kasami map `x ↦ x^{d 2}` (`d 2 = 13`) is

```
   B(x,u) = s·(a·(x⁸u⁴+x⁴u⁸) + a⁴·(x⁸u+xu⁸) + a⁸·(x⁴u+xu⁴)),
```

obtained from Freshman's dream (`add_pow_char_pow`) on the weight-2 exponents
`12 = 8+4`, `9 = 8+1`, `5 = 4+1` of `Δf_a(x) = (x+a)¹³ + x¹³`. -/
omit [Fintype F] [DecidableEq F] in
theorem kasami_two_derivForm_polar (s a x u : F) :
    polar (fun x => s * MTuple.deriv (fun x : F => x ^ CollisionAnalysis.d 2) a x
        + s * MTuple.deriv (fun x : F => x ^ CollisionAnalysis.d 2) a 0) x u
      = s * (a * (x ^ 8 * u ^ 4 + x ^ 4 * u ^ 8) + a ^ 4 * (x ^ 8 * u + x * u ^ 8)
          + a ^ 8 * (x ^ 4 * u + x * u ^ 4)) := by
  have hd : CollisionAnalysis.d 2 = 13 := by decide
  simp only [polar, MTuple.deriv, hd]
  have p13 : ∀ y : F, y ^ 13 = y ^ 8 * y ^ 4 * y := fun y => by ring
  have f8 : ∀ p q : F, (p + q) ^ 8 = p ^ 8 + q ^ 8 := fun p q => add_pow_char_pow p q 2 3
  have f4 : ∀ p q : F, (p + q) ^ 4 = p ^ 4 + q ^ 4 := fun p q => add_pow_char_pow p q 2 2
  simp only [p13, f8, f4]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (s*x*u^12 + s*x*a^12 + s*x^4*u^9 + s*x^4*a^9 + s*x^5*u^8 + s*x^5*a^8
    + s*x^8*u^5 + s*x^8*a^5 + s*x^9*u^4 + s*x^9*a^4 + s*x^12*u + s*x^12*a + 2*s*x^13
    + s*u*a^12 + s*u^4*a^9 + s*u^5*a^8 + s*u^8*a^5 + s*u^9*a^4 + s*u^12*a + 2*s*u^13
    + 3*s*a^13) * h2

/- **The `k = 2` Kasami derivative radical as a trace-trivial kernel.**  `u` lies in
the radical of the derivative form iff the explicit polar form `B(x,u)` is
trace-trivial for every `x`. -/
omit [DecidableEq F] in
theorem kasami_two_derivForm_mem_radical (s a u : F) :
    u ∈ radical (fun x => s * MTuple.deriv (fun x : F => x ^ CollisionAnalysis.d 2) a x
        + s * MTuple.deriv (fun x : F => x ^ CollisionAnalysis.d 2) a 0)
      ↔ ∀ x : F, Tr (s * (a * (x ^ 8 * u ^ 4 + x ^ 4 * u ^ 8) + a ^ 4 * (x ^ 8 * u + x * u ^ 8)
          + a ^ 8 * (x ^ 4 * u + x * u ^ 4))) = 0 := by
  rw [mem_radical]
  constructor
  · intro h x; rw [← kasami_two_derivForm_polar]; exact h x
  · intro h x; rw [kasami_two_derivForm_polar]; exact h x

/-! ## 2. The corrected value-set reduction (from the AB upper bound) -/

/-- **Corrected quadratic value set: from divisibility and the AB upper bound.**  For
a genuine quadratic form `Q` over `GF(2ⁿ)` (`n` odd) with `2^{(n+1)/2} ∣ S(Q)` **and**
`S(Q)² ≤ 2q`, the squared Gauss sum is `S(Q)² ∈ {0, 2q}`.

This replaces `quadGaussSum_sq_value_of_div` (which used the unsatisfiable hypothesis
`#(radical) ≤ 2`).  Proof: `quadGaussSum_sq_eq_or` gives `S² = 0` (done) or
`S² = q·#radical`; divisibility forces `2 ∣ #radical`, so `S² = q·#radical ≥ 2q`;
the upper bound `S² ≤ 2q` then pins `S² = 2q`. -/
theorem quadGaussSum_sq_value_of_div_ub {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) {Q : F → F} (hQ : IsQuadraticForm Q)
    (hub : quadGaussSum Q ^ 2 ≤ 2 * (Fintype.card F : ℤ))
    (hdiv : (2 : ℤ) ^ ((n + 1) / 2) ∣ quadGaussSum Q) :
    quadGaussSum Q ^ 2 = 0 ∨ quadGaussSum Q ^ 2 = 2 * (Fintype.card F : ℤ) := by
  rcases quadGaussSum_sq_eq_or hQ with h | h
  · exact Or.inl h
  · right
    have hsqdvd : (2 : ℤ) ^ (n + 1) ∣ quadGaussSum Q ^ 2 := by
      have hh : ((2 : ℤ) ^ ((n + 1) / 2)) ^ 2 ∣ quadGaussSum Q ^ 2 := pow_dvd_pow_of_dvd hdiv 2
      have hnn : (n + 1) / 2 * 2 = n + 1 := by obtain ⟨t, ht⟩ := hodd; omega
      rwa [← pow_mul, hnn] at hh
    have hrpos : 0 < (radical Q).card := Finset.card_pos.mpr ⟨0, zero_mem_radical hQ⟩
    set q : ℤ := (2 : ℤ) ^ n with hq
    set r : ℤ := ((radical Q).card : ℤ) with hr
    have hqpos : 0 < q := by positivity
    have hcast : quadGaussSum Q ^ 2 = q * r := by rw [h, hcard]; push_cast; ring
    have hsq2 : (2 : ℤ) * q ∣ quadGaussSum Q ^ 2 := by
      rw [pow_succ] at hsqdvd; rwa [mul_comm] at hsqdvd
    rw [hcast, mul_comm 2 q] at hsq2
    have h2r : (2 : ℤ) ∣ r := (mul_dvd_mul_iff_left (ne_of_gt hqpos)).mp hsq2
    have hge : (2 : ℤ) ≤ r := by
      rcases h2r with ⟨c, hc⟩
      have hrp : 0 < r := by rw [hr]; exact_mod_cast hrpos
      omega
    rw [hcast, hcard] at hub ⊢
    push_cast at hub ⊢
    nlinarith [hub, hge, hqpos]

/-- **Cross-correlation value set from the AB upper bound.**  If the derivative form
`Q_s(x) = s·Δf_a(x)` has vanishing third discrete derivative and the cross-correlation
satisfies the almost-bent upper bound `R(s)² ≤ 2q`, then over `GF(2ⁿ)` (`n` odd)
`R(s)² ∈ {0, 2q}`.  Transfers `quadGaussSum_sq_value_of_div_ub` through the affine
`χ`-shift `Q̃_s = Q_s + Q_s 0`. -/
theorem crossCorr_sq_value_of_third_deriv_ub {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) (f : F → F) (a s : F)
    (h3 : ∀ x y z : F,
      (s * MTuple.deriv f a (x + y + z)) + (s * MTuple.deriv f a (x + y))
      + (s * MTuple.deriv f a (x + z)) + (s * MTuple.deriv f a (y + z))
      + (s * MTuple.deriv f a x) + (s * MTuple.deriv f a y) + (s * MTuple.deriv f a z)
      + (s * MTuple.deriv f a 0) = 0)
    (hub : autocorrScaled f s a ^ 2 ≤ 2 * (Fintype.card F : ℤ)) :
    autocorrScaled f s a ^ 2 = 0 ∨ autocorrScaled f s a ^ 2 = 2 * (Fintype.card F : ℤ) := by
  have h_quad : IsQuadraticForm (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) := by
    apply isQuadraticForm_of_third_deriv_zero
    · grind +suggestions
    · grind +splitImp
  have h_div : (2 : ℤ) ^ ((n + 1) / 2) ∣ quadGaussSum (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) := by
    convert quadGaussSum_two_adic_div_of_third_deriv hcard hodd ( fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0 ) _ using 1
    grind +qlia
  have h_eq : quadGaussSum (fun x => s * MTuple.deriv f a x) = χ (s * MTuple.deriv f a 0) * quadGaussSum (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) := by
    unfold quadGaussSum
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext x ; rw [ ← WalshAB.χ_mul ]
    simp only []
    rw [ add_comm ( s * MTuple.deriv f a x ) ( s * MTuple.deriv f a 0 ), ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add ]
  have h_sq : quadGaussSum (fun x => s * MTuple.deriv f a x) ^ 2 = quadGaussSum (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) ^ 2 := by
    rw [ h_eq, mul_pow, WalshAB.χ_sq ] ; norm_num
  have hR : autocorrScaled f s a = quadGaussSum (fun x => s * MTuple.deriv f a x) := by
    rw [autocorrScaled_eq_quadGaussSum]
  have hub' : quadGaussSum (fun x => s * MTuple.deriv f a x + s * MTuple.deriv f a 0) ^ 2 ≤ 2 * (Fintype.card F : ℤ) := by
    rw [← h_sq, ← hR]; exact hub
  have := quadGaussSum_sq_value_of_div_ub hcard hodd h_quad hub' h_div
  rw [hR, h_sq]; exact this

/-- **The derivative 4-collision count from the everywhere AB upper bound.**  For an
APN map `f` over `GF(2ⁿ)` (`n` odd) whose derivative forms all have vanishing third
derivative and satisfy the almost-bent upper bound `R(s)² ≤ 2q` for every `s ≠ 0`,
the derivative 4-collision count is `preCount₄ = q³ + 2q²`. -/
theorem preCount4_of_third_deriv_ub {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) (f : F → F) (hf : IsAPN f)
    (a : F) (ha : a ≠ 0)
    (h3 : ∀ s x y z : F,
      (s * MTuple.deriv f a (x + y + z)) + (s * MTuple.deriv f a (x + y))
      + (s * MTuple.deriv f a (x + z)) + (s * MTuple.deriv f a (y + z))
      + (s * MTuple.deriv f a x) + (s * MTuple.deriv f a y) + (s * MTuple.deriv f a z)
      + (s * MTuple.deriv f a 0) = 0)
    (hub : ∀ s : F, s ≠ 0 → autocorrScaled f s a ^ 2 ≤ 2 * (Fintype.card F : ℤ)) :
    (MTuple.preCount 4 f a (fun _ => 1) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 := by
  apply Vanish.Foundations.preCount4_of_value_set f hf a ha
  exact fun s hs => Vanish.Foundations.crossCorr_sq_value_of_third_deriv_ub hcard hodd f a s
    (h3 s) (hub s (Finset.ne_of_mem_erase hs))

/-! ## 3. The true frontier leaf (`k = 2`) and the corrected count -/

/-- **True frontier leaf (`k = 2`, `a = 1`): the almost-bent upper bound.**  For the
Kasami map `x ↦ x^{d 2}` (`d 2 = 13`) over `GF(2ⁿ)` (`n` odd), the derivative
cross-correlation at the shift `a = 1` satisfies the almost-bent upper bound
`R₁(s)² ≤ 2q` for every `s ≠ 0`.

This is the *satisfiable* replacement for the false `kasami_two_derivForm_radical`
(which asserted `radical.card ≤ 2` for all `s`, disproved at `s = 3` over `GF(2⁵)`;
see `KasamiTwoRadicalDisproof.lean`).  Over `GF(2⁵)` the derivative value set is
`R(s) ∈ {0, ±8}`, so `R(s)² ∈ {0, 64} = {0, 2q}`, in particular `R(s)² ≤ 2q`.  It is
the genuine almost-bent (Kasami-1971) datum, isolated here at the single shift
`a = 1` (the general shift is reduced to it by `kasami_two_crossCorr_sq_ub`). -/
theorem kasami_two_crossCorr_sq_ub_one {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (hkn : 2 < n) (hcop : Nat.Coprime 2 n)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4)
    (s : F) (hs : s ≠ 0) :
    autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 ^ 2
      ≤ 2 * (Fintype.card F : ℤ) := by
  -- input (A) divisibility is *green* (the `k = 2` derivative form is quadratic).
  have hf := KasamiAB.kasami_is_apn_pred hcard 2 (by norm_num) hkn hcop hodd (by omega)
  have hdiv := crossCorr_hdiv_of_third_deriv hcard hodd
    (fun x : F => x ^ CollisionAnalysis.d 2) 1
    (fun s x y z => kasami_two_deriv_third_deriv_zero s 1 x y z)
  -- input (B) fourth moment is derived (green) from the Wiener–Khinchin bridge `hWK`.
  have hfourth := kasami_autocorr_fourthMoment_offDiag_of_bridge hcard
    (by norm_num) hkn hcop hodd (by omega) 1 one_ne_zero hWK
  have hval : ((2 : ℤ) ^ ((n + 1) / 2)) ^ 2 = 2 * (Fintype.card F : ℤ) := by
    have he : (n + 1) / 2 * 2 = n + 1 := by obtain ⟨t, ht⟩ := hodd; omega
    rw [← pow_mul, he, hcard, pow_succ]; push_cast; ring
  rcases crossCorr_three_valued_of_div_fourth hcard hodd
      (fun x : F => x ^ CollisionAnalysis.d 2) hf 1 one_ne_zero hdiv hfourth s hs
    with h | h | h
  · rw [h, zero_pow (two_ne_zero), hcard]; positivity
  · rw [h]; exact le_of_eq hval
  · rw [h, neg_sq]; exact le_of_eq hval

/-- **The almost-bent upper bound for every shift (`k = 2`).**  From the `a = 1`
result `kasami_two_crossCorr_sq_ub_one` and the power-map shift invariance
`autocorrScaled_pow_shift` (`R_a(s) = R_1(s·a^N)`), the upper bound `R(s)² ≤ 2q`
holds for every `a ≠ 0`, `s ≠ 0`.  Green modulo the single shared Wiener–Khinchin
bridge core `hWK`. -/
theorem kasami_two_crossCorr_sq_ub {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (hkn : 2 < n) (hcop : Nat.Coprime 2 n)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4)
    (a : F) (s : F) (ha : a ≠ 0) (hs : s ≠ 0) :
    autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s a ^ 2
      ≤ 2 * (Fintype.card F : ℤ) := by
  rw [autocorrScaled_pow_shift (CollisionAnalysis.d 2) a ha s]
  exact kasami_two_crossCorr_sq_ub_one hcard hodd hkn hcop hWK
    (s * a ^ CollisionAnalysis.d 2) (mul_ne_zero hs (pow_ne_zero _ ha))

/-- **The `k = 2` almost-bent 4-collision count (corrected assembly).**  Combines the
green wiring `preCount4_of_third_deriv_ub` with the green third-derivative vanishing
`kasami_two_deriv_third_deriv_zero` and the (now `sorry`-free) upper bound
`kasami_two_crossCorr_sq_ub`.  The whole `k = 2` input-(B) branch is now green modulo
the single shared Wiener–Khinchin bridge core `hWK` (input (A) is fully green). -/
theorem kasami_two_a1_preCount4 {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hkn : 2 < n) (hcop : Nat.Coprime 2 n) (hodd : Odd n)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4)
    (a : F) (ha : a ≠ 0) :
    (MTuple.preCount 4 (fun x : F => x ^ CollisionAnalysis.d 2) a (fun _ => 1) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 :=
  preCount4_of_third_deriv_ub hcard hodd _
    (KasamiAB.kasami_is_apn_pred hcard 2 (by norm_num) hkn hcop hodd (by omega)) a ha
    (fun s x y z => kasami_two_deriv_third_deriv_zero s a x y z)
    (fun s hs => kasami_two_crossCorr_sq_ub hcard hodd hkn hcop hWK a s ha hs)

/-! ## 4. The full `k = 2` value set and multiplicity table (modulo the WK bridge)

For `k = 2` input (A) (the divisibility `hdiv`) is **green** (`crossCorr_hdiv_of_third_deriv`,
since the derivative form is quadratic), so the four-valued value set and the Pless
multiplicity table specialize to the single shared Wiener–Khinchin bridge core `hWK`
(from which input (B), the fourth moment, is green).  These are the direct inputs to the
`vanish_iff_sign_sum` reduction on the m-tuple count path. -/

/-- **The full `k = 2` cross-correlation value set (modulo the WK bridge).**  Every
value `R(s)` at the shift `a = 1` lies in `{q, 0, +2^{(n+1)/2}, -2^{(n+1)/2}}`.
Input (A) is discharged green; only the shared bridge core `hWK` remains. -/
theorem kasami_two_crossCorr_value_set {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (hkn : 2 < n) (hcop : Nat.Coprime 2 n)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4)
    (s : F) :
    autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = (Fintype.card F : ℤ)
    ∨ autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = 0
    ∨ autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = 2 ^ ((n + 1) / 2)
    ∨ autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = -2 ^ ((n + 1) / 2) := by
  have hdiv := crossCorr_hdiv_of_third_deriv hcard hodd
    (fun x : F => x ^ CollisionAnalysis.d 2) 1
    (fun s x y z => kasami_two_deriv_third_deriv_zero s 1 x y z)
  have hfourth := kasami_autocorr_fourthMoment_offDiag_of_bridge hcard
    (by norm_num) hkn hcop hodd (by omega) 1 one_ne_zero hWK
  exact kasami_crossCorr_value_set hcard (by norm_num) hkn hcop hodd (by omega)
    1 one_ne_zero hdiv hfourth s

/-- **The `k = 2` cross-correlation multiplicity table (modulo the WK bridge).**  The
Pless solve of the first and second moments over the nonzero frequencies pins the
signed excess and total support of the two nonzero values `±2^{(n+1)/2}`.  Input (A)
is discharged green; only the shared bridge core `hWK` remains. -/
theorem kasami_two_crossCorr_value_table {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (hkn : 2 < n) (hcop : Nat.Coprime 2 n)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4) :
    (2 : ℤ) ^ ((n + 1) / 2)
        * (((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = 2 ^ ((n + 1) / 2))).card : ℤ)
          - ((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = -2 ^ ((n + 1) / 2))).card : ℤ))
        = -(Fintype.card F : ℤ)
    ∧ ((2 : ℤ) ^ ((n + 1) / 2)) ^ 2
        * (((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = 2 ^ ((n + 1) / 2))).card : ℤ)
          + ((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1 = -2 ^ ((n + 1) / 2))).card : ℤ))
        = (Fintype.card F : ℤ) ^ 2 := by
  have hdiv := crossCorr_hdiv_of_third_deriv hcard hodd
    (fun x : F => x ^ CollisionAnalysis.d 2) 1
    (fun s x y z => kasami_two_deriv_third_deriv_zero s 1 x y z)
  have hfourth := kasami_autocorr_fourthMoment_offDiag_of_bridge hcard
    (by norm_num) hkn hcop hodd (by omega) 1 one_ne_zero hWK
  exact kasami_crossCorr_value_table hcard (by norm_num) hkn hcop hodd (by omega)
    1 one_ne_zero hdiv hfourth

end Vanish.Foundations
