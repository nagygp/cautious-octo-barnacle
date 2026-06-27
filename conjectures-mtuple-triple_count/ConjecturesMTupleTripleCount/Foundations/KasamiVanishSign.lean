import ConjecturesMTupleTripleCount.Foundations.KasamiCrossCorrelationValueSet
import ConjecturesMTupleTripleCount.Foundations.SpectralSum

/-!
# Foundations, Layer 12 — the explicit `Vanish` discharge as a sign-correlation

This module realizes the **discharge step** of Layer 10 of the "Kasami is Vanish"
roadmap (`Docs/VanishFutureDirections.md`): turning the *value set* of the Kasami
cross-correlation (the previous layer's
`crossCorr_three_valued_of_div_fourth` / `kasami_crossCorr_value_set`) into an
**explicit, elementary characterization of the admissible coefficient tuples** —
the general-`k` analogue of the cube/`k = 1` characterization
`cube_admissible_iff` (`Foundations/KasamiCrossCorrelation.lean`).

## The reduction

For `s ≠ 0` the cross-correlation `R(s) = autocorrScaled f s a` takes the three
values `{0, +A, -A}` with `A = 2^{(n+1)/2}` (Layer 10's value set).  Writing
`R(s) = A·σ(s)` with the integer **sign** `σ(s) ∈ {-1, 0, 1}`
(`crossCorrSign`), a coefficient tuple `c : Fin m → F` with all `c i ≠ 0` has,
for every `t ≠ 0`,

  `∏_i R(t·c_i) = Aᵐ · ∏_i σ(t·c_i)` ,

since each `t·c_i ≠ 0`.  Summing over `t ≠ 0` and dividing by `Aᵐ ≠ 0`:

  `Vanish m f a c  ⟺  ∑_{t≠0} ∏_i σ(t·c_i) = 0`   (`vanish_iff_sign_sum`).

So the *admissible* class is **exactly** the set of nonzero coefficient tuples
whose **triple (m-fold) sign correlation vanishes**.  For `m = 3` this is the
general-`k` `cube_admissible_iff` (`kasami_admissible_iff_sign_sum`).

## Why this is genuinely subtle (unlike `k = 1`)

For `k = 1` the cross-correlation is supported on the two-point set `{0, a^{-3}}`,
so `σ` is a single Kronecker spike and the sign correlation vanishes precisely
when the `c_i` are **not all equal** (`cube_admissible_iff`).  For general `k` the
sign `σ` is the genuinely spread-out three-valued AB sign function, and the sign
correlation is a non-trivial weighted count over `t`.  In particular a tuple with
a repeated coefficient, `c = (c, c, c')`, has

  `∑_{t≠0} σ(t·c)² · σ(t·c')`

(`crossCorrSign_sq`: `σ(s)² = [R(s) ≠ 0]`), i.e. the `σ(t·c')` values summed over
the *support* of `s ↦ R(t·c)`, which has **no reason to vanish** — so the
admissible class is *not* simply "not all equal".  This matches the numerical
observation recorded in the roadmap: `(c, c, c')` can already fail for `k ≥ 2`.

This module therefore does **not** claim an unconditional admissible class; it
provides the exact reduction (conditional on the still-open scalar inputs **(A)**
divisibility and **(B)** the fourth moment that pin down the value set), isolating
the remaining work to evaluating the explicit sign-correlation sum.

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM 2000); Carlet, *Boolean
Functions for Cryptography and Coding Theory* (2021), Ch. 6; Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The integer sign of a three-valued cross-correlation -/

/-- The integer **sign** of the cross-correlation at frequency `s`: `+1` if
`R(s) = 2^e`, `-1` if `R(s) = -2^e`, and `0` otherwise.  On the support of a
`{0, ±2^e}`-valued `R` this gives the decomposition `R(s) = 2^e · σ(s)`
(`crossCorr_eq_pow_mul_sign`). -/
noncomputable def crossCorrSignDef_placeholder : Unit := ()

noncomputable def crossCorrSign (f : F → F) (a : F) (e : ℕ) (s : F) : ℤ :=
  if autocorrScaled f s a = 2 ^ e then 1
  else if autocorrScaled f s a = -2 ^ e then -1
  else 0

/-
On a three-valued frequency `R(s) ∈ {0, 2^e, -2^e}`, the cross-correlation
factors as `R(s) = 2^e · σ(s)`.
-/
omit [DecidableEq F] in
theorem crossCorr_eq_pow_mul_sign (f : F → F) (a : F) (e : ℕ) (s : F)
    (h : autocorrScaled f s a = 0
        ∨ autocorrScaled f s a = 2 ^ e
        ∨ autocorrScaled f s a = -2 ^ e) :
    autocorrScaled f s a = 2 ^ e * crossCorrSign f a e s := by
  cases' h with h h <;> simp_all +decide [ crossCorrSign ];
  grind

/-
The square of the sign is the indicator of the support `R(s) ≠ 0` on a
three-valued frequency: `σ(s)² = 1` if `R(s) = ±2^e`, else `0`.  This exposes why
a repeated-coefficient tuple `(c, c, c')` need not be admissible.
-/
omit [DecidableEq F] in
theorem crossCorrSign_sq (f : F → F) (a : F) (e : ℕ) (s : F) :
    (crossCorrSign f a e s) ^ 2
      = if autocorrScaled f s a = 2 ^ e ∨ autocorrScaled f s a = -2 ^ e
        then 1 else 0 := by
  unfold crossCorrSign; aesop;

/-! ## The explicit `Vanish` reduction (abstract three-valued form) -/

/-
**The sign-correlation reduction of `Vanish`.**  If the cross-correlation is
three-valued off the trivial frequency (`R(s) ∈ {0, ±2^e}` for `s ≠ 0`) and every
coefficient `c i` is nonzero, then `Vanish m f a c` holds **iff** the `m`-fold
sign correlation `∑_{t≠0} ∏_i σ(t·c_i)` vanishes.  This makes the admissible
class explicit and elementary, conditional only on the value set.
-/
theorem vanish_iff_sign_sum {m : ℕ} (f : F → F) (a : F) (e : ℕ)
    (c : Fin m → F) (hc : ∀ i, c i ≠ 0)
    (hvals : ∀ s : F, s ≠ 0 →
      autocorrScaled f s a = 0
        ∨ autocorrScaled f s a = 2 ^ e
        ∨ autocorrScaled f s a = -2 ^ e) :
    Vanish m f a c
      ↔ ∑ t ∈ univ.erase (0 : F), ∏ i : Fin m, crossCorrSign f a e (t * c i) = 0 := by
  -- By definition of crossCorrSign, we can rewrite the product as the product of crossCorrSign terms multiplied by (2^e)^m.
  have h_prod : ∀ t ∈ univ.erase 0, ∏ i, autocorrScaled f (t * c i) a = (2 ^ e) ^ m * ∏ i, crossCorrSign f a e (t * c i) := by
    intro t ht;
    rw [ ← Fin.prod_const ];
    rw [ ← Finset.prod_mul_distrib ] ; exact Finset.prod_congr rfl fun i _ => by rw [ crossCorr_eq_pow_mul_sign _ _ _ _ ( hvals _ ( mul_ne_zero ( Finset.ne_of_mem_erase ht ) ( hc i ) ) ) ] ;
  unfold Vanish;
  rw [ Finset.sum_congr rfl h_prod, ← Finset.mul_sum _ _ _, mul_eq_zero ] ; norm_num

/-! ## Kasami specialization: the explicit admissible class -/

variable {n k : ℕ}

/-
**The general-`k` Kasami `Vanish` discharge as a sign correlation.**  For the
Kasami map `x ↦ x^{d k}` over `GF(2ⁿ)` (`n` odd, `1 ≤ k < n`, `gcd(k,n)=1`), given
the two classical scalar inputs **(A)** divisibility and **(B)** the fourth moment
that pin down the value set, and nonzero coefficients `c`, the nonzero-frequency
spectral sum vanishes **iff** the `m`-fold sign correlation vanishes.
-/
theorem kasami_vanish_iff_sign_sum {m : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin m → F) (hc : ∀ i, c i ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    Vanish m (fun x : F => x ^ d k) a c
      ↔ ∑ t ∈ univ.erase (0 : F),
          ∏ i : Fin m, crossCorrSign (fun x : F => x ^ d k) a ((n + 1) / 2) (t * c i)
        = 0 := by
  apply vanish_iff_sign_sum;
  · exact hc;
  · convert crossCorr_three_valued_of_div_fourth _ _ _ _ _ _ _ _ using 1;
    all_goals try assumption;
    exact KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn

/-
**The explicit general-`k` admissible-triple characterization.**  The
general-`k` analogue of `cube_admissible_iff`: under the value-set inputs, a
nonzero coefficient triple is admissible (`imgCount 3 = 2^{2n-3}`) **iff** its
three-fold sign correlation vanishes.
-/
theorem kasami_admissible_iff_sign_sum (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F) (hc : ∀ i, c i ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    AdmissibleTriple n (fun x : F => x ^ d k) a c
      ↔ ∑ t ∈ univ.erase (0 : F),
          ∏ i : Fin 3, crossCorrSign (fun x : F => x ^ d k) a ((n + 1) / 2) (t * c i)
        = 0 := by
  convert Vanish.Foundations.kasami_vanish_iff_sign_sum hcard hk hkn hcop hnodd ( by linarith ) a ha c hc hdiv hfourth using 1;
  apply Vanish.Foundations.kasami_admissibleTriple_iff_vanish hcard hk hkn hcop hnodd hn a ha c

end Vanish.Foundations