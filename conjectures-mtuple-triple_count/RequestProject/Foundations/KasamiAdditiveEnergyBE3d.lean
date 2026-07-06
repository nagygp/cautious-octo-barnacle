import RequestProject.Foundations.ABSpectrum
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# Foundations, Layer BE3.3.0′ — moments of the autocorrelation from the AB direct spectrum

This module is a companion to `KasamiAdditiveEnergyBE3c.lean` for the open core
BE3.3 of `Docs/VanishFutureDirections.md` §8.3.  Where BE3c re-keyed the second
Parseval bridge through the **differential** spectrum (the APN image data), this
module derives the same autocorrelation second moment **purely from the
three-valued AB *direct* (Walsh) spectrum** — the object the Kasami / AB property
controls (`IsAB`) — exactly the route requested for input (B): *formalize the
Kasami AB property (3-valued direct spectrum) and derive the energy value from
it.*

## The mathematical content

For an AB permutation `f` on `GF(2ⁿ)` the off-axis power spectrum is two-valued,
`W(a,b)² ∈ {0, 2^{n+1}}` for `a ≠ 0` (`IsAB`), and the axis term vanishes,
`W(0,b) = 0` for `b ≠ 0` (`walsh_a_zero_perm`).  Two elementary moment facts then
pin the fourth moment of the **direct** spectrum in the linear-frequency
direction:

* **Dual Parseval** (`walsh_sq_sum_a`): `∑_a W(a,b)² = q²` for every `b`.  (From
  `W(a,b)² = ∑_u χ(a·u)·R_b(u)` and orthogonality `∑_a χ(a·u) = q·[u=0]`, leaving
  `q·R_b(0) = q·q`.)
* **AB squaring**: since `W(a,b)² ∈ {0, 2^{n+1}}` for every `a` (the `a = 0` term
  vanishes for `b ≠ 0`), `W(a,b)⁴ = 2^{n+1}·W(a,b)²` pointwise.

Summing gives the **AB direct-spectrum fourth moment**

  `∑_a W(a,b)⁴ = 2^{n+1}·q² = 2·q³`   (`walsh_fourth_sum_a_ab`),

and feeding this into the project's Wiener–Khinchin bridge
`walsh_fourth_sum_a : ∑_a W(a,b)⁴ = q·∑_u R_b(u)²` yields the autocorrelation
second moment

  `∑_u R_b(u)² = 2·q²`   (`autocorr_secondMoment_b_ab`),

derived entirely from the 3-valued AB property (no APN/differential input).  The
Kasami specializations `kasami_walsh_fourth_sum_a` and
`kasami_autocorr_secondMoment_b` instantiate these at the Kasami power map via
`KasamiAB.kasami_is_ab` / `KasamiAB.kasami_bijective`.

## What is established (sorry-free)

* `walsh_sq_sum_a` — dual Parseval `∑_a W(a,b)² = q²` (any permutation, any `b`).
* `walsh_fourth_sum_a_ab` — AB direct-spectrum fourth moment `∑_a W(a,b)⁴ = 2q³`.
* `autocorr_secondMoment_b_ab` — `∑_u R_b(u)² = 2q²` from the AB spectrum.
* `kasami_walsh_fourth_sum_a`, `kasami_autocorr_secondMoment_b` — the Kasami
  specializations.

## Scope

This layer is sorry-free and project-internal (built on `walsh_sq_eq_autocorr_sum`,
`walsh_fourth_sum_a`, `IsAB`, `walsh_a_zero_perm`); it needs no theory absent from
Mathlib.  The genuinely open content of BE3.3 — the autocorrelation **fourth**
moment `∑_s R(s)⁴ = 2q³` (the additive energy, needing the second-derivative AB
multiplicities) — remains the deep core, deliberately neither axiomatized nor
`sorry`-ed.

## Sources

Chabaud–Vaudenay §3 (the moment method `∑W² = q²`, `∑W⁴ = 2q³`); Carlet, Ch. 6;
Tao–Vu, §4.1.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. Dual Parseval in the linear-frequency direction -/

/-
**Dual Parseval.**  Summing the power spectrum over the linear frequency `a`
at a fixed multiplier `b` gives `q²`:

  `∑_a W(a,b)² = q²`.

Proof: expand `W(a,b)² = ∑_u χ(a·u)·R_b(u)` (`walsh_sq_eq_autocorr_sum`), swap
the order of summation, and use `∑_a χ(a·u) = q·[u = 0]` (`χ_sum_dual`), leaving
`q·R_b(0)`; finally `R_b(0) = ∑_x χ(b·0) = q`.
-/
theorem walsh_sq_sum_a (f : F → F) (b : F) :
    ∑ a : F, walsh f a b ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  rw [ Finset.sum_congr rfl fun a _ => WalshAB.walsh_sq_eq_autocorr_sum f a b ];
  -- By the properties of the characters and the orthogonality relations, we can simplify the sum.
  have h_simp : ∑ u, (∑ a, χ (a * u)) * autocorrScaled f b u = ∑ u, if u = 0 then (Fintype.card F : ℤ) * autocorrScaled f b u else 0 := by
    refine' Finset.sum_congr rfl fun u hu => _;
    convert congr_arg ( · * autocorrScaled f b u ) ( χ_sum_dual u ) using 1;
    split_ifs <;> ring;
  convert h_simp using 1;
  · rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_mul _ _ _ ];
  · simp +decide [ autocorrScaled ];
    simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
    simp +decide [ sq, χ ]

/-! ## 2. The AB direct-spectrum fourth moment -/

/-
**AB direct-spectrum fourth moment.**  For an AB permutation `f` and `b ≠ 0`,

  `∑_a W(a,b)⁴ = 2·q³`.

Pointwise `W(a,b)⁴ = 2^{n+1}·W(a,b)²` (using `W(a,b)² ∈ {0, 2^{n+1}}` for `a ≠ 0`
and `W(0,b) = 0`), so the sum is `2^{n+1}·∑_a W(a,b)² = 2^{n+1}·q² = 2·q³`.
-/
theorem walsh_fourth_sum_a_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f) (b : F)
    (hb : b ≠ 0) :
    ∑ a : F, walsh f a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3 := by
  convert congr_arg ( fun x : ℤ => ( 2 ^ ( n + 1 ) : ℤ ) * x ) ( Vanish.Foundations.walsh_sq_sum_a f b ) using 1;
  · rw [ Finset.mul_sum _ _ _ ] ; congr ; ext a ; by_cases ha : a = 0 <;> simp_all +decide [ IsAB ]
    · rw [ WalshAB.walsh_a_zero_perm ] <;> simp +decide [ * ];
    · cases hAB a ha b <;> simp_all +decide [ pow_succ, mul_assoc ];
  · norm_cast ; rw [ hcard ] ; ring

/-! ## 3. The autocorrelation second moment from the AB spectrum -/

/-
**Autocorrelation second moment from the AB direct spectrum.**  For an AB
permutation `f` and `b ≠ 0`,

  `∑_u R_b(u)² = 2·q²`,

obtained by feeding the AB direct-spectrum fourth moment `∑_a W(a,b)⁴ = 2q³` into
the Wiener–Khinchin bridge `∑_a W(a,b)⁴ = q·∑_u R_b(u)²` (`walsh_fourth_sum_a`)
and cancelling the factor `q`.
-/
theorem autocorr_secondMoment_b_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f) (b : F)
    (hb : b ≠ 0) :
    ∑ u : F, (autocorrScaled f b u) ^ 2 = 2 * (Fintype.card F : ℤ) ^ 2 := by
  have h1 := walsh_fourth_sum_a f b;
  exact mul_left_cancel₀ ( Nat.cast_ne_zero.mpr ( Fintype.card_ne_zero ) ) ( by linarith [ walsh_fourth_sum_a_ab hcard hf hAB b hb ] )

/-! ## 4. The Kasami specializations -/

/-
**Kasami AB direct-spectrum fourth moment.**  For the Kasami power map on
`GF(2ⁿ)` (`n` odd, `1 ≤ k < n`, `gcd(k,n) = 1`) and `b ≠ 0`,
`∑_a W(a,b)⁴ = 2q³`.
-/
theorem kasami_walsh_fourth_sum_a {n k : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (b : F) (hb : b ≠ 0) :
    ∑ a : F, walsh (fun x : F => x ^ d k) a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3 := by
  apply_rules [walsh_fourth_sum_a_ab];
  · apply KasamiAB.kasami_bijective hcard k hk hcop hnodd (by omega);
  · apply KasamiAB.kasami_is_ab hcard k hk hkn hcop hnodd (by omega)

/-
**Kasami autocorrelation second moment.**  For the Kasami power map on
`GF(2ⁿ)` (`n` odd, `1 ≤ k < n`, `gcd(k,n) = 1`) and `b ≠ 0`,
`∑_u R_b(u)² = 2q²`.
-/
theorem kasami_autocorr_secondMoment_b {n k : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (b : F) (hb : b ≠ 0) :
    ∑ u : F, (autocorrScaled (fun x : F => x ^ d k) b u) ^ 2
      = 2 * (Fintype.card F : ℤ) ^ 2 := by
  convert KasamiAB.kasami_is_ab hcard k hk hkn hcop hnodd ( by omega ) |> fun hAB => Vanish.Foundations.autocorr_secondMoment_b_ab hcard ( KasamiAB.kasami_bijective hcard k hk hcop hnodd ( by omega ) ) hAB b hb using 1

end Vanish.Foundations