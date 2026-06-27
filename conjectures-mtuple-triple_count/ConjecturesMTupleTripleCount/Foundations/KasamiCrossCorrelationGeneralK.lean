import ConjecturesMTupleTripleCount.Foundations.CubeMTupleCount

/-!
# Foundations, Layer 9 — the general-`k` Kasami cross-correlation distribution

This module realizes **Layer 9** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`).  Layers 7–8 settled the `k = 1` (cube/Gold)
case completely, because the cube derivative is `F₂`-affine and its
cross-correlation is a *single* additive-character sum with a two-point support
`{0, a^{-3}}`.  For general `k` the Kasami map `x ↦ x^{d k}` is **not quadratic**,
so the derivative is no longer affine and that single-character-sum collapse
fails.

What *is* recoverable from first principles — directly from the APN /
permutation structure already established for the Kasami map
(`KasamiAB.kasami_bijective`, `KasamiAB.kasami_is_apn_pred`) — is the
**structural and moment data** of the cross-correlation
`R(s) = autocorrScaled f s a = ∑_x χ(s·Δf_a x)`.  This is the *engine* of the
classical Kasami weight-distribution computation (the Pless-power-moment method
flagged in Layers 6–7 of the roadmap), and it is what Layers 10–11 consume.

## The 2-to-1 structural reduction

Because the derivative `Δf_a` of an APN map is exactly two-to-one onto its image
(`MTuple.deriv_fiber_card`), the cross-correlation is twice a character sum over
the image set:

* `crossCorr_eq_two_mul_image` —
  `R(s) = 2 · ∑_{v ∈ Im Δf_a} χ(s·v)`;
* `crossCorr_even` — in particular `R(s)` is always even.

So `R` is (twice) the Fourier transform of the indicator of the derivative
image — the precise object whose value/multiplicity table is the Kasami
cross-correlation spectrum.

## The moments of the cross-correlation distribution

The first two power moments are pinned down unconditionally:

* `crossCorr_first_moment` — `∑_s R(s) = 0` (for a *permutation* `f` and
  `a ≠ 0`: the derivative never vanishes, so the trivial-frequency contribution
  cancels);
* `crossCorr_first_moment_nonzero` — `∑_{s ≠ 0} R(s) = −q`;
* `crossCorr_second_moment` — `∑_s R(s)² = 2·q²` (for an *APN* `f` and `a ≠ 0`:
  the two-to-one structure gives `#{(x,y) : Δf_a x = Δf_a y} = 2q`);
* `crossCorr_second_moment_nonzero` — `∑_{s ≠ 0} R(s)² = q²`.

These are exactly the Pless power moments of the cross-correlation distribution.

## Kasami specializations

Feeding `KasamiAB.kasami_bijective` / `KasamiAB.kasami_is_apn_pred` to the general
lemmas gives the same structural reduction and moments for the general-`k` Kasami
map `x ↦ x^{d k}`:

* `kasami_crossCorr_eq_two_mul_image`, `kasami_crossCorr_even`;
* `kasami_crossCorr_first_moment`, `kasami_crossCorr_first_moment_nonzero`;
* `kasami_crossCorr_second_moment`, `kasami_crossCorr_second_moment_nonzero`.

## What remains (the closed-form value/multiplicity table)

The *closed-form* three- or five-valued Kasami cross-correlation spectrum (the
exact values `R(s)` takes and how often) is the deep Kasami-1971 / Dobbertin /
Canteaut–Charpin–Dobbertin computation; it needs the fourth moment and weight
divisibility beyond the first-principles inputs collected here.  The moment
engine of this module is the data that the higher layers (10–11) combine — via
the Pless power-moment balance — to discharge `Vanish` for general `k`.

## Sources

Kasami (1971); Dobbertin (1999); Canteaut–Charpin–Dobbertin (SIAM 2000);
Chabaud–Vaudenay §3; MacWilliams–Sloane (Pless power moments).

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): each general lemma has a single
responsibility (a structural reduction or one power moment) and an
intention-revealing name; the Kasami results are thin specializations (DRY).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The 2-to-1 structural reduction -/

/-
**The cross-correlation is twice a character sum over the derivative image.**
For an APN map `f` and `a ≠ 0`, the derivative `Δf_a` is exactly two-to-one onto
its image, so `R(s) = ∑_x χ(s·Δf_a x) = 2·∑_{v ∈ Im Δf_a} χ(s·v)`.
-/
theorem crossCorr_eq_two_mul_image (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (s : F) :
    autocorrScaled f s a = 2 * ∑ v ∈ MTuple.derivImage f a, χ (s * v) := by
  have h_sum : ∑ x : F, χ (s * MTuple.deriv f a x) = ∑ v ∈ MTuple.derivImage f a, ∑ x ∈ Finset.univ.filter (fun x => MTuple.deriv f a x = v), χ (s * v) := by
    rw [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ⟨ MTuple.deriv f a x, x ⟩ ) _ _ _ _ <;> simp +decide;
    · exact fun x => Finset.mem_image_of_mem _ ( Finset.mem_univ x );
    · grind;
  simp_all +decide [ Finset.mul_sum _ _ _ ];
  convert h_sum using 1;
  exact Finset.sum_congr rfl fun x hx => by rw [ show ( Finset.card ( Finset.filter ( fun y => MTuple.deriv f a y = x ) Finset.univ ) : ℕ ) = 2 from by simpa using MTuple.deriv_fiber_card f hf a ha x hx ] ; norm_cast;

/-
**The cross-correlation is even.**  Immediate from the two-to-one reduction.
-/
theorem crossCorr_even (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) (s : F) :
    (2 : ℤ) ∣ autocorrScaled f s a := by
  rw [ crossCorr_eq_two_mul_image f hf a ha s ] ; norm_num [ ← even_iff_two_dvd, parity_simps ]

/-! ## First moment -/

/-
**First moment.**  For a *permutation* `f` and `a ≠ 0`, the derivative
`Δf_a x = f(x+a)+f x` never vanishes (`f(x+a) = f x ⟹ x = x+a ⟹ a = 0`), so
`∑_s R(s) = ∑_x q·𝟙(Δf_a x = 0) = 0`.
-/
theorem crossCorr_first_moment (f : F → F) (hf : Function.Bijective f)
    (a : F) (ha : a ≠ 0) :
    ∑ s : F, autocorrScaled f s a = 0 := by
  convert WalshAB.χ_sum_dual ( f ( a ) - f 0 ) using 1;
  · rw [ Finset.sum_congr rfl fun x hx => MTuple.autocorrScaled_eq f x a ];
    rw [ Finset.sum_comm ];
    rw [ Finset.sum_eq_single 0 ] <;> simp +decide [ MTuple.deriv ];
    · simp +decide [ sub_eq_add_neg, CharTwo.neg_eq ];
    · intro b hb; have := χ_sum_dual ( f ( b + a ) + f b ) ; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      have := Fintype.bijective_iff_injective_and_card f; simp_all +decide [ Function.Injective ] ;
      grind +splitImp;
  · rw [ if_neg ( sub_ne_zero_of_ne <| by intro h; exact ha <| by simpa [ sub_eq_zero ] using hf.injective h ) ]

/-
**First moment over nonzero frequencies.**  Since `R(0) = q`, the first
moment identity gives `∑_{s ≠ 0} R(s) = −q`.
-/
theorem crossCorr_first_moment_nonzero (f : F → F) (hf : Function.Bijective f)
    (a : F) (ha : a ≠ 0) :
    ∑ s ∈ univ.erase (0 : F), autocorrScaled f s a = -(Fintype.card F : ℤ) := by
  convert congr_arg ( fun x : ℤ => x - Fintype.card F ) ( Vanish.Foundations.crossCorr_first_moment f hf a ha ) using 1;
  · rw [ Finset.sum_erase_eq_sub ( Finset.mem_univ 0 ), MTuple.autocorrScaled_zero ];
  · grobner

/-! ## Second moment -/

/-
**Second moment.**  For an *APN* map `f` and `a ≠ 0`,
`∑_s R(s)² = q·#{(x,y) : Δf_a x = Δf_a y}`, and the two-to-one structure
(`MTuple.deriv_fiber_card`) gives `#{(x,y) : Δf_a x = Δf_a y} = 2q`, hence
`∑_s R(s)² = 2·q²`.
-/
theorem crossCorr_second_moment (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    ∑ s : F, (autocorrScaled f s a) ^ 2 = 2 * (Fintype.card F : ℤ) ^ 2 := by
  -- By definition of autocorrelation, we can write $R(s)^2$ as a double sum over $x$ and $y$.
  have h_double_sum : ∀ s : F, (autocorrScaled f s a) ^ 2 = ∑ x : F, ∑ y : F, χ (s * (MTuple.deriv f a x + MTuple.deriv f a y)) := by
    intro s
    rw [MTuple.autocorrScaled_eq];
    simp +decide only [pow_two, Finset.mul_sum _ _ _, sum_mul, mul_add, χ_mul];
    exact Finset.sum_comm;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ s : F, ∑ x : F, ∑ y : F, χ (s * (MTuple.deriv f a x + MTuple.deriv f a y)) = ∑ x : F, ∑ y : F, ∑ s : F, χ (s * (MTuple.deriv f a x + MTuple.deriv f a y)) := by
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  -- By definition of $χ$, we know that $\sum_{s} χ(s * (deriv f a x + deriv f a y))$ is zero unless $deriv f a x + deriv f a y = 0$.
  have h_sum_zero : ∀ x y : F, ∑ s : F, χ (s * (MTuple.deriv f a x + MTuple.deriv f a y)) = if MTuple.deriv f a x + MTuple.deriv f a y = 0 then (Fintype.card F : ℤ) else 0 := by
    intro x y;
    convert WalshAB.χ_sum_dual ( MTuple.deriv f a x + MTuple.deriv f a y ) using 1;
  -- By definition of $MTuple.deriv$, we know that $MTuple.deriv f a x + MTuple.deriv f a y = 0$ if and only if $MTuple.deriv f a x = MTuple.deriv f a y$.
  have h_eq : ∀ x y : F, MTuple.deriv f a x + MTuple.deriv f a y = 0 ↔ MTuple.deriv f a x = MTuple.deriv f a y := by
    grind +suggestions;
  -- By definition of $MTuple.deriv$, we know that $MTuple.deriv f a x = MTuple.deriv f a y$ if and only if $x$ and $y$ are in the same fiber of $MTuple.deriv f a$.
  have h_fiber : ∀ x : F, ∑ y : F, (if MTuple.deriv f a x = MTuple.deriv f a y then 1 else 0) = 2 := by
    intro x
    have h_fiber_card : (Finset.univ.filter (fun y => MTuple.deriv f a y = MTuple.deriv f a x)).card = 2 := by
      convert MTuple.deriv_fiber_card f hf a ha ( MTuple.deriv f a x ) ( Finset.mem_image_of_mem _ ( Finset.mem_univ x ) ) using 1;
    simp_all +decide [ eq_comm ];
  simp_all +decide [ Finset.sum_ite ];
  ring

/-
**Second moment over nonzero frequencies.**  Since `R(0)² = q²`, the second
moment identity gives `∑_{s ≠ 0} R(s)² = q²`.
-/
theorem crossCorr_second_moment_nonzero (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) :
    ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  convert congr_arg ( fun x : ℤ => x - ( autocorrScaled f 0 a ) ^ 2 ) ( crossCorr_second_moment f hf a ha ) using 1;
  · exact eq_sub_of_add_eq <| Finset.sum_erase_add _ _ <| Finset.mem_univ _;
  · rw [ MTuple.autocorrScaled_zero ] ; ring

/-! ## Kasami specializations -/

variable {n k : ℕ}

/-- **Kasami cross-correlation: two-to-one reduction.** -/
theorem kasami_crossCorr_eq_two_mul_image (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) (s : F) :
    autocorrScaled (fun x : F => x ^ d k) s a
      = 2 * ∑ v ∈ MTuple.derivImage (fun x : F => x ^ d k) a, χ (s * v) :=
  crossCorr_eq_two_mul_image _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha s

/-- **Kasami cross-correlation is even.** -/
theorem kasami_crossCorr_even (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) (s : F) :
    (2 : ℤ) ∣ autocorrScaled (fun x : F => x ^ d k) s a :=
  crossCorr_even _ (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha s

/-- **Kasami cross-correlation: first moment** `∑_s R(s) = 0`. -/
theorem kasami_crossCorr_first_moment (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) :
    ∑ s : F, autocorrScaled (fun x : F => x ^ d k) s a = 0 :=
  crossCorr_first_moment _ (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn) a ha

/-- **Kasami cross-correlation: first moment over nonzero frequencies**
`∑_{s ≠ 0} R(s) = −q`. -/
theorem kasami_crossCorr_first_moment_nonzero (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) :
    ∑ s ∈ univ.erase (0 : F), autocorrScaled (fun x : F => x ^ d k) s a
      = -(Fintype.card F : ℤ) :=
  crossCorr_first_moment_nonzero _
    (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn) a ha

/-- **Kasami cross-correlation: second moment** `∑_s R(s)² = 2·q²`. -/
theorem kasami_crossCorr_second_moment (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) :
    ∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 2
      = 2 * (Fintype.card F : ℤ) ^ 2 :=
  crossCorr_second_moment _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha

/-- **Kasami cross-correlation: second moment over nonzero frequencies**
`∑_{s ≠ 0} R(s)² = q²`. -/
theorem kasami_crossCorr_second_moment_nonzero (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) :
    ∑ s ∈ univ.erase (0 : F), (autocorrScaled (fun x : F => x ^ d k) s a) ^ 2
      = (Fintype.card F : ℤ) ^ 2 :=
  crossCorr_second_moment_nonzero _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha

end Vanish.Foundations