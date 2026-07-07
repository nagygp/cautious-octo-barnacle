import RequestProject.Foundations.KasamiAdditiveEnergyBE3e
import Mathlib

/-!
# Foundations, Layer BE3.3.2 — moments of the second-derivative collision distribution

This module **implements direction (B)**: the second-derivative per-value
multiplicity distribution used to evaluate `∑_{z≠0} derivPairCount(f,a,z)²`.

Recall (BE3.2) `derivPairCount f a z = #{(x,y) : Δf_a x + Δf_a y = z}` is the
second-difference collision count, and (BE3.3.1, `KasamiAdditiveEnergyBE3e.lean`)

```
   16·offDiagEnergy(Im Δf_a) = ∑_{z≠0} derivPairCount(f,a,z)²,
```

so the additive-energy value of input (B) is exactly the **second moment** of the
collision distribution `derivPairCount(f,a,·)`.  Here we compute the lower-order
data of that distribution unconditionally and pin the second moment to the AB
fourth-moment input:

* **The diagonal value** `derivPairCount f a 0 = 2q` (`derivPairCount_zero`).  By
  APN-ness each image value has two preimages, so the diagonal collisions are the
  `4`-to-`1` lift of the `q/2` image values, `4·(q/2) = 2q`.
* **The off-diagonal mass (first moment)**
  `∑_{z≠0} derivPairCount f a z = q² − 2q` (`derivPairCount_sum_offDiag`), the
  `4`-to-`1` lift of `∑_{z≠0} r_S(z) = |S|² − |S|` with `|S| = q/2`.  This is the
  total mass on which the second moment sits.
* **The second moment ⟺ the autocorrelation fourth moment**
  (`derivPairCount_sq_offDiag_iff_fourthMoment`): chaining BE3.3.1 with the
  Fourier route BE3.1/BE3,
  ```
     ∑_{z≠0} derivPairCount² = q³ − 2q²   ⟺   ∑_{s≠0} R(s)⁴ = 2q³.
  ```
  This is the exact statement that *evaluating* `∑ derivPairCount²` is the same as
  the AB additive-energy / fourth-moment input.
* **The evaluation from the AB input**
  (`derivPairCount_sq_offDiag_of_fourthMoment`): feeding the AB autocorrelation
  fourth moment `∑_{s≠0} R(s)⁴ = 2q³` (the per-value multiplicity distribution,
  carried as a named hypothesis matching the project convention) gives
  `∑_{z≠0} derivPairCount² = q³ − 2q²`.

## Scope

The zeroth and first moments are sorry-free and unconditional (APN suffices).  The
second moment is delivered as an explicit equivalence with, and a derivation from,
the AB autocorrelation fourth moment — the genuine deep input (B), which is **not**
implied by APN alone (it fails for APN-but-not-AB functions) and which the project
carries as a named hypothesis rather than an axiom or `sorry`.

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (representation function, additive
energy); Carlet, Ch. 6 (APN/AB functions, second-order derivatives);
Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The diagonal collision value -/

/-
**The diagonal collision value** `derivPairCount f a 0 = 2q`.  By APN-ness each
image value has exactly two preimages, so the `4`-to-`1` lift of the `q/2` image
values (`derivPairCount = 4·reprCount`, `reprCount(S,0) = |S| = q/2`) is `2q`.
-/
theorem derivPairCount_zero (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    derivPairCount f a 0 = 2 * Fintype.card F := by
  convert congr_arg ( fun x : ℕ => 4 * x ) ( Vanish.Foundations.reprCount_zero ( derivImage f a ) ) using 1;
  · exact Eq.symm ( Vanish.Foundations.four_mul_reprCount_eq_derivPairCount f hf a ha 0 );
  · linarith [ Vanish.Foundations.derivImage_card_eq_half n hn hcard f hf a ha ]

/-! ## 2. The off-diagonal mass (first moment) -/

/-
**The off-diagonal collision mass (first moment)**
`∑_{z≠0} derivPairCount f a z = q² − 2q`.  The `4`-to-`1` lift of the
off-diagonal representation mass `∑_{z≠0} r_S(z) = |S|² − |S|`
(`reprCount_sum_offDiag`) with `|S| = q/2`.
-/
theorem derivPairCount_sum_offDiag (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    (∑ z ∈ univ.erase (0 : F), (derivPairCount f a z : ℤ))
      = (Fintype.card F : ℤ) ^ 2 - 2 * (Fintype.card F : ℤ) := by
  convert congr_arg ( fun x : ℕ => ( x : ℤ ) ) ( show ∑ z ∈ Finset.univ.erase 0, derivPairCount f a z = ( Fintype.card F ) ^ 2 - 2 * Fintype.card F from ?_ ) using 1;
  · norm_cast;
  · rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith [ Nat.pow_le_pow_right two_pos hn ];
  · have h_sum : ∑ z ∈ univ.erase 0, derivPairCount f a z = 4 * (derivImage f a).card ^ 2 - 4 * (derivImage f a).card := by
      convert congr_arg ( fun x : ℕ => 4 * x ) ( reprCount_sum_offDiag ( derivImage f a ) ) using 1;
      · rw [ Finset.mul_sum _ _ _, Finset.sum_congr rfl fun x hx => four_mul_reprCount_eq_derivPairCount f hf a ha x ];
      · rw [ Nat.mul_sub_left_distrib ];
    convert h_sum using 1;
    rw [ show Fintype.card F = 2 * #(derivImage f a) by linarith [ derivImage_card_eq_half n hn hcard f hf a ha ] ] ; ring_nf

/-! ## 3. The second moment ⟺ the autocorrelation fourth moment -/

/-
**The second moment of the collision distribution is the AB fourth moment.**
Chaining BE3.3.1 (`additiveEnergy_value_iff_derivPairCount_sq`) with the Fourier
route BE3 (`additiveEnergy_value_iff_fourthMoment`):
`∑_{z≠0} derivPairCount² = q³ − 2q²  ⟺  ∑_{s≠0} R(s)⁴ = 2q³`.
-/
theorem derivPairCount_sq_offDiag_iff_fourthMoment (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    ((∑ z ∈ univ.erase (0 : F), (derivPairCount f a z : ℤ) ^ 2)
        = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2)
      ↔ (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) := by
  convert Vanish.Foundations.additiveEnergy_value_iff_derivPairCount_sq n hn hcard f hf a ha |> Iff.symm |> Iff.trans <| Vanish.Foundations.additiveEnergy_value_iff_fourthMoment f hf a ha using 1

/-! ## 4. The evaluation from the AB input -/

/-- **Evaluating `∑ derivPairCount²` from the AB fourth moment.**  Feeding the AB
autocorrelation fourth moment `∑_{s≠0} R(s)⁴ = 2q³` (the genuine deep input (B),
carried as a named hypothesis) gives the second moment of the collision
distribution `∑_{z≠0} derivPairCount² = q³ − 2q²`. -/
theorem derivPairCount_sq_offDiag_of_fourthMoment (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (hAB : ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (∑ z ∈ univ.erase (0 : F), (derivPairCount f a z : ℤ) ^ 2)
      = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2 :=
  (derivPairCount_sq_offDiag_iff_fourthMoment n hn hcard f hf a ha).mpr hAB

end Vanish.Foundations