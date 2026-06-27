import ConjecturesMTupleTripleCount.Foundations.KasamiWeightEnumerator
import Mathlib

/-!
# Foundations, Layer A4 — MacWilliams identity / Pless power moments ⟹ input (B)

This module transcribes the **mechanism** of **Layer A4** of the value-set
dependency chain in `Docs/VanishFutureDirections.md` §6: the *Pless power-moment*
engine that expresses the open scalar input **(B)** — the nonzero-frequency
fourth moment `∑_{s≠0} R(s)⁴ = 2·q³` (the hypothesis `hfourth` of
`kasami_crossCorr_value_set`) — as a single, concrete *collision count*, and
restates it on the **dual Kasami code weight distribution** through the Layer A3
Delsarte bridge.

## The Pless power-moment engine

`crossCorr_power_moment` (Layer 10) already gives the *full*-frequency moment
`∑_s R(s)^m = q · preCount m f a 1` as the `c ≡ 1` case of Fourier inversion.
Splitting off the trivial frequency `R(0) = q` gives the **nonzero-frequency
Pless power moment**
```
  ∑_{s≠0} R(s)^m = q · preCount m f a 1 − qᵐ          (crossCorr_powerMoment_nonzero)
```
where `preCount m f a 1 = #{x : Fin m → F | ∑ᵢ Δf_a(xᵢ) = 0}` is the
**m-collision count** of the derivative.  At `m = 4` this turns **(B)** into a
*single equality of integers* about the additive structure of `Im Δf_a`:
```
  (∑_{s≠0} R(s)⁴ = 2·q³)  ↔  (preCount 4 f a 1 = q³ + 2·q²)
```
(`fourthMoment_eq_iff_collisionCount`) — exactly the "derivative 4-collision
count `= q³ + 2q²`" reformulation flagged in §6.

## The weight-enumerator (MacWilliams) form

Through the Layer A3 Delsarte bridge `R(s) = q − 2·w(s)`
(`two_mul_codeWeight_eq`), input **(B)** is *verbatim* the **fourth Pless power
moment of the dual Kasami code weight distribution**
```
  ∑_{s≠0} (q − 2·w(s))⁴ = 2·q³                         (fourthMoment_codeWeight_form)
```
i.e. the MacWilliams transform reads `∑_{s≠0} R(s)⁴` off the weights `w(s)`.
This is the precise sense in which "the MacWilliams identity expresses the fourth
moment through the weights" — the algebra is supplied here; the only remaining
gap is the *number* `2·q³` itself.

## Scope and the Mathlib gap

What this module supplies sorry-free is the **moment ↔ collision-count ↔
weight-distribution dictionary** (the Pless power-moment formalism) that isolates
input **(B)** to a single scalar fact.  The *value* of that scalar — equivalently
the derivative 4-collision count `q³ + 2q²`, or the fourth Pless power moment of
the (low-weight, hence in principle computable) *primal* Kasami/BCH code —
requires the MacWilliams identity together with the cyclic-code / BCH machinery
that is **not present in Mathlib** (the documented Layer A3/A4 gap).  It is
deliberately *not* axiomatized: input **(B)** remains the hypothesis `hfourth`,
now exposed in three equivalent forms.

## Sources

MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 5 (Pless power
moments), Ch. 7–8 (weight enumerators); Carlet, Ch. 6; Kasami (1971).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The nonzero-frequency Pless power moment (the engine) -/

/-- **The nonzero-frequency Pless power moment.**  For any `f` and `a`, splitting
the trivial frequency `R(0) = q` off the full power moment
`∑_s R(s)^m = q · preCount m f a 1` gives
`∑_{s≠0} R(s)^m = q · preCount m f a 1 − qᵐ`, where
`preCount m f a 1 = #{x : Fin m → F | ∑ᵢ Δf_a(xᵢ) = 0}` is the derivative
`m`-collision count. -/
theorem crossCorr_powerMoment_nonzero (m : ℕ) (f : F → F) (a : F) :
    ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ m
      = (Fintype.card F : ℤ) * (preCount m f a (fun _ => 1) : ℤ)
          - (Fintype.card F : ℤ) ^ m := by
  have hfull := crossCorr_power_moment m f a
  have hsplit : ∑ s : F, (autocorrScaled f s a) ^ m
      = (autocorrScaled f 0 a) ^ m
        + ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ m := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]; ring
  rw [MTuple.autocorrScaled_zero] at hsplit
  rw [hfull] at hsplit
  linarith [hsplit]

/-- **Fourth Pless power moment over nonzero frequencies.**
`∑_{s≠0} R(s)⁴ = q · preCount 4 f a 1 − q⁴`. -/
theorem crossCorr_fourthMoment_nonzero (f : F → F) (a : F) :
    ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
      = (Fintype.card F : ℤ) * (preCount 4 f a (fun _ => 1) : ℤ)
          - (Fintype.card F : ℤ) ^ 4 :=
  crossCorr_powerMoment_nonzero 4 f a

/-! ## Input (B) as a collision count -/

/-- **Input (B) ⟺ the derivative 4-collision count.**  The nonzero-frequency
fourth moment is `2·q³` **iff** the derivative 4-collision count is `q³ + 2q²`:
```
  (∑_{s≠0} R(s)⁴ = 2·q³)  ↔  (preCount 4 f a 1 = q³ + 2·q²) .
```
This is the reformulation of input **(B)** flagged in `VanishFutureDirections.md`
§6. -/
theorem fourthMoment_eq_iff_collisionCount (f : F → F) (a : F) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3)
      ↔ ((preCount 4 f a (fun _ => 1) : ℤ)
          = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2) := by
  have hcard : (0 : ℤ) < (Fintype.card F : ℤ) := by
    exact_mod_cast Fintype.card_pos
  rw [crossCorr_fourthMoment_nonzero]
  constructor
  · intro h
    have hq : (Fintype.card F : ℤ)
        * (preCount 4 f a (fun _ => 1) : ℤ)
        = (Fintype.card F : ℤ)
            * ((Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2) := by
      ring_nf; ring_nf at h; linarith [h]
    exact mul_left_cancel₀ (ne_of_gt hcard) hq
  · intro h
    rw [h]; ring

/-! ## The weight-enumerator (MacWilliams) form, through the Layer A3 bridge -/

/-- **Input (B) as the fourth Pless power moment of the dual code weights.**
Through the Layer A3 Delsarte bridge `R(s) = q − 2·w(s)` (`two_mul_codeWeight_eq`),
input **(B)** is exactly the fourth power moment of the dual Kasami code weight
distribution:
```
  (∑_{s≠0} R(s)⁴ = 2·q³)  ↔  (∑_{s≠0} (q − 2·w(s))⁴ = 2·q³) .
```
The MacWilliams transform reads `∑_{s≠0} R(s)⁴` off the codeword weights `w(s)`. -/
theorem fourthMoment_codeWeight_form (f : F → F) (a : F) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3)
      ↔ (∑ s ∈ univ.erase (0 : F),
            ((Fintype.card F : ℤ) - 2 * (codeWeight f s a : ℤ)) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) := by
  have hterm : ∀ s : F,
      ((Fintype.card F : ℤ) - 2 * (codeWeight f s a : ℤ)) = autocorrScaled f s a := by
    intro s; have h := two_mul_codeWeight_eq f s a; linarith [h]
  have hsum : ∑ s ∈ univ.erase (0 : F),
        ((Fintype.card F : ℤ) - 2 * (codeWeight f s a : ℤ)) ^ 4
      = ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4 :=
    Finset.sum_congr rfl (fun s _ => by rw [hterm s])
  rw [hsum]

/-! ## Kasami specializations -/

variable {n k : ℕ}

/-- **Kasami: input (B) ⟺ the derivative 4-collision count.**  The Kasami
specialization of `fourthMoment_eq_iff_collisionCount`: the hypothesis `hfourth`
of `kasami_crossCorr_value_set` holds **iff** the Kasami derivative 4-collision
count is `q³ + 2q²`. -/
theorem kasami_fourthMoment_iff_collisionCount (a : F) :
    (∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3)
      ↔ ((preCount 4 (fun x : F => x ^ d k) a (fun _ => 1) : ℤ)
          = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2) :=
  fourthMoment_eq_iff_collisionCount _ a

/-- **Kasami: input (B) in weight-enumerator form.**  The Kasami specialization
of `fourthMoment_codeWeight_form`. -/
theorem kasami_fourthMoment_codeWeight_form (a : F) :
    (∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3)
      ↔ (∑ s ∈ univ.erase (0 : F),
            ((Fintype.card F : ℤ)
              - 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ)) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :=
  fourthMoment_codeWeight_form _ a

end Vanish.Foundations
