import RequestProject.Foundations.KasamiSecondDerivMultiplicity
import RequestProject.Foundations.KasamiAdditiveEnergy
import RequestProject.Foundations.KasamiCrossCorrelationTable
import RequestProject.Foundations.KasamiFourthMomentCanonical
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# Decomposition library — Core (B·fp·s1): the AB second-derivative second moment, bottom-up

This module **expands the deep core**
`FPSecondDerivative.kasami_derivPairCount_sq_offDiag`
(`∑_{z≠0} derivPairCount² = q³ − 2q²`) into a bottom-up skeleton.  The diagonal term
is separated by a **real proof** (using the already-proven `derivPairCount_zero`),
and the second moment is re-expressed as a single **quadruple solution count** — a
concrete fourth-order point count that is the genuine almost-bent leaf.

## The chain

* `derivQuadrupleCount` — a real definition: the number of `(x,y,x′,y′)` with
  `Δf_a x + Δf_a y = Δf_a x′ + Δf_a y′`.
* `derivPairCount_sq_sum_eq_quadruple` — the real fiberwise identity
  `∑_z derivPairCount(z)² = derivQuadrupleCount`.
* `kasami_derivQuadrupleCount` — the deep almost-bent leaf:
  `derivQuadrupleCount (·^{dk}) a = q³ + 2q²` (the additive-energy value in raw
  point-count form; AB-specific, not implied by APN).
* `kasami_derivPairCount_sq_offDiag` — the assembled core, a **real proof** that
  subtracts the diagonal `derivPairCount(0)² = (2q)²` from the total.

## Sources

Carlet, *Boolean Functions …*, Ch. 6; Chabaud–Vaudenay §3; CCD (IEEE-IT 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Decomp

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The second-derivative quadruple count** (real definition): the number of
ordered `(x,y,x′,y′)` whose two derivative-pair sums agree. -/
noncomputable def derivQuadrupleCount (f : F → F) (a : F) : ℕ :=
  (univ.filter (fun p : (F × F) × (F × F) =>
    deriv f a p.1.1 + deriv f a p.1.2 = deriv f a p.2.1 + deriv f a p.2.2)).card

/-
**Fiberwise identity.**  Summing the squared fiber sizes recovers the matching
count: `∑_z derivPairCount(z)² = derivQuadrupleCount`.
-/
omit [CharP F 2] in
theorem derivPairCount_sq_sum_eq_quadruple (f : F → F) (a : F) :
    (∑ z : F, (derivPairCount f a z : ℤ) ^ 2)
      = (derivQuadrupleCount f a : ℤ) := by
  unfold derivQuadrupleCount;
  simp +decide only [derivPairCount, card_filter];
  push_cast [ sq, Finset.sum_mul ];
  rw [ Finset.sum_comm ];
  simp +decide;
  rw [ ← Nat.cast_sum ];
  rw [ Finset.sum_congr rfl fun x hx => Finset.card_filter _ _ ];
  rw [ ← Finset.sum_product' ];
  simp +decide [ eq_comm ]

/-- **The quadruple count is `16·` the derivative-image additive energy.**  For any
APN `f` and `a ≠ 0`, the second-derivative quadruple count equals
`16·additiveEnergy (derivImage f a)`.  This is genuine (sorry-free) Fourier wiring:
`q·derivQuadrupleCount = ∑_s R(s)⁴` (the `m = 4` power moment, since
`derivQuadrupleCount = preCount 4`) and `∑_s R(s)⁴ = 16·q·E`
(`crossCorr_fourthMoment_eq_energy`), so cancelling `q > 0` gives the identity.  It
recasts the deep almost-bent leaf `kasami_derivQuadrupleCount` into the standard
additive-energy form `16·E = q³ + 2q²`. -/
theorem derivQuadrupleCount_eq_additiveEnergy (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) :
    (derivQuadrupleCount f a : ℤ)
      = 16 * (additiveEnergy (derivImage f a) : ℤ) := by
  have hpre : (Fintype.card F : ℤ) * (derivQuadrupleCount f a : ℤ)
      = (Fintype.card F : ℤ) * (MTuple.preCount 4 f a (fun _ => 1) : ℤ) := by
    congr 1
    rw [show MTuple.preCount 4 f a (fun _ => 1) = derivQuadrupleCount f a from ?_]
    · unfold derivQuadrupleCount MTuple.preCount
      refine Finset.card_bij (fun x _ => ((x 0, x 1), (x 2, x 3))) ?_ ?_ ?_ <;>
        simp +decide
      · intro x hx
        rw [Fin.sum_univ_four] at hx
        simp_all +decide [add_eq_zero_iff_eq_neg]
        grind
      · exact fun a₁ ha₁ a₂ ha₂ h₀ h₁ h₂ h₃ => by ext i; fin_cases i <;> assumption
      · intro x y z t h
        refine ⟨fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else t, ?_, ?_⟩
        · simp +decide [Fin.sum_univ_four]; grind +qlia
        · simp +decide
  rw [← Vanish.Foundations.crossCorr_fourth_moment f a] at hpre
  rw [Vanish.Foundations.crossCorr_fourthMoment_eq_energy f hf a ha] at hpre
  have hq : (0 : ℤ) < (Fintype.card F : ℤ) := by exact_mod_cast Fintype.card_pos
  nlinarith [hpre, hq]

/-- **The second-derivative quadruple count is the derivative point count.**  The
ordered `(x,y,x′,y′)` with `Δf_a x + Δf_a y = Δf_a x′ + Δf_a y′` are in bijection with
the `4`-tuples `x : Fin 4 → F` with `∑ᵢ Δf_a(xᵢ) = 0` (char 2), so
`derivQuadrupleCount f a = preCount₄(a)`. -/
theorem derivQuadrupleCount_eq_preCount4 (f : F → F) (a : F) :
    derivQuadrupleCount f a = MTuple.preCount 4 f a (fun _ => 1) := by
  symm
  unfold derivQuadrupleCount MTuple.preCount
  refine Finset.card_bij (fun x _ => ((x 0, x 1), (x 2, x 3))) ?_ ?_ ?_ <;> simp +decide
  · intro x hx
    rw [Fin.sum_univ_four] at hx
    simp_all +decide [add_eq_zero_iff_eq_neg]
    grind
  · exact fun a₁ ha₁ a₂ ha₂ h₀ h₁ h₂ h₃ => by ext i; fin_cases i <;> assumption
  · intro x y z t h
    refine ⟨fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else t, ?_, ?_⟩
    · simp +decide [Fin.sum_univ_four]; grind +qlia
    · simp +decide

/-- **The almost-bent second-derivative quadruple count (real proof).**  For the
Kasami map, the second-derivative quadruple count attains its almost-bent value
`q³ + 2q²`.  This is now derived from the single canonical point count
`Vanish.Foundations.kasami_preCount4` (input (B)), via `derivQuadrupleCount_eq_preCount4`. -/
theorem kasami_derivQuadrupleCount {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (derivQuadrupleCount (fun x : F => x ^ d k) a : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 := by
  have hpc := Vanish.Foundations.kasami_preCount4 hcard hk hkn hcop hnodd hn a ha
  rw [derivQuadrupleCount_eq_preCount4]
  exact_mod_cast hpc

/-- **The assembled AB second-derivative second moment.**  Subtracting the diagonal
term `derivPairCount(0)² = (2q)²` (via the proven `derivPairCount_zero`) from the
total `kasami_derivQuadrupleCount` gives `∑_{z≠0} derivPairCount² = q³ − 2q²`.
Real wiring. -/
theorem kasami_derivPairCount_sq_offDiag {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (∑ z ∈ univ.erase (0 : F), (derivPairCount (fun x : F => x ^ d k) a z) ^ 2 : ℤ)
      = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2 := by
  have hapn : IsAPN (fun x : F => x ^ d k) :=
    KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn
  have htot := derivPairCount_sq_sum_eq_quadruple (fun x : F => x ^ d k) a
  have hquad := kasami_derivQuadrupleCount hcard hk hkn hcop hnodd hn a ha
  have hzero := derivPairCount_zero n hn hcard (fun x : F => x ^ d k) hapn a ha
  have hsplit :
      (∑ z : F, (derivPairCount (fun x : F => x ^ d k) a z : ℤ) ^ 2)
        = (derivPairCount (fun x : F => x ^ d k) a 0 : ℤ) ^ 2
          + ∑ z ∈ univ.erase (0 : F), (derivPairCount (fun x : F => x ^ d k) a z : ℤ) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]
    ring
  rw [hquad] at htot
  rw [hsplit, hzero] at htot
  push_cast at htot ⊢
  nlinarith [htot]

end Vanish.Foundations.FirstPrinciples.Decomp