import Mathlib
import AuditSBox.PrimeFieldDiffUnif
import RequestProject.DiffUniformity.DifferentialUniformityUpstream

/-!
# Routing the prime-field bounds through the abstract framework

The prime-field power-map theory in `AuditSBox.PrimeFieldDiffUnif` is phrased with
its own bespoke `PrimeFieldAudit.fiberCard` / `PrimeFieldAudit.isDiffBounded`
notions.  The abstract, characteristic-free differential-uniformity framework
lives in `APN` (file `RequestProject.DiffUniformity.DifferentialUniformityUpstream`),
where `APN.differentialUniformity` is the single security notion that every
specialization should specialize.

This file is the bridge: it identifies the two fibre-count notions and turns the
prime-field bounds into statements about `APN.differentialUniformity`, so that the
prime-field side is expressed in terms of the one shared abstract layer.

## Main results

* `fiberCard_eq`            — the bespoke `PrimeFieldAudit.fiberCard` equals
  `APN.fiberCard` for any `f : ZMod p → ZMod p`.
* `isDiffBounded_iff_diffUnif_le` — `isDiffBounded δ f` is exactly
  `APN.differentialUniformity f ≤ δ`.
* `powerMap_diffUnif_le`    — `APN.differentialUniformity (powerMap d) ≤ d - 1`.
* `poseidon_diffUnif_le_four`, `cube_diffUnif_le_two`, … — the named S-boxes,
  now as abstract-uniformity statements.
-/

open scoped Classical

namespace PrimeFieldAudit

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The discrete derivative used here agrees with the abstract `APN.derivMap`. -/
lemma diff_eq_derivMap (f : ZMod p → ZMod p) (a x : ZMod p) :
    diff f a x = APN.derivMap f a x := rfl

/-- The bespoke fibre count equals the abstract one. -/
lemma fiberCard_eq (f : ZMod p → ZMod p) (a b : ZMod p) :
    fiberCard f a b = APN.fiberCard f a b := by
  classical
  unfold fiberCard fiber APN.fiberCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1

/-- `isDiffBounded δ f` is exactly the abstract bound
`APN.differentialUniformity f ≤ δ`. -/
theorem isDiffBounded_iff_diffUnif_le (δ : ℕ) (f : ZMod p → ZMod p) :
    isDiffBounded δ f ↔ APN.differentialUniformity f ≤ δ := by
  rw [APN.diffUnif_le_iff]
  unfold isDiffBounded
  constructor <;> intro h a ha b
  · rw [← fiberCard_eq]; exact h a ha b
  · rw [fiberCard_eq]; exact h a ha b

/-- The power map `x ↦ x ^ d` over `ZMod p` has abstract differential uniformity
`≤ d - 1`, provided `d ≥ 2` and `p ∤ d`. -/
theorem powerMap_diffUnif_le (d : ℕ) (hd : 2 ≤ d) (hpd : ¬ (p ∣ d)) :
    APN.differentialUniformity (powerMap (p := p) d) ≤ d - 1 :=
  (isDiffBounded_iff_diffUnif_le _ _).mp (power_map_bounded d hd hpd)

/-- Poseidon `x^5` S-box: abstract differential uniformity `≤ 4` for `p > 5`. -/
theorem poseidon_diffUnif_le_four (hp5 : 5 < p) :
    APN.differentialUniformity (powerMap (p := p) 5) ≤ 4 :=
  (isDiffBounded_iff_diffUnif_le _ _).mp (poseidon_sbox_bounded hp5)

/-- Cubing `x^3` S-box: abstract differential uniformity `≤ 2` for `p > 3`. -/
theorem cube_diffUnif_le_two (hp3 : 3 < p) :
    APN.differentialUniformity (powerMap (p := p) 3) ≤ 2 :=
  (isDiffBounded_iff_diffUnif_le _ _).mp (cube_map_bounded hp3)

end PrimeFieldAudit
