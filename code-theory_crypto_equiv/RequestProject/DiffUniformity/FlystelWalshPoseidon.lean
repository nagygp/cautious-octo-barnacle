import Mathlib
import RequestProject.DiffUniformity.FlystelWalsh
import RequestProject.DiffUniformity.FlystelTheorem33

/-!
# A concrete Poseidon-style (x⁵) Flystel and its Walsh certificate

This module extends the Layer-2 concrete S-box verification
(`FlystelWalshAnemoi.lean`) from the Anemoi `x³` instance to the **Poseidon**
`x⁵` power S-box, the other standard arithmetisation-oriented permutation power.

We take the smallest prime field on which `x ↦ x⁵` is a permutation: over `F₁₃`,
`gcd(5, 13−1) = gcd(5, 12) = 1`, so `E : x ↦ x⁵` is a permutation with
`d = deg E = 5`. With quadratic coordinate functions `Q_γ = Q_δ : x ↦ x²` of
identical leading coefficient, the closed Flystel `V` again has fully
machine-checked vanishing-Walsh certificates through the closed-Flystel / CCZ
structure.

We additionally record the **concrete conditional Theorem 3.3 bound**
`‖W_V(ψ, a, b)‖ ≤ (d−1)·p = 4·13 = 52` for all nonzero masks, derived from the
Layer-4 assembly `closedFlystel_walsh_norm_le` given the Rojas-León
character-sum input on the deep entries.

## Main results

* `E5_bijective` — `x ↦ x⁵` is a permutation of `F₁₃` (checked by `decide`).
* `walsh_V5_zero_zero`, `walsh_V5_eq_zero_of_b_zero`,
  `walsh_V5_eq_zero_of_snd_zero`, `walsh_V5_eq_zero_of_fst_zero` — the
  Theorem 3.3 zero entries for the Poseidon closed Flystel.
* `walsh_V5_norm_le` — the conditional `(d−1)·p = 52` bound for nonzero masks.
-/

open Finset

namespace APN
namespace FlystelWalsh
namespace Poseidon

/-- The prime field we work over, `F₁₃`. -/
abbrev p : ℕ := 13

instance : Fact (Nat.Prime p) := ⟨by norm_num⟩

/-- The Poseidon `α = 5` S-box power permutation `E : x ↦ x⁵` over `F₁₃`.
It is a permutation because `gcd(5, |F₁₃ˣ|) = gcd(5, 12) = 1`; here `d = deg E = 5`. -/
def E5 : ZMod p → ZMod p := fun x => x ^ 5

/-- The first quadratic coordinate function `Q_γ : x ↦ x²`. -/
def Qγ : ZMod p → ZMod p := fun x => x ^ 2

/-- The second quadratic coordinate function `Q_δ : x ↦ x²`, with the same
leading coefficient as `Q_γ`. -/
def Qδ : ZMod p → ZMod p := fun x => x ^ 2

/-- The concrete Poseidon closed Flystel `V` of `(Q_γ, E₅, Q_δ)`. -/
def V5 : ZMod p × ZMod p → ZMod p × ZMod p := closedFlystelMap E5 Qγ Qδ

/-- The Poseidon `x ↦ x⁵` S-box is a permutation of `F₁₃` (machine-checked). -/
theorem E5_bijective : Function.Bijective E5 := by decide

/-- **Trivial coefficient.** `W_V(ψ, 0, 0) = q² = 169`. -/
theorem walsh_V5_zero_zero (ψ : AddChar (ZMod p) ℂ) :
    walsh ψ V5 0 0 = (169 : ℂ) := by
  rw [walsh_zero_zero]
  norm_num [p, ZMod.card]

/-- **Theorem 3.3, case `a ≠ 0, b = 0`.** -/
theorem walsh_V5_eq_zero_of_b_zero (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (a : ZMod p × ZMod p) (ha : a ≠ 0) :
    walsh ψ V5 a 0 = 0 :=
  walsh_eq_zero_of_b_zero ψ hψ V5 a ha

/-- **Theorem 3.3 zero entry, `a₂ = b₂ = 0`, `b₁ ≠ 0`.** -/
theorem walsh_V5_eq_zero_of_snd_zero (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (a b : ZMod p × ZMod p) (ha2 : a.2 = 0) (hb2 : b.2 = 0) (hb1 : b.1 ≠ 0) :
    walsh ψ V5 a b = 0 :=
  walsh_closedFlystel_eq_zero_of_snd_zero ψ hψ E5 Qγ Qδ E5_bijective a b ha2 hb2 hb1

/-- **Theorem 3.3 zero entry, `a₁ = b₁ = 0`, `b₂ ≠ 0`.** -/
theorem walsh_V5_eq_zero_of_fst_zero (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (a b : ZMod p × ZMod p) (ha1 : a.1 = 0) (hb1 : b.1 = 0) (hb2 : b.2 ≠ 0) :
    walsh ψ V5 a b = 0 :=
  walsh_closedFlystel_eq_zero_of_fst_zero ψ hψ E5 Qγ Qδ E5_bijective a b ha1 hb1 hb2

/-- **Conditional Theorem 3.3 bound for the Poseidon closed Flystel.** Given the
Rojas-León character-sum input on the deep entries, every nonzero-mask Walsh
coefficient obeys `‖W_V(ψ, a, b)‖ ≤ (d−1)·p = 4·13 = 52`. -/
theorem walsh_V5_norm_le (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hdeep : ∀ a b : ZMod p × ZMod p, DeepEntry a b →
      CharSumBounds.RojasLeonBoundTwo ψ (walshFun V5 a b) 5)
    (a b : ZMod p × ZMod p) (hab : a ≠ 0 ∨ b ≠ 0) :
    ‖walsh ψ V5 a b‖ ≤ (52 : ℝ) := by
  have h := closedFlystel_walsh_norm_le (K := ZMod p) ψ hψ E5 Qγ Qδ E5_bijective 5
    (by norm_num) hdeep a b hab
  have hcard : (Fintype.card (ZMod p) : ℝ) = 13 := by
    rw [ZMod.card]; norm_num [p]
  rw [hcard] at h
  norm_num at h
  exact h

end Poseidon
end FlystelWalsh
end APN
