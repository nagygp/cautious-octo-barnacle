import Mathlib
import RequestProject.DiffUniformity.FlystelWalsh

/-!
# A concrete Anemoi Flystel and a machine‑checked Walsh certificate

This module is **Layer 2** of `FLYSTEL_WALSH_ROADMAP.md`: a concrete S‑box, with
the elementary (gate‑free) entries of Theorem 3.3 of

> M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
> Designs, Codes and Cryptography **93** (2025) 2245–2262

instantiated to a fully `sorry`‑free certificate that the designated Walsh
coefficients of the S‑box **vanish**.

We take the smallest interesting Anemoi instance: the power permutation
`E : x ↦ x³` over the prime field `F₁₁` (a permutation since
`gcd(3, 11−1) = 1`, here `d = deg E = 3`), and quadratic coordinate functions
`Q_γ = Q_δ : x ↦ x²` with identical leading coefficient (as required by the
paper). The closed Flystel `V` is verified through the proven
`closedFlystelMap` zero‑entry theorems — i.e. through the closed‑Flystel /
CCZ structure the paper exploits, rather than by brute‑force enumeration of the
open Flystel `H`.

## Main results

* `E_bijective` — the power map `x ↦ x³` is a permutation of `F₁₁`
  (checked by `decide`).
* `walsh_V_eq_zero_of_b_zero` — every coefficient with nonzero input mask and
  zero output mask vanishes (Theorem 3.3, `b = 0`).
* `walsh_V_eq_zero_of_snd_zero`, `walsh_V_eq_zero_of_fst_zero` — the Theorem 3.3
  zero entries `a₂=b₂=0, b₁≠0` and `a₁=b₁=0, b₂≠0`.
* `walsh_V_zero_zero` — the trivial coefficient is `q² = 121`.
-/

open Finset

namespace APN
namespace FlystelWalsh
namespace Anemoi

/-- The prime field we work over, `F₁₁`. -/
abbrev p : ℕ := 11

instance : Fact (Nat.Prime p) := ⟨by norm_num⟩

/-- The Anemoi `α = 3` S‑box power permutation `E : x ↦ x³` over `F₁₁`.
It is a permutation because `gcd(3, |F₁₁ˣ|) = gcd(3, 10) = 1`; here `d = deg E = 3`. -/
def E : ZMod p → ZMod p := fun x => x ^ 3

/-- The first quadratic coordinate function `Q_γ : x ↦ x²`. -/
def Qγ : ZMod p → ZMod p := fun x => x ^ 2

/-- The second quadratic coordinate function `Q_δ : x ↦ x²`, with the **same
leading coefficient** as `Q_γ` (the paper's standing hypothesis on `Q_γ, Q_δ`). -/
def Qδ : ZMod p → ZMod p := fun x => x ^ 2

/-- The concrete closed Flystel `V` of `(Q_γ, E, Q_δ)`. -/
def V : ZMod p × ZMod p → ZMod p × ZMod p := closedFlystelMap E Qγ Qδ

/-- The Anemoi `x ↦ x³` S‑box is a permutation of `F₁₁` (machine‑checked). -/
theorem E_bijective : Function.Bijective E := by decide

/-- **Trivial coefficient.** `W_V(ψ, 0, 0) = q² = 121`. -/
theorem walsh_V_zero_zero (ψ : AddChar (ZMod p) ℂ) :
    walsh ψ V 0 0 = (121 : ℂ) := by
  rw [walsh_zero_zero]
  norm_num [p, ZMod.card]

/-- **Theorem 3.3, case `a ≠ 0, b = 0`.** The Walsh coefficient of the concrete
Anemoi closed Flystel vanishes for every nonzero input mask and the trivial
output mask. -/
theorem walsh_V_eq_zero_of_b_zero (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (a : ZMod p × ZMod p) (ha : a ≠ 0) :
    walsh ψ V a 0 = 0 :=
  walsh_eq_zero_of_b_zero ψ hψ V a ha

/-- **Theorem 3.3 zero entry, `a₂ = b₂ = 0`, `b₁ ≠ 0`.** -/
theorem walsh_V_eq_zero_of_snd_zero (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (a b : ZMod p × ZMod p) (ha2 : a.2 = 0) (hb2 : b.2 = 0) (hb1 : b.1 ≠ 0) :
    walsh ψ V a b = 0 :=
  walsh_closedFlystel_eq_zero_of_snd_zero ψ hψ E Qγ Qδ E_bijective a b ha2 hb2 hb1

/-- **Theorem 3.3 zero entry, `a₁ = b₁ = 0`, `b₂ ≠ 0`.** -/
theorem walsh_V_eq_zero_of_fst_zero (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (a b : ZMod p × ZMod p) (ha1 : a.1 = 0) (hb1 : b.1 = 0) (hb2 : b.2 ≠ 0) :
    walsh ψ V a b = 0 :=
  walsh_closedFlystel_eq_zero_of_fst_zero ψ hψ E Qγ Qδ E_bijective a b ha1 hb1 hb2

end Anemoi
end FlystelWalsh
end APN
