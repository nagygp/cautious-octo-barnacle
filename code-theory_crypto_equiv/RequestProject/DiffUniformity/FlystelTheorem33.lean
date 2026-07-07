import Mathlib
import RequestProject.DiffUniformity.FlystelWalsh
import RequestProject.DiffUniformity.CharSumBounds

/-!
# Theorem 3.3 assembly and the design conjecture — Layer 4

This module is **Layer 4** of `FLYSTEL_WALSH_ROADMAP.md`. It assembles the Walsh
spectrum bound of

> M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
> Designs, Codes and Cryptography **93** (2025) 2245–2262, Theorem 3.3

from the two earlier layers:

* the **elementary, gate-free zero entries** of Theorem 3.3, proved
  unconditionally in `FlystelWalsh.lean` (Layer 1);
* the **character-sum gates** of `CharSumBounds.lean` (Layer 3), supplied here as
  the explicit hypothesis `RojasLeonBoundTwo` on the *deep* (non-zero) entries.

The result is a genuine **conditional** Theorem 3.3: for every Anemoi closed
Flystel and every prime field for which the Rojas-León character-sum bound holds
on the deep entries, the Walsh transform obeys `‖W_V(ψ, a, b)‖ ≤ (d-1)·p` for
all nonzero masks. The CCZ-equivalence of the open and closed Flystel (the
inverse-permutation relation of `Flystel.lean`) is realised at the Walsh level
by the exact identity `W_{F⁻¹}(ψ, a, b) = W_F(ψ, b, a)` (`walsh_symm`), so the
same bound transfers from the closed Flystel `V` to the open Flystel `H`.

## Main results

* `walsh_eq_charSumTwo` — the Walsh coefficient is the two-variable character sum
  of its linear-approximation function (the bridge to Layer 3).
* `walsh_norm_le_of_rojasLeonBoundTwo` — the Rojas-León input bound gives
  `‖W_F(ψ, a, b)‖ ≤ (d-1)·p` (the deep entries of Theorem 3.3).
* `walsh_symm`, `walsh_norm_symm` — the **CCZ / inverse-permutation transfer**:
  `W_{F⁻¹}(ψ, a, b) = W_F(ψ, b, a)`, hence equal absolute Walsh spectra.
* `closedFlystel_walsh_norm_le` — the assembled Theorem 3.3 bound `(d-1)·p` for
  the closed Flystel, combining the Layer-1 zero entries with the Rojas-León
  input on the remaining (deep) entries.
* `openFlystel_walsh_norm_le_of_closed` — transfer of the bound to the open
  Flystel via `walsh_symm`.
* `Linearity`, `LogLinearityConjecture`, `logLinearityConjecture_of_bound` — the
  Anemoi designers' conjectured `p·log₂ p` linearity bound and its derivation
  from the `(d-1)·p` bound whenever `d - 1 ≤ log₂ p`.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

open CharSumBounds

variable {K : Type*} [Field K] [Fintype K]

/-- The two-variable linear-approximation function `g(x₁,x₂) = ⟨a, x⟩ + ⟨b, F x⟩`
attached to the Walsh coefficient `W_F(ψ, a, b)`. -/
def walshFun (F : K × K → K × K) (a b : K × K) : K → K → K :=
  fun x₁ x₂ => dotProd a (x₁, x₂) + dotProd b (F (x₁, x₂))

/-- **Bridge to Layer 3.** The Walsh coefficient is exactly the two-variable
character sum of its linear-approximation function. -/
theorem walsh_eq_charSumTwo (ψ : AddChar K ℂ) (F : K × K → K × K) (a b : K × K) :
    walsh ψ F a b = charSumTwo ψ (walshFun F a b) := by
  unfold walsh charSumTwo walshFun
  rw [Fintype.sum_prod_type]

/-- **Deep entries of Theorem 3.3.** The Rojas-León two-variable character-sum
bound on the linear-approximation function yields the Walsh bound
`‖W_F(ψ, a, b)‖ ≤ (d-1)·p`. -/
theorem walsh_norm_le_of_rojasLeonBoundTwo (ψ : AddChar K ℂ) (F : K × K → K × K)
    (a b : K × K) (d : ℕ) (h : RojasLeonBoundTwo ψ (walshFun F a b) d) :
    ‖walsh ψ F a b‖ ≤ ((d : ℝ) - 1) * (Fintype.card K : ℝ) := by
  rw [walsh_eq_charSumTwo]
  exact h

/-! ### CCZ / inverse-permutation transfer (open ↔ closed Flystel) -/

/-- **Walsh transform of the inverse permutation.** For a permutation `F` of
`K × K`, `W_{F⁻¹}(ψ, a, b) = W_F(ψ, b, a)`: passing to the inverse permutation
swaps the input and output masks. This is the Walsh-level realisation of the
inverse-permutation CCZ-equivalence (`Flystel.lean`) that relates the open and
closed Flystel. -/
theorem walsh_symm (ψ : AddChar K ℂ) (F : Equiv.Perm (K × K)) (a b : K × K) :
    walsh ψ (⇑F.symm) a b = walsh ψ (⇑F) b a := by
  unfold walsh
  rw [← Equiv.sum_comp F (fun x => ψ (dotProd a x + dotProd b (F.symm x)))]
  congr 1
  funext u
  simp only [Equiv.symm_apply_apply]
  rw [add_comm]

/-- Absolute Walsh spectra are preserved by passing to the inverse permutation
(with masks swapped): `‖W_{F⁻¹}(ψ, a, b)‖ = ‖W_F(ψ, b, a)‖`. -/
theorem walsh_norm_symm (ψ : AddChar K ℂ) (F : Equiv.Perm (K × K)) (a b : K × K) :
    ‖walsh ψ (⇑F.symm) a b‖ = ‖walsh ψ (⇑F) b a‖ := by
  rw [walsh_symm]

/-! ### Assembled Theorem 3.3 for the closed Flystel -/

/-- The **deep-entry predicate**: the linear-approximation masks `(a, b)` of the
closed Flystel that are *not* handled by the Layer-1 zero entries
(`walsh_eq_zero_of_b_zero`, `walsh_closedFlystel_eq_zero_of_snd_zero`,
`walsh_closedFlystel_eq_zero_of_fst_zero`). These are exactly the cases on which
the paper invokes the Rojas-León character-sum bound. -/
def DeepEntry (a b : K × K) : Prop :=
  (b.1 ≠ 0 ∧ b.2 ≠ 0) ∨
  (b.2 = 0 ∧ b.1 ≠ 0 ∧ a.2 ≠ 0) ∨
  (b.1 = 0 ∧ b.2 ≠ 0 ∧ a.1 ≠ 0)

/-- **Theorem 3.3 (assembled), closed Flystel.** Combining the proven Layer-1
zero entries with the Rojas-León character-sum input on the deep entries, every
nonzero-mask Walsh coefficient of the closed Flystel obeys `‖W_V‖ ≤ (d-1)·p`. -/
theorem closedFlystel_walsh_norm_le [DecidableEq K] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (E Qγ Qδ : K → K) (hE : Function.Bijective E) (d : ℕ) (hd : 1 ≤ d)
    (hdeep : ∀ a b : K × K, DeepEntry a b →
      RojasLeonBoundTwo ψ (walshFun (closedFlystelMap E Qγ Qδ) a b) d)
    (a b : K × K) (hab : a ≠ 0 ∨ b ≠ 0) :
    ‖walsh ψ (closedFlystelMap E Qγ Qδ) a b‖ ≤ ((d : ℝ) - 1) * (Fintype.card K : ℝ) := by
  have hrhs : (0 : ℝ) ≤ ((d : ℝ) - 1) * (Fintype.card K : ℝ) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have : (0 : ℝ) ≤ (Fintype.card K : ℝ) := by positivity
    nlinarith
  by_cases hb : b = 0
  · -- output mask zero: `a ≠ 0`, and the coefficient vanishes
    subst hb
    have ha : a ≠ 0 := by tauto
    rw [walsh_eq_zero_of_b_zero ψ hψ _ a ha]
    simpa using hrhs
  · -- `b ≠ 0`: split on the coordinates of `b`
    by_cases hb1 : b.1 = 0
    · -- `b.1 = 0`, so `b.2 ≠ 0`
      have hb2 : b.2 ≠ 0 := by
        intro h; apply hb; ext <;> simp [hb1, h]
      by_cases ha1 : a.1 = 0
      · rw [walsh_closedFlystel_eq_zero_of_fst_zero ψ hψ E Qγ Qδ hE a b ha1 hb1 hb2]
        simpa using hrhs
      · exact walsh_norm_le_of_rojasLeonBoundTwo _ _ a b d
          (hdeep a b (Or.inr (Or.inr ⟨hb1, hb2, ha1⟩)))
    · -- `b.1 ≠ 0`
      by_cases hb2 : b.2 = 0
      · by_cases ha2 : a.2 = 0
        · rw [walsh_closedFlystel_eq_zero_of_snd_zero ψ hψ E Qγ Qδ hE a b ha2 hb2 hb1]
          simpa using hrhs
        · exact walsh_norm_le_of_rojasLeonBoundTwo _ _ a b d
            (hdeep a b (Or.inr (Or.inl ⟨hb2, hb1, ha2⟩)))
      · exact walsh_norm_le_of_rojasLeonBoundTwo _ _ a b d
          (hdeep a b (Or.inl ⟨hb1, hb2⟩))

/-- **Transfer to the open Flystel.** If the closed Flystel `V = F.symm` obeys
the Theorem 3.3 bound at the swapped masks `(b, a)`, then the open Flystel
`H = F` obeys it at `(a, b)`. This is the open ↔ closed transfer realised through
`walsh_symm`. -/
theorem openFlystel_walsh_norm_le_of_closed (ψ : AddChar K ℂ)
    (F : Equiv.Perm (K × K)) (a b : K × K) (B : ℝ)
    (hclosed : ‖walsh ψ (⇑F.symm) b a‖ ≤ B) :
    ‖walsh ψ (⇑F) a b‖ ≤ B := by
  calc ‖walsh ψ (⇑F) a b‖ = ‖walsh ψ (⇑F.symm) b a‖ := (walsh_norm_symm ψ F b a).symm
    _ ≤ B := hclosed

/-! ### The Anemoi designers' linearity conjecture (Eq. 1) -/

/-- The **linearity** of `F`: the supremum of `‖W_F(ψ, a, b)‖` over all nonzero
masks. Here packaged as a uniform bound predicate `L` (every nonzero-mask
coefficient is `≤ L`). -/
def Linearity (ψ : AddChar K ℂ) (F : K × K → K × K) (L : ℝ) : Prop :=
  ∀ a b : K × K, (a ≠ 0 ∨ b ≠ 0) → ‖walsh ψ F a b‖ ≤ L

/-- The Anemoi designers' **`p·log₂ p` linearity conjecture** (Eq. 1): the
Walsh linearity of the Flystel is bounded by `p · log₂ p`. -/
def LogLinearityConjecture (ψ : AddChar K ℂ) (F : K × K → K × K) : Prop :=
  Linearity ψ F ((Fintype.card K : ℝ) * Real.logb 2 (Fintype.card K))

/-- **From Theorem 3.3 to the conjecture.** Whenever the `(d-1)·p` bound of
Theorem 3.3 holds and the degree satisfies `d - 1 ≤ log₂ p`, the conjectured
`p·log₂ p` linearity bound follows. (For the Anemoi instances the S-box degree is
small and `p` large, so this hypothesis holds.) -/
theorem logLinearityConjecture_of_bound (ψ : AddChar K ℂ) (F : K × K → K × K)
    (d : ℕ)
    (hbound : Linearity ψ F (((d : ℝ) - 1) * (Fintype.card K : ℝ)))
    (hdeg : (d : ℝ) - 1 ≤ Real.logb 2 (Fintype.card K)) :
    LogLinearityConjecture ψ F := by
  intro a b hab
  refine le_trans (hbound a b hab) ?_
  have hp : (0 : ℝ) ≤ (Fintype.card K : ℝ) := by positivity
  calc ((d : ℝ) - 1) * (Fintype.card K : ℝ)
      ≤ Real.logb 2 (Fintype.card K) * (Fintype.card K : ℝ) :=
        mul_le_mul_of_nonneg_right hdeg hp
    _ = (Fintype.card K : ℝ) * Real.logb 2 (Fintype.card K) := by ring

end FlystelWalsh
end APN
