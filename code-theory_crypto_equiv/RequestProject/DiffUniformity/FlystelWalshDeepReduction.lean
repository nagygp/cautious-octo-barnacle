import Mathlib
import RequestProject.DiffUniformity.FlystelWalshAnemoi
import RequestProject.DiffUniformity.FlystelWalshPoseidon
import RequestProject.DiffUniformity.FlystelWalshSandwich
import RequestProject.DiffUniformity.CharSumRojasLeonReduction

/-!
# Closing the conditional gap: reducing the Flystel deep-entry bound to the
classical one-variable Weil bound (ZK track, item 3)

The conditional Walsh sandwiches of `FlystelWalshSandwich.lean` take as an input
the **two-variable Rojas–León bound** `RojasLeonBoundTwo ψ (walshFun V a b) d` on
the deep entries.  That two-variable estimate is the genuinely deep,
algebraic-geometry ("`d ≥ 3` Rojas–León") input.

This module discharges the *reduction* half of the gap: it proves that, over the
concrete Anemoi (`F₁₁`, `d = 3`) and Poseidon (`F₁₃`, `d = 5`) closed Flystels,
the two-variable deep-entry bound **follows from the classical one-variable Weil
bound** on the completed-square residual polynomial.  Concretely, after the linear
change of variables `u = y − v` and completing the square in the remaining
variable, every deep-entry phase is either

* an inner-affine sum (handled *unconditionally*, no Weil input needed), or
* of the shape `c·(v + s u)² + P u` with `c ≠ 0` and `P` a one-variable
  polynomial of degree `d`, for which `CharSumBounds.rojasLeonBoundTwo_of_factor`
  turns the two-variable bound into the one-variable Weil bound `WeilBoundOne ψ P d`.

So the **only** remaining open input is the classical, one-variable degree-`d`
Weil bound `WeilBoundOne` on an explicit residual polynomial — precisely Weil's
theorem for one-variable character sums (the quadratic and monomial cases of which
are already proved unconditionally in `CharSumWeilGaussSum.lean` /
`CharSumMonomialWeil.lean`).  This is a strictly sharper, more standard hypothesis
than the two-variable Rojas–León estimate it replaces.

## Main results

* `charSumTwo_reindex_sub` — `charSumTwo` is invariant under the linear
  reindexing `y ↦ y + v` of the first summation variable (the `u = y − v`
  substitution).
* `Anemoi.OneVarWeil`, `Poseidon.OneVarWeil` — the classical one-variable
  degree-`d` Weil bound over the concrete field, packaged as a single predicate.
* `Anemoi.hdeep_of_oneVarWeil`, `Poseidon.hdeep_of_oneVarWeil` — the deep-entry
  two-variable bound derived from the one-variable Weil bound.
* `Anemoi.sandwich_of_oneVarWeil`, `Poseidon.sandwich_of_oneVarWeil` — the Walsh
  sandwich, now conditional only on the classical one-variable Weil bound.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

open CharSumBounds

variable {K : Type*} [Field K] [Fintype K]

/-
**Reindexing invariance.** Summing the two-variable phase over `(y, v)` is the
same as summing the `u = y − v` substituted phase over `(u, v)`: for each fixed
`v`, `y ↦ y + v` is a bijection of `K`.
-/
theorem charSumTwo_reindex_sub (ψ : AddChar K ℂ) (g : K → K → K) :
    charSumTwo ψ g = charSumTwo ψ (fun u v => g (u + v) v) := by
  convert Finset.sum_comm using 1;
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Equiv.sum_comp ( Equiv.addRight _ ) fun x => ψ ( g x _ ) )

/-- Consequently the two-variable Rojas–León bound is invariant under the same
substitution. -/
theorem rojasLeonBoundTwo_reindex_sub (ψ : AddChar K ℂ) (g : K → K → K) (d : ℕ)
    (h : RojasLeonBoundTwo ψ (fun u v => g (u + v) v) d) :
    RojasLeonBoundTwo ψ g d := by
  unfold RojasLeonBoundTwo at *
  rwa [charSumTwo_reindex_sub ψ g]

end FlystelWalsh
end APN

namespace APN
namespace FlystelWalsh
namespace Anemoi

open CharSumBounds

/-- The classical one-variable **cubic Weil bound** over `F₁₁`: for the additive
character `ψ`, every cubic `c₃u³ + c₂u² + c₁u + c₀` obeys
`‖∑_u ψ(cubic u)‖ ≤ 2·√11`.  (Weil's theorem for one-variable character sums; the
single remaining classical open input.) -/
def OneVarWeil (ψ : AddChar (ZMod p) ℂ) : Prop :=
  ∀ c₃ c₂ c₁ c₀ : ZMod p,
    WeilBoundOne ψ (fun u => c₃ * u ^ 3 + c₂ * u ^ 2 + c₁ * u + c₀) 3

/-
**Deep-entry bound from the one-variable Weil bound.** Given the classical
cubic Weil bound over `F₁₁`, the two-variable deep-entry Rojas–León bound for the
Anemoi `x³` closed Flystel holds on every deep entry.
-/
theorem hdeep_of_oneVarWeil (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hweil : OneVarWeil ψ) :
    ∀ a b : ZMod p × ZMod p, DeepEntry a b →
      RojasLeonBoundTwo ψ (walshFun V a b) 3 := by
  intros a b hab
  set c := b.1 + b.2
  by_cases hc : c ≠ 0;
  · apply rojasLeonBoundTwo_reindex_sub;
    apply rojasLeonBoundTwo_of_factor ψ hψ (by
    rw [ ZMod.ringChar_zmod_n ] ; decide) c hc (fun u => (2 * b.1 * u + (a.1 + a.2)) / (2 * c)) (fun u => c * u ^ 3 + (b.1 - b.1 ^ 2 / c) * u ^ 2 + (a.1 - b.1 * (a.1 + a.2) / c) * u + -((a.1 + a.2) ^ 2 / (4 * c))) (fun u v => walshFun V a b (u + v) v) 3 (by
    intro u v; simp +decide [ walshFun, V, closedFlystelMap, E, Qγ, Qδ, dotProd ] ; ring;
    grind) (by
    exact hweil _ _ _ _);
  · -- Since $c = 0$, we have $b₂ = -b₁$. From DeepEntry, $b ≠ (0,0)$; with $b₂ = -b₁$ this forces $b₁ ≠ 0$.
    have hb1_ne_zero : b.1 ≠ 0 := by
      cases hab <;> aesop;
    -- For u ≠ u₀, charSumOne ψ (fun v => h u v) = 0 by charSumOne_affine_eq_zero ψ hψ (A u) (b₁*u^2+a₁*u) (by ...: A u ≠ 0) after rewriting h u v = A u * v + (b₁*u^2+a₁*u).
    have h_charSumOne_zero : ∀ u : ZMod p, u ≠ -(a.1 + a.2) * (2 * b.1)⁻¹ → charSumOne ψ (fun v => walshFun V a b (u + v) v) = 0 := by
      intro u hu
      have h_inner : ∀ v : ZMod p, walshFun V a b (u + v) v = (2 * b.1 * u + (a.1 + a.2)) * v + (b.1 * u ^ 2 + a.1 * u) := by
        intro v
        simp [walshFun, V, closedFlystelMap, E, Qγ, Qδ]
        ring;
        simp +zetaDelta at *;
        unfold dotProd; rw [ show b.2 = -b.1 by linear_combination' hc ] ; ring;
      convert charSumOne_affine_eq_zero ψ hψ ( 2 * b.1 * u + ( a.1 + a.2 ) ) ( b.1 * u ^ 2 + a.1 * u ) _ using 1;
      · exact congr_arg _ ( funext h_inner );
      · grind +suggestions;
    -- By `Finset.sum_eq_single u₀ ...`, `charSumTwo ψ h = charSumOne ψ (fun v => h u₀ v)`.
    have h_charSumTwo_eq_charSumOne : charSumTwo ψ (fun u v => walshFun V a b (u + v) v) = charSumOne ψ (fun v => walshFun V a b (-(a.1 + a.2) * (2 * b.1)⁻¹ + v) v) := by
      convert Finset.sum_eq_single ( - ( a.1 + a.2 ) * ( 2 * b.1 ) ⁻¹ ) _ _ using 1 <;> simp_all +decide [ charSumTwo, charSumOne ];
    -- Then `‖charSumTwo ψ h‖ ≤ Fintype.card (ZMod 11) = 11` by `norm_charSumOne_le`, and `11 ≤ (3-1)*11 = 22`.
    have h_norm_charSumTwo_le : ‖charSumTwo ψ (fun u v => walshFun V a b (u + v) v)‖ ≤ (Fintype.card (ZMod p) : ℝ) := by
      exact h_charSumTwo_eq_charSumOne.symm ▸ norm_charSumOne_le ψ _;
    exact rojasLeonBoundTwo_reindex_sub ψ ( walshFun V a b ) 3 ( by exact le_trans h_norm_charSumTwo_le ( by erw [ ZMod.card ] ; norm_num ) )

/-- **Anemoi `x³` Walsh sandwich, conditional only on the classical one-variable
Weil bound.** This replaces the two-variable Rojas–León hypothesis of
`walsh_V_anemoi_sandwich` by the strictly weaker classical one-variable cubic Weil
bound. -/
theorem sandwich_of_oneVarWeil (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hweil : OneVarWeil ψ) :
    ∃ a b : ZMod p × ZMod p, (a, b) ≠ (0, 0) ∧
      (14641 : ℝ) / 122 ≤ Complex.normSq (walsh ψ V a b) ∧
      ‖walsh ψ V a b‖ ≤ (22 : ℝ) :=
  walsh_V_anemoi_sandwich ψ hψ (hdeep_of_oneVarWeil ψ hψ hweil)

end Anemoi
end FlystelWalsh
end APN

namespace APN
namespace FlystelWalsh
namespace Poseidon

open CharSumBounds

/-- The classical one-variable **quintic Weil bound** over `F₁₃`: every quintic
`c₅u⁵ + … + c₀` obeys `‖∑_u ψ(quintic u)‖ ≤ 4·√13`. -/
def OneVarWeil (ψ : AddChar (ZMod p) ℂ) : Prop :=
  ∀ c₅ c₄ c₃ c₂ c₁ c₀ : ZMod p,
    WeilBoundOne ψ
      (fun u => c₅ * u ^ 5 + c₄ * u ^ 4 + c₃ * u ^ 3 + c₂ * u ^ 2 + c₁ * u + c₀) 5

/-
**Deep-entry bound from the one-variable Weil bound** for the Poseidon `x⁵`
closed Flystel over `F₁₃`.
-/
theorem hdeep_of_oneVarWeil (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hweil : OneVarWeil ψ) :
    ∀ a b : ZMod p × ZMod p, DeepEntry a b →
      RojasLeonBoundTwo ψ (walshFun V5 a b) 5 := by
  intros a b hab
  apply rojasLeonBoundTwo_reindex_sub ψ (walshFun V5 a b) 5;
  by_cases hc : b.1 + b.2 = 0;
  · -- Since $c = 0$, we have $b₂ = -b₁$. From $DeepEntry$, $b$ cannot be $(0,0)$, so $b₁ ≠ 0$.
    have hb1_ne_zero : b.1 ≠ 0 := by
      cases hab <;> aesop;
    -- Set $u₀ = -(a₁ + a₂) * (2 * b₁)⁻¹$. For $u ≠ u₀$, the inner sum vanishes.
    set u₀ : ZMod p := -(a.1 + a.2) * (2 * b.1)⁻¹
    have h_inner_zero : ∀ u : ZMod p, u ≠ u₀ → charSumOne ψ (fun v => walshFun V5 a b (u + v) v) = 0 := by
      intro u hu_ne_u₀
      have h_inner_zero : ∀ v : ZMod p, walshFun V5 a b (u + v) v = (2 * b.1 * u + (a.1 + a.2)) * v + (b.1 * u^2 + a.1 * u) := by
        intro v
        simp [walshFun, V5]
        ring;
        unfold dotProd closedFlystelMap E5 Qγ Qδ; simp +decide [ show b.2 = -b.1 by linear_combination' hc ] ; ring;
      convert charSumOne_affine_eq_zero ψ hψ ( 2 * b.1 * u + ( a.1 + a.2 ) ) ( b.1 * u ^ 2 + a.1 * u ) _ using 1;
      · exact congr_arg _ ( funext h_inner_zero );
      · grind +suggestions;
    -- Therefore, the sum reduces to the term for $u = u₀$.
    have h_sum_u₀ : charSumTwo ψ (fun u v => walshFun V5 a b (u + v) v) = charSumOne ψ (fun v => walshFun V5 a b (u₀ + v) v) := by
      rw [ charSumTwo_eq_sum_charSumOne ];
      rw [ Finset.sum_eq_single u₀ ] <;> aesop;
    -- Therefore, the norm of the sum is at most the norm of the term for $u = u₀$.
    have h_norm_u₀ : ‖charSumTwo ψ (fun u v => walshFun V5 a b (u + v) v)‖ ≤ (Fintype.card (ZMod p) : ℝ) := by
      exact h_sum_u₀.symm ▸ norm_charSumOne_le _ _;
    exact le_trans h_norm_u₀ ( by erw [ ZMod.card ] ; norm_num );
  · obtain ⟨c, s, P, hg, hP⟩ : ∃ c : ZMod p, ∃ s : ZMod p → ZMod p, ∃ P : ZMod p → ZMod p, c ≠ 0 ∧ (∀ u v, walshFun V5 a b (u + v) v = c * (v + s u) ^ 2 + P u) ∧ WeilBoundOne ψ P 5 := by
      refine' ⟨ b.1 + b.2, fun u => ( 2 * b.1 * u + ( a.1 + a.2 ) ) / ( 2 * ( b.1 + b.2 ) ), fun u => ( b.1 + b.2 ) * u ^ 5 + 0 * u ^ 4 + 0 * u ^ 3 + ( b.1 - b.1 ^ 2 / ( b.1 + b.2 ) ) * u ^ 2 + ( a.1 - b.1 * ( a.1 + a.2 ) / ( b.1 + b.2 ) ) * u + ( - ( ( a.1 + a.2 ) ^ 2 / ( 4 * ( b.1 + b.2 ) ) ) ), _, _, _ ⟩;
      · assumption;
      · intro u v; simp +decide [ walshFun, V5, E5, Qγ, Qδ, dotProd, closedFlystelMap ] ; ring;
        grind;
      · convert hweil ( b.1 + b.2 ) 0 0 ( b.1 - b.1 ^ 2 / ( b.1 + b.2 ) ) ( a.1 - b.1 * ( a.1 + a.2 ) / ( b.1 + b.2 ) ) ( - ( ( a.1 + a.2 ) ^ 2 / ( 4 * ( b.1 + b.2 ) ) ) ) using 1;
    convert rojasLeonBoundTwo_of_factor ψ hψ _ c hg s P _ 5 hP.1 hP.2 using 1;
    rw [ ZMod.ringChar_zmod_n ] ; decide

/-- **Poseidon `x⁵` Walsh sandwich, conditional only on the classical one-variable
Weil bound.** -/
theorem sandwich_of_oneVarWeil (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hweil : OneVarWeil ψ) :
    ∃ a b : ZMod p × ZMod p, (a, b) ≠ (0, 0) ∧
      (28561 : ℝ) / 170 ≤ Complex.normSq (walsh ψ V5 a b) ∧
      ‖walsh ψ V5 a b‖ ≤ (52 : ℝ) :=
  walsh_V5_poseidon_sandwich ψ hψ (hdeep_of_oneVarWeil ψ hψ hweil)

end Poseidon
end FlystelWalsh
end APN