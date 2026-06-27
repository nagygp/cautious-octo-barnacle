/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import CodeTheoryCryptoEquiv.Upstream.MDS

/-!
# Reed–Solomon codes and their MDS property

> Intended Mathlib target path: this extends the linear-code files
> (`Mathlib/InformationTheory/LinearCode.lean`, cf. `Upstream/LinearCode.lean`,
> `Upstream/Dual.lean`, `Upstream/MDS.lean`).
>
> For the actual pull request the blanket `import Mathlib` pulled in via
> `Upstream.MDS` should be minimised (e.g. with `shake`).

This file constructs the **Reed–Solomon codes** and proves they are *maximum
distance separable* (MDS): fixing a dimension parameter `k` and a family `pts` of
`n` distinct evaluation points in a field `F`, the Reed–Solomon code is the image
of the polynomials of degree `< k` under evaluation at the points
(MacWilliams–Sloane, Ch. 10).  Its minimum distance meets the Singleton bound,
`d = n - k + 1`, because a nonzero polynomial of degree `< k` has fewer than `k`
roots.

## Main definitions

* `LinearCode.rsEval pts` — the evaluation map `F[X] →ₗ[F] (ι → F)`,
  `p ↦ (i ↦ p.eval (pts i))`.
* `LinearCode.reedSolomon pts k` — the Reed–Solomon `[n, k]` code.

## Main results

* `LinearCode.mem_reedSolomon_iff` — membership in the code.
* `LinearCode.dim_reedSolomon` — for distinct points and `k ≤ n`, `dim = k`.
* `LinearCode.reedSolomon_ne_bot` — the code is nonzero when `1 ≤ k`.
* `LinearCode.isMDS_reedSolomon` — **MacWilliams–Sloane, Ch. 10**: a
  Reed–Solomon code with `1 ≤ k ≤ n` and distinct evaluation points is MDS.
* `LinearCode.minDist_reedSolomon` — the minimum distance is `d = n - k + 1`.

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 10, Ch. 11 §3.)

## Tags

linear code, Reed–Solomon code, MDS, maximum distance separable, evaluation code,
Singleton bound
-/

open scoped Classical
open Polynomial

namespace LinearCode

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The **evaluation linear map** `F[X] →ₗ[F] (ι → F)` of a family of points
`pts : ι → F`, sending a polynomial `p` to the word `i ↦ p.eval (pts i)`. -/
noncomputable def rsEval (pts : ι → F) : F[X] →ₗ[F] (ι → F) :=
  LinearMap.pi (fun i => (Polynomial.aeval (pts i)).toLinearMap)

omit [Fintype ι] in
@[simp] theorem rsEval_apply (pts : ι → F) (p : F[X]) (i : ι) :
    rsEval pts p i = p.eval (pts i) := by
  simp only [rsEval, LinearMap.pi_apply, AlgHom.toLinearMap_apply, aeval_def, eval]; rfl

/-- The **Reed–Solomon code** of dimension parameter `k` with evaluation points
`pts : ι → F`: the image under `rsEval pts` of the space of polynomials of degree
`< k`. -/
noncomputable def reedSolomon (pts : ι → F) (k : ℕ) : LinearCode ι F :=
  (Polynomial.degreeLT F k).map (rsEval pts)

/-- Membership in the Reed–Solomon code: a word is a codeword iff it is the
evaluation of some polynomial of degree `< k`. -/
theorem mem_reedSolomon_iff {pts : ι → F} {k : ℕ} {c : ι → F} :
    c ∈ reedSolomon pts k ↔ ∃ p : F[X], p.degree < (k : ℕ) ∧ rsEval pts p = c := by
  simp only [reedSolomon, Submodule.mem_map, Polynomial.mem_degreeLT]

/-
The evaluation map restricted to the polynomials of degree `< k` is injective
when there are at least `k` distinct evaluation points: a nonzero polynomial of
degree `< k` cannot vanish at `k` distinct points.
-/
theorem rsEval_domRestrict_injective {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk : k ≤ Fintype.card ι) :
    Function.Injective ((rsEval pts).domRestrict (Polynomial.degreeLT F k)) := by
  intro p q hpq
  simp_all +decide [ funext_iff, rsEval_apply ];
  refine' Subtype.ext ( Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _ );
  exact Finset.image pts Finset.univ;
  · rw [ Finset.card_image_of_injective _ hpts ];
    refine' lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) ( max_lt _ _ );
    · exact lt_of_lt_of_le ( Polynomial.mem_degreeLT.mp p.2 ) ( WithBot.coe_le_coe.mpr hk );
    · exact lt_of_lt_of_le ( Polynomial.mem_degreeLT.mp q.2 ) ( mod_cast hk );
  · aesop

/-
**Dimension of a Reed–Solomon code.** With distinct evaluation points and
`k ≤ n`, the Reed–Solomon code has dimension exactly `k`.
-/
theorem dim_reedSolomon {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk : k ≤ Fintype.card ι) :
    (reedSolomon pts k).dim = k := by
  convert LinearMap.finrank_range_of_inj ( rsEval_domRestrict_injective hpts hk ) using 1;
  · congr;
    ext; simp [reedSolomon];
  · convert ( Polynomial.degreeLTEquiv F k ).finrank_eq.symm;
    simp +decide

/-
A Reed–Solomon code with `1 ≤ k` is nonzero (it contains the evaluations of
the nonzero constant polynomials).
-/
theorem reedSolomon_ne_bot [Nonempty ι] {pts : ι → F} {k : ℕ} (hk : 1 ≤ k) :
    reedSolomon pts k ≠ ⊥ := by
  simp +decide [ Submodule.eq_bot_iff ];
  refine' ⟨ _, ⟨ 1, _, rfl ⟩, _ ⟩;
  · exact Polynomial.mem_degreeLT.mpr ( by aesop );
  · exact fun h => by simpa using congr_fun h ( Classical.arbitrary ι ) ;

/-
**Reed–Solomon codes are MDS** (MacWilliams–Sloane, Ch. 10).  A Reed–Solomon
code with distinct evaluation points and `1 ≤ k ≤ n` meets the Singleton bound
with equality.
-/
theorem isMDS_reedSolomon {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    IsMDS (reedSolomon pts k) := by
  have hMDS : ∀ S : Finset ι, S.card = (reedSolomon pts k).dim → Disjoint (reedSolomon pts k) (vanishingOn S) := by
    intro S hS_card
    have h_dim : (reedSolomon pts k).dim = k := by
      exact?;
    rw [ disjoint_iff_inf_le ];
    intro c hc
    obtain ⟨p, hp_deg, hp_eval⟩ := (mem_reedSolomon_iff.mp hc.left)
    have hp_zero : p = 0 := by
      refine' Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p ( S.image pts ) _ _;
      · aesop;
      · rw [ Finset.card_image_of_injective _ hpts ] ; rw [ hS_card, h_dim ] ; exact lt_of_not_ge fun h => hp_deg.not_ge <| by rw [ Polynomial.degree_eq_natDegree <| by aesop_cat ] ; exact_mod_cast h;
    have hc_zero : c = 0 := by
      aesop
    exact hc_zero;
  convert isMDS_iff_forall_disjoint_vanishing (reedSolomon_ne_bot hk1) |>.2 hMDS using 1;
  exact Fintype.card_pos_iff.mp ( pos_of_gt ( lt_of_lt_of_le hk1 hkn ) )

/-
The minimum distance of a Reed–Solomon code is `d = n - k + 1`.
-/
theorem minDist_reedSolomon {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    minDist (reedSolomon pts k) = Fintype.card ι - k + 1 := by
  convert LinearCode.IsMDS.minDist_eq ( isMDS_reedSolomon hpts hk1 hkn );
  rw [ dim_reedSolomon hpts hkn ]

end LinearCode