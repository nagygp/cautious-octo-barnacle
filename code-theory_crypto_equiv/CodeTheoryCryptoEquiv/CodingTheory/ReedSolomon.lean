import CodeTheoryCryptoEquiv.CodingTheory.MDS

/-!
# Reed–Solomon codes and their MDS property

This module continues the coding-theory development of
`CodeTheoryCryptoEquiv/CodingTheory/LinearCode.lean`,
`CodeTheoryCryptoEquiv/CodingTheory/Dual.lean`,
`CodeTheoryCryptoEquiv/CodingTheory/GeneratorParityCheck.lean` and
`CodeTheoryCryptoEquiv/CodingTheory/MDS.lean`, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977.

It implements the cleanest nontrivial family of maximum distance separable (MDS)
codes flagged in §3.11 of `CODING_THEORY_DIRECTIONS.md`: the **Reed–Solomon
codes** (MacWilliams–Sloane, Ch. 10).  These are *evaluation codes*: fixing
`k` and a list `pts` of `n` distinct evaluation points in `F`, the code is the
image of the space of polynomials of degree `< k` under evaluation at the points.
The Singleton bound is met with equality (`d = n - k + 1`) because a nonzero
polynomial of degree `< k` has fewer than `k` roots, so it can vanish on at most
`k - 1` coordinates.

We keep the conventions of the foundational modules: words live in `ι → F` with
`[Fintype ι] [Field F]`, a linear `[n, k]` code is a subspace
`C : Submodule F (ι → F)` of length `n = #ι` (`codeLength`) and dimension
`dim C` (`codeDim`), and the `n` evaluation points are packaged as an injective
map `pts : ι → F` (so necessarily `k ≤ n ≤ #F`).

## Main definitions

* `rsEval pts` — the evaluation linear map `F[X] →ₗ[F] (ι → F)`,
  `p ↦ (i ↦ p.eval (pts i))`.
* `reedSolomonCode pts k` — the Reed–Solomon `[n, k]` code, i.e. the image under
  `rsEval pts` of the polynomials of degree `< k`.

## Main results

* `mem_reedSolomonCode_iff` — membership: `c` is a codeword iff `c = rsEval pts p`
  for some `p` of degree `< k`.
* `codeDim_reedSolomonCode` — for distinct points and `k ≤ n`, `dim = k`.
* `reedSolomonCode_ne_bot` — the code is nonzero when `1 ≤ k`.
* `isMDS_reedSolomonCode` — **MacWilliams–Sloane, Ch. 10**: a Reed–Solomon code
  with `1 ≤ k ≤ n` and distinct evaluation points is MDS.
* `minDist_reedSolomonCode` — the resulting minimum distance `d = n - k + 1`.

## References

* MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 10, Ch. 11 §3.
-/

namespace CodingTheory

open scoped Classical
open Polynomial

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
noncomputable def reedSolomonCode (pts : ι → F) (k : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F k).map (rsEval pts)

omit [Fintype ι] in
/-- Membership in the Reed–Solomon code: a word is a codeword iff it is the
evaluation of some polynomial of degree `< k`. -/
theorem mem_reedSolomonCode_iff {pts : ι → F} {k : ℕ} {c : ι → F} :
    c ∈ reedSolomonCode pts k ↔ ∃ p : F[X], p.degree < (k : ℕ) ∧ rsEval pts p = c := by
  simp only [reedSolomonCode, Submodule.mem_map, Polynomial.mem_degreeLT]

/-
The evaluation map restricted to the polynomials of degree `< k` is injective
when there are at least `k` distinct evaluation points: a nonzero polynomial of
degree `< k` cannot vanish at `k` distinct points.
-/
theorem rsEval_domRestrict_injective {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk : k ≤ Fintype.card ι) :
    Function.Injective ((rsEval pts).domRestrict (Polynomial.degreeLT F k)) := by
  intro p q hpq;
  simp_all +decide [ funext_iff, rsEval_apply ];
  refine' Subtype.ext ( Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _ );
  exact Finset.image pts Finset.univ;
  · refine' lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) _;
    simp +decide [ Finset.card_image_of_injective _ hpts ];
    exact ⟨ lt_of_lt_of_le ( Polynomial.mem_degreeLT.mp p.2 ) ( WithBot.coe_le_coe.mpr hk ), lt_of_lt_of_le ( Polynomial.mem_degreeLT.mp q.2 ) ( WithBot.coe_le_coe.mpr hk ) ⟩;
  · aesop

/-
**Dimension of a Reed–Solomon code.** With distinct evaluation points and
`k ≤ n`, the Reed–Solomon code has dimension exactly `k`.
-/
theorem codeDim_reedSolomonCode {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk : k ≤ Fintype.card ι) :
    codeDim (reedSolomonCode pts k) = k := by
  convert LinearMap.finrank_range_of_inj _;
  convert rfl;
  convert LinearMap.range_domRestrict ( Polynomial.degreeLT F k ) ( rsEval pts );
  · convert LinearEquiv.finrank_eq ( Polynomial.degreeLTEquiv F k ) |> Eq.symm;
    simp +decide;
  · exact rsEval_domRestrict_injective hpts hk

/-
A Reed–Solomon code with `1 ≤ k` is nonzero (it contains the evaluations of
the nonzero constant polynomials).
-/
omit [Fintype ι] in
theorem reedSolomonCode_ne_bot [Nonempty ι] {pts : ι → F} {k : ℕ} (hk : 1 ≤ k) :
    reedSolomonCode pts k ≠ ⊥ := by
  simp +decide [ Submodule.eq_bot_iff ];
  -- The constant polynomial `1` has degree `0 < k` (since `1 ≤ k`), so `1 ∈ degreeLT F k`.
  have hp : (1 : F[X]) ∈ Polynomial.degreeLT F k := by
    exact Polynomial.mem_degreeLT.mpr ( by aesop );
  refine' ⟨ _, ⟨ _, hp, rfl ⟩, _ ⟩;
  exact fun h => by simpa using congr_fun h ( Classical.arbitrary ι ) ;

/-
**Reed–Solomon codes are MDS** (MacWilliams–Sloane, Ch. 10).  A Reed–Solomon
code with distinct evaluation points and `1 ≤ k ≤ n` meets the Singleton bound
with equality.
-/
theorem isMDS_reedSolomonCode {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    IsMDS (reedSolomonCode pts k) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.mp ( pos_of_gt ( lt_of_lt_of_le hk1 hkn ) )
  refine ( isMDS_iff_forall_disjoint_vanishing ( reedSolomonCode_ne_bot hk1 ) ).mpr ?_
  · intro S hS
    have hT : (S.image pts).card = k := by
      rw [ Finset.card_image_of_injective _ hpts, hS, codeDim_reedSolomonCode hpts hkn ];
    rw [ Submodule.disjoint_def ] ; intro c hc hc' ; simp_all +decide [ mem_reedSolomonCode_iff, mem_vanishingOn_iff ] ;
    obtain ⟨ p, hp, rfl ⟩ := hc; have := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p ( Finset.image pts S ) ; simp_all +decide ;
    exact funext fun i => by rw [ this ( lt_of_not_ge fun h => hp.not_ge <| by rw [ Polynomial.degree_eq_natDegree <| by aesop_cat ] ; exact_mod_cast h ) ] ; simp +decide ;

/-
The minimum distance of a Reed–Solomon code is `d = n - k + 1`.
-/
theorem minDist_reedSolomonCode {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    minDist (reedSolomonCode pts k) = Fintype.card ι - k + 1 := by
  convert ( isMDS_reedSolomonCode hpts hk1 hkn |> And.right ) using 1;
  rw [ codeDim_reedSolomonCode hpts hkn ]

end CodingTheory