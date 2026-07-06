import RequestProject.Geometry.Arcs
import RequestProject.CodingTheory.ReedSolomon

/-!
# The normal rational curve (Vandermonde arc) and conics

This module continues the finite-geometry track of
`RequestProject/Geometry/Arcs.lean` (arcs ⇄ MDS codes) and the Reed–Solomon
theory of `RequestProject/CodingTheory/ReedSolomon.lean`.

The **normal rational curve** of `PG(k-1, q)` is the image of the map
`t ↦ (1 : t : t² : ⋯ : t^{k-1})`.  Its points are the columns of the
**Vandermonde generator matrix** `G_{r,i} = (pts i)^r`, whose row space is exactly
the Reed–Solomon code with evaluation points `pts`.  Since Reed–Solomon codes are
MDS (`isMDS_reedSolomonCode`) and MDS ⇄ arc (`isMDS_genCode_iff_isArc`), the
columns of `G` form an **arc**: every `k` of them are linearly independent.  For
`k = 3` this is the classical fact that a **conic** `t ↦ (1 : t : t²)` is an arc.

## Main definitions

* `vandermondeGen pts k` — the Vandermonde generator matrix
  `G_{r,i} = (pts i)^r` (`r : Fin k`).

## Main results

* `genCode_vandermondeGen_eq` — the row space of `G` is the Reed–Solomon code:
  `genCode (vandermondeGen pts k) = reedSolomonCode pts k`.
* `vandermondeGen_rows_li` — for distinct points and `k ≤ n`, the rows are
  linearly independent.
* `vandermondeGen_isArc` — **the normal rational curve is an arc**: for distinct
  points and `1 ≤ k ≤ n`, every `k` columns of `G` are linearly independent.
* `conic_isArc` — the `k = 3` special case: a conic `t ↦ (1 : t : t²)` is an arc.
-/

namespace CodingTheory

open scoped Classical
open Matrix Polynomial

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The **Vandermonde generator matrix** of evaluation points `pts : ι → F`:
`G_{r,i} = (pts i)^r` for `r : Fin k`.  Its `i`-th column is the point
`(1 : pts i : (pts i)² : ⋯ : (pts i)^{k-1})` of the normal rational curve. -/
def vandermondeGen (pts : ι → F) (k : ℕ) : Matrix (Fin k) ι F :=
  fun r i => pts i ^ (r : ℕ)

omit [Fintype ι] in
/-
The `r`-th row of the Vandermonde matrix is the Reed–Solomon evaluation of the
monomial `X^r`.
-/
theorem vandermondeGen_row_eq (pts : ι → F) (k : ℕ) (r : Fin k) :
    vandermondeGen pts k r = rsEval pts (Polynomial.X ^ (r : ℕ)) := by
  ext i; simp +decide [ rsEval_apply, vandermondeGen ] ;

/-
**The row space of the Vandermonde matrix is the Reed–Solomon code.**
`genCode (vandermondeGen pts k) = reedSolomonCode pts k`.
-/
theorem genCode_vandermondeGen_eq (pts : ι → F) (k : ℕ) :
    genCode (vandermondeGen pts k) = reedSolomonCode pts k := by
  refine' le_antisymm _ _;
  · intro x hx;
    obtain ⟨ p, hp, rfl ⟩ := ( Finsupp.mem_span_range_iff_exists_finsupp.mp hx );
    refine' ⟨ ∑ i ∈ p.support, p i • Polynomial.X ^ ( i : ℕ ), _, _ ⟩ <;> simp_all +decide [ Polynomial.degreeLT ];
    · exact fun i hi => Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Fin.is_lt x ] );
    · exact Finset.sum_congr rfl fun _ _ => by congr; ext; simp +decide [ vandermondeGen_row_eq ] ;
  · intro c hc
    obtain ⟨p, hp_deg, hp_eval⟩ := mem_reedSolomonCode_iff.mp hc;
    -- Expand `p` as a sum of monomials.
    have hp_sum : p = ∑ r ∈ Finset.range k, Polynomial.C (p.coeff r) * Polynomial.X ^ r := by
      ext; simp [hp_deg];
      exact fun h => Polynomial.coeff_eq_zero_of_degree_lt <| lt_of_lt_of_le hp_deg <| WithBot.coe_le_coe.mpr h;
    -- Substitute the expansion of `p` into the evaluation.
    have hp_eval_sum : c = ∑ r ∈ Finset.range k, Polynomial.coeff p r • rsEval pts (Polynomial.X ^ r) := by
      convert hp_eval.symm using 1;
      conv_rhs => rw [ hp_sum ];
      simp +decide [ rsEval, funext_iff ];
    rw [hp_eval_sum];
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ ⟨ i, Finset.mem_range.mp hi ⟩, by simp +decide [ vandermondeGen_row_eq ] ⟩ )

/-
**The rows of the Vandermonde matrix are linearly independent** for distinct
evaluation points and `k ≤ n`.
-/
theorem vandermondeGen_rows_li {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk : k ≤ Fintype.card ι) :
    LinearIndependent F (vandermondeGen pts k) := by
  have h_genCode : genCode (vandermondeGen pts k) = reedSolomonCode pts k := by
    convert genCode_vandermondeGen_eq pts k using 1;
  have h_card : Fintype.card (Fin k) = Module.finrank F (Submodule.span F (Set.range (vandermondeGen pts k))) := by
    have h_finrank : Module.finrank F (Submodule.span F (Set.range (vandermondeGen pts k))) = k := by
      convert codeDim_reedSolomonCode hpts hk using 1;
      exact h_genCode ▸ rfl;
    aesop;
  rw [ linearIndependent_iff_card_eq_finrank_span ];
  convert h_card using 1

/-
**The normal rational curve is an arc** (MacWilliams–Sloane, Ch. 11).  For
distinct evaluation points and `1 ≤ k ≤ n`, every `k` columns of the Vandermonde
matrix are linearly independent.
-/
theorem vandermondeGen_isArc {pts : ι → F} {k : ℕ}
    (hpts : Function.Injective pts) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    IsArc (vandermondeGen pts k) := by
  apply (isMDS_genCode_iff_isArc (vandermondeGen_rows_li hpts hkn) hk1).mp;
  exact genCode_vandermondeGen_eq pts k ▸ isMDS_reedSolomonCode hpts hk1 hkn

/-
**A conic is an arc** (the `k = 3` case).  For distinct evaluation points and
`3 ≤ n`, every `3` of the points `t ↦ (1 : t : t²)` are linearly independent.
-/
theorem conic_isArc {pts : ι → F} (hpts : Function.Injective pts)
    (hn : 3 ≤ Fintype.card ι) :
    IsArc (vandermondeGen pts 3) :=
  vandermondeGen_isArc hpts (by norm_num) hn

end CodingTheory