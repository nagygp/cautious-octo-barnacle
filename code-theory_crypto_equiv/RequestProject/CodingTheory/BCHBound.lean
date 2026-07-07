import Mathlib

/-!
# The BCH bound on the minimum distance of a code

This module continues the coding-theory development (`CODING_THEORY_DIRECTIONS.md`,
item 13: *BCH and cyclic codes*) by proving the **BCH bound**, the classical lower
bound on the minimum distance of a (cyclic / BCH) code in terms of a run of
consecutive zero "syndromes".

The result is stated in its essential, code-family-agnostic form via the
Vandermonde determinant. Fix distinct nonzero field elements `x₀, …, x_{n-1}`
(for a genuine BCH code these are the powers `α^i` of a primitive `n`-th root of
unity). For a word `c : Fin n → F`, the *syndrome* at exponent `e` is
`S_e(c) = ∑_i c_i · x_iᵉ`. The BCH bound says: if `δ − 1` **consecutive**
syndromes `S_b, S_{b+1}, …, S_{b+δ−2}` all vanish and `c ≠ 0`, then the Hamming
weight of `c` is at least `δ`.

The proof is the standard Vandermonde / square-system argument: restricting to the
support of `c`, the consecutive syndrome equations form a square Vandermonde-type
linear system with nonzero determinant, whose only solution is the zero vector —
contradicting `c ≠ 0` on its support.

## Main results

* `bch_square_vanishing` — the square Vandermonde core: `m` distinct nonzero nodes
  and `m` consecutive vanishing syndromes force the coefficient vector to vanish.
* `bch_bound` — the BCH bound: `δ − 1` consecutive vanishing syndromes of a
  nonzero word force Hamming weight `≥ δ`.
-/

open Finset BigOperators Matrix

namespace CodingTheory
namespace BCH

variable {F : Type*} [Field F]

/-
**Square Vandermonde core of the BCH bound.** Given `m` distinct nonzero
nodes `y₀, …, y_{m-1}` and a coefficient vector `c : Fin m → F` whose `m`
consecutive syndromes `∑_i c_i · y_i^{b+l}` (for `l = 0, …, m-1`) all vanish, the
coefficient vector must be zero. (This is the statement that a square Vandermonde
system with distinct nonzero nodes is nonsingular.)
-/
theorem bch_square_vanishing {m : ℕ} (y : Fin m → F)
    (hy : Function.Injective y) (hy0 : ∀ i, y i ≠ 0) (c : Fin m → F) (b : ℕ)
    (hsyn : ∀ l : Fin m, ∑ i, c i * (y i) ^ (b + (l : ℕ)) = 0) :
    c = 0 := by
  -- Consider the square matrix $M : \text{Matrix} (\text{Fin} m) (\text{Fin} m) F$ defined by $M l i = (y i)^{b+l}$.
  set M : Matrix (Fin m) (Fin m) F := fun l i => (y i) ^ (b + l.val);
  -- The determinant of $M$ is non-zero because $y$ is injective and non-zero.
  have h_det_nonzero : Matrix.det M ≠ 0 := by
    -- The determinant of $M$ is non-zero because $y$ is injective and non-zero. We can use the fact that the determinant of a Vandermonde matrix is non-zero.
    have h_det_nonzero : Matrix.det M = (∏ i, (y i) ^ b) * Matrix.det (Matrix.vandermonde y) := by
      convert Matrix.det_transpose ( Matrix.diagonal ( fun i => y i ^ b ) * Matrix.vandermonde y ) using 1;
      · congr ; ext i j
        simp [M, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vandermonde_apply, pow_add]
      · simp +decide [ Matrix.det_mul, Matrix.det_diagonal ];
    simp_all +decide [ Finset.prod_eq_zero_iff, pow_eq_zero_iff' ];
    grind +suggestions;
  have h_c_zero : M.mulVec c = 0 := by
    exact funext fun l => by simpa [ Matrix.mulVec, dotProduct, mul_comm ] using hsyn l;
  exact Matrix.eq_zero_of_mulVec_eq_zero h_det_nonzero h_c_zero

/-
**The BCH bound.** Let `x₀, …, x_{n-1}` be distinct nonzero field elements
(e.g. the powers of a primitive `n`-th root of unity). If a nonzero word
`c : Fin n → F` has `δ − 1` consecutive vanishing syndromes
`∑_i c_i · x_i^{b+l} = 0` for `l = 0, …, δ − 2`, then its Hamming weight is at
least `δ`.
-/
theorem bch_bound [DecidableEq F] {n : ℕ} (x : Fin n → F)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0)
    (c : Fin n → F) (hc : c ≠ 0) (b δ : ℕ)
    (hsyn : ∀ l : ℕ, l < δ - 1 → ∑ i, c i * (x i) ^ (b + l) = 0) :
    δ ≤ hammingNorm c := by
  contrapose! hc with h;
  -- Let `S := Finset.univ.filter (fun i => c i ≠ 0)` be the support. By definition `hammingNorm c = S.card`.
  set S : Finset (Fin n) := Finset.univ.filter (fun i => c i ≠ 0)
  have hS_card : S.card < δ := by
    convert h using 1;
  -- Apply `bch_square_vanishing` to conclude `c' = 0`.
  have hc'_zero : ∀ k : Fin S.card, c (S.orderEmbOfFin rfl k) = 0 := by
    have hc'_zero : ∀ l : Fin S.card, ∑ k : Fin S.card, c (S.orderEmbOfFin rfl k) * (x (S.orderEmbOfFin rfl k)) ^ (b + l) = 0 := by
      intro l
      have hsum_eq : ∑ i, c i * x i ^ (b + l) = ∑ i ∈ S, c i * x i ^ (b + l) := by
        rw [ Finset.sum_filter_of_ne ] ; aesop;
      convert hsum_eq.symm.trans ( hsyn l ( Nat.lt_of_lt_of_le l.2 ( Nat.le_sub_one_of_lt hS_card ) ) ) using 1;
      refine' Finset.sum_bij ( fun i _ => S.orderEmbOfFin rfl i ) _ _ _ _ <;> simp +decide;
      intro i hi; have := Finset.mem_image.mp ( show i ∈ Finset.image ( fun a : Fin #S => S.orderEmbOfFin rfl a ) Finset.univ from by aesop ) ; aesop;
    convert bch_square_vanishing ( fun k => x ( S.orderEmbOfFin rfl k ) ) ( fun i j hij => ?_ ) ( fun k => hx0 _ ) ( fun k => c ( S.orderEmbOfFin rfl k ) ) b hc'_zero using 1;
    · exact ⟨ fun h => funext h, fun h => fun k => congr_fun h k ⟩;
    · simpa [ Fin.ext_iff ] using hx hij;
  contrapose! hc'_zero;
  exact ⟨ ⟨ 0, Finset.card_pos.mpr ⟨ Classical.choose ( Function.ne_iff.mp hc'_zero ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec ( Function.ne_iff.mp hc'_zero ) ⟩ ⟩ ⟩, Finset.mem_filter.mp ( Finset.orderEmbOfFin_mem S rfl ⟨ 0, Finset.card_pos.mpr ⟨ Classical.choose ( Function.ne_iff.mp hc'_zero ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec ( Function.ne_iff.mp hc'_zero ) ⟩ ⟩ ⟩ ) |>.2 ⟩

end BCH
end CodingTheory