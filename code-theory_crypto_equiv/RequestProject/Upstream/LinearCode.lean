/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import Mathlib

/-!
# Linear codes: minimum weight, minimum distance, and the Singleton bound

> Intended Mathlib target path: `Mathlib/InformationTheory/LinearCode.lean`
> (it builds directly on `Mathlib/InformationTheory/Hamming.lean`).
>
> For the actual pull request the blanket `import Mathlib` above should be
> minimised (e.g. with `shake`) to the relevant modules, which are essentially
> `Mathlib.InformationTheory.Hamming`, `Mathlib.LinearAlgebra.Finrank` /
> `Mathlib.LinearAlgebra.Dimension.*`, and `Mathlib.Data.Nat.Lattice`.

This file develops the basic theory of linear error-correcting codes on top of
Mathlib's existing Hamming metric (`hammingDist` / `hammingNorm`,
`Mathlib.InformationTheory.Hamming`).

## Design

We fix a field `F` and a finite index type `ι` of coordinate positions, so that
the ambient *word space* is `ι → F` (classically written `F^n` with `n = #ι`).
A **linear code** is then a subspace of `ι → F`, packaged as the reducible
abbreviation

* `LinearCode ι F := Submodule F (ι → F)`.

Using an abbreviation rather than a fresh structure means that the full
`Submodule` API (membership, `add_mem`, `smul_mem`, `finrank`, lattice
operations, …) is available on a `LinearCode` with no glue code, while the
abbreviation still provides a meaningful name and a home for dot-notation such
as `C.minDist`.

## Main definitions

* `LinearCode ι F` — a linear code: a subspace of `ι → F`.
* `LinearCode.length C` — the code length `n = #ι`.
* `LinearCode.dim C` — the dimension `k = finrank F C`.
* `LinearCode.weightSet C` / `LinearCode.distSet C` — the set of Hamming weights
  of nonzero codewords, resp. of Hamming distances between distinct codewords.
* `LinearCode.minWeight C` / `LinearCode.minDist C` — the minimum weight and
  minimum distance (`0` by convention for the zero code / a code with `< 2`
  codewords).
* `LinearCode.IsMDS C` — `C` is maximum distance separable: it is nonzero and
  meets the Singleton bound with equality.

## Main results

* `LinearCode.minDist_eq_minWeight` — for a *linear* code the minimum distance
  equals the minimum weight (MacWilliams–Sloane, Ch. 1, Thm 2). This is the key
  fact that makes the minimum distance of a linear code computable from a single
  pass over the codewords, and is the most reusable standalone contribution
  here.
* `LinearCode.singleton_bound` / `LinearCode.singleton_bound_dist` — the
  **Singleton bound** `d ≤ n - k + 1` (MacWilliams–Sloane, Ch. 1, Thm 11).
* `LinearCode.IsMDS.minDist_eq` — the defining equality of an MDS code.

Supporting API: `minWeight_le`, `exists_eq_minWeight`, `minWeight_pos`,
`minWeight_le_length`, `minDist_le`, `exists_eq_minDist`, and the puncturing
lemma `finrank_le_of_card_compl_lt_minWeight`.

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 1, Thm 2 and Thm 11.)

## Tags

linear code, coding theory, Hamming distance, Hamming weight, minimum distance,
minimum weight, Singleton bound, MDS, maximum distance separable
-/

open scoped Classical

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- A **linear code** of length `#ι` over the field `F`: a subspace of the word
space `ι → F`. This is a reducible abbreviation for `Submodule F (ι → F)`, so the
whole `Submodule` API is available directly on a `LinearCode`. -/
abbrev LinearCode (ι F : Type*) [Fintype ι] [Field F] : Type _ := Submodule F (ι → F)

namespace LinearCode

/-- The **length** of a code, i.e. the number `n = #ι` of coordinate positions. -/
def length (_C : LinearCode ι F) : ℕ := Fintype.card ι

/-- The **dimension** `k` of a linear code, i.e. its `F`-rank as a subspace. -/
noncomputable def dim (C : LinearCode ι F) : ℕ := Module.finrank F C

/-- The set of Hamming weights of nonzero codewords of `C`. -/
def weightSet (C : LinearCode ι F) : Set ℕ :=
  { w | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = w }

/-- The set of Hamming distances between distinct codewords of `C`. -/
def distSet (C : LinearCode ι F) : Set ℕ :=
  { d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d }

/-- The **minimum weight** of a code: the least Hamming weight of a nonzero
codeword (and `0` by convention for the zero code). -/
noncomputable def minWeight (C : LinearCode ι F) : ℕ := sInf (weightSet C)

/-- The **minimum distance** of a code: the least Hamming distance between two
distinct codewords (and `0` by convention when there are fewer than two
codewords). -/
noncomputable def minDist (C : LinearCode ι F) : ℕ := sInf (distSet C)

@[simp] theorem length_eq_card (C : LinearCode ι F) : C.length = Fintype.card ι := rfl

theorem dim_eq_finrank (C : LinearCode ι F) : C.dim = Module.finrank F C := rfl

/-- The minimum weight is a lower bound for the weight of every nonzero
codeword. -/
theorem minWeight_le {C : LinearCode ι F} {c : ι → F} (hc : c ∈ C) (hc0 : c ≠ 0) :
    minWeight C ≤ hammingNorm c :=
  Nat.sInf_le ⟨c, hc, hc0, rfl⟩

/-- For a nonzero code the minimum weight is attained by some nonzero codeword. -/
theorem exists_eq_minWeight {C : LinearCode ι F} (hC : C ≠ ⊥) :
    ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = minWeight C :=
  Nat.sInf_mem (show {v | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = v}.Nonempty from by
    exact Exists.elim (Submodule.ne_bot_iff _ |>.1 hC) fun x hx => ⟨_, ⟨x, hx.1, hx.2, rfl⟩⟩)
    |> fun ⟨x, hx⟩ => ⟨x, hx⟩

/-- For a nonzero code the minimum weight is strictly positive. -/
theorem minWeight_pos {C : LinearCode ι F} (hC : C ≠ ⊥) : 0 < minWeight C := by
  obtain ⟨c, hc, hc0, h_eq⟩ := exists_eq_minWeight hC
  exact h_eq ▸ hammingNorm_pos_iff.2 hc0

/-- For a nonzero code the minimum weight is at most the length `n`. -/
theorem minWeight_le_length {C : LinearCode ι F} (hC : C ≠ ⊥) :
    minWeight C ≤ C.length := by
  obtain ⟨c, _, _, hc₃⟩ := exists_eq_minWeight hC
  exact hc₃ ▸ Finset.card_le_univ _

/-- The minimum distance is a lower bound for the distance between any two
distinct codewords. -/
theorem minDist_le {C : LinearCode ι F} {x y : ι → F} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x ≠ y) : minDist C ≤ hammingDist x y :=
  Nat.sInf_le ⟨x, hx, y, hy, hxy, rfl⟩

/--
**MacWilliams–Sloane, Ch. 1, Theorem 2.** For a *linear* code the minimum
distance equals the minimum weight: the distance set and weight set coincide,
because `d(x, y) = wt(x - y)` and `x - y` ranges over the nonzero codewords as
`x ≠ y` range over the code.

This is the cornerstone that makes the minimum distance of a linear code
computable from a single pass over the codewords.
-/
theorem minDist_eq_minWeight (C : LinearCode ι F) : minDist C = minWeight C := by
  by_cases h : C = ⊥ <;> simp_all +decide [minDist, minWeight]
  · unfold distSet weightSet; aesop
  · congr with x
    constructor <;> intro hx
    · obtain ⟨c, hc, d, hd, hcd, rfl⟩ := hx
      exact ⟨c - d, C.sub_mem hc hd, sub_ne_zero.mpr hcd, by
        simp +decide [hammingDist_eq_hammingNorm]⟩
    · obtain ⟨c, hc, hc0, rfl⟩ := hx
      exact ⟨c, hc, 0, C.zero_mem, hc0, by simp +decide [hammingDist_eq_hammingNorm]⟩

/-- For a nonzero code the minimum distance is attained by two distinct
codewords. -/
theorem exists_eq_minDist {C : LinearCode ι F} (hC : C ≠ ⊥) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = minDist C := by
  obtain ⟨c, hc, hc0, hcw⟩ := exists_eq_minWeight hC
  refine ⟨c, hc, 0, C.zero_mem, hc0, ?_⟩
  rw [minDist_eq_minWeight, ← hcw, hammingDist_eq_hammingNorm]; simp

/--
Core step of the Singleton bound: deleting a set `Tᶜ` of fewer than `d`
coordinates leaves an injection of `C` into `T → F`, so `k ≤ #T`. Indeed if two
codewords agree on `T` their difference is a codeword supported on `Tᶜ`, hence of
weight `< d`, hence zero.
-/
theorem finrank_le_of_card_compl_lt_minWeight (C : LinearCode ι F) (T : Finset ι)
    (hT : Tᶜ.card < minWeight C) :
    Module.finrank F C ≤ T.card := by
  have h_inj : Function.Injective (fun c : C => fun t : T => c.val t) := by
    intro c1 c2 h_eq
    by_contra h_neq
    have h_diff : ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ Tᶜ.card := by
      refine' ⟨c1 - c2, _, _, _⟩ <;>
        simp_all +decide [funext_iff, Submodule.sub_mem_iff_left]
      · exact not_forall.mp fun h => h_neq <| Subtype.ext <| funext fun x => sub_eq_zero.mp <| h x
      · exact Finset.card_le_card fun x hx => by aesop
    obtain ⟨c, hc₁, hc₂, hc₃⟩ := h_diff; linarith [minWeight_le hc₁ hc₂]
  have := LinearMap.finrank_le_finrank_of_injective
    (show Function.Injective (show C →ₗ[F] (T → F) from
      { toFun := fun c => fun t => c.val t
        map_add' := fun c d => by ext; simp +decide
        map_smul' := fun c d => by ext; simp +decide }) from h_inj)
  aesop

/--
**MacWilliams–Sloane, Ch. 1, Theorem 11: the Singleton bound.** For a nonzero
linear `[n, k]` code with minimum weight `d`, one has `d ≤ n - k + 1`.
-/
theorem singleton_bound (C : LinearCode ι F) (hC : C ≠ ⊥) :
    minWeight C ≤ C.length - C.dim + 1 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, T.card = C.length - (minWeight C - 1) := by
    have := Finset.exists_subset_card_eq
      (show C.length - (minWeight C - 1) ≤ Finset.card (Finset.univ : Finset ι) from ?_)
    · aesop
    · exact Nat.sub_le _ _
  have := finrank_le_of_card_compl_lt_minWeight C T ?_
  · rcases n : minWeight C with (_ | _ | n) <;> simp_all +decide [dim, length]
    exact lt_tsub_iff_left.mpr (by
      linarith! [Nat.sub_add_cancel
        (show Fintype.card ι ≥ (‹_› + 1) from le_of_lt
          (Nat.lt_of_sub_ne_zero (by aesop_cat)))])
  · have hT_compl : Tᶜ.card = C.length - T.card := by
      simp +decide [Finset.card_compl, length]
    rw [hT_compl, hT, tsub_lt_iff_left]
    · linarith [Nat.sub_add_cancel (show 1 ≤ minWeight C from minWeight_pos hC),
        Nat.sub_add_cancel (show minWeight C - 1 ≤ C.length from
          Nat.sub_le_of_le_add <| by linarith [minWeight_le_length hC])]
    · exact Nat.sub_le _ _

/-- The Singleton bound stated in terms of the minimum *distance* (equal to the
minimum weight by `minDist_eq_minWeight`). -/
theorem singleton_bound_dist (C : LinearCode ι F) (hC : C ≠ ⊥) :
    minDist C ≤ C.length - C.dim + 1 := by
  rw [minDist_eq_minWeight]; exact singleton_bound C hC

/-- A linear code is **maximum distance separable** (MDS) when it is nonzero and
meets the Singleton bound with equality: `d = n - k + 1`. -/
def IsMDS (C : LinearCode ι F) : Prop :=
  C ≠ ⊥ ∧ minDist C = C.length - C.dim + 1

/-- An MDS code is nonzero. -/
theorem IsMDS.ne_bot {C : LinearCode ι F} (h : IsMDS C) : C ≠ ⊥ := h.1

/-- The defining equality of an MDS code: its minimum distance meets the
Singleton bound. -/
theorem IsMDS.minDist_eq {C : LinearCode ι F} (h : IsMDS C) :
    minDist C = C.length - C.dim + 1 := h.2

/-- An MDS code can equivalently be described through its minimum *weight*. -/
theorem isMDS_iff_minWeight {C : LinearCode ι F} :
    IsMDS C ↔ C ≠ ⊥ ∧ minWeight C = C.length - C.dim + 1 := by
  unfold IsMDS; rw [minDist_eq_minWeight]

end LinearCode
