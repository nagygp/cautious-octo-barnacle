import Mathlib

/-!
# Linear codes: minimum weight, minimum distance, and the Singleton bound

This is a *foundational* coding-theory module transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977.

It is intended as the starting point of a coding-theory library built on top of
Mathlib's `hammingDist` / `hammingNorm`.  We fix a finite field `F` and a finite
index set `ι` of coordinate positions, so that an ambient *word space* is
`ι → F` (the book's `F^n`, where `n = #ι`).

A **linear `[n, k]` code** is a `k`-dimensional `F`-subspace `C` of `ι → F`
(MacWilliams–Sloane, Ch. 1, §2).  We package a code simply as a
`Submodule F (ι → F)`; its *length* is `n = #ι` and its *dimension* `k` is
`Module.finrank F C`.

The main results of this module are the two cornerstones of Chapter 1:

* `minDist_eq_minWeight` — for a *linear* code the minimum distance between
  distinct codewords equals the minimum (Hamming) weight of a nonzero codeword
  (MacWilliams–Sloane, Ch. 1, Theorem 2).  This is what makes the minimum
  distance of a linear code computable from a single pass over the codewords.

* `singleton_bound` — the **Singleton bound** `d ≤ n - k + 1` relating the
  minimum distance `d`, the length `n` and the dimension `k`
  (MacWilliams–Sloane, Ch. 1, Theorem 11; Ch. 11, §3).  Codes meeting it with
  equality are the *maximum distance separable* (MDS) codes.
-/

namespace CodingTheory

open scoped Classical

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The **length** of the ambient word space `ι → F`, i.e. the book's `n`. -/
abbrev codeLength (_C : Submodule F (ι → F)) : ℕ := Fintype.card ι

/-- The **dimension** `k` of a linear code `C ⊆ ι → F`. -/
noncomputable abbrev codeDim (C : Submodule F (ι → F)) : ℕ := Module.finrank F C

/-- The set of Hamming weights of nonzero codewords of `C`. -/
def weightSet (C : Submodule F (ι → F)) : Set ℕ :=
  { w | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = w }

/-- The set of Hamming distances between distinct codewords of `C`. -/
def distSet (C : Submodule F (ι → F)) : Set ℕ :=
  { d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d }

/-- The **minimum weight** of a code: the least Hamming weight of a nonzero
codeword (and `0` by convention for the zero code). -/
noncomputable def minWeight (C : Submodule F (ι → F)) : ℕ := sInf (weightSet C)

/-- The **minimum distance** of a code: the least Hamming distance between two
distinct codewords (and `0` by convention if there are none). -/
noncomputable def minDist (C : Submodule F (ι → F)) : ℕ := sInf (distSet C)

/--
The minimum weight is a lower bound for the weight of every nonzero codeword.
-/
theorem minWeight_le {C : Submodule F (ι → F)} {c : ι → F} (hc : c ∈ C) (hc0 : c ≠ 0) :
    minWeight C ≤ hammingNorm c := by
  exact Nat.sInf_le ⟨ c, hc, hc0, rfl ⟩

/--
For a nonzero code the minimum weight is attained by some nonzero codeword.
-/
theorem exists_eq_minWeight {C : Submodule F (ι → F)} (hC : C ≠ ⊥) :
    ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = minWeight C := by
  exact Nat.sInf_mem ( show { v | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = v }.Nonempty from by
                        exact Exists.elim ( Submodule.ne_bot_iff _ |>.1 hC ) fun x hx => ⟨ _, ⟨ x, hx.1, hx.2, rfl ⟩ ⟩ ) |> fun ⟨ x, hx ⟩ => ⟨ x, hx ⟩

/--
For a nonzero code the minimum weight is strictly positive.
-/
theorem minWeight_pos {C : Submodule F (ι → F)} (hC : C ≠ ⊥) : 0 < minWeight C := by
  -- By `exists_eq_minWeight hC` obtain `c ∈ C`, `c ≠ 0`, `hammingNorm c = minWeight C`.
  obtain ⟨c, hc, hc0, h_eq⟩ := exists_eq_minWeight hC;
  -- Since `c ≠ 0` and `hammingNorm c ≠ 0` (by `hammingNorm_pos_iff` / `hammingNorm_eq_zero`, since `c ≠ 0`), we have `minWeight C = hammingNorm c > 0`.
  exact h_eq ▸ hammingNorm_pos_iff.2 hc0;

/--
For a nonzero code the minimum weight is at most the length `n`.
-/
theorem minWeight_le_length {C : Submodule F (ι → F)} (hC : C ≠ ⊥) :
    minWeight C ≤ codeLength C := by
  obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := exists_eq_minWeight hC;
  exact hc₃ ▸ Finset.card_le_univ _

/--
**MacWilliams–Sloane, Ch. 1, Theorem 2.** For a *linear* code the minimum
distance equals the minimum weight: the distance sets and weight sets coincide,
because `d(x,y) = wt(x - y)` and `x - y` ranges over the nonzero codewords as
`x ≠ y` range over the code.
-/
theorem minDist_eq_minWeight (C : Submodule F (ι → F)) : minDist C = minWeight C := by
  by_cases h : C = ⊥ <;> simp_all +decide [ minDist, minWeight ];
  · unfold distSet weightSet; aesop;
  · congr with x;
    constructor <;> intro hx;
    · obtain ⟨ c, hc, d, hd, hcd, rfl ⟩ := hx;
      exact ⟨ c - d, C.sub_mem hc hd, sub_ne_zero.mpr hcd, by simp +decide [ hammingDist_eq_hammingNorm ] ⟩;
    · obtain ⟨ c, hc, hc0, rfl ⟩ := hx; exact ⟨ c, hc, 0, C.zero_mem, hc0, by simp +decide [ hammingDist_eq_hammingNorm ] ⟩ ;

/--
Core step of the Singleton bound: deleting a set `Tᶜ` of fewer than `d`
coordinates leaves an injection of `C` into `T → F`, so `k ≤ #T`.  Indeed if two
codewords agree on `T` their difference is a codeword supported on `Tᶜ`, hence of
weight `< d`, hence zero.
-/
theorem finrank_le_of_card_compl_lt_minWeight (C : Submodule F (ι → F)) (T : Finset ι)
    (hT : Tᶜ.card < minWeight C) :
    Module.finrank F C ≤ T.card := by
  have h_inj : Function.Injective (fun c : C => fun t : T => c.val t) := by
    intro c1 c2 h_eq
    by_contra h_neq
    have h_diff : ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ Tᶜ.card := by
      refine' ⟨ c1 - c2, _, _, _ ⟩ <;> simp_all +decide [ funext_iff, Submodule.sub_mem_iff_left ];
      · exact not_forall.mp fun h => h_neq <| Subtype.ext <| funext fun x => sub_eq_zero.mp <| h x;
      · exact Finset.card_le_card fun x hx => by aesop;
    obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := h_diff; linarith [ minWeight_le hc₁ hc₂ ] ;
  have := LinearMap.finrank_le_finrank_of_injective ( show Function.Injective ( show C →ₗ[F] ( T → F ) from { toFun := fun c => fun t => c.val t, map_add' := fun c d => by ext; simp +decide, map_smul' := fun c d => by ext; simp +decide } ) from h_inj ) ; aesop;

/--
**MacWilliams–Sloane, Ch. 1, Theorem 11: the Singleton bound.** For a
nonzero linear `[n, k]` code with minimum distance `d`, one has `d ≤ n - k + 1`.
-/
theorem singleton_bound (C : Submodule F (ι → F)) (hC : C ≠ ⊥) :
    minWeight C ≤ codeLength C - codeDim C + 1 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, T.card = codeLength C - (minWeight C - 1) := by
    have := Finset.exists_subset_card_eq ( show codeLength C - ( minWeight C - 1 ) ≤ Finset.card ( Finset.univ : Finset ι ) from ?_ ) ; aesop;
    exact Nat.sub_le _ _;
  have := finrank_le_of_card_compl_lt_minWeight C T ?_;
  · rcases n : minWeight C with ( _ | _ | n ) <;> simp_all +decide;
    exact lt_tsub_iff_left.mpr ( by linarith! [ Nat.sub_add_cancel ( show codeLength C ≥ ( ‹_› + 1 ) from le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop_cat ) ) ) ] );
  · have hT_compl : Tᶜ.card = codeLength C - T.card := by
      simp +decide [ Finset.card_compl ];
    rw [ hT_compl, hT, tsub_lt_iff_left ];
    · linarith [ Nat.sub_add_cancel ( show 1 ≤ minWeight C from minWeight_pos hC ), Nat.sub_add_cancel ( show minWeight C - 1 ≤ codeLength C from Nat.sub_le_of_le_add <| by linarith [ minWeight_le_length hC ] ) ];
    · exact Nat.sub_le _ _

/-- The Singleton bound in terms of the minimum *distance* (equal to the minimum
weight by `minDist_eq_minWeight`). -/
theorem singleton_bound_dist (C : Submodule F (ι → F)) (hC : C ≠ ⊥) :
    minDist C ≤ codeLength C - codeDim C + 1 := by
  rw [minDist_eq_minWeight]
  exact singleton_bound C hC

end CodingTheory