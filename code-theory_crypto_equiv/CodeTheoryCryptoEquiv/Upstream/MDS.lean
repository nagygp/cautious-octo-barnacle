/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import CodeTheoryCryptoEquiv.Upstream.GeneratorParityCheck

/-!
# Maximum distance separable (MDS) codes and MDS duality

> Intended Mathlib target path: this extends the linear-code file
> (`Mathlib/InformationTheory/LinearCode.lean`, cf. `Upstream/LinearCode.lean`,
> `Upstream/Dual.lean`, `Upstream/GeneratorParityCheck.lean`).
>
> For the actual pull request the blanket `import Mathlib` pulled in via
> `Upstream.GeneratorParityCheck` should be minimised (e.g. with `shake`).

This file proves the headline structural theorem about **maximum distance
separable** (MDS) codes: *the dual of an MDS code is again MDS*
(MacWilliams–Sloane, Ch. 11, Theorem 2).  The `IsMDS` predicate itself is defined
in `Upstream/LinearCode.lean`.

## The information-set picture

The proof runs through the *information-set* characterization of the minimum
distance.  For a `k`-subset `S` of coordinates, `vanishingOn S` is the coordinate
subspace of words that vanish on `S`.  A code `C` of dimension `k` is MDS exactly
when **every** `k`-subset `S` is an *information set*, i.e. `Disjoint C
(vanishingOn S)`: no nonzero codeword vanishes on a full set of `k` coordinates.

Duality is then transparent: `vanishingOn S` and `vanishingOn Sᶜ` are dual
coordinate subspaces (`dual_vanishingOn`), and disjointness with complementary
dimensions dualizes (`dual_disjoint`), so `S` is an information set for `C` iff
`Sᶜ` is an information set for `Cᗮ`.

## Main definitions

* `LinearCode.vanishingOn S` — the coordinate subspace `{x | ∀ i ∈ S, x i = 0}`.

## Main results

* `LinearCode.dual_vanishingOn` — `(vanishingOn S)ᗮ = vanishingOn Sᶜ`.
* `LinearCode.dim_vanishingOn` — `dim (vanishingOn S) = n - #S`.
* `LinearCode.dual_disjoint` — disjointness with complementary dimensions
  dualizes.
* `LinearCode.isMDS_iff_forall_disjoint_vanishing` — the information-set
  characterization.
* `LinearCode.IsMDS.dual` — **MacWilliams–Sloane, Ch. 11, Theorem 2**: the dual
  of an MDS code (that is not the whole space) is MDS.
* `LinearCode.isMDS_dual_iff` — `C` is MDS iff `Cᗮ` is MDS, for `⊥ ≠ C ≠ ⊤`.

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 11, §3.)

## Tags

linear code, MDS, maximum distance separable, dual code, information set,
Singleton bound
-/

open scoped Classical

namespace LinearCode

open Matrix

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The dual of a sup is the inf of the duals: `(C ⊔ D)ᗮ = Cᗮ ⊓ Dᗮ`. -/
theorem dual_sup (C D : LinearCode ι F) :
    dual (C ⊔ D) = dual C ⊓ dual D := by
  apply le_antisymm
  · exact le_inf (dual_antitone le_sup_left) (dual_antitone le_sup_right)
  · rw [SetLike.le_def]
    rintro y ⟨hyC, hyD⟩
    simp only [SetLike.mem_coe, mem_dual_iff] at hyC hyD ⊢
    intro x hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have e : ∀ i, (a + b) i * y i = a i * y i + b i * y i := fun i => by
      rw [Pi.add_apply]; ring
    simp only [e, Finset.sum_add_distrib, hyC a ha, hyD b hb, add_zero]

/-- The coordinate subspace of words that **vanish on** a finite set `S` of
positions: `{x | ∀ i ∈ S, x i = 0}` (equivalently, words supported on `Sᶜ`). -/
def vanishingOn (S : Finset ι) : LinearCode ι F :=
  LinearMap.ker (LinearMap.pi (fun i : S => LinearMap.proj (i : ι)) :
    (ι → F) →ₗ[F] (S → F))

/-- Membership in `vanishingOn S`: a word lies in it iff it vanishes on `S`. -/
@[simp] theorem mem_vanishingOn_iff {S : Finset ι} {x : ι → F} :
    x ∈ vanishingOn S ↔ ∀ i ∈ S, x i = 0 := by
  unfold vanishingOn
  rw [LinearMap.mem_ker, funext_iff]
  constructor
  · intro h i hi; simpa using h ⟨i, hi⟩
  · intro h j; simpa using h j.1 j.2

/-
The dimension of `vanishingOn S` is `n - #S`: the free coordinates are those
outside `S`.
-/
theorem dim_vanishingOn (S : Finset ι) :
    (vanishingOn (F := F) S).dim = (vanishingOn (F := F) S).length - S.card := by
  rw [ eq_tsub_iff_add_eq_of_le ];
  · convert LinearMap.finrank_range_add_finrank_ker ( LinearMap.pi ( fun i : S => LinearMap.proj ( i : ι ) ) : ( ι → F ) →ₗ[F] ( S → F ) ) using 1;
    · convert add_comm _ _;
      rw [ LinearMap.range_eq_top.mpr ] <;> norm_num;
      intro x; use fun i => if hi : i ∈ S then x ⟨ i, hi ⟩ else 0; aesop;
    · simp +decide [ LinearCode.length ];
  · exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide [ LinearCode.length ] )

/-
The dual of a coordinate subspace is the complementary coordinate subspace:
`(vanishingOn S)ᗮ = vanishingOn Sᶜ`.
-/
theorem dual_vanishingOn (S : Finset ι) :
    dual (vanishingOn (F := F) S) = vanishingOn (F := F) Sᶜ := by
  ext y
  simp [LinearCode.mem_dual_iff, LinearCode.mem_vanishingOn_iff, Finset.mem_compl];
  constructor <;> intro h;
  · intro i hi; specialize h ( fun j => if j = i then 1 else 0 ) ; aesop;
  · exact fun x hx => Finset.sum_eq_zero fun i hi => by by_cases hi' : i ∈ S <;> simp +decide [ hx i, h i, hi' ] ;

/-
**Disjointness with complementary dimensions dualizes.** If `C` and `D` are
disjoint with dimensions summing to the length, then their duals are disjoint.
-/
theorem dual_disjoint {C D : LinearCode ι F} (hCD : Disjoint C D)
    (hdim : C.dim + D.dim = C.length) :
    Disjoint (dual C) (dual D) := by
  refine' disjoint_iff.mpr _;
  convert Submodule.eq_bot_iff _ |>.2 _;
  intro x hx; have := dual_sup C D; simp_all +decide [ SetLike.ext_iff ] ;
  have h_top : C ⊔ D = ⊤ := by
    refine' Submodule.eq_top_of_finrank_eq _;
    have := Submodule.finrank_sup_add_finrank_inf_eq C D; simp_all +decide [ LinearCode.dim ] ;
    rw [ ← this, show C ⊓ D = ⊥ from hCD.eq_bot ] ; simp +decide;
  specialize this x; aesop;

/-
The existence of a low-weight nonzero codeword (weight `≤ n - k`) is the same
as the failure of some `k`-subset to be an information set.
-/
theorem exists_lowWeight_iff_exists_vanishing {C : LinearCode ι F} :
    (∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ C.length - C.dim) ↔
      ∃ S : Finset ι, S.card = C.dim ∧ ¬ Disjoint C (vanishingOn S) := by
  refine ⟨ fun ⟨ c, hc, hc', hc'' ⟩ => ?_, fun ⟨ S, hS, hS' ⟩ => ?_ ⟩;
  · -- Let $Z$ be the zero set of $c$, i.e., $Z = \{i \in \text{univ} \mid c(i) = 0\}$.
    set Z := Finset.univ.filter (fun i => c i = 0) with hZ_def;
    -- Since $|Z| \geq k$, we can choose a subset $S \subseteq Z$ with $|S| = k$.
    obtain ⟨S, hS⟩ : ∃ S : Finset ι, S ⊆ Z ∧ S.card = C.dim := by
      refine' Finset.exists_subset_card_eq _;
      have hZ_card : Z.card = Fintype.card ι - hammingNorm c := by
        simp +decide [ hammingNorm, Finset.filter_not, Finset.card_sdiff ];
        rw [ Nat.sub_sub_self ( Finset.card_le_univ _ ) ];
      simp_all +decide [ LinearCode.length ];
      exact le_tsub_of_add_le_left ( by linarith [ Nat.sub_add_cancel ( show C.dim ≤ Fintype.card ι from le_trans ( Submodule.finrank_le _ ) ( by simp +decide ) ) ] );
    refine' ⟨ S, hS.2, _ ⟩;
    rw [ Submodule.disjoint_def ];
    simp_all +decide [ Finset.subset_iff ];
    exact ⟨ c, hc, hS.1, hc' ⟩;
  · simp_all +decide [ Submodule.disjoint_def ];
    obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := hS';
    refine' ⟨ c, hc₁, hc₃, _ ⟩;
    exact le_trans ( Finset.card_le_card ( show Finset.univ.filter ( fun i => c i ≠ 0 ) ⊆ Finset.univ \ S from fun i hi => by aesop ) ) ( by simp +decide [ Finset.card_sdiff, * ] )

/-
**The information-set characterization of MDS codes.** A nonzero code `C` of
dimension `k` is MDS iff every `k`-subset of coordinates is an information set,
i.e. `C` meets each `vanishingOn S` trivially.
-/
theorem isMDS_iff_forall_disjoint_vanishing {C : LinearCode ι F} (hC : C ≠ ⊥) :
    IsMDS C ↔ ∀ S : Finset ι, S.card = C.dim → Disjoint C (vanishingOn S) := by
  constructor;
  · intro hMDS S hS_card
    have h_minWeight : C.minWeight = C.length - C.dim + 1 := by
      exact hMDS.2 ▸ LinearCode.minDist_eq_minWeight C ▸ rfl;
    refine' disjoint_iff_inf_le.mpr _;
    intro x hx
    by_contra hx_nonzero
    have h_weight : hammingNorm x ≤ C.length - C.dim := by
      have h_weight : hammingNorm x ≤ Finset.card (Finset.univ \ S) := by
        exact Finset.card_le_card fun i hi => by aesop;
      simp_all +decide [ Finset.card_sdiff ];
    exact absurd h_minWeight ( ne_of_lt ( lt_of_le_of_lt ( LinearCode.minWeight_le hx.1 hx_nonzero ) ( Nat.lt_succ_of_le h_weight ) ) );
  · intro h;
    refine' ⟨ hC, le_antisymm _ _ ⟩;
    · exact singleton_bound_dist C hC;
    · contrapose! h;
      -- By `exists_lowWeight_iff_exists_vanishing`, there exists a nonzero codeword `c` with `hammingNorm c ≤ C.length - C.dim`.
      obtain ⟨c, hc⟩ : ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ C.length - C.dim := by
        obtain ⟨ c, hc ⟩ := exists_eq_minWeight hC;
        exact ⟨ c, hc.1, hc.2.1, hc.2.2.symm ▸ Nat.le_of_lt_succ ( by linarith [ LinearCode.minDist_eq_minWeight C ] ) ⟩;
      exact exists_lowWeight_iff_exists_vanishing.mp ⟨ c, hc ⟩

/-
**MacWilliams–Sloane, Ch. 11, Theorem 2.** The dual of an MDS code that is
not the whole space is again MDS.
-/
theorem IsMDS.dual {C : LinearCode ι F} (h : IsMDS C)
    (hC : LinearCode.dual C ≠ ⊥) : IsMDS (LinearCode.dual C) := by
  rw [ isMDS_iff_forall_disjoint_vanishing ] at *;
  · intro S hS_card
    have hS_compl : Sᶜ.card = C.dim := by
      have := LinearCode.dim_add_dim_dual C; simp_all +decide [ Finset.card_compl ] ;
      rw [ ← this, Nat.add_sub_cancel ];
    convert dual_disjoint ( h Sᶜ hS_compl ) _ using 1;
    · rw [ ← dual_vanishingOn, dual_dual ];
    · rw [ dim_vanishingOn, LinearCode.length_eq_card ];
      rw [ hS_compl, LinearCode.length_eq_card, add_tsub_cancel_of_le ( show C.dim ≤ Fintype.card ι from le_trans ( Submodule.finrank_le _ ) ( by simp +decide ) ) ];
  · exact h.1;
  · grind +revert

/-
For a code strictly between `⊥` and `⊤`, `C` is MDS iff its dual is MDS.
-/
theorem isMDS_dual_iff {C : LinearCode ι F} (hbot : C ≠ ⊥) (htop : C ≠ ⊤) :
    IsMDS (dual C) ↔ IsMDS C := by
  constructor <;> intro h;
  · have := h.dual;
    aesop;
  · apply IsMDS.dual h;
    intro h';
    have := LinearCode.dual_dual C; simp_all +decide ;

end LinearCode