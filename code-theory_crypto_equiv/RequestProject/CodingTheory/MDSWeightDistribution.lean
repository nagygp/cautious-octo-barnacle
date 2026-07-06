import RequestProject.CodingTheory.MDS
import RequestProject.CodingTheory.WeightEnumerator

/-!
# The minimum-weight count of an MDS code

This module continues `RequestProject/CodingTheory/MDS.lean` and
`RequestProject/CodingTheory/WeightEnumerator.lean`, transcribing the first
coefficient of the **MDS weight distribution** (MacWilliams–Sloane, Ch. 11,
Thm 6).  For an `[n, k, d]` MDS code (`d = n - k + 1`) the number of
minimum-weight codewords is exactly

  `A_d = (q − 1) · C(n, d)`.

## Proof

For a `(k-1)`-subset `T` of coordinates, the codewords vanishing on `T` form the
subspace `C ⊓ vanishingOn T`, which for an MDS code is exactly **one-dimensional**
(`IsMDS.finrank_inf_vanishingOn`): its dimension is `≥ k + (n-k+1) - n = 1` by the
modular law, and `≤ 1` because a `2`-dimensional space of words supported on the
`d`-set `Tᶜ` would contain a nonzero word vanishing at one extra coordinate, of
weight `< d`, contradicting the minimum weight.

Each such one-dimensional space has `q − 1` nonzero words, and every one has
support **exactly** `Tᶜ` (weight `≥ d` forces weight `= d`).  Conversely every
minimum-weight codeword `c` determines `T = (support c)ᶜ` of size `k - 1`.  Summing
`q − 1` over the `C(n, k-1) = C(n, d)` choices of `T` gives `A_d = (q-1) C(n,d)`.

## Main results

* `IsMDS.finrank_inf_vanishingOn` — `dim (C ⊓ vanishingOn T) = 1` for `|T| = k-1`.
* `IsMDS.weightDistribution_minDist` — `A_d = (q-1) · C(n, d)`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
**The key one-dimensionality lemma.**  For an MDS code `C` of dimension `k`
and a `(k-1)`-subset `T` of coordinates, the codewords vanishing on `T` form a
one-dimensional space: `dim (C ⊓ vanishingOn T) = 1`.
-/
theorem IsMDS.finrank_inf_vanishingOn {C : Submodule F (ι → F)} (h : IsMDS C)
    (T : Finset ι) (hT : T.card = codeDim C - 1) :
    Module.finrank F (C ⊓ vanishingOn T : Submodule F (ι → F)) = 1 := by
  -- Let $k := codeDim C$, and $D := vanishingOn T$.
  set k := codeDim C
  set D := vanishingOn (F := F) T;
  -- Lower bound `m ≥ 1`: By the modular identity `Submodule.finrank_sup_add_finrank_inf_eq C D : finrank (C ⊔ D) + finrank (C ⊓ D) = finrank C + finrank D`, and `finrank (C ⊔ D) ≤ finrank (⊤ : Submodule F (ι → F)) = n` (`Submodule.finrank_le`), we get `m = finrank C + finrank D - finrank (C ⊔ D) ≥ k + (n - (k-1)) - n = 1`.
  have h_lower_bound : 1 ≤ Module.finrank F (↥(C ⊓ D)) := by
    have h_lower_bound : Module.finrank F (↥(C ⊔ D)) + Module.finrank F (↥(C ⊓ D)) = k + (codeLength C - T.card) := by
      rw [ Submodule.finrank_sup_add_finrank_inf_eq ];
      convert congr_arg₂ ( · + · ) rfl ( codeDim_vanishingOn T ) using 1;
    have h_lower_bound : Module.finrank F (↥(C ⊔ D)) ≤ codeLength C := by
      exact le_trans ( Submodule.finrank_le _ ) ( by simp +decide [ codeLength ] );
    have h_lower_bound : k ≥ 1 := by
      exact Nat.pos_of_ne_zero ( by intro h0; have := h.1; aesop );
    omega;
  -- Upper bound `m ≤ 1`: Suppose `m ≥ 2`. The coordinate-evaluation functional is linear `φ : (C ⊓ D) →ₗ[F] F`, `φ ⟨v, _⟩ = v i0` for a chosen `i0 ∈ Tᶜ` (such `i0` exists since `Tᶜ.card = n - (k-1) = d ≥ 1`).
  by_contra h_contra
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∈ Tᶜ := by
    have h_card_Tc : Tᶜ.card = Fintype.card ι - (k - 1) := by
      rw [ ← hT, Finset.card_compl ];
    have h_card_Tc_pos : Fintype.card ι - (k - 1) ≥ 1 := by
      exact Nat.sub_pos_of_lt ( by linarith! [ Nat.sub_add_cancel ( show 1 ≤ codeDim C from Nat.pos_of_ne_zero ( by aesop_cat ) ), Nat.sub_add_cancel ( show codeDim C ≤ Fintype.card ι from Submodule.finrank_le _ |> le_trans <| by simp +decide [ codeLength ] ), minDist C ] );
    exact Finset.card_pos.mp ( h_card_Tc.symm ▸ h_card_Tc_pos );
  -- Then there is a nonzero `v ∈ C ⊓ D` with `v i0 = 0`.
  obtain ⟨v, hv⟩ : ∃ v : ι → F, v ∈ C ∧ v ∈ D ∧ v i0 = 0 ∧ v ≠ 0 := by
    have h_kernel : Module.finrank F (LinearMap.ker (LinearMap.comp (LinearMap.proj i0) (Submodule.subtype (C ⊓ D)))) ≥ 1 := by
      have := LinearMap.finrank_range_add_finrank_ker ( LinearMap.comp ( LinearMap.proj i0 ) ( Submodule.subtype ( C ⊓ D ) ) );
      linarith [ show Module.finrank F ( LinearMap.range ( LinearMap.comp ( LinearMap.proj i0 ) ( Submodule.subtype ( C ⊓ D ) ) ) ) ≤ 1 from le_trans ( Submodule.finrank_le _ ) ( by simp +decide ) , Nat.lt_of_le_of_ne h_lower_bound ( Ne.symm h_contra ) ];
    obtain ⟨ v, hv ⟩ := ( show ∃ v : ↥ ( C ⊓ D ), v ≠ 0 ∧ ( LinearMap.proj i0 ∘ₗ ( C ⊓ D ).subtype ) v = 0 from by
                            obtain ⟨ v, hv ⟩ := ( show ∃ v : ↥ ( LinearMap.ker ( LinearMap.proj i0 ∘ₗ ( C ⊓ D ).subtype ) ), v ≠ 0 from by
                                                    exact not_forall_not.mp fun h => by rw [ show LinearMap.ker ( LinearMap.proj i0 ∘ₗ ( C ⊓ D ).subtype ) = ⊥ by exact eq_bot_iff.mpr fun x hx => by aesop ] at h_kernel; simp +decide at h_kernel; );
                            exact ⟨ v, by simpa using hv, v.2 ⟩ );
    exact ⟨ v, v.2.1, v.2.2, hv.2, by simpa using hv.1 ⟩;
  -- Then `v ∈ C`, `v ≠ 0`, so `minWeight C ≤ hammingNorm v`, i.e. `d ≤ hammingNorm v`.
  have h_minWeight_le_hammingNorm : codeLength C - codeDim C + 1 ≤ hammingNorm v := by
    have h_minWeight_le_hammingNorm : minWeight C ≤ hammingNorm v := by
      exact minWeight_le hv.1 hv.2.2.2;
    rw [ ← isMDS_iff_minWeight.mp h |>.2 ] ; aesop;
  -- But `v ∈ D = vanishingOn T` means `v i = 0` for all `i ∈ T`; together with `v i0 = 0` (`i0 ∉ T`), the support of `v` is contained in `Tᶜ \ {i0}`, so `hammingNorm v ≤ (Tᶜ.erase i0).card = Tᶜ.card - 1 = d - 1`.
  have h_hammingNorm_le_card : hammingNorm v ≤ (Tᶜ.erase i0).card := by
    refine' Finset.card_le_card _;
    intro i hi; simp_all +decide [ Finset.subset_iff ] ;
    exact ⟨ by rintro rfl; exact hi hv.2.2.1, fun hi' => hi <| by simpa [ hi' ] using mem_vanishingOn_iff.mp hv.2.1 i hi' ⟩;
  simp_all +decide [ Finset.card_compl ];
  unfold codeLength at * ; omega

/-
**The MDS minimum-weight count** (MacWilliams–Sloane, Ch. 11, Thm 6, first
coefficient).  An `[n, k, d]` MDS code has exactly `A_d = (q-1) · C(n, d)`
codewords of minimum weight `d = n - k + 1`.
-/
set_option maxHeartbeats 1600000 in
theorem IsMDS.weightDistribution_minDist {C : Submodule F (ι → F)} (h : IsMDS C) :
    weightDistribution C (codeLength C - codeDim C + 1)
      = (Fintype.card F - 1) * (Fintype.card ι).choose (codeLength C - codeDim C + 1) := by
  have h_card : weightDistribution C (codeLength C - codeDim C + 1) = (Finset.univ.filter (fun c : C => hammingNorm (c : ι → F) = codeLength C - codeDim C + 1)).card := by
    convert Nat.card_eq_finsetCard _;
    simp +decide [ weightDistribution ];
  -- Let $T$ be a subset of $\iota$ with cardinality $k - 1$.
  have h_subset : ∀ (T : Finset ι), T.card = codeDim C - 1 → (Finset.univ.filter (fun c : C => (fun i => (c : ι → F) i ≠ 0) ⁻¹' {True} = Tᶜ ∧ c ≠ 0)).card = Fintype.card F - 1 := by
    intro T hT
    have h_fiber : (Finset.univ.filter (fun c : C => (fun i => (c : ι → F) i ≠ 0) ⁻¹' {True} = Tᶜ ∧ c ≠ 0)).card = (Finset.univ.filter (fun c : (C ⊓ vanishingOn (F := F) T : Submodule F (ι → F)) => c ≠ 0)).card := by
      refine' Finset.card_bij ( fun c hc => ⟨ c, _ ⟩ ) _ _ _ <;> simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
      · grind;
      · intro a ha hT' ha' x; have := h.2; simp_all +decide [ IsMDS ] ;
        have h_support : hammingNorm a ≥ codeLength C - codeDim C + 1 := by
          exact this ▸ minDist_eq_minWeight C ▸ minWeight_le ha ha';
        have h_support : hammingNorm a ≤ codeLength C - T.card := by
          have h_support : hammingNorm a ≤ Finset.card (Finset.univ \ T) := by
            exact Finset.card_le_card fun i hi => by aesop;
          simp_all +decide [ Finset.card_sdiff ];
        have h_support : hammingNorm a = codeLength C - T.card := by
          omega;
        have h_support : (Finset.univ.filter (fun i => a i ≠ 0)) = Tᶜ := by
          refine' Finset.eq_of_subset_of_card_le ( fun i hi => _ ) _ <;> simp_all +decide [ Finset.card_compl ];
          · exact fun hi' => hi ( hT' i hi' );
          · simp_all +decide [ hammingNorm ];
            grind;
        simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    have h_card : Fintype.card (C ⊓ vanishingOn (F := F) T : Submodule F (ι → F)) = Fintype.card F ^ 1 := by
      have h_card : Module.finrank F (C ⊓ vanishingOn (F := F) T : Submodule F (ι → F)) = 1 := by
        convert IsMDS.finrank_inf_vanishingOn h T hT using 1;
      have := Module.finBasis F ( C ⊓ vanishingOn T : Submodule F ( ι → F ) );
      have := this.repr;
      exact Fintype.card_congr this.toEquiv ▸ by simp +decide [ h_card ] ;
    simp_all +decide [ Finset.filter_ne' ];
  -- By summing over all subsets $T$ of $\iota$ with cardinality $k - 1$, we obtain the desired result.
  have h_sum : (Finset.univ.filter (fun c : C => hammingNorm (c : ι → F) = codeLength C - codeDim C + 1)).card = ∑ T ∈ Finset.powersetCard (codeDim C - 1) (Finset.univ : Finset ι), (Finset.univ.filter (fun c : C => (fun i => (c : ι → F) i ≠ 0) ⁻¹' {True} = Tᶜ ∧ c ≠ 0)).card := by
    rw [ ← Finset.card_biUnion ];
    · congr with c ; simp +decide [ hammingNorm ];
      constructor <;> intro h;
      · refine' ⟨ Finset.univ \ Finset.filter ( fun i => ¬c.val i = 0 ) Finset.univ, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_sdiff ];
        · unfold codeLength at *;
          rw [ tsub_add_eq_tsub_tsub, tsub_tsub_cancel_of_le ];
          exact le_trans ( Submodule.finrank_le _ ) ( by simp +decide );
        · simp +decide [ Set.ext_iff ];
        · rintro rfl; simp_all +decide [ codeLength ];
      · obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h;
        simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
        simp +decide [ Finset.filter_not, Finset.card_sdiff, * ];
        rw [ tsub_tsub_assoc ];
        · exact Submodule.finrank_le _ |> le_trans <| by simp +decide [ codeLength ] ;
        · exact Nat.pos_of_ne_zero ( by rintro h; simp_all +decide [ IsMDS ] );
    · intro T hT T' hT' hTT'; simp_all +decide [ Finset.disjoint_left ] ;
  have h_choose : Nat.choose (Fintype.card ι) (codeDim C - 1) = Nat.choose (Fintype.card ι) (codeLength C - codeDim C + 1) := by
    rw [ Nat.choose_symm_of_eq_add ] ; simp +decide [ codeLength ];
    rw [ tsub_add_eq_add_tsub ];
    · rw [ ← add_assoc, Nat.add_sub_cancel' ];
      · rfl;
      · exact le_trans ( Submodule.finrank_le _ ) ( by simp +decide [ codeLength ] );
    · exact Nat.pos_of_ne_zero ( by intro h0; exact h.1 ( Submodule.finrank_eq_zero.mp h0 ) );
  rw [ h_card, h_sum, Finset.sum_congr rfl fun T hT => h_subset T <| Finset.mem_powersetCard.mp hT |>.2 ] ; simp +decide [ mul_comm, h_choose ]

end CodingTheory