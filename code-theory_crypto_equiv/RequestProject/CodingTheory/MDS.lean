import RequestProject.CodingTheory.GeneratorParityCheck

/-!
# Maximum distance separable (MDS) codes and MDS duality

This module continues the coding-theory development of
`RequestProject/CodingTheory/LinearCode.lean`,
`RequestProject/CodingTheory/Dual.lean`, and
`RequestProject/CodingTheory/GeneratorParityCheck.lean`, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977.

It implements the **MDS predicate** and the headline structural theorem of
§1.1 of `CODING_THEORY_DIRECTIONS.md`: *the dual of an MDS code is MDS*
(MacWilliams–Sloane, Ch. 11, Theorem 2).

We keep the conventions of the foundational modules: a word lives in `ι → F` with
`[Fintype ι] [Field F]`, and a linear `[n, k]` code is a subspace
`C : Submodule F (ι → F)` of length `n = #ι` (`codeLength`) and dimension
`k = dim C` (`codeDim`).

## The information-set picture

The proof runs through the *information-set* characterization of the minimum
distance.  For a `k`-subset `S` of coordinates, write `vanishingOn S` for the
coordinate subspace of words that vanish on `S`.  Then a code `C` of dimension
`k` is MDS exactly when **every** `k`-subset `S` is an *information set*, i.e.
`C` meets `vanishingOn S` trivially (`Disjoint C (vanishingOn S)`): no nonzero
codeword vanishes on a full set of `k` coordinates.

Duality is then transparent: `vanishingOn S` and `vanishingOn Sᶜ` are dual
coordinate subspaces (`dualCode_vanishingOn`), and disjointness with
complementary dimensions dualizes (`dualCode_disjoint`), so `S` is an information
set for `C` iff `Sᶜ` is an information set for `Cᗮ`.  Running this over all
`k`-subsets gives the MDS duality.

## Main definitions

* `vanishingOn S` — the coordinate subspace `{x | ∀ i ∈ S, x i = 0}`.
* `IsMDS C` — `C` is nonzero and meets the Singleton bound with equality.

## Main results

* `dualCode_vanishingOn` — `(vanishingOn S)ᗮ = vanishingOn Sᶜ`.
* `codeDim_vanishingOn` — `dim (vanishingOn S) = n - #S`.
* `dualCode_disjoint` — disjointness with complementary dimensions dualizes.
* `isMDS_iff_forall_disjoint_vanishing` — the information-set characterization.
* `IsMDS.dualCode` — **MacWilliams–Sloane, Ch. 11, Theorem 2**: the dual of an
  MDS code (that is not the whole space) is MDS.
* `isMDS_dualCode_iff` — `C` is MDS iff `Cᗮ` is MDS, for `⊥ ≠ C ≠ ⊤`.

## References

* MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 11, §3.
-/

namespace CodingTheory

open scoped Classical

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The dual of a sup is the inf of the duals: `(C ⊔ D)ᗮ = Cᗮ ⊓ Dᗮ`. -/
theorem dualCode_sup (C D : Submodule F (ι → F)) :
    dualCode (C ⊔ D) = dualCode C ⊓ dualCode D := by
  apply le_antisymm
  · exact le_inf (dualCode_antitone le_sup_left) (dualCode_antitone le_sup_right)
  · rw [SetLike.le_def]
    rintro y ⟨hyC, hyD⟩
    simp only [SetLike.mem_coe, mem_dualCode_iff] at hyC hyD ⊢
    intro x hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have e : ∀ i, (a + b) i * y i = a i * y i + b i * y i := fun i => by
      rw [Pi.add_apply]; ring
    simp only [e, Finset.sum_add_distrib, hyC a ha, hyD b hb, add_zero]

/-- The coordinate subspace of words that **vanish on** a finite set `S` of
positions: `{x | ∀ i ∈ S, x i = 0}` (equivalently, words supported on `Sᶜ`). -/
def vanishingOn (S : Finset ι) : Submodule F (ι → F) :=
  LinearMap.ker (LinearMap.pi (fun i : S => LinearMap.proj (i : ι)) :
    (ι → F) →ₗ[F] (S → F))

omit [Fintype ι] in
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
theorem codeDim_vanishingOn (S : Finset ι) :
    codeDim (vanishingOn (F := F) S) = codeLength (vanishingOn (F := F) S) - S.card := by
  have h_surjective : Function.Surjective (fun v : ι → F => fun i : S => v i) := by
    intro g
    use fun i => if h : i ∈ S then g ⟨i, h⟩ else 0
    simp;
  have h_rank_nullity : Module.finrank F (LinearMap.ker (LinearMap.pi (fun i : S => LinearMap.proj (i : ι)) : (ι → F) →ₗ[F] (S → F))) + Module.finrank F (LinearMap.range (LinearMap.pi (fun i : S => LinearMap.proj (i : ι)) : (ι → F) →ₗ[F] (S → F))) = Fintype.card ι := by
    have := LinearMap.finrank_range_add_finrank_ker ( LinearMap.pi fun i : S => LinearMap.proj ( i : ι ) : ( ι → F ) →ₗ[F] S → F );
    simp_all +decide [ add_comm ];
  convert Nat.eq_sub_of_add_eq h_rank_nullity using 1;
  rw [ LinearMap.range_eq_top.mpr ] <;> aesop

/-
The dual of a coordinate subspace is the complementary coordinate subspace:
`(vanishingOn S)ᗮ = vanishingOn Sᶜ`.
-/
theorem dualCode_vanishingOn (S : Finset ι) :
    dualCode (vanishingOn (F := F) S) = vanishingOn (F := F) Sᶜ := by
  refine' le_antisymm _ _ <;> intro x hx <;> simp_all +decide [ mem_vanishingOn_iff, mem_dualCode_iff ];
  · intro i hi; specialize hx ( fun j => if j = i then 1 else 0 ) ; aesop;
  · exact fun y hy => Finset.sum_eq_zero fun i hi => by by_cases hi' : i ∈ S <;> simp +decide [ hx i, hy i, hi' ] ;

/-
**Disjointness with complementary dimensions dualizes.** If `C` and `D` are
disjoint with dimensions summing to the length, then their duals are disjoint.
-/
theorem dualCode_disjoint {C D : Submodule F (ι → F)} (hCD : Disjoint C D)
    (hdim : codeDim C + codeDim D = codeLength C) :
    Disjoint (dualCode C) (dualCode D) := by
  rw [ Submodule.disjoint_def ] at *;
  intro x hx hx';
  have h_sum : C ⊔ D = ⊤ := by
    refine' Submodule.eq_top_of_finrank_eq _;
    have := Submodule.finrank_sup_add_finrank_inf_eq C D;
    rw [ show C ⊓ D = ⊥ by exact eq_bot_iff.mpr fun x hx => hCD x hx.1 hx.2 ] at this ; aesop;
  have h_sum : dualCode (C ⊔ D) = ⊥ := by
    rw [ h_sum, dualCode_top ];
  rw [ dualCode_sup ] at h_sum;
  exact Submodule.eq_bot_iff _ |>.1 h_sum x ⟨ hx, hx' ⟩

/-- A linear code is **maximum distance separable** (MDS) when it is nonzero and
meets the Singleton bound with equality: `d = n - k + 1`. -/
def IsMDS (C : Submodule F (ι → F)) : Prop :=
  C ≠ ⊥ ∧ minDist C = codeLength C - codeDim C + 1

/-- An MDS code is nonzero. -/
theorem IsMDS.ne_bot {C : Submodule F (ι → F)} (h : IsMDS C) : C ≠ ⊥ := h.1

/-- An MDS code can equivalently be described through its minimum weight. -/
theorem isMDS_iff_minWeight {C : Submodule F (ι → F)} :
    IsMDS C ↔ C ≠ ⊥ ∧ minWeight C = codeLength C - codeDim C + 1 := by
  unfold IsMDS; rw [minDist_eq_minWeight]

/-
The existence of a low-weight nonzero codeword (weight `≤ n - k`) is the same
as the failure of some `k`-subset to be an information set.
-/
theorem exists_lowWeight_iff_exists_vanishing {C : Submodule F (ι → F)} :
    (∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ codeLength C - codeDim C) ↔
      ∃ S : Finset ι, S.card = codeDim C ∧ ¬ Disjoint C (vanishingOn S) := by
  constructor;
  · rintro ⟨ c, hc₁, hc₂, hc₃ ⟩;
    obtain ⟨S, hS⟩ : ∃ S : Finset ι, S.card = codeDim C ∧ ∀ i ∈ S, c i = 0 := by
      have h_card : (Finset.univ.filter (fun i => c i = 0)).card ≥ codeDim C := by
        simp_all +decide [ hammingNorm ];
        rw [ Finset.filter_not, Finset.card_sdiff ] at hc₃ ; simp_all +decide [ Finset.card_univ ];
        linarith! [ Nat.sub_add_cancel ( show codeDim C ≤ codeLength C from le_trans ( Submodule.finrank_le _ ) ( by simp +decide [ codeLength ] ) ) ];
      exact Exists.elim ( Finset.exists_subset_card_eq h_card ) fun S hS => ⟨ S, hS.2, fun i hi => Finset.mem_filter.mp ( hS.1 hi ) |>.2 ⟩;
    exact ⟨ S, hS.1, fun h => hc₂ <| by rw [ Submodule.disjoint_def ] at h; specialize h c hc₁ ( by aesop ) ; aesop ⟩;
  · simp +decide [ Submodule.disjoint_def ];
    intro S hS x hx hx' hx''; use x; simp_all +decide [ hammingNorm ] ;
    convert Finset.card_le_card ( show Finset.filter ( fun i => ¬x i = 0 ) Finset.univ ⊆ Finset.univ \ S from fun i hi => by aesop ) using 1 ; simp +decide [ Finset.card_sdiff, * ]

/-
**The information-set characterization of MDS codes.** A nonzero code `C` of
dimension `k` is MDS iff every `k`-subset of coordinates is an information set,
i.e. `C` meets each `vanishingOn S` trivially.
-/
theorem isMDS_iff_forall_disjoint_vanishing {C : Submodule F (ι → F)} (hC : C ≠ ⊥) :
    IsMDS C ↔ ∀ S : Finset ι, S.card = codeDim C → Disjoint C (vanishingOn S) := by
  constructor <;> intro hS;
  · intro S hS_card
    by_contra h_not_disjoint
    obtain ⟨c, hcC, hc_ne_zero, hc_weight⟩ : ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ codeLength C - codeDim C := by
      obtain ⟨c, hcC, hc_ne_zero, hc_weight⟩ : ∃ c ∈ C, c ≠ 0 ∧ ∀ i ∈ S, c i = 0 := by
        rw [ disjoint_iff ] at h_not_disjoint;
        simp_all +decide [ Submodule.eq_bot_iff ];
        exact ⟨ h_not_disjoint.choose, h_not_disjoint.choose_spec.1, h_not_disjoint.choose_spec.2.2, h_not_disjoint.choose_spec.2.1 ⟩;
      have hc_weight : hammingNorm c ≤ Finset.card (Finset.univ \ S) := by
        exact Finset.card_le_card fun i hi => by aesop;
      grind;
    have := hS.2 ▸ minDist_eq_minWeight C ▸ minWeight_le hcC hc_ne_zero; omega;
  · refine' ⟨ hC, le_antisymm _ _ ⟩;
    · convert singleton_bound_dist C hC using 1;
    · have h_existsLowWeight : ¬∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ codeLength C - codeDim C := by
        rw [ exists_lowWeight_iff_exists_vanishing ];
        aesop;
      obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := exists_eq_minWeight hC;
      exact Nat.succ_le_of_lt ( lt_of_not_ge fun h => h_existsLowWeight ⟨ c, hc₁, hc₂, hc₃.symm ▸ h ⟩ ) |> le_trans <| by rw [ minDist_eq_minWeight ] ;

/-
**MacWilliams–Sloane, Ch. 11, Theorem 2.** The dual of an MDS code that is
not the whole space is again MDS.
-/
theorem IsMDS.dualCode {C : Submodule F (ι → F)} (h : IsMDS C)
    (hC : dualCode C ≠ ⊥) : IsMDS (dualCode C) := by
  convert isMDS_iff_forall_disjoint_vanishing hC |>.2 _ using 1;
  intro S hS;
  have h_disjoint : Disjoint C (vanishingOn Sᶜ) := by
    convert isMDS_iff_forall_disjoint_vanishing h.1 |>.1 h ( Sᶜ ) _ using 1;
    have := codeDim_add_codeDim_dualCode C; simp_all +decide [ Finset.card_compl ] ;
    exact Nat.sub_eq_of_eq_add ( by linarith! );
  convert dualCode_disjoint h_disjoint _ using 1;
  · rw [ dualCode_vanishingOn, Finset.compl_eq_univ_sdiff ];
    simp +decide [ Finset.compl_eq_univ_sdiff ];
  · convert codeDim_add_codeDim_dualCode C using 1;
    rw [ codeDim_vanishingOn ];
    simp +decide [ Finset.card_compl, codeLength ];
    rw [ Nat.sub_sub_self ( hS.symm ▸ codeDim_dualCode C ▸ Nat.sub_le _ _ ), hS ]

/-
For a code strictly between `⊥` and `⊤`, `C` is MDS iff its dual is MDS.
-/
theorem isMDS_dualCode_iff {C : Submodule F (ι → F)} (hbot : C ≠ ⊥) (htop : C ≠ ⊤) :
    IsMDS (dualCode C) ↔ IsMDS C := by
  constructor <;> intro h;
  · convert h.dualCode _;
    · rw [ dualCode_dualCode ];
    · simp +decide [ hbot, dualCode_dualCode ];
  · apply IsMDS.dualCode h;
    contrapose! htop;
    rw [ ← dualCode_dualCode C, htop, dualCode_bot ]

end CodingTheory