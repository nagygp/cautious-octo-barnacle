import Mathlib
import RequestProject.CodingTheory.LinearCode

/-!
# Coding theory: the direct sum of linear codes

Given linear codes `C₁ ⊆ ι → F` and `C₂ ⊆ κ → F`, their **direct sum**
`C₁ ⊕ C₂` is the code in `(ι ⊕ κ) → F` consisting of the concatenations
`(u | v)` with `u ∈ C₁`, `v ∈ C₂` (MacWilliams–Sloane, Ch. 2, §9).  It has the
classical parameters `[n₁ + n₂, k₁ + k₂, min(d₁, d₂)]`:

* length `n₁ + n₂` (the ambient index type `ι ⊕ κ`),
* dimension `k₁ + k₂` (`finrank_directSumCode`), because the concatenation map is
  a linear isomorphism onto `C₁ × C₂`,
* minimum distance `min(d₁, d₂)` (`minWeight_directSumCode`): a codeword's weight
  is the sum of the weights of its two halves, and the minimum is attained by
  taking a minimum-weight word of the smaller code and padding the other half
  with zeros.

This complements the `(u | u+v)` (Plotkin) construction of
`RequestProject/CodingTheory/PlotkinConstruction.lean` and feeds the
statistical-mechanics track: the partition function factorizes over a direct sum
(`RequestProject/Physics/FreeEnergyAdditive.lean`).

## Main results

* `directSumCode` — the direct-sum code in `(ι ⊕ κ) → F`.
* `mem_directSumCode` — membership: `c ∈ C₁ ⊕ C₂ ↔ c∘inl ∈ C₁ ∧ c∘inr ∈ C₂`.
* `finrank_directSumCode` — `dim (C₁ ⊕ C₂) = dim C₁ + dim C₂`.
* `hammingNorm_sum` — a word's weight is the sum of the weights of its halves.
* `minWeight_directSumCode` — `minWeight (C₁ ⊕ C₂) = min (minWeight C₁) (minWeight C₂)`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {F : Type*} [Field F]

/-- The **direct sum** `C₁ ⊕ C₂` of two linear codes, as a code in `(ι ⊕ κ) → F`:
the concatenations `Sum.elim u v` with `u ∈ C₁`, `v ∈ C₂`. -/
noncomputable def directSumCode (C₁ : Submodule F (ι → F)) (C₂ : Submodule F (κ → F)) :
    Submodule F ((ι ⊕ κ) → F) :=
  (C₁.prod C₂).map (LinearEquiv.sumArrowLequivProdArrow ι κ F F).symm.toLinearMap

/-
Membership in the direct-sum code: a word lies in `C₁ ⊕ C₂` iff its left half
lies in `C₁` and its right half lies in `C₂`.
-/
theorem mem_directSumCode {C₁ : Submodule F (ι → F)} {C₂ : Submodule F (κ → F)}
    (c : (ι ⊕ κ) → F) :
    c ∈ directSumCode C₁ C₂ ↔ (c ∘ Sum.inl) ∈ C₁ ∧ (c ∘ Sum.inr) ∈ C₂ := by
  unfold directSumCode;
  aesop

/-
**Dimension of a direct sum.** `dim (C₁ ⊕ C₂) = dim C₁ + dim C₂`.
-/
theorem finrank_directSumCode (C₁ : Submodule F (ι → F)) (C₂ : Submodule F (κ → F)) :
    Module.finrank F (directSumCode C₁ C₂) =
      Module.finrank F C₁ + Module.finrank F C₂ := by
  convert LinearEquiv.finrank_eq _;
  rw [ ← Module.finrank_prod ];
  refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
  refine' { toFun := fun x => ⟨ ⟨ x.val ∘ Sum.inl, _ ⟩, ⟨ x.val ∘ Sum.inr, _ ⟩ ⟩, map_add' := _, map_smul' := _ };
  all_goals norm_num [ Function.Injective, Function.Surjective ];
  any_goals intro a ha b hb; simp_all +decide [ funext_iff, Sum.forall ];
  · exact mem_directSumCode _ |>.1 x.2 |>.1;
  · exact mem_directSumCode _ |>.1 x.2 |>.2;
  · exact fun m a ha => ⟨ rfl, rfl ⟩;
  · refine' ⟨ Sum.elim a b, _, _ ⟩ <;> simp +decide [ *, directSumCode ];
    aesop

/-
A word on `ι ⊕ κ` has Hamming weight equal to the sum of the weights of its
two halves.
-/
theorem hammingNorm_sum (c : (ι ⊕ κ) → F) :
    hammingNorm c = hammingNorm (c ∘ Sum.inl) + hammingNorm (c ∘ Sum.inr) := by
  convert Fintype.sum_sum_type ( fun x => if c x = 0 then 0 else 1 ) using 1;
  · unfold hammingNorm; simp +decide [ Finset.sum_ite ] ;
  · simp +decide [ hammingNorm ];
    simp +decide [ Finset.sum_ite ]

/-
**Minimum distance of a direct sum.** For nonzero codes `C₁, C₂`, the
direct sum `C₁ ⊕ C₂` has minimum weight `min (minWeight C₁) (minWeight C₂)`.
-/
theorem minWeight_directSumCode {C₁ : Submodule F (ι → F)} {C₂ : Submodule F (κ → F)}
    (h₁ : C₁ ≠ ⊥) (h₂ : C₂ ≠ ⊥) :
    minWeight (directSumCode C₁ C₂) = min (minWeight C₁) (minWeight C₂) := by
  refine' le_antisymm ( le_min _ _ ) _ <;> simp_all +decide [ minWeight ];
  · refine' le_csInf _ _;
    · exact exists_eq_minWeight h₁ |> fun ⟨ c, hc₁, hc₂, hc₃ ⟩ => ⟨ _, ⟨ c, hc₁, hc₂, hc₃ ⟩ ⟩;
    · intro b hb
      obtain ⟨c, hc₁, hc₂, hc₃⟩ := hb
      have h_mem : Sum.elim c 0 ∈ directSumCode C₁ C₂ := by
        exact ⟨ ( c, 0 ), ⟨ hc₁, C₂.zero_mem ⟩, by ext i; cases i <;> simp +decide ⟩;
      refine' Nat.sInf_le ⟨ Sum.elim c 0, h_mem, _, _ ⟩ <;> simp_all +decide [ hammingNorm_sum ];
      exact fun h => hc₂ ( by ext i; simpa using congr_fun h ( Sum.inl i ) );
  · refine' le_csInf _ _;
    · exact exists_eq_minWeight h₂ |> fun ⟨ c, hc₁, hc₂, hc₃ ⟩ => ⟨ _, ⟨ c, hc₁, hc₂, hc₃ ⟩ ⟩;
    · intro b hb; obtain ⟨ c, hc, hc0, rfl ⟩ := hb; refine' csInf_le _ _ <;> norm_num [ mem_directSumCode ] ; (
      refine' ⟨ Sum.elim 0 c, _, _, _ ⟩ <;> simp_all +decide [ mem_directSumCode ];
      · exact fun h => hc0 ( by ext x; simpa using congr_fun h ( Sum.inr x ) );
      · convert hammingNorm_sum ( Sum.elim 0 c ) using 1 ; simp +decide [ hammingNorm ]);
  · obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := exists_eq_minWeight ( show directSumCode C₁ C₂ ≠ ⊥ from by
                                                          obtain ⟨ u, hu ⟩ := Submodule.ne_bot_iff _ |>.1 h₁;
                                                          simp_all +decide [ Submodule.eq_bot_iff ];
                                                          refine' ⟨ _, ⟨ ( u, 0 ), ⟨ hu.1, Submodule.zero_mem _ ⟩, rfl ⟩, _ ⟩ ; simp_all +decide [ funext_iff, Sum.forall ] );
    cases' ( mem_directSumCode c ).mp hc₁ with hc₁ hc₂ ; simp_all +decide [ hammingNorm_sum ];
    by_cases h : c ∘ Sum.inl = 0 <;> by_cases h' : c ∘ Sum.inr = 0 <;> simp_all +decide [ weightSet ];
    · exact False.elim ( hc₂ ( by ext x; cases x <;> simp_all +decide [ funext_iff ] ) );
    · refine' Or.inr ( le_trans _ ( le_of_eq hc₃ ) );
      exact Nat.sInf_le ⟨ _, hc₂, h', rfl ⟩;
    · exact Or.inl ( le_trans ( csInf_le ⟨ 0, by rintro x ⟨ c, hc₁, hc₂, rfl ⟩ ; exact Nat.zero_le _ ⟩ ⟨ _, hc₁, h, rfl ⟩ ) ( hc₃ ▸ le_rfl ) );
    · refine' Or.inl ( le_trans _ ( le_trans ( Nat.le_add_right _ _ ) hc₃.le ) );
      exact Nat.sInf_le ⟨ _, hc₁, h, rfl ⟩

end CodingTheory