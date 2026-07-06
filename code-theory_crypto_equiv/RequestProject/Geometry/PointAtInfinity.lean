import RequestProject.Geometry.NormalRationalCurve

/-!
# The point at infinity and the `(q+1)`-arc

This module continues `RequestProject/Geometry/NormalRationalCurve.lean`.  The
normal rational curve over **all** of `F` gives a `q`-arc in `PG(k-1, q)` (its
points are the columns `(1 : t : ⋯ : t^{k-1})`, `t ∈ F`).  Adjoining the
**point at infinity** `(0 : ⋯ : 0 : 1) = e_{k-1}` produces the classical
**`(q+1)`-arc** — the longest arc available for all `k` in the Segre/MDS range,
corresponding to the doubly-extended Reed–Solomon code of length `q+1`.

We index the extended point set by `Option F`: the value `some t` is the finite
curve point at `t`, and `none` is the point at infinity `e_{k-1}`.  The generator
matrix is

  `G r (some t) = t^r`,  `G r none = if r = k-1 then 1 else 0`.

The arc property splits into two cases for a `k`-subset `S` of `Option F`:

* `none ∉ S` (all finite): the columns are a square Vandermonde of `k` distinct
  field points, linearly independent — this is `vandermondeGen_isArc`.
* `none ∈ S`: writing `S = {∞} ∪ T` with `|T| = k-1`, the rows `0 … k-2` give the
  `(k-1)`-Vandermonde of the distinct points `T` (independent), forcing the finite
  coefficients to vanish, and then row `k-1` forces the `∞`-coefficient to vanish.

## Main definitions

* `extendedNRCgen k` — the generator matrix `G : Matrix (Fin k) (Option F) F`
  of the normal rational curve together with the point at infinity.

## Main results

* `extendedNRCgen_isArc` — **the extended normal rational curve is a `(q+1)`-arc**:
  for `1 ≤ k ≤ q+1` every `k` of its `q+1` columns are linearly independent.
* `card_option` packaging: the point set has `q + 1 = #F + 1` points.
-/

namespace CodingTheory

open scoped Classical
open Matrix Finset

variable {F : Type*} [Field F] [Fintype F]

/-- The generator matrix of the normal rational curve over `F` together with the
**point at infinity** `e_{k-1} = (0 : ⋯ : 0 : 1)`, indexed by `Option F`:
`G r (some t) = t^r` and `G r none = if r = k-1 then 1 else 0`. -/
def extendedNRCgen (k : ℕ) : Matrix (Fin k) (Option F) F :=
  fun r i => match i with
    | some t => t ^ (r : ℕ)
    | none   => if (r : ℕ) = k - 1 then (1 : F) else 0

omit [Fintype F] in
/-- The `i`-th column of `extendedNRCgen` for a finite point `some t` is the
normal-rational-curve column `(1 : t : ⋯ : t^{k-1})`. -/
theorem arcColumn_extendedNRCgen_some (k : ℕ) (t : F) :
    arcColumn (extendedNRCgen k) (some t) = fun r : Fin k => t ^ (r : ℕ) := rfl

omit [Fintype F] in
/-- The `i`-th column of `extendedNRCgen` at infinity is the basis vector
`e_{k-1}`. -/
theorem arcColumn_extendedNRCgen_none (k : ℕ) :
    arcColumn (extendedNRCgen (F := F) k) none
      = fun r : Fin k => if (r : ℕ) = k - 1 then (1 : F) else 0 := rfl

/-
The finite case of the arc property: a `k`-subset of `Option F` avoiding the
point at infinity gives `k` distinct finite curve points whose columns form a
square Vandermonde, hence are linearly independent.
-/
theorem extendedNRCgen_li_of_not_mem_none {k : ℕ} (hk1 : 1 ≤ k)
    (S : Finset (Option F)) (hS : S.card = k) (hnone : none ∉ S) :
    LinearIndependent F (fun i : S => arcColumn (extendedNRCgen k) (i : Option F)) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset F, S = T.image Option.some ∧ T.card = k := by
    refine' ⟨ Finset.univ.filter fun t => some t ∈ S, _, _ ⟩;
    · ext x; cases x <;> aesop;
    · convert hS using 1;
      refine' Finset.card_bij ( fun x hx => some x ) _ _ _ <;> simp +decide [ hnone ];
      exact fun x hx => by cases x <;> aesop;
  obtain ⟨hT_sub, hT_card⟩ := hT;
  have hT_arc : LinearIndependent F (fun j : T => arcColumn (vandermondeGen (id : F → F) k) (j : F)) := by
    convert vandermondeGen_isArc ( Function.injective_id ) hk1 ( by linarith [ show Fintype.card F ≥ k from by rw [ ← hT_card ] ; exact Finset.card_le_univ _ ] ) T hT_card;
  have hT_arc_comp : LinearIndependent F (fun i : S => arcColumn (vandermondeGen (id : F → F) k) (Option.get (i : Option F) (by
  grind))) := by
    all_goals generalize_proofs at *;
    convert hT_arc.comp _ _;
    rotate_left;
    use fun i => ⟨ Option.get i ( by
      grind ), by
      grind ⟩
    all_goals generalize_proofs at *;
    · intro i j hij; aesop;
    · rfl
  generalize_proofs at *;
  convert hT_arc_comp using 2;
  rename_i i; rcases i with ⟨ i, hi ⟩ ; rcases i with ( _ | i ) <;> simp_all +decide [ arcColumn ] ;
  · grind;
  · exact funext fun r => by simp +decide [ arcColumn, vandermondeGen, extendedNRCgen ] ;

/-- **The extended normal rational curve is a `(q+1)`-arc.**  For `1 ≤ k ≤ q+1`,
every `k`-subset of the `q+1` columns of `extendedNRCgen k` is linearly
independent. -/
theorem extendedNRCgen_isArc {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card F + 1) :
    IsArc (extendedNRCgen (F := F) k) := by
  intro S hS;
  by_cases hnone : none ∈ S;
  · -- Let $T := S.erase none$; then $none ∉ T$, $T ⊆ S$, and $T.card = k - 1$, and $S = insert none T$.
    set T := S.erase none
    have hT_card : T.card = k - 1 := by
      rw [ Finset.card_erase_of_mem hnone, hS ]
    have hT_subset : T ⊆ S := by
      exact Finset.erase_subset _ _
    have hS_eq : S = insert none T := by
      rw [ Finset.insert_erase hnone ];
    by_cases hk2 : 2 ≤ k;
    · -- For rows with `(r:ℕ) ≠ k - 1`, there `extendedNRCgen k r none = 0` and `extendedNRCgen k r (some t) = t^(r:ℕ)`, so the `none` term drops and we get `∑ (over the some-elements t of S) g(·) * t^(r:ℕ) = 0`.
      have h_vandermonde : LinearIndependent F (fun i : T => arcColumn (vandermondeGen (id : F → F) (k - 1)) (i.val.getD 0)) := by
        have hT_distinct : (Finset.image (fun i : Option F => i.getD 0) T).card = k - 1 := by
          rw [ ← hT_card, Finset.card_image_of_injOn ];
          intro x hx y hy; simp +decide at hx hy ⊢;
          cases x <;> cases y <;> simp +decide at hx hy ⊢;
          · exact absurd hx ( by simp +decide [ T ] );
          · exact absurd hy ( by simp +decide [ T ] );
        have h_vandermonde : LinearIndependent F (fun i : Finset.image (fun i : Option F => i.getD 0) T => arcColumn (vandermondeGen (id : F → F) (k - 1)) (i : F)) := by
          apply vandermondeGen_isArc;
          · exact Function.injective_id;
          · exact Nat.le_sub_one_of_lt hk2;
          · omega;
          · exact hT_distinct;
        convert h_vandermonde.comp _ _;
        rotate_left;
        use fun x => ⟨ x.val.getD 0, Finset.mem_image_of_mem _ x.2 ⟩;
        · intro x y hxy;
          rcases x with ⟨ _ | x, hx ⟩ <;> rcases y with ⟨ _ | y, hy ⟩ <;> norm_num at *;
          · exact absurd hx ( Finset.notMem_erase _ _ );
          · exact absurd hy ( by simp +decide [ T ] );
          · exact hxy;
        · rfl;
      rw [ Fintype.linearIndependent_iff ] at h_vandermonde ⊢;
      intro g hg i
      have h_sum_zero : ∑ i : T, g ⟨i, hT_subset i.2⟩ • arcColumn (vandermondeGen (id : F → F) (k - 1)) (i.val.getD 0) = 0 := by
        convert congr_arg ( fun x : Fin k → F => fun r : Fin ( k - 1 ) => x ⟨ r, Nat.lt_of_lt_of_le r.2 ( Nat.pred_le _ ) ⟩ ) hg using 1;
        ext r; simp +decide [ Finset.sum_apply, arcColumn ] ;
        rw [ ← Finset.sum_subset ( show Finset.image ( fun x : T => ⟨ x, hT_subset x.2 ⟩ ) Finset.univ ⊆ Finset.attach S from Finset.image_subset_iff.mpr fun x _ => Finset.mem_attach _ _ ) ];
        · refine' Finset.sum_bij ( fun x _ => ⟨ x, hT_subset x.2 ⟩ ) _ _ _ _ <;> simp +decide;
          intro a ha; rcases a with ( _ | a ) <;> simp +decide [ vandermondeGen, extendedNRCgen ] at ha ⊢;
          exact absurd ha ( Finset.notMem_erase _ _ );
        · simp +contextual [ Finset.mem_image ];
          grind +locals;
      by_cases hi : i.val = none;
      · replace hg := congr_fun hg ⟨ k - 1, Nat.sub_lt hk1 zero_lt_one ⟩ ; simp +decide [ hi, arcColumn_extendedNRCgen_none ] at hg ⊢;
        rw [ Finset.sum_eq_single ⟨ none, hnone ⟩ ] at hg <;> simp +decide [ hi, arcColumn_extendedNRCgen_none ] at hg ⊢;
        · convert hg;
        · intro a ha ha'; specialize h_vandermonde ( fun i => g ⟨ i, hT_subset i.2 ⟩ ) ; simp +decide [ Finset.sum_apply, arcColumn ] at h_vandermonde ⊢;
          exact Or.inl ( h_vandermonde h_sum_zero a ( Finset.mem_erase_of_ne_of_mem ha' ha ) );
      · convert h_vandermonde ( fun j => g ⟨ j, hT_subset j.2 ⟩ ) h_sum_zero ⟨ i, by
          exact Finset.mem_erase_of_ne_of_mem hi i.2 ⟩;
    · interval_cases k ; simp_all +singlePass;
      refine' Fintype.linearIndependent_iff.2 _;
      simp +decide [ hS_eq, arcColumn ];
      rintro g hg a rfl; rw [ show S.attach = { ⟨ none, by simp +decide [ hS_eq ] ⟩ } from by ext ⟨ x, hx ⟩ ; aesop ] at hg; simp_all +decide [ arcColumn ] ;
      exact hg.resolve_right ( by intro h; have := congr_fun h ⟨ 0, by simp +decide [ hS_eq ] ⟩ ; simp +decide [ arcColumn, extendedNRCgen ] at this );
  · exact extendedNRCgen_li_of_not_mem_none hk1 S hS hnone

omit [Field F] in
/-- The extended point set has exactly `q + 1 = #F + 1` points: together with
`extendedNRCgen_isArc` this exhibits a `(q+1)`-arc in `PG(k-1, q)`, the maximal
length available across the Segre/MDS range. -/
theorem card_extendedNRC_points : Fintype.card (Option F) = Fintype.card F + 1 :=
  Fintype.card_option

end CodingTheory