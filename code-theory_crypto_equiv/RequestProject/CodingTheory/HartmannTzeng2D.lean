import Mathlib
import RequestProject.CodingTheory.BCHBound
import RequestProject.CodingTheory.BCHMinDist
import RequestProject.CodingTheory.BCHPrimitiveRoot
import RequestProject.CodingTheory.HartmannTzeng

/-!
# The two-dimensional Hartmann–Tzeng / Roos bound

This module proves the genuine **two-dimensional** Hartmann–Tzeng bound, where the
defining set of zeros is a full two-parameter grid of exponents

```
{ b + i₁·c₁ + i₂·c₂ : 0 ≤ i₁ ≤ m − 1, 0 ≤ i₂ ≤ s }
```

(with both steps `c₁, c₂` coprime to the length `n`), going beyond the single
arithmetic-progression case of `HartmannTzeng.lean`. The conclusion is the
Hartmann–Tzeng distance bound

```
d(C) ≥ (m + 1) + s = δ + s          (δ := m + 1).
```

The algebraic heart is `ht_vanishing`, proved by **induction on the number `s` of
second-direction shifts**:

* base `s = 0`: a single block of `m` consecutive (step `c₁`) vanishing
  syndromes is the BCH / square-Vandermonde bound, giving `card ≥ m + 1`;
* step `s → s + 1`: removing one support node `l₀` and reweighting the
  coefficients by `Z l − Z l₀` (the "telescoping" / derivative trick) turns the
  `s + 1`-shift system on `T` into an `s`-shift system on `T.erase l₀`, whose
  coefficients stay nonzero precisely because `Z` is injective on the support
  (this is where coprimality of `c₂` is used). The inductive hypothesis then
  yields one more.

## Main results

* `ht_vanishing` — the abstract two-parameter vanishing/cardinality bound.
* `ht_bound` — the Hartmann–Tzeng bound on the Hamming weight of a nonzero word
  with a two-dimensional grid of zero syndromes.
* `htCode`, `mem_htCode`, `htCode_minDist_ge` — the corresponding cyclic code and
  its minimum-distance bound.
-/

open Finset BigOperators

open scoped Classical

namespace CodingTheory
namespace BCH

variable {F : Type*} [Field F]

/-
**The abstract two-parameter Hartmann–Tzeng vanishing bound.** Let `Y, Z` be
field-valued node data, injective on a finite support `T`, and let the
coefficients `U` be nonzero on `T`. If the two-parameter power sums
`∑_{l ∈ T} U l · (Y l)^{i₁} · (Z l)^{i₂}` vanish for all `0 ≤ i₁ < m`
(`m ≥ 1`) and `0 ≤ i₂ ≤ s`, then either `T` is empty or `m + 1 + s ≤ #T`.
-/
theorem ht_vanishing {ι : Type*} [DecidableEq ι] (Y Z : ι → F) (m : ℕ) (hm : 1 ≤ m) :
    ∀ (s : ℕ) (T : Finset ι) (U : ι → F),
      Set.InjOn Y T → Set.InjOn Z T → (∀ l ∈ T, U l ≠ 0) →
      (∀ i₁ < m, ∀ i₂ ≤ s, ∑ l ∈ T, U l * Y l ^ i₁ * Z l ^ i₂ = 0) →
      T = ∅ ∨ m + 1 + s ≤ T.card := by
  intros s T U hY hZ hU hsyn; induction' s with s ih generalizing T U;
  · by_contra! h;
    -- Since T is nonempty and has cardinality less than m + 1, we can order its elements.
    obtain ⟨l, hl⟩ : ∃ l : Fin T.card → ι, Function.Injective l ∧ ∀ i, l i ∈ T := by
      have := Finset.equivFin T;
      exact ⟨ _, Subtype.val_injective.comp this.symm.injective, fun i => this.symm i |>.2 ⟩;
    have h_vandermonde : ∀ i₁ : Fin T.card, ∑ i₂ : Fin T.card, U (l i₂) * Y (l i₂) ^ (i₁ : ℕ) = 0 := by
      intro i₁
      have h_sum : ∑ l ∈ T, U l * Y l ^ (i₁ : ℕ) = 0 := by
        simpa using hsyn i₁ ( by linarith [ Fin.is_lt i₁ ] ) 0 bot_le;
      have h_sum : ∑ l ∈ Finset.image l Finset.univ, U l * Y l ^ (i₁ : ℕ) = 0 := by
        rw [ ← h_sum, Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hl.2 i ) ( by rw [ Finset.card_image_of_injective _ hl.1, Finset.card_fin ] ) ];
      rwa [ Finset.sum_image <| by tauto ] at h_sum;
    have h_vandermonde : Matrix.det (Matrix.of (fun (i₁ i₂ : Fin T.card) => Y (l i₂) ^ (i₁ : ℕ))) ≠ 0 := by
      erw [ Matrix.det_transpose, Matrix.det_vandermonde ];
      simp +decide [ Finset.prod_eq_zero_iff, sub_eq_zero, hl.1.eq_iff, hY.eq_iff ( hl.2 _ ) ( hl.2 _ ) ];
    have h_vandermonde : Matrix.mulVec (Matrix.of (fun (i₁ i₂ : Fin T.card) => Y (l i₂) ^ (i₁ : ℕ))) (fun i => U (l i)) = 0 := by
      ext i₁; simp_all +decide [ Matrix.mulVec, dotProduct, mul_comm ] ;
    have := Matrix.eq_zero_of_mulVec_eq_zero ‹_› h_vandermonde; simp_all +decide [ funext_iff ] ;
    exact this ⟨ 0, Finset.card_pos.mpr h.1 ⟩;
  · by_cases hT : T.Nonempty;
    · obtain ⟨l₀, hl₀⟩ : ∃ l₀, l₀ ∈ T := hT;
      specialize ih ( T.erase l₀ ) ( fun l => U l * ( Z l - Z l₀ ) ) ?_ ?_ ?_ ?_;
      · exact hY.mono ( Finset.erase_subset _ _ );
      · exact hZ.mono ( Finset.erase_subset _ _ );
      · simp +contextual [ sub_eq_zero, hU, hZ.eq_iff ];
        exact fun l hl hl' => hZ.ne hl' hl₀ hl;
      · intro i₁ hi₁ i₂ hi₂
        have h_sum : ∑ l ∈ T, U l * (Z l - Z l₀) * Y l ^ i₁ * Z l ^ i₂ = 0 := by
          have h_sum : ∑ l ∈ T, U l * (Z l - Z l₀) * Y l ^ i₁ * Z l ^ i₂ = ∑ l ∈ T, U l * Y l ^ i₁ * Z l ^ (i₂ + 1) - Z l₀ * ∑ l ∈ T, U l * Y l ^ i₁ * Z l ^ i₂ := by
            rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; ring;
          rw [ h_sum, hsyn i₁ hi₁ ( i₂ + 1 ) ( by linarith ), hsyn i₁ hi₁ i₂ ( by linarith ), MulZeroClass.mul_zero, sub_zero ];
        rw [ ← h_sum, Finset.sum_erase_eq_sub ( Finset.mem_coe.mpr hl₀ ) ] ; simp +decide [ mul_assoc, mul_sub, sub_mul ];
      · cases' ih with h h;
        · specialize hsyn 0 ( by linarith ) 0 ; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, pow_nonneg ];
          rw [ Finset.erase_eq_iff_eq_insert ] at h <;> aesop;
        · grind;
    · exact Or.inl <| Finset.not_nonempty_iff_eq_empty.mp hT

/-
**The Hartmann–Tzeng bound (two-dimensional defining set).** For a primitive
`n`-th root of unity `α` and steps `c₁, c₂` both coprime to `n`, a nonzero word
with vanishing syndromes on the grid of exponents
`{b + i₁·c₁ + i₂·c₂ : 0 ≤ i₁ < m, 0 ≤ i₂ ≤ s}` (`m ≥ 1`) has Hamming weight at
least `(m + 1) + s = δ + s`.
-/
theorem ht_bound {α : F} {n : ℕ} (hα : orderOf α = n)
    (c₁ c₂ : ℕ) (hc1 : c₁ ≠ 0) (hc2 : c₂ ≠ 0)
    (hcop1 : Nat.Coprime n c₁) (hcop2 : Nat.Coprime n c₂)
    (w : Fin n → F) (hw : w ≠ 0) (b m s : ℕ) (hm : 1 ≤ m)
    (hsyn : ∀ i₁ < m, ∀ i₂ ≤ s,
      ∑ i, w i * (α ^ (i : ℕ)) ^ (b + i₁ * c₁ + i₂ * c₂) = 0) :
    m + 1 + s ≤ hammingNorm w := by
  -- Let's define the sets Y, Z, and U as given in the problem.
  set Y : Fin n → F := fun i => (α ^ (i : ℕ)) ^ c₁
  set Z : Fin n → F := fun i => (α ^ (i : ℕ)) ^ c₂
  set U : Fin n → F := fun i => w i * (α ^ (i : ℕ)) ^ b
  set T : Finset (Fin n) := Finset.univ.filter (fun i => w i ≠ 0) with hT_def;
  convert ht_vanishing Y Z m hm s T U _ _ _ _ |> Or.resolve_left <| ?_ using 1;
  · intro i hi j hj hij; have := orderOf_pow_coprime hc1 hcop1 hα; simp_all +decide [ pow_eq_pow_iff_modEq ] ;
    have h_inj : Function.Injective (fun i : Fin n => (α ^ c₁) ^ (i : ℕ)) := by
      have := primitiveRoot_nodes_injective ( show orderOf ( α ^ c₁ ) = n from this ) ; aesop;
    exact h_inj ( by convert hij using 1 <;> ring );
  · intro i hi j hj hij;
    have := CodingTheory.BCH.primitiveRoot_nodes_injective ( hα := orderOf_pow_coprime hc2 hcop2 hα ) ; simp_all +decide [ Fin.ext_iff ] ;
    convert congr_arg Fin.val ( this ( show ( α ^ c₂ ) ^ ( i : ℕ ) = ( α ^ c₂ ) ^ ( j : ℕ ) from ?_ ) ) using 1;
    convert hij using 1 <;> ring!;
  · by_cases hα0 : α = 0 <;> simp_all +decide [ pow_eq_zero_iff' ];
    · lia;
    · exact fun i hi => mul_ne_zero hi ( pow_ne_zero _ ( pow_ne_zero _ hα0 ) );
  · intro i₁ hi₁ i₂ hi₂; convert hsyn i₁ hi₁ i₂ hi₂ using 1; rw [ Finset.sum_filter_of_ne ] ; ring;
    · exact Finset.sum_congr rfl fun _ _ => by ring;
    · aesop;
  · exact Finset.Nonempty.ne_empty ⟨ Classical.choose ( Function.ne_iff.mp hw ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec ( Function.ne_iff.mp hw ) ⟩ ⟩

/-- The **two-dimensional Hartmann–Tzeng code**: words whose syndromes vanish on
the grid of exponents `{b + i₁·c₁ + i₂·c₂ : 0 ≤ i₁ < m, 0 ≤ i₂ ≤ s}`. -/
def htCode {n : ℕ} (x : Fin n → F) (b c₁ c₂ m s : ℕ) : Submodule F (Fin n → F) where
  carrier := { w | ∀ i₁ < m, ∀ i₂ ≤ s, ∑ i, w i * (x i) ^ (b + i₁ * c₁ + i₂ * c₂) = 0 }
  add_mem' := by
    intro a c ha hc i₁ hi₁ i₂ hi₂
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha i₁ hi₁ i₂ hi₂,
      hc i₁ hi₁ i₂ hi₂, add_zero]
  zero_mem' := by intro i₁ hi₁ i₂ hi₂; simp
  smul_mem' := by
    intro r c hc i₁ hi₁ i₂ hi₂
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc i₁ hi₁ i₂ hi₂,
      mul_zero]

/-- Membership in the two-dimensional Hartmann–Tzeng code. -/
theorem mem_htCode {n : ℕ} (x : Fin n → F) (b c₁ c₂ m s : ℕ) (w : Fin n → F) :
    w ∈ htCode x b c₁ c₂ m s
      ↔ ∀ i₁ < m, ∀ i₂ ≤ s, ∑ i, w i * (x i) ^ (b + i₁ * c₁ + i₂ * c₂) = 0 :=
  Iff.rfl

/-- **The Hartmann–Tzeng bound through the minimum-distance API.** -/
theorem htCode_minDist_ge {α : F} {n : ℕ} (hα : orderOf α = n)
    (c₁ c₂ : ℕ) (hc1 : c₁ ≠ 0) (hc2 : c₂ ≠ 0)
    (hcop1 : Nat.Coprime n c₁) (hcop2 : Nat.Coprime n c₂) (b m s : ℕ) (hm : 1 ≤ m)
    (hC : htCode (primitiveRootNodes α n) b c₁ c₂ m s ≠ ⊥) :
    m + 1 + s ≤ minDist (htCode (primitiveRootNodes α n) b c₁ c₂ m s) := by
  rw [minDist_eq_minWeight]
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_eq_minWeight hC
  rw [← hw3]
  refine ht_bound hα c₁ c₂ hc1 hc2 hcop1 hcop2 w hw2 b m s hm ?_
  intro i₁ hi₁ i₂ hi₂
  have := (mem_htCode (primitiveRootNodes α n) b c₁ c₂ m s w).mp hw1 i₁ hi₁ i₂ hi₂
  simpa [primitiveRootNodes] using this

end BCH
end CodingTheory