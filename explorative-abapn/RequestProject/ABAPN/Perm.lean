/-
# APN Functions and Permutations

Connections between APN functions, permutation polynomials, and
injectivity properties of the difference map.

Built on `Equiv.Perm`, `Function.Injective`, `Fintype.card`.
-/
import Mathlib
import RequestProject.ABAPN.Defs

open Finset Function ABAPN

namespace ABAPN.Perm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Two-to-one maps -/

/-- A function is at-most-two-to-one if every fiber has at most 2 elements. -/
def IsAtMostTwoToOne (g : F → F) : Prop :=
  ∀ b : F, (Finset.univ.filter (fun x => g x = b)).card ≤ 2

/-
APN means every nonzero directional derivative is at-most-two-to-one.
-/
lemma isAPN_iff_diffMap_atMost2to1 (f : F → F) :
    IsAPN f ↔ ∀ a : F, a ≠ 0 → IsAtMostTwoToOne (diffMap f a) := by
  constructor <;> intro h a ha b <;> simp_all +decide [ IsAPN, IsAtMostTwoToOne ];
  · exact h a ha b;
  · exact h a ha b

/-! ### APN and injectivity of the "normalized" difference -/

/-
For a power function `x ↦ x^d`, the equation `(x+1)^d + x^d = b`
    determines APN-ness (normalizing `a` out).
-/
lemma powerFn_apn_normalize (d : ℕ) (_hd : 0 < d) [CharP F 2] :
    IsAPN (fun (x : F) => x ^ d) ↔
    ∀ b : F, (Finset.univ.filter (fun x => (x + 1) ^ d - x ^ d = b)).card ≤ 2 := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · convert h 1 one_ne_zero using 1;
  · intro a ha b
    have h_card : (Finset.filter (fun x => (x + a) ^ d - x ^ d = b) Finset.univ).card ≤ 2 := by
      convert h ( b / a ^ d ) using 1;
      refine' Finset.card_bij ( fun x hx => x / a ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_univ, div_eq_iff, mul_pow ];
      · field_simp;
        intro x hx; rw [ ← hx ] ; simp +decide [ ha, sub_mul, div_pow ] ;
      · intro x hx; rw [ show x * a + a = a * ( x + 1 ) by ring, mul_pow ] ; rw [ eq_div_iff ( pow_ne_zero _ ha ) ] at hx; linear_combination hx;
    convert h_card using 1

/-! ### Fiber sizes and permutation property -/

/-
If `g` is a permutation, every fiber has exactly one element.
-/
lemma fiber_card_of_perm (g : Equiv.Perm F) (b : F) :
    (Finset.univ.filter (fun x => g x = b)).card = 1 := by
  exact Finset.card_eq_one.mpr ⟨ g.symm b, by aesop ⟩

/-
A bijective function is at-most-two-to-one (vacuously).
-/
lemma bijective_isAtMostTwoToOne (g : F → F) (hg : Function.Bijective g) :
    IsAtMostTwoToOne g := by
  intro b
  have h_card : (Finset.univ.filter (fun x => g x = b)).card ≤ 1 := by
    exact Finset.card_le_one.2 fun x hx y hy => hg.injective <| by aesop;
  linarith [h_card]

/-! ### Pairing structure of APN fibers -/

/-
In characteristic 2, if `x` is a solution to `f(x+a) + f(x) = b`,
    then so is `x + a`. This is the "pairing" property.
-/
lemma deltaSet_pair [CharP F 2] (f : F → F) (a b : F) (x : F)
    (hx : x ∈ deltaSet f a b) : (x + a) ∈ deltaSet f a b := by
  simp_all +decide [ deltaSet, sub_eq_iff_eq_add ];
  simp_all +decide [ add_assoc, CharTwo.add_self_eq_zero ];
  simp +decide [ ← add_assoc, CharTwo.add_self_eq_zero ]

/-
In characteristic 2, solutions come in pairs `{x, x+a}`,
    so `deltaCount f a b` is always even (for `a ≠ 0`).
-/
lemma deltaCount_even [CharP F 2] (f : F → F) (a : F) (ha : a ≠ 0) (b : F) :
    Even (deltaCount f a b) := by
  -- By definition of $deltaSet$, we know that if $x \in deltaSet f a b$, then $x + a \in deltaSet f a b$.
  have h_pair : ∀ x ∈ ABAPN.deltaSet f a b, x + a ∈ ABAPN.deltaSet f a b := by
    exact?;
  -- Since the involution $x \mapsto x + a$ is fixed-point-free and maps deltaSet to itself, its cardinality is even.
  have h_even_card : ∃ S : Finset (Finset F), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) ∧ ABAPN.deltaSet f a b = Finset.biUnion S id := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) ( ABAPN.deltaSet f a b ), _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · grind +ring;
    · ext x; aesop;
  obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_even_card; simp_all +decide [ deltaCount, Finset.card_biUnion ] ;
  rw [ Finset.card_biUnion ] ; aesop;
  exact fun x hx y hy hxy => hS₂ x hx y hy hxy

/-
Combining: in char 2, APN means `deltaCount ∈ {0, 2}` for `a ≠ 0`.
-/
lemma isAPN_iff_deltaCount_zero_or_two [CharP F 2] (f : F → F) :
    IsAPN f ↔ ∀ a : F, a ≠ 0 → ∀ b : F,
      deltaCount f a b = 0 ∨ deltaCount f a b = 2 := by
  constructor <;> intro hAPN a ha b <;> have := hAPN a ha b <;> simp_all +decide [ IsAPN ];
  · have := ABAPN.Perm.deltaCount_even f a ha b; specialize hAPN a ha b; interval_cases _ : Finset.card ( Finset.filter ( fun x => f ( x + a ) - f x = b ) Finset.univ ) <;> simp_all +decide ;
  · cases hAPN a ha b <;> aesop

end ABAPN.Perm