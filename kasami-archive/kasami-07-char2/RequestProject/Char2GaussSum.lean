import Mathlib

/-!
# Gauss Sum Evaluation for Quadratic Forms in Characteristic 2

## Overview

Over a finite field of characteristic 2, quadratic forms behave fundamentally differently
from odd characteristic. The associated bilinear form `B(x,y) = Q(x+y) + Q(x) + Q(y)` is
always alternating (symplectic), forcing the underlying space to have even dimension for
non-degeneracy.

## Main Result

For a non-degenerate quadratic form `Q : 𝔽₂ⁿ → 𝔽₂` (with `n = 2m`), the **Gauss sum**
  `G(Q) = ∑_{v ∈ 𝔽₂ⁿ} (-1)^{Q(v)}`
satisfies `G(Q)² = 2ⁿ`, so `G(Q) = ±2ᵐ`.

The proof proceeds by expanding `G(Q)²` as a double sum, substituting `w = v + u`,
and using non-degeneracy to show that the inner character sum vanishes for `u ≠ 0`.
-/

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

/-- The `𝔽₂`-vector space `(Fin n → ZMod 2)`. -/
abbrev F2Vec (n : ℕ) := Fin n → ZMod 2

/-- A quadratic form over `𝔽₂` on `𝔽₂ⁿ`, represented as a plain function. -/
structure Char2QuadForm (n : ℕ) where
  /-- The quadratic form itself. -/
  Q : F2Vec n → ZMod 2
  /-- `Q(0) = 0`. -/
  map_zero' : Q 0 = 0
  /-- The quadratic property: `Q(x + y) + Q(x) + Q(y)` is bilinear.
      Equivalently, we require `Q(x + y) = Q(x) + Q(y) + B(x, y)` for the
      associated bilinear form `B`. Here we capture it via the polarization identity. -/
  quadratic' : ∀ (x y z : F2Vec n),
    Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z) + Q x + Q y + Q z + Q 0 = 0

/-- The associated (symmetric = alternating in char 2) bilinear form. -/
def Char2QuadForm.polarForm (QF : Char2QuadForm n) (x y : F2Vec n) : ZMod 2 :=
  QF.Q (x + y) + QF.Q x + QF.Q y

/-- Non-degeneracy of the polar form: for every nonzero `u`, there exists `v`
    with `B(u, v) ≠ 0`. -/
def Char2QuadForm.IsNondegenerate (QF : Char2QuadForm n) : Prop :=
  ∀ u : F2Vec n, u ≠ 0 → ∃ v : F2Vec n, QF.polarForm u v ≠ 0

/-- The Gauss sum of a char-2 quadratic form, as an integer:
    `G(Q) = ∑_{v ∈ 𝔽₂ⁿ} (-1)^{Q(v).val}` -/
def Char2QuadForm.gaussSum (QF : Char2QuadForm n) : ℤ :=
  ∑ v : F2Vec n, (-1 : ℤ) ^ (ZMod.val (QF.Q v))

/-
============================================================================
Helper lemmas
============================================================================

In `ZMod 2`, `val` is either 0 or 1.
-/
lemma ZMod2_val_eq_zero_or_one (a : ZMod 2) : ZMod.val a = 0 ∨ ZMod.val a = 1 := by
  native_decide +revert

/-
`(-1 : ℤ) ^ (ZMod.val a)` for `a : ZMod 2` equals `1 - 2 * (ZMod.val a)`.
-/
lemma neg_one_pow_ZMod2_val (a : ZMod 2) :
    (-1 : ℤ) ^ (ZMod.val a) = 1 - 2 * (ZMod.val a : ℤ) := by
  decide +revert

/-
The character sum of a nontrivial `𝔽₂`-linear functional vanishes.
    If `f : 𝔽₂ⁿ → 𝔽₂` is a nonzero linear map, then `∑_v (-1)^{f(v).val} = 0`.
-/
lemma char_sum_nonzero_linear_vanishes
    (f : F2Vec n →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) :
    ∑ v : F2Vec n, (-1 : ℤ) ^ (ZMod.val (f v)) = 0 := by
  -- Since `f` is nonzero, its kernel has index 2, so exactly half the elements map to 0 and half to 1.
  have h_half : ∑ v : F2Vec n, (-1 : ℤ) ^ (f v).val = ∑ v : F2Vec n, (-1 : ℤ) ^ ((f v + 1).val) := by
    -- Since `f` is nonzero, there exists some `w` such that `f(w) = 1`.
    obtain ⟨w, hw⟩ : ∃ w : F2Vec n, f w = 1 := by
      exact not_forall_not.mp fun h => hf <| LinearMap.ext fun x => by have := h x; have := Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ ; aesop;
    rw [ ← Equiv.sum_comp ( Equiv.addRight w ) ] ; aesop;
  have h_half : ∀ v : F2Vec n, (-1 : ℤ) ^ ((f v + 1).val) = -(-1 : ℤ) ^ (f v).val := by
    intro v; rcases Fin.exists_fin_two.mp ⟨ f v, rfl ⟩ with ( h | h ) <;> simp +decide [ h ] ;
  norm_num [ Finset.sum_neg_distrib, h_half ] at * ; linarith

/-
For a non-degenerate quadratic form, `u ↦ B(u, ·)` is a nonzero linear functional
    whenever `u ≠ 0`. This is a restatement of non-degeneracy.
-/
lemma polar_as_linear_map (QF : Char2QuadForm n) (u : F2Vec n) :
    ∃ fu : F2Vec n →ₗ[ZMod 2] ZMod 2,
      ∀ v, fu v = QF.polarForm u v := by
  refine' ⟨ { toFun := fun v => QF.polarForm u v, map_add' := _, map_smul' := _ }, fun v => rfl ⟩;
  · intro x y; have := QF.quadratic' u x y; ring;
    unfold Char2QuadForm.polarForm; simp_all +decide [ add_assoc ] ;
    grind +suggestions;
  · intro m x; fin_cases m <;> simp +decide [ Char2QuadForm.polarForm ] ;
    simp +decide [ ← two_mul, QF.map_zero' ]

/-
The total number of elements in `𝔽₂ⁿ` is `2^n`.
-/
lemma F2Vec_card (n : ℕ) : Fintype.card (F2Vec n) = 2 ^ n := by
  simp +decide [ F2Vec ]

/-
Summing `1` over all elements of `𝔽₂ⁿ` gives `2^n`.
-/
lemma F2Vec_sum_one (n : ℕ) : ∑ (_ : F2Vec n), (1 : ℤ) = 2 ^ n := by
  norm_num [ F2Vec_card ]

/-
Substitution lemma: summing `g(v + u)` over all `v` equals summing `g(v)`.
    (Translation invariance of finite group summation.)
-/
lemma sum_translate_F2Vec
    (g : F2Vec n → ℤ) (u : F2Vec n) :
    ∑ v : F2Vec n, g (v + u) = ∑ v : F2Vec n, g v := by
  exact Equiv.sum_comp ( Equiv.addRight u ) g

/-
============================================================================
Inner character sum for the double-sum expansion
============================================================================

For a quadratic form `Q` and fixed `u`, the inner sum
    `∑_v (-1)^{Q(v+u) + Q(v)}` equals `(-1)^{Q(u)} * ∑_v (-1)^{B(u,v)}`
    where `B` is the polar form. This follows from the polarization identity
    `Q(v+u) = Q(v) + Q(u) + B(v,u)` (in char 2, addition = subtraction).
-/
lemma inner_sum_polar (QF : Char2QuadForm n) (u : F2Vec n) :
    ∑ v : F2Vec n, (-1 : ℤ) ^ (ZMod.val (QF.Q (v + u) + QF.Q v)) =
    (-1 : ℤ) ^ (ZMod.val (QF.Q u)) *
      ∑ v : F2Vec n, (-1 : ℤ) ^ (ZMod.val (QF.polarForm v u)) := by
  have h_polar : ∀ v : F2Vec n, (QF.Q (v + u) + QF.Q v).val = (QF.Q u + QF.polarForm v u).val := by
    unfold Char2QuadForm.polarForm;
    grind +suggestions;
  rw [ Finset.mul_sum _ _ _ ];
  refine' Finset.sum_congr rfl fun v hv => _;
  rcases h : QF.Q u with ( _ | _ | u ) <;> rcases h' : QF.polarForm v u with ( _ | _ | v ) <;> simp_all +decide;
  · linarith;
  · linarith;
  · linarith;
  · linarith

/-
For nonzero `u`, if the polar form is non-degenerate, the inner character sum
    `∑_v (-1)^{B(v, u)}` vanishes.
-/
lemma inner_char_sum_vanishes (QF : Char2QuadForm n) (u : F2Vec n)
    (hu : u ≠ 0) (hnd : QF.IsNondegenerate) :
    ∑ v : F2Vec n, (-1 : ℤ) ^ (ZMod.val (QF.polarForm v u)) = 0 := by
  obtain ⟨ fu, hfu ⟩ := ( polar_as_linear_map QF u );
  convert char_sum_nonzero_linear_vanishes fu _ using 1;
  · simp +decide [ hfu, Char2QuadForm.polarForm ];
    ac_rfl;
  · exact fun h => by obtain ⟨ v, hv ⟩ := hnd u hu; specialize hfu v; aesop;

/-
============================================================================
Main theorem: G(Q)² = 2ⁿ
============================================================================

**Gauss sum squared evaluation for char-2 quadratic forms.**

For a non-degenerate quadratic form `Q` on `𝔽₂ⁿ`,
  `G(Q)² = 2ⁿ`.

**Proof sketch.** Expand `G(Q)² = (∑_v (-1)^{Q(v)})² = ∑_{v,w} (-1)^{Q(v)+Q(w)}`.
Substitute `w = v + u`:
  `G(Q)² = ∑_u ∑_v (-1)^{Q(v) + Q(v+u)}`
The inner sum, by the polarization identity `Q(v+u) = Q(v) + Q(u) + B(v,u)`, becomes
  `(-1)^{Q(u)} · ∑_v (-1)^{B(v,u)}`.
For `u ≠ 0`, non-degeneracy implies `v ↦ B(v,u)` is a nontrivial linear functional,
so `∑_v (-1)^{B(v,u)} = 0`.
For `u = 0`, the inner sum is `∑_v 1 = 2ⁿ`, and `(-1)^{Q(0)} = 1`.
Hence `G(Q)² = 1 · 2ⁿ = 2ⁿ`.
-/
theorem char2_gauss_sum_sq (QF : Char2QuadForm n)
    (hnd : QF.IsNondegenerate) :
    QF.gaussSum ^ 2 = 2 ^ n := by
  -- Expand the square into a double sum: $G(Q)^2 = \sum_{v} \sum_{u} (-1)^{Q(v) + Q(v+u)}$
  have h_double_sum : (QF.gaussSum : ℤ) ^ 2 = ∑ u : F2Vec n, ∑ v : F2Vec n, (-1 : ℤ) ^ (QF.Q (v + u) + QF.Q v |> ZMod.val) := by
    convert Finset.sum_comm using 3 ; ring;
    rw [ sq, Char2QuadForm.gaussSum ];
    rw [ Finset.sum_mul ];
    simp +decide only [Finset.mul_sum _ _ _];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ ← Equiv.sum_comp ( Equiv.addLeft x ) ] ; norm_num;
    refine' Finset.sum_congr rfl fun y hy => _;
    cases Fin.exists_fin_two.mp ⟨ QF.Q x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ QF.Q ( x + y ), rfl ⟩ <;> simp_all +decide;
  -- We can now apply the lemma about inner sums to each term in the double sum.
  have h_inner_sum : ∀ u : F2Vec n, u ≠ 0 → ∑ v : F2Vec n, (-1 : ℤ) ^ (ZMod.val (QF.Q (v + u) + QF.Q v)) = 0 := by
    intros u hu; rw [ inner_sum_polar QF u ] ; simp_all +decide [ inner_char_sum_vanishes ] ;
  simp_all +decide;
  rw [ Finset.sum_eq_single_of_mem 0 ] <;> simp_all +decide [ ZMod.val_add ];
  norm_num [ ← two_mul ]

/-
As a corollary, `|G(Q)| = 2^(n/2)` when `n` is even, i.e., `G(Q) = ±2^m`
    for `n = 2m`.
-/
theorem char2_gauss_sum_abs (m : ℕ) (QF : Char2QuadForm (2 * m))
    (hnd : QF.IsNondegenerate) :
    QF.gaussSum = 2 ^ m ∨ QF.gaussSum = -(2 ^ m) := by
  exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [ char2_gauss_sum_sq QF hnd ] ; ring;

end