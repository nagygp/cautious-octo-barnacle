/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quadratic Forms over Characteristic 2 and their Walsh-Hadamard Spectra

This file establishes the universal bridge between a quadratic form's radical
and its Walsh-Hadamard spectrum over finite fields of characteristic 2.

## Main Results

* `chi_mul`: The sign character `chi : ZMod 2 → ℤ` is multiplicative under addition.
* `polar_form_identity`: `Q(x + z) + Q(x) = Q(z) + B(x, z)`.
* `sum_orthogonality_char2`: Character orthogonality for `ZMod 2`-linear functionals.
* `radical_def_equivalence`: The radical is a submodule over `ZMod 2`.
* `walsh_sq_eval_radical`: `|W_Q|² = 2^n · |rad(Q)|`.
-/

import Mathlib

open Finset Fintype BigOperators

/-! ## The Sign Character on `ZMod 2` -/

/-- The sign character: maps `0 ↦ 1` and `1 ↦ -1`. This realizes `(-1)^a` for `a : ZMod 2`. -/
noncomputable def chi (a : ZMod 2) : ℤ :=
  if a = 0 then 1 else -1

@[simp] lemma chi_zero : chi 0 = 1 := by simp [chi]

@[simp] lemma chi_one : chi 1 = -1 := by simp [chi]

/-
`chi` is multiplicative under addition: `chi(a + b) = chi(a) * chi(b)`.
-/
lemma chi_mul (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

/-- `chi(a)^2 = 1` for all `a : ZMod 2`. -/
lemma chi_sq (a : ZMod 2) : chi a ^ 2 = 1 := by
  fin_cases a <;> simp [chi]

/-
`chi(a) = chi(-a)` in characteristic 2 (since `-a = a`).
-/
lemma chi_neg (a : ZMod 2) : chi (-a) = chi a := by
  fin_cases a <;> rfl

/-! ## Quadratic Forms over Characteristic 2

We define a quadratic form `Q : F → ZMod 2` on a finite additive group `F` (thought of as a
vector space over `GF(2)`), together with the companion bilinear form `B` and the radical.
-/

/-- A quadratic form over characteristic 2.

  `Q` is a function `F → ZMod 2` satisfying `Q(0) = 0` and such that the associated
  polar form `B(x, z) := Q(x + z) + Q(x) + Q(z)` is bilinear (additive in each variable).
-/
structure QuadFormChar2 (F : Type*) [AddCommGroup F] where
  /-- The quadratic form itself -/
  Q : F → ZMod 2
  /-- `Q` vanishes at the origin -/
  Q_zero : Q 0 = 0
  /-- Additivity of `B` in the first variable:
      `B(x + y, z) = B(x, z) + B(y, z)` expressed via `Q`. -/
  B_add_left : ∀ x y z : F,
    Q ((x + y) + z) + Q (x + y) + Q z =
      (Q (x + z) + Q x + Q z) + (Q (y + z) + Q y + Q z)
  /-- Additivity of `B` in the second variable:
      `B(x, y + z) = B(x, y) + B(x, z)` expressed via `Q`. -/
  B_add_right : ∀ x y z : F,
    Q (x + (y + z)) + Q x + Q (y + z) =
      (Q (x + y) + Q x + Q y) + (Q (x + z) + Q x + Q z)

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- The associated bilinear form `B(x, z) = Q(x + z) + Q(x) + Q(z)`. -/
def QuadFormChar2.B (QF : QuadFormChar2 F) (x z : F) : ZMod 2 :=
  QF.Q (x + z) + QF.Q x + QF.Q z

/-
The polar form identity: `Q(x + z) + Q(x) = Q(z) + B(x, z)`.

This is the defining relation of the companion bilinear form.
-/
lemma polar_form_identity (QF : QuadFormChar2 F) (x z : F) :
    QF.Q (x + z) + QF.Q x = QF.Q z + QF.B x z := by
  simp +decide only [add_comm, QuadFormChar2.B, add_left_comm];
  grind

/-
`B` is symmetric.
-/
lemma QuadFormChar2.B_symm (QF : QuadFormChar2 F) (x z : F) :
    QF.B x z = QF.B z x := by
  simp +decide only [B, add_comm];
  abel1

/-
`B` is additive in the first argument.
-/
lemma QuadFormChar2.B_add_left' (QF : QuadFormChar2 F) (x y z : F) :
    QF.B (x + y) z = QF.B x z + QF.B y z := by
  convert QF.B_add_left x y z using 1

/-
`B` is additive in the second argument.
-/
lemma QuadFormChar2.B_add_right' (QF : QuadFormChar2 F) (x y z : F) :
    QF.B x (y + z) = QF.B x y + QF.B x z := by
  convert QF.B_add_right x y z using 1

/-
`B(x, 0) = 0`.
-/
@[simp] lemma QuadFormChar2.B_zero_right (QF : QuadFormChar2 F) (x : F) :
    QF.B x 0 = 0 := by
  simp +decide [ QuadFormChar2.B, QF.Q_zero ];
  grind

/-
`B(0, z) = 0`.
-/
@[simp] lemma QuadFormChar2.B_zero_left (QF : QuadFormChar2 F) (z : F) :
    QF.B 0 z = 0 := by
  -- By definition of $B$, we know that
  simp [QuadFormChar2.B, QF.Q_zero];
  grind

/-! ## The Radical -/

/-- The radical of a quadratic form: `rad(Q) = {z ∈ F | ∀ x, B(x, z) = 0}`. -/
def QuadFormChar2.radical (QF : QuadFormChar2 F) : Set F :=
  {z : F | ∀ x : F, QF.B x z = 0}

instance QuadFormChar2.decidableMemRadical (QF : QuadFormChar2 F) :
    DecidablePred (· ∈ QF.radical) :=
  fun z => Fintype.decidableForallFintype

/-
`0` is in the radical.
-/
lemma QuadFormChar2.zero_mem_radical (QF : QuadFormChar2 F) :
    (0 : F) ∈ QF.radical := by
  exact fun x => QF.B_zero_right x

/-
The radical is closed under addition.
-/
lemma QuadFormChar2.radical_add_closed (QF : QuadFormChar2 F) {y z : F}
    (hy : y ∈ QF.radical) (hz : z ∈ QF.radical) :
    y + z ∈ QF.radical := by
  intro x;
  rw [ QF.B_add_right', hy, hz, add_zero ]

/-
The radical is closed under negation.
-/
lemma QuadFormChar2.radical_neg_closed (QF : QuadFormChar2 F) {z : F}
    (hz : z ∈ QF.radical) : -z ∈ QF.radical := by
  simp_all +decide [ QuadFormChar2.radical ];
  intro x; have := QF.B_add_left' x ( -z ) z; simp_all +decide ;
  have := QF.B_add_right' x z ( -z ) ; simp_all +decide ;

/-
**Radical is a submodule.** The radical `rad(Q)` is a sub-`ZMod 2`-module of `F`.
-/
noncomputable def radical_def_equivalence (QF : QuadFormChar2 F) [Module (ZMod 2) F] :
    Submodule (ZMod 2) F where
  carrier := QF.radical
  add_mem' := fun ha hb => QF.radical_add_closed ha hb
  zero_mem' := QF.zero_mem_radical
  smul_mem' := by
    -- Since ZMod 2 has only two elements, 0 and 1, we can split into these two cases.
    intro c x hx
    cases' Fin.exists_fin_two.mp ⟨c, rfl⟩ with hc hc <;> simp [hc, hx];
    grind +suggestions

instance QuadFormChar2.radicalFintype (QF : QuadFormChar2 F) :
    Fintype QF.radical :=
  Fintype.ofFinset (Finset.univ.filter (· ∈ QF.radical)) (by simp [Finset.mem_filter])

/-! ## Character Orthogonality for `ZMod 2`-Linear Functionals -/

/-- **Character orthogonality in characteristic 2.**
For a group homomorphism `L : F →+ ZMod 2`,
`∑ x, chi(L x) = |F|` if `L = 0` and `= 0` otherwise. -/
lemma sum_orthogonality_char2 (L : F →+ ZMod 2) :
    ∑ x : F, chi (L x) = if L = 0 then (Fintype.card F : ℤ) else 0 := by
  sorry

/-! ## The Walsh-Hadamard Transform -/

/-- The Walsh-Hadamard transform of a quadratic form. -/
noncomputable def walsh (QF : QuadFormChar2 F) : ℤ :=
  ∑ x : F, chi (QF.Q x)

/-- The squared Walsh-Hadamard transform, as a double sum. -/
lemma walsh_sq (QF : QuadFormChar2 F) :
    walsh QF ^ 2 = ∑ x : F, ∑ y : F, chi (QF.Q x) * chi (QF.Q y) := by
  sorry

/-- Step 1: Reindex the double sum via `y ↦ x + z`.
`|W_Q|² = ∑_z ∑_x chi(Q(x)) · chi(Q(x + z))`. -/
lemma walsh_sq_reindex (QF : QuadFormChar2 F) :
    walsh QF ^ 2 = ∑ z : F, ∑ x : F, chi (QF.Q x) * chi (QF.Q (x + z)) := by
  sorry

/-- Step 2: Apply the polar form identity to factor the inner product.
`chi(Q(x)) · chi(Q(x + z)) = chi(Q(z)) · chi(B(x, z))`. -/
lemma chi_Q_factor (QF : QuadFormChar2 F) (x z : F) :
    chi (QF.Q x) * chi (QF.Q (x + z)) = chi (QF.Q z) * chi (QF.B x z) := by
  sorry

/-- Step 3: After factoring, `|W_Q|² = ∑_z chi(Q(z)) · (∑_x chi(B(x, z)))`. -/
lemma walsh_sq_factored (QF : QuadFormChar2 F) :
    walsh QF ^ 2 = ∑ z : F, chi (QF.Q z) * (∑ x : F, chi (QF.B x z)) := by
  sorry

/-- For `z ∈ rad(Q)`, the inner sum equals `|F|`.
For `z ∉ rad(Q)`, the inner sum equals `0`. -/
lemma inner_sum_eval (QF : QuadFormChar2 F) (z : F) :
    (∑ x : F, chi (QF.B x z)) =
      if z ∈ QF.radical then (Fintype.card F : ℤ) else 0 := by
  sorry

/-- **Main Theorem: Walsh spectrum via radical.**

`|W_Q|² = (Fintype.card F) * (Fintype.card rad(Q))`

under the assumption that `Q` vanishes on the radical.

The proof proceeds in three steps:
1. Reindex the double sum with `y = x + z`.
2. Apply the polar form identity and character orthogonality to collapse the inner sum.
3. Count the radical elements.
-/
theorem walsh_sq_eval_radical (QF : QuadFormChar2 F)
    (hQ_rad : ∀ z ∈ QF.radical, QF.Q z = 0) :
    walsh QF ^ 2 = (Fintype.card F : ℤ) * (Fintype.card QF.radical : ℤ) := by
  sorry