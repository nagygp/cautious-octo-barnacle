/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Additive Character Orthogonality over Full Dual Groups of Finite Fields

This module establishes the orthogonality relation for additive characters
summed over the full Pontryagin dual group of finite fields `F_{2^n}`.

## The dual group

For a finite abelian group `G`, the **Pontryagin dual** `Ĝ = AddChar G ℂ` is the group
of all additive characters `ψ : G → ℂ×`. For finite fields `F_{2^n}`, the dual group
is canonically isomorphic to `F_{2^n}` itself, via the parametrization
`a ↦ ψ_a` where `ψ_a(x) = χ(ax)`, and `χ` is the canonical additive character
defined by `χ(x) = (-1)^{Tr(x)}`.

## Main results

### Full dual group orthogonality (ℂ-valued)
- `dual_orthogonality_C`: `∑_{ψ : AddChar F ℂ} ψ(s) = |F|` if `s = 0`, else `0`
- `dual_orthogonality_C_ne_zero`: `∑_{ψ} ψ(s) = 0` for `s ≠ 0`
- `card_addChar_F2n`: `|AddChar (F2n n) ℂ| = 2^n`

### Parametrization by the field (ℤ-valued)
- `dualChar`: the map `a ↦ ψ_a` where `ψ_a(x) = χ(ax)`
- `dualChar_injective`: the parametrization is injective
- `dualChar_orthogonality`: `∑_a χ(a·s) = 2^n · [s = 0]` (summing over `a`)
- `chi_inner_product_dual`: `∑_a χ(a·x) · χ(a·y) = 2^n · [x = y]`

### Connection between ℂ and ℤ formulations
- `dualChar_sum_cast`: the ℤ-valued sum embeds into ℂ correctly
- `dual_orthogonality_consistent`: consistency of ℤ and ℂ formulations

### Additional identities
- `dual_plancherel`: `∑_a χ(a·s)² = 2^n` (Plancherel)
- `dual_convolution`: convolution identity via dual characters
- `fourier_coefficient_recovery`: Fourier inversion

## Mathematical background

The key theorem is the **second orthogonality relation** for characters of finite
abelian groups:

  `∑_{ψ ∈ Ĝ} ψ(s) = |G| · δ_{s,0}`

This is dual to the first orthogonality relation `∑_{x ∈ G} ψ(x) = |G| · δ_{ψ,1}`.

For `G = F_{2^n}`, this is essential in:
- Walsh–Hadamard transform inversion
- Parseval's identity for the WHT
- The spectral approach to P₃ and difference set theory
- Fourier analysis on Boolean functions

## References
- [Lidl, Niederreiter, *Finite Fields*][lidl1997], Chapter 5
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §2.3, §4.1
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ## Section 1: ℂ-Valued Dual Group Orthogonality

These results use Mathlib's Pontryagin duality machinery for `AddChar G ℂ`.
The main theorem `AddChar.sum_apply_eq_ite` gives the orthogonality relation
directly for any finite abelian group. We specialize it to `F_{2^n}`.
-/

/-- The cardinality of the dual group `AddChar (F2n n) ℂ` equals `2^n`.
    This is a consequence of Pontryagin duality for finite abelian groups:
    the dual group has the same cardinality as the original group. -/
theorem card_addChar_F2n {n : ℕ} (hn : n ≠ 0) :
    Fintype.card (AddChar (F2n n) ℂ) = 2 ^ n := by
  rw [AddChar.card_eq, F2n.card n hn]

/-- **Dual orthogonality (ℂ-valued)**: The sum of all additive characters at a point `s`
    equals `|F_{2^n}|` if `s = 0` and `0` if `s ≠ 0`.
    This is the **second orthogonality relation** for characters. -/
theorem dual_orthogonality_C {n : ℕ} (hn : n ≠ 0) (s : F2n n) :
    ∑ ψ : AddChar (F2n n) ℂ, ψ s =
    if s = 0 then (2 ^ n : ℂ) else 0 := by
  rw [AddChar.sum_apply_eq_ite]
  split_ifs <;> simp [F2n.card n hn]

/-- Dual orthogonality for nonzero elements: `∑_ψ ψ(s) = 0` when `s ≠ 0`. -/
theorem dual_orthogonality_C_ne_zero {n : ℕ} (s : F2n n) (hs : s ≠ 0) :
    ∑ ψ : AddChar (F2n n) ℂ, ψ s = 0 := by
  rwa [AddChar.sum_apply_eq_zero_iff_ne_zero]

/-- Dual orthogonality for zero: `∑_ψ ψ(0) = 2^n`. -/
theorem dual_orthogonality_C_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ ψ : AddChar (F2n n) ℂ, ψ 0 = (2 ^ n : ℂ) := by
  rw [AddChar.sum_apply_eq_ite, if_pos rfl]
  simp [F2n.card n hn]

/-! ## Section 2: The Dual Character Parametrization

For finite fields `F_{2^n}`, every additive character is of the form
`ψ_a(x) = χ(ax)` for some `a ∈ F_{2^n}`, where `χ` is the canonical
character defined by `χ(x) = (-1)^{Tr(x)}`.

We construct the parametrization `a ↦ ψ_a` as an `AddChar`, prove it is
injective, and use it to reduce dual group sums to sums over the field.
-/

/-- The family of additive characters `ψ_a(x) = χ(a·x)` for `a ∈ F_{2^n}`.
    This map `a ↦ ψ_a` is an injective group homomorphism from `F_{2^n}`
    to the dual group `AddChar (F2n n) ℤ`. -/
noncomputable def dualChar {n : ℕ} (a : F2n n) : AddChar (F2n n) ℤ where
  toFun := fun x => chi n (a * x)
  map_zero_eq_one' := by simp [chi_zero]
  map_add_eq_mul' := by intro x y; rw [mul_add, chi_add]

@[simp]
theorem dualChar_apply {n : ℕ} (a x : F2n n) : dualChar a x = chi n (a * x) := rfl

/-- `ψ_0` is the trivial character. -/
@[simp]
theorem dualChar_zero {n : ℕ} : (dualChar (0 : F2n n)) = 1 := by
  ext x; simp [chi_zero]

/-
`ψ_a = ψ_b` implies `a = b` (the parametrization is injective).

    *Proof.* If `ψ_a = ψ_b`, then `χ(ax) = χ(bx)` for all `x`.
    So `χ((a-b)x) = 1` for all `x`, meaning `Tr((a-b)x) = 0` for all `x`.
    Since `Tr` is surjective, this forces `a - b = 0`, i.e., `a = b`.
-/
theorem dualChar_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (dualChar (n := n)) := by
  intro a b h_eq
  have h_eq_char : ∀ x : F2n n, chi n (a * x) = chi n (b * x) := by
    exact fun x => congr_arg ( fun f => f x ) h_eq;
  -- If `a ≠ b`, then `a + b ≠ 0`, so we can apply `chi_orthogonality`.
  by_cases hab : a + b = 0;
  · grind;
  · have h_sum : ∑ x : F2n n, chi n ((a + b) * x) = 0 := by
      exact chi_orthogonality hn _ hab;
    simp_all +decide [ add_mul, chi_add ];
    simp_all +decide [ ← sq, chi_sq ]

/-- The parametrization is a group homomorphism: `ψ_{a+b} = ψ_a · ψ_b`. -/
theorem dualChar_add {n : ℕ} (a b : F2n n) :
    dualChar (a + b) = dualChar a * dualChar b := by
  ext x; simp [add_mul, chi_add]

/-! ## Section 3: ℤ-Valued Dual Orthogonality

The key orthogonality relation in the ℤ-valued formulation used by the
Walsh–Hadamard transform machinery. Since all ℂ-valued characters of `F_{2^n}`
are of the form `ψ_a`, summing over the dual group is equivalent to summing
over `a ∈ F_{2^n}`.
-/

/-- **ℤ-valued dual orthogonality**: `∑_a χ(a·s) = 2^n` if `s = 0`, else `0`.
    This is the parametrized form of the second orthogonality relation,
    obtained by summing `ψ_a(s) = χ(as)` over all `a ∈ F_{2^n}`. -/
theorem dualChar_orthogonality {n : ℕ} (hn : n ≠ 0) (s : F2n n) :
    ∑ a : F2n n, chi n (a * s) = if s = 0 then (2 ^ n : ℤ) else 0 := by
  -- This is equivalent to chi_sum with arguments swapped via commutativity.
  have : ∀ a : F2n n, chi n (a * s) = chi n (s * a) := fun a => by ring_nf
  simp_rw [this]
  exact chi_sum hn s

/-- Dual orthogonality for nonzero elements (ℤ version). -/
theorem dualChar_orthogonality_ne_zero {n : ℕ} (hn : n ≠ 0) (s : F2n n) (hs : s ≠ 0) :
    ∑ a : F2n n, chi n (a * s) = 0 := by
  rw [dualChar_orthogonality hn s, if_neg hs]

/-- Dual orthogonality at zero (ℤ version). -/
theorem dualChar_orthogonality_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ a : F2n n, chi n (a * 0) = (2 ^ n : ℤ) := by
  rw [dualChar_orthogonality hn 0, if_pos rfl]

/-- **Kronecker delta property**: `∑_a ψ_a(x) · ψ_a(y) = 2^n · [x = y]`.
    This is the inner product orthogonality in the dual formulation. -/
theorem chi_inner_product_dual {n : ℕ} (hn : n ≠ 0) (x y : F2n n) :
    ∑ a : F2n n, chi n (a * x) * chi n (a * y) =
    if x = y then (2 ^ n : ℤ) else 0 := by
  have key : ∀ a : F2n n,
      chi n (a * x) * chi n (a * y) = chi n (a * (x + y)) := by
    intro a; rw [mul_add, ← chi_add]
  simp_rw [key]
  rw [dualChar_orthogonality hn]
  simp [add_eq_zero_iff_eq_neg]

/-! ## Section 4: Fourier Inversion Components

These lemmas provide the building blocks for Fourier inversion and
the Walsh–Hadamard transform on `F_{2^n}`.
-/

/-- **Fourier inversion kernel**: `∑_a χ(a·(x+y)) = 2^n · δ_{x,y}`.
    In char 2, `x - y = x + y`, so `x + y = 0 ↔ x = y`. -/
theorem fourier_inversion_kernel {n : ℕ} (hn : n ≠ 0) (x y : F2n n) :
    ∑ a : F2n n, chi n (a * (x + y)) =
    if x = y then (2 ^ n : ℤ) else 0 := by
  rw [dualChar_orthogonality hn]
  simp [add_eq_zero_iff_eq_neg]

/-
**Fourier expansion coefficient**: For any function `f : F_{2^n} → ℤ`,
    `∑_a (∑_x f(x) · χ(ax)) · χ(as) = 2^n · f(s)`.
-/
theorem fourier_coefficient_recovery {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → ℤ) (s : F2n n) :
    ∑ a : F2n n, (∑ x : F2n n, f x * chi n (a * x)) * chi n (a * s) =
    (2 ^ n : ℤ) * f s := by
  simp +decide only [Finset.sum_mul _ _ _];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ x : F2n n, ∑ i : F2n n, f i * chi n (x * i) * chi n (x * s) = ∑ i : F2n n, f i * ∑ x : F2n n, chi n (x * (i + s)) := by
    rw [ Finset.sum_comm ];
    simp +decide only [mul_assoc, mul_add, chi_add, Finset.mul_sum _ _ _];
  rw [ h_fubini, Finset.sum_eq_single s ];
  · simp_all +decide [ F2n.add_self, mul_add, chi_add ];
    rw [ mul_comm, chi_zero ] ; norm_num [ F2n.card n hn ];
  · intro b _ hb; rw [ dualChar_orthogonality_ne_zero hn ( b + s ) ( by simpa [ add_eq_zero_iff_eq_neg ] using hb ) ] ; ring;
  · aesop

/-! ## Section 5: Connection Between ℂ and ℤ Formulations

We show that the ℤ-valued orthogonality is consistent with Mathlib's
ℂ-valued Pontryagin duality. The canonical character `χ` lifts to ℂ
via the embedding `ℤ ↪ ℂ`, and the parametric family covers all
ℂ-valued characters of `F_{2^n}`.
-/

/-- The canonical character lifted to `ℂ`: `χ_ℂ(x) = (-1)^{Tr(x)}`. -/
noncomputable def chiC (n : ℕ) (x : F2n n) : ℂ :=
  (chi n x : ℂ)

theorem chiC_eq_coe {n : ℕ} (x : F2n n) : chiC n x = ↑(chi n x) := rfl

theorem chiC_add {n : ℕ} (x y : F2n n) : chiC n (x + y) = chiC n x * chiC n y := by
  simp [chiC, chi_add, Int.cast_mul]

theorem chiC_zero (n : ℕ) : chiC n (0 : F2n n) = 1 := by
  simp [chiC, chi_zero]

/-- The canonical character as a ℂ-valued `AddChar`. -/
noncomputable def chiAddCharC (n : ℕ) : AddChar (F2n n) ℂ where
  toFun := chiC n
  map_zero_eq_one' := chiC_zero n
  map_add_eq_mul' := chiC_add

@[simp]
theorem chiAddCharC_apply {n : ℕ} (x : F2n n) : chiAddCharC n x = ↑(chi n x) := rfl

/-- The ℂ-valued dual character family: `ψ_a^ℂ(x) = χ_ℂ(ax)`. -/
noncomputable def dualCharC {n : ℕ} (a : F2n n) : AddChar (F2n n) ℂ where
  toFun := fun x => chiC n (a * x)
  map_zero_eq_one' := by simp [chiC_zero]
  map_add_eq_mul' := by intro x y; rw [mul_add]; exact chiC_add _ _

@[simp]
theorem dualCharC_apply {n : ℕ} (a x : F2n n) : dualCharC a x = ↑(chi n (a * x)) := rfl

/-
The ℂ-valued parametrization is injective.
-/
theorem dualCharC_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (dualCharC (n := n)) := by
  -- If dualCharC a = dualCharC b, then for all x, chiC(ax) = chiC(bx), which means chi(ax) = chi(bx) (since chiC is just the cast of chi). Then use dualChar_injective to conclude a = b.
  intro a b hab
  have h_eq : ∀ x : F2n n, chi n (a * x) = chi n (b * x) := by
    intro x; exact_mod_cast (by simpa [chiAddCharC_apply] using congr_arg (fun f : AddChar (F2n n) ℂ => f x) hab : (chi n (a * x) : ℂ) = chi n (b * x));
  exact dualChar_injective hn ( by ext x; simpa using h_eq x )

/-- The ℤ-valued sum embeds into the ℂ-valued sum under `Int.cast`. -/
theorem dualChar_sum_cast {n : ℕ} (s : F2n n) :
    (↑(∑ a : F2n n, chi n (a * s)) : ℂ) =
    ∑ a : F2n n, (↑(chi n (a * s)) : ℂ) := by
  push_cast; rfl

/-
The ℤ-valued dual orthogonality is consistent with the ℂ-valued version:
    the parametric sum equals the full dual group sum under the embedding.
-/
theorem dual_orthogonality_consistent {n : ℕ} (hn : n ≠ 0) (s : F2n n) :
    (↑(∑ a : F2n n, chi n (a * s)) : ℂ) =
    if s = 0 then (2 ^ n : ℂ) else 0 := by
  rw [dualChar_sum_cast, show ∑ a : F2n n, (↑(chi n (a * s)) : ℂ) =
      ∑ a : F2n n, dualCharC a s from by simp]
  convert dualChar_orthogonality hn s using 1;
  erw [ ← @Int.cast_inj ℂ ] ; norm_num [ dualChar_sum_cast ]

/-! ## Section 6: Plancherel and Convolution -/

/-- **Plancherel identity**: `∑_a χ(a·s)² = 2^n`.
    Since `χ(x)² = 1` for all `x`, this just counts the elements. -/
theorem dual_plancherel {n : ℕ} (hn : n ≠ 0) (s : F2n n) :
    ∑ a : F2n n, chi n (a * s) ^ 2 = (2 ^ n : ℤ) := by
  simp only [chi_sq, Finset.sum_const, Finset.card_univ]
  rw [F2n.card n hn]; simp

/-- **Character sum indicator**: `∑_a ψ_a(s) · ψ_a(t)⁻¹ = 2^n · [s = t]`.
    In char 2, `ψ_a⁻¹ = ψ_a` (since `χ² = 1`), so this reduces to
    `chi_inner_product_dual`. -/
theorem dualChar_indicator {n : ℕ} (hn : n ≠ 0) (s t : F2n n) :
    ∑ a : F2n n, chi n (a * s) * chi n (a * t) =
    if s = t then (2 ^ n : ℤ) else 0 :=
  chi_inner_product_dual hn s t

/-
**Convolution via dual characters**: For `f, g : F_{2^n} → ℤ`,
    `∑_a (∑_x f(x)χ(ax))(∑_y g(y)χ(ay)) = 2^n · ∑_z f(z) · g(z)`.
    (In char 2, `-z = z`.)
-/
theorem dual_convolution {n : ℕ} (hn : n ≠ 0)
    (f g : F2n n → ℤ) :
    ∑ a : F2n n, (∑ x : F2n n, f x * chi n (a * x)) *
                 (∑ y : F2n n, g y * chi n (a * y)) =
    (2 ^ n : ℤ) * ∑ z : F2n n, f z * g z := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, (∑ x : F2n n, f x * chi n (a * x)) * (∑ y : F2n n, g y * chi n (a * y)) = ∑ x : F2n n, ∑ y : F2n n, f x * g y * ∑ a : F2n n, chi n (a * (x + y)) := by
    simp +decide only [Finset.sum_mul _ _ _, Finset.mul_sum, mul_left_comm];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_comm ] ; congr ; ext ; ring;
    simp +decide only [mul_comm, chi_add];
    ac_rfl;
  -- By the orthogonality of the characters, we know that $\sum_{a} \chi(a(x+y))$ is $2^n$ if $x = y$ and $0$ otherwise.
  have h_orthogonality : ∀ x y : F2n n, ∑ a : F2n n, chi n (a * (x + y)) = if x = y then (2 ^ n : ℤ) else 0 := by
    exact fun x y => fourier_inversion_kernel hn x y
  simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ]

end
end Kasami