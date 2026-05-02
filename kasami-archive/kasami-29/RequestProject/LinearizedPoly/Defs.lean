/-
# Linearized Polynomials over Finite Fields — Definitions and Basic Properties

This module defines q-linearized polynomials over finite fields and establishes
their fundamental properties.

## Main definitions

* `IsLinearizedFn` : Predicate that a function `F → F` is additive
* `frobIter` : The iterated Frobenius `x ↦ x^{2^k}` in characteristic 2
* `artinSchreier` : The Artin-Schreier map `x ↦ x² + x`
* `linPolyL` : The operator `L_k(x) = x^{2^{2k}} + x^{2^k} + x`
* `linPolyM` : The operator `M_k(x) = x^{2^k} + x`

## References

* Lidl, Niederreiter, *Finite Fields*, Chapter 3.4
-/
import Mathlib

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Iterated Frobenius -/

/-- The iterated Frobenius endomorphism `x ↦ x^{2^k}` in characteristic 2. -/
def frobIter (k : ℕ) (x : F) : F := x ^ (2 ^ k)

/-- The iterated Frobenius is additive in characteristic 2. -/
theorem frobIter_add (k : ℕ) (x y : F) :
    frobIter k (x + y) = frobIter k x + frobIter k y := by
  simp only [frobIter]
  exact add_pow_char_pow x y 2 k

/-- Composition of iterated Frobenius. -/
theorem frobIter_comp (j k : ℕ) (x : F) :
    frobIter j (frobIter k x) = frobIter (k + j) x := by
  simp only [frobIter, ← pow_mul, pow_add]

/-! ### Additive (Linearized) Functions -/

/-- A function `P : F → F` is *linearized* (additive) if `P(x + y) = P(x) + P(y)`. -/
def IsLinearizedFn (P : F → F) : Prop :=
  ∀ x y : F, P (x + y) = P x + P y

/-- An additive function maps 0 to 0. -/
theorem IsLinearizedFn.map_zero {P : F → F} (hP : IsLinearizedFn P) : P 0 = 0 := by
  have h := hP 0 0; rw [add_zero] at h; rw [h, CharTwo.add_self_eq_zero]

/-- The kernel of an additive function is closed under addition. -/
theorem IsLinearizedFn.ker_add {P : F → F} (hP : IsLinearizedFn P)
    {x y : F} (hx : P x = 0) (hy : P y = 0) : P (x + y) = 0 := by
  rw [hP x y, hx, hy, add_zero]

/-- The iterated Frobenius is linearized. -/
theorem frobIter_linearized (k : ℕ) : IsLinearizedFn (frobIter (F := F) k) :=
  fun x y => frobIter_add k x y

/-- A sum of linearized functions is linearized. -/
theorem IsLinearizedFn.add {P Q : F → F} (hP : IsLinearizedFn P) (hQ : IsLinearizedFn Q) :
    IsLinearizedFn (fun x => P x + Q x) := by
  intro x y; simp only []; rw [hP x y, hQ x y]; ring

/-! ### Artin-Schreier Map -/

/-- The Artin-Schreier map `x ↦ x² + x` in characteristic 2. -/
def artinSchreier (x : F) : F := x ^ 2 + x

/-- The Artin-Schreier map is additive. -/
theorem artinSchreier_add (x y : F) :
    artinSchreier (x + y) = artinSchreier x + artinSchreier y := by
  unfold artinSchreier
  rw [add_pow_char x y 2]; ring

/-- The Artin-Schreier map is linearized. -/
theorem artinSchreier_linearized : IsLinearizedFn (artinSchreier (F := F)) :=
  fun x y => artinSchreier_add x y

/-- `artinSchreier(x) = x * (x + 1)`. -/
theorem artinSchreier_eq_mul (x : F) :
    artinSchreier x = x * (x + 1) := by
  unfold artinSchreier; ring

/-- `artinSchreier(x) = 0 ↔ x = 0 ∨ x = 1`. -/
theorem artinSchreier_eq_zero_iff (x : F) :
    artinSchreier x = 0 ↔ x = 0 ∨ x = 1 := by
  rw [artinSchreier_eq_mul, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right; exact CharTwo.add_self_eq_zero 1

/-- The kernel of the Artin-Schreier map is `{0, 1}`. -/
theorem artinSchreier_ker_eq :
    (Finset.univ.filter (fun x : F => artinSchreier x = 0)) = ({0, 1} : Finset F) := by
  ext x; simp [artinSchreier_eq_zero_iff]

/-- The kernel of the Artin-Schreier map has exactly 2 elements. -/
theorem artinSchreier_ker_card :
    (Finset.univ.filter (fun x : F => artinSchreier x = 0)).card = 2 := by
  rw [artinSchreier_ker_eq]
  simp [Finset.card_pair (show (0 : F) ≠ 1 from one_ne_zero.symm)]

/-! ### The Linearized Operator L_k -/

/-- The linearized operator `L_k(x) = x^{2^{2k}} + x^{2^k} + x`.
    Its conventional polynomial associate is `t^{2k} + t^k + 1`. -/
def linPolyL (k : ℕ) (x : F) : F :=
  x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + x

/-- `L_k` is additive (linearized). -/
theorem linPolyL_add (k : ℕ) (x y : F) :
    linPolyL k (x + y) = linPolyL k x + linPolyL k y := by
  unfold linPolyL
  rw [add_pow_char_pow x y 2 (2 * k), add_pow_char_pow x y 2 k]; ring

/-- `L_k` is linearized. -/
theorem linPolyL_linearized (k : ℕ) : IsLinearizedFn (linPolyL (F := F) k) :=
  fun x y => linPolyL_add k x y

/-- `L_k(0) = 0`. -/
@[simp]
theorem linPolyL_zero (k : ℕ) : linPolyL (F := F) k 0 = 0 := by
  simp [linPolyL]

/-- The kernel of `L_k` is closed under addition. -/
theorem linPolyL_ker_add (k : ℕ) {x y : F}
    (hx : linPolyL k x = 0) (hy : linPolyL k y = 0) :
    linPolyL k (x + y) = 0 :=
  (linPolyL_linearized k).ker_add hx hy

/-! ### The operator M_k(x) = x^{2^k} + x -/

/-- The operator `M_k(x) = x^{2^k} + x`. Special case: `M_1 = artinSchreier`. -/
def linPolyM (k : ℕ) (x : F) : F := x ^ (2 ^ k) + x

/-- `M_k` is additive. -/
theorem linPolyM_add (k : ℕ) (x y : F) :
    linPolyM k (x + y) = linPolyM k x + linPolyM k y := by
  unfold linPolyM
  rw [add_pow_char_pow x y 2 k]; ring

/-- `M_k` is linearized. -/
theorem linPolyM_linearized (k : ℕ) : IsLinearizedFn (linPolyM (F := F) k) :=
  fun x y => linPolyM_add k x y

/-- `M_1` is the Artin-Schreier map. -/
theorem linPolyM_one_eq_artinSchreier (x : F) :
    linPolyM 1 x = artinSchreier x := by
  simp [linPolyM, artinSchreier]

end
