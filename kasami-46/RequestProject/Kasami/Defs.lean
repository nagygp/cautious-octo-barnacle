/-
# Kasami Codes: Basic Definitions

This file establishes the foundational definitions for the formalization
of Kasami's 1971 work on subcodes of the 2nd-order binary Reed-Muller codes.

We define:
- Linear codes over GF(2) as submodules of `Fin n → ZMod 2`
- Hamming weight and distance
- Weight enumerator polynomials
- Dual codes via inner product
- Cyclic codes
- The minimum distance of a code
-/

import Mathlib

open Finset BigOperators

noncomputable section

/-! ## Linear Codes over GF(2) -/

/-- A binary linear code of length `n` is a submodule of `(Fin n → ZMod 2)` over `ZMod 2`. -/
abbrev BinaryLinearCode (n : ℕ) := Submodule (ZMod 2) (Fin n → ZMod 2)

namespace BinaryLinearCode

variable {n : ℕ}

/-- The dimension of a binary linear code. -/
noncomputable def dimension (C : BinaryLinearCode n) : ℕ :=
  Module.finrank (ZMod 2) C

/-- The Hamming weight of a codeword (number of nonzero coordinates). -/
def weight (c : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => c i ≠ 0)).card

/-- The minimum weight of a nonzero codeword in a code. -/
noncomputable def minWeight (C : BinaryLinearCode n) : ℕ :=
  sInf {w : ℕ | ∃ c ∈ C, (c : Fin n → ZMod 2) ≠ 0 ∧ weight c = w}

/-- The inner product over GF(2). -/
def innerGF2 {n : ℕ} (x y : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, x i * y i

/-- The dual code of a binary linear code. -/
def dual (C : BinaryLinearCode n) : BinaryLinearCode n where
  carrier := {y | ∀ x ∈ C, innerGF2 x y = 0}
  add_mem' := by
    intro a b ha hb x hx
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    unfold innerGF2
    simp only [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
    have := ha x hx; unfold innerGF2 at this; rw [this]
    have := hb x hx; unfold innerGF2 at this; rw [this, add_zero]
  zero_mem' := by
    intro x _
    simp [innerGF2]
  smul_mem' := by
    intro r a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    intro x hx
    unfold innerGF2
    simp only [Pi.smul_apply, smul_eq_mul]
    have : r = 0 ∨ r = 1 := by fin_cases r <;> simp
    rcases this with rfl | rfl
    · simp
    · simp only [one_mul]
      exact ha x hx

/-- The number of codewords of weight `w` in a code `C`,
    counting over elements of `Fin n → ZMod 2` that belong to `C`. -/
noncomputable def weightCount (C : BinaryLinearCode n) (w : ℕ) : ℕ :=
  Set.ncard {c : Fin n → ZMod 2 | c ∈ C ∧ weight c = w}

/-- The weight enumerator of a code as a function ℕ → ℕ. -/
noncomputable def weightEnumerator (C : BinaryLinearCode n) : ℕ → ℕ := weightCount C

/-! ## Basic Properties -/

theorem weight_zero : weight (0 : Fin n → ZMod 2) = 0 := by
  simp [weight]

theorem weight_le_n (c : Fin n → ZMod 2) : weight c ≤ n := by
  unfold weight
  calc (univ.filter (fun i => c i ≠ 0)).card ≤ univ.card := card_filter_le _ _
    _ = n := Fintype.card_fin n

theorem weightCount_zero_eq_one (C : BinaryLinearCode n) :
    weightCount C 0 = 1 := by
      convert Set.ncard_eq_one.mpr ?_;
      use 0; ext c; simp [weight];
      exact ⟨ fun h => funext h.2, fun h => ⟨ h.symm ▸ C.zero_mem, fun _ => h.symm ▸ rfl ⟩ ⟩

/-! ## Cyclic Codes -/

/-- Cyclic shift of a vector by one position: (c₀, c₁, ..., c_{n-1}) ↦ (c_{n-1}, c₀, ..., c_{n-2}). -/
def cyclicShift (hn : n > 0) (c : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => c ⟨(i.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩

/-- A code is cyclic if it is closed under the cyclic shift operation. -/
def IsCyclic (hn : n > 0) (C : BinaryLinearCode n) : Prop :=
  ∀ c ∈ C, cyclicShift hn c ∈ C

/-! ## Polynomial Representation of Codewords -/

/-- Map a codeword to its polynomial representation.
    A vector `(c₀, c₁, ..., c_{n-1})` maps to `c₀ + c₁x + ... + c_{n-1}x^{n-1}`. -/
noncomputable def toPolynomial (c : Fin n → ZMod 2) : Polynomial (ZMod 2) :=
  ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

/-- Map a polynomial back to a codeword (taking coefficients). -/
noncomputable def fromPolynomial (p : Polynomial (ZMod 2)) : Fin n → ZMod 2 :=
  fun i => p.coeff i.val

end BinaryLinearCode

/-! ## Trace Function over Finite Fields -/

/-- The trace map from GF(2^m) to GF(2), viewed as a linear map. -/
noncomputable def fieldTrace (m : ℕ) : GaloisField 2 m →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) (GaloisField 2 m)

/-! ## Reed-Muller and Kasami Code Parameters -/

/-- Parameters for Kasami codes: m must be odd and ≥ 3. -/
structure KasamiParams where
  m : ℕ
  m_ge_three : m ≥ 3
  m_odd : m % 2 = 1

namespace KasamiParams

variable (P : KasamiParams)

/-- The code length n = 2^m - 1. -/
def codeLength : ℕ := 2 ^ P.m - 1

/-- The half-exponent s = (m-1)/2. -/
def halfExp : ℕ := (P.m - 1) / 2

/-- The value 2^s. -/
def twoToS : ℕ := 2 ^ P.halfExp

/-- For Kasami codes, the possible nonzero weights are:
    - 2^(m-1) - 2^((m-1)/2)
    - 2^(m-1)
    - 2^(m-1) + 2^((m-1)/2) -/
def possibleWeights : Finset ℕ :=
  {0, 2 ^ (P.m - 1) - 2 ^ P.halfExp, 2 ^ (P.m - 1), 2 ^ (P.m - 1) + 2 ^ P.halfExp}

/-- The dimension of the Kasami code is 2m. -/
def kasamiDimension : ℕ := 2 * P.m

/-- The number of codewords in the Kasami code is 2^(2m). -/
def kasamiSize : ℕ := 2 ^ P.kasamiDimension

end KasamiParams

end