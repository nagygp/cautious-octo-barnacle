import Mathlib

/-!
# Generalized m-Tuple Count Theory — Primal, Dual, and Equivalence

Formalization of the m-tuple count theory from the CIC specifications
(mTuple-count/CIC_Main_Results.md, mTuple-count/CIC_Dual.md).

## Mathematical Content

Given a finite field 𝔽 = GF(2ⁿ) and a function f : 𝔽 → 𝔽, the
**differential set** Δ(f) := { f(x) + f(x + 1) + 1 | x ∈ 𝔽 } and the
**m-tuple count** κ_m count the number of m-tuples in Δ^m satisfying
a weighted zero-sum condition.

### Main Results (all sorry-free)

**Primal Direction** (from two black-boxed known results):
  Given KR₁ : |Δ(f)| = 2^{n-1} and KR₂ : |𝔽| · κ_m = |Δ|^m,
  we derive κ_m = 2^{(m-1)·n - m}.

**Dual Direction** (reversing the arrows):
  Given the observed count κ_m = 2^{(m-1)·n - m} and the spectral
  identity |𝔽| · κ = δ^m, we recover δ = 2^{n-1} and force C = m.

**Bidirectional Equivalence**:
  κ = 2^{(m-1)·n - m} ↔ δ = 2^{n-1}, given the spectral identity.

## References
- [Kasami 1971], [BBMM 2006, Thm 3]
- mTuple-count/CIC_Main_Results.md
- mTuple-count/CIC_Dual.md
-/

open Finset BigOperators

noncomputable section

-- ════════════════════════════════════════════════════════════════
-- §1  DEFINITIONS
-- ════════════════════════════════════════════════════════════════

/-- The differential set of a function f over a finite field of
    characteristic 2: Δ(f) := { f(x) + f(x+1) + 1 | x ∈ 𝔽 }. -/
def differentialSet (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (f : 𝔽 → 𝔽) : Finset 𝔽 :=
  Finset.univ.image (fun x => f x + f (x + 1) + 1)

/-- The m-tuple set: vectors in Δ^m satisfying a weighted zero-sum
    ∑ᵢ coeffs(i) · x(i) = 0. -/
def mTupleSet (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (f : 𝔽 → 𝔽) (m : ℕ) (coeffs : Fin m → 𝔽) : Finset (Fin m → 𝔽) :=
  Finset.univ.filter fun x =>
    (∀ i, x i ∈ differentialSet 𝔽 f) ∧
    ∑ i, coeffs i * x i = 0

/-- The m-tuple count κ_m: cardinality of the m-tuple set. -/
def mTupleCount' (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (f : 𝔽 → 𝔽) (m : ℕ) (coeffs : Fin m → 𝔽) : ℕ :=
  (mTupleSet 𝔽 f m coeffs).card

-- ════════════════════════════════════════════════════════════════
-- §2  NATURAL NUMBER SUBTRACTION HELPERS
-- ════════════════════════════════════════════════════════════════

/-- Key bound: (m-1)·n ≥ m when n ≥ 3 and m ≥ 2. -/
private theorem sub_bound (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m ≤ (m - 1) * n := by
  calc (m - 1) * n ≥ (m - 1) * 3 := Nat.mul_le_mul_left _ hn
    _ ≥ (m - 1) * 2 := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (m - 1) := by ring
    _ ≥ m := by omega

-- ════════════════════════════════════════════════════════════════
-- §3  ARITHMETIC LEMMAS  (fully proved, no sorry)
-- ════════════════════════════════════════════════════════════════

/-- **Lemma α (Power of power)**: (2^{n-1})^m = 2^{m·(n-1)}. -/
theorem power_of_power (n m : ℕ) :
    (2 ^ (n - 1)) ^ m = 2 ^ (m * (n - 1)) := by
  rw [← pow_mul]; ring_nf

/-- **Lemma β (Exponent identity)**: m·(n-1) = n + ((m-1)·n - m)
    when n ≥ 3 and m ≥ 2. -/
theorem exponent_identity (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m * (n - 1) = n + ((m - 1) * n - m) := by
  zify [show 1 ≤ n by omega, show 1 ≤ m by omega, sub_bound n m hn hm]
  ring

/-- **Lemma γ (Exponent split)**: 2^{m·(n-1)} = 2^n · 2^{(m-1)·n - m}. -/
theorem exponent_split (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    2 ^ (m * (n - 1)) = 2 ^ n * 2 ^ ((m - 1) * n - m) := by
  rw [← pow_add, exponent_identity n m hn hm]

/-- **Combined**: (2^{n-1})^m = 2^n · 2^{(m-1)n - m}. -/
theorem power_split (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    (2 ^ (n - 1)) ^ m = 2 ^ n * 2 ^ ((m - 1) * n - m) := by
  rw [power_of_power, exponent_split n m hn hm]

/-- Parseval-type identity: 2^n · 2^{(m-1)n - m} = (2^{n-1})^m. -/
theorem parseval_arithmetic (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    2 ^ n * 2 ^ ((m - 1) * n - m) = (2 ^ (n - 1)) ^ m :=
  (power_split n m hn hm).symm

-- ════════════════════════════════════════════════════════════════
-- §4  PRIMAL THEOREM
-- ════════════════════════════════════════════════════════════════

/-- **Primal Theorem (P)**: Under the spectral identity and APN
    cardinality, the m-tuple count equals 2^{(m-1)·n - m}. -/
theorem primal_mTupleCount
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hδ : δ = 2 ^ (n - 1))
    (hKR₂ : 2 ^ n * κ = δ ^ m) :
    κ = 2 ^ ((m - 1) * n - m) := by
  rw [hδ, power_split n m hn hm] at hKR₂
  exact mul_left_cancel₀ (by positivity) hKR₂

/-- **Corollary P₃ (Triple count, m = 3)**: κ₃ = 2^{2n - 3}. -/
theorem triple_count (n δ κ : ℕ) (hn : 3 ≤ n)
    (hδ : δ = 2 ^ (n - 1))
    (hKR₂ : 2 ^ n * κ = δ ^ 3) :
    κ = 2 ^ (2 * n - 3) := by
  have h := primal_mTupleCount n 3 δ κ hn (by omega) hδ hKR₂
  simpa using h

/-- **Corollary P₄ (Quadruple count, m = 4)**: κ₄ = 2^{3n - 4}. -/
theorem quadruple_count (n δ κ : ℕ) (hn : 3 ≤ n)
    (hδ : δ = 2 ^ (n - 1))
    (hKR₂ : 2 ^ n * κ = δ ^ 4) :
    κ = 2 ^ (3 * n - 4) := by
  have h := primal_mTupleCount n 4 δ κ hn (by omega) hδ hKR₂
  simpa using h

/-- **Corollary P₅ (Quintuple count, m = 5)**: κ₅ = 2^{4n - 5}. -/
theorem quintuple_count (n δ κ : ℕ) (hn : 3 ≤ n)
    (hδ : δ = 2 ^ (n - 1))
    (hKR₂ : 2 ^ n * κ = δ ^ 5) :
    κ = 2 ^ (4 * n - 5) := by
  have h := primal_mTupleCount n 5 δ κ hn (by omega) hδ hKR₂
  simpa using h

-- ════════════════════════════════════════════════════════════════
-- §5  DUAL LEMMAS
-- ════════════════════════════════════════════════════════════════

/-- **Dual Lemma D₁ (Count determines product)**:
    2^n · 2^{(m-1)n - m} = 2^{mn - m}. -/
theorem dual_count_product (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    2 ^ n * 2 ^ ((m - 1) * n - m) = 2 ^ (m * n - m) := by
  rw [← pow_add]; congr 1
  zify [show 1 ≤ n by omega, show 1 ≤ m by omega, sub_bound n m hn hm,
        show m ≤ m * n by nlinarith]
  ring

/-- **Dual Lemma D₃ (Unique m-th root in ℕ)**:
    If d^m = (2^{n-1})^m and m ≥ 1, then d = 2^{n-1}. -/
theorem dual_unique_mth_root (d n m : ℕ) (hm : m ≠ 0)
    (h : d ^ m = (2 ^ (n - 1)) ^ m) :
    d = 2 ^ (n - 1) :=
  Nat.pow_left_injective hm h

/-- **Dual Lemma D₃' (alternate form)**:
    If d^m = 2^{mn - m} and m ≥ 1 and n ≥ 1, then d = 2^{n-1}. -/
theorem dual_unique_mth_root' (d n m : ℕ) (hm : m ≠ 0) (hn : 1 ≤ n)
    (h : d ^ m = 2 ^ (m * n - m)) :
    d = 2 ^ (n - 1) := by
  have key : 2 ^ (m * n - m) = (2 ^ (n - 1)) ^ m := by
    rw [← pow_mul]; congr 1
    zify [show 1 ≤ m by omega, show m ≤ m * n by nlinarith, hn]
    ring
  rw [key] at h
  exact Nat.pow_left_injective hm h

/-- **Dual Lemma D₄ (C is forced to equal m)**: -/
theorem dual_C_forced (n m C : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hC_le : C ≤ (m - 1) * n)
    (hδ : 2 ^ (n + ((m - 1) * n - C)) = 2 ^ ((n - 1) * m)) :
    C = m := by
  have := Nat.pow_right_injective (show 2 ≤ 2 by omega) hδ
  zify [show 1 ≤ n by omega, show 1 ≤ m by omega,
        sub_bound n m hn hm, hC_le] at *
  linarith

-- ════════════════════════════════════════════════════════════════
-- §6  DUAL MAIN THEOREM
-- ════════════════════════════════════════════════════════════════

/-- **Dual Theorem (D)**: Given the spectral identity 2^n · κ = δ^m
    and the observed count κ = 2^{(m-1)·n - m}, we recover δ = 2^{n-1}. -/
theorem dual_theorem (n m δ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * 2 ^ ((m - 1) * n - m) = δ ^ m) :
    δ = 2 ^ (n - 1) := by
  rw [dual_count_product n m hn hm] at hKR₂
  exact dual_unique_mth_root' δ n m (by omega) (by omega) hKR₂.symm

/-- Dual part (b): C is forced to equal m. -/
theorem dual_C_eq_m (n m δ C : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hC_le : C ≤ (m - 1) * n)
    (hKR₂ : 2 ^ n * 2 ^ ((m - 1) * n - C) = δ ^ m)
    (hδ : δ = 2 ^ (n - 1)) :
    C = m := by
  rw [hδ, ← pow_mul, ← pow_add] at hKR₂
  exact dual_C_forced n m C hn hm hC_le hKR₂

-- ════════════════════════════════════════════════════════════════
-- §7  BIDIRECTIONAL EQUIVALENCE
-- ════════════════════════════════════════════════════════════════

/-- **Equivalence Theorem (E)**: κ = 2^{(m-1)·n - m} ↔ δ = 2^{n-1},
    given the spectral identity 2^n · κ = δ^m. -/
theorem primal_dual_equivalence
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * κ = δ ^ m) :
    κ = 2 ^ ((m - 1) * n - m) ↔ δ = 2 ^ (n - 1) := by
  constructor
  · intro hκ; rw [hκ] at hKR₂; exact dual_theorem n m δ hn hm hKR₂
  · intro hδ; exact primal_mTupleCount n m δ κ hn hm hδ hKR₂

-- ════════════════════════════════════════════════════════════════
-- §8  KASAMI TRIPLE COUNT CONNECTION
-- ════════════════════════════════════════════════════════════════

/-- The m = 3 case: κ₃ = 2^{2n-3} ↔ |Δ| = 2^{n-1}. -/
theorem kasami_triple_equivalence
    (n δ κ : ℕ) (hn : 3 ≤ n)
    (hKR₂ : 2 ^ n * κ = δ ^ 3) :
    κ = 2 ^ (2 * n - 3) ↔ δ = 2 ^ (n - 1) := by
  have h := primal_dual_equivalence n 3 δ κ hn (by omega) hKR₂
  constructor
  · intro hκ; exact h.mp (by simpa using hκ)
  · intro hδ; simpa using h.mpr hδ

-- ════════════════════════════════════════════════════════════════
-- §9  TWO-POWER INJECTIVITY
-- ════════════════════════════════════════════════════════════════

/-- 2^a = 2^b → a = b. -/
theorem two_pow_injective (a b : ℕ) (h : 2 ^ a = 2 ^ b) : a = b :=
  Nat.pow_right_injective (by omega) h

-- ════════════════════════════════════════════════════════════════
-- §10  COMPLETE PRIMAL-DUAL PACKAGE
-- ════════════════════════════════════════════════════════════════

/-- **Complete m-Tuple Count Package**: bundles the primal theorem,
    dual theorem, and bidirectional equivalence.

    Given n ≥ 3, m ≥ 2, and the spectral identity 2^n · κ = δ^m:
    (i)   Consistency: 2^n · 2^{(m-1)n-m} = (2^{n-1})^m
    (ii)  Equivalence: κ = 2^{(m-1)n-m} ↔ δ = 2^{n-1}
    (iii) C is forced: κ = 2^{(m-1)n-m} → κ = 2^{(m-1)n-C} → C = m -/
theorem mTupleCount_complete_package
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * κ = δ ^ m) :
    (2 ^ n * 2 ^ ((m - 1) * n - m) = (2 ^ (n - 1)) ^ m) ∧
    (κ = 2 ^ ((m - 1) * n - m) ↔ δ = 2 ^ (n - 1)) ∧
    (κ = 2 ^ ((m - 1) * n - m) →
      ∀ C, C ≤ (m - 1) * n → κ = 2 ^ ((m - 1) * n - C) → C = m) := by
  refine ⟨parseval_arithmetic n m hn hm,
         primal_dual_equivalence n m δ κ hn hm hKR₂, ?_⟩
  intro hκ C hCle hκC
  have heq : 2 ^ ((m - 1) * n - m) = 2 ^ ((m - 1) * n - C) := hκ ▸ hκC
  have hsub := sub_bound n m hn hm
  have := two_pow_injective _ _ heq
  omega

-- ════════════════════════════════════════════════════════════════
-- §11  AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════

#print axioms power_of_power
#print axioms exponent_identity
#print axioms exponent_split
#print axioms power_split
#print axioms parseval_arithmetic
#print axioms primal_mTupleCount
#print axioms triple_count
#print axioms quadruple_count
#print axioms quintuple_count
#print axioms dual_count_product
#print axioms dual_unique_mth_root
#print axioms dual_unique_mth_root'
#print axioms dual_C_forced
#print axioms dual_theorem
#print axioms dual_C_eq_m
#print axioms primal_dual_equivalence
#print axioms kasami_triple_equivalence
#print axioms mTupleCount_complete_package

end
