/-
# Strategy A: Norm Quotient DAG

## Attack on `lam_forced_trivial` via Norm Quotient

### DAG Overview

The norm quotient strategy decomposes the proof into:

```
lam_forced_trivial
├── norm_quotient_equation          -- P^{q+1} = lam^{q+1} · s^{q+1}
│   ├── norm_of_product             -- N(ab) = N(a) · N(b)
│   └── lam_def_as_ratio            -- lam = P/s, so P = lam · s
├── norm_expansion_s                -- s^{q+1} expanded via collision data
│   └── s_norm_equation_char2       -- char 2 simplification
├── norm_expansion_P                -- P^{q+1} expanded via collision data
│   └── p_norm_equation_char2       -- char 2 simplification
├── norm_difference_zero            -- P^{q+1} - lam^{q+1} · s^{q+1} = 0
│   ├── norm_quotient_equation
│   ├── norm_expansion_s
│   └── norm_expansion_P
├── norm_diff_factored              -- ... = s^{q+1} · g(lam) · L_k(lam)
│   ├── norm_difference_zero
│   └── cross_substitution          -- use key equation c^{q³}+c = cross
│       └── key_equation_char2      -- key equation in char 2
└── linPolyL_zero_from_factor       -- L_k(lam) = 0
    ├── norm_diff_factored
    ├── s_nonzero                   -- s ≠ 0 (hypothesis)
    └── cofactor_nonzero            -- f(lam) ≠ 0 (from coprimality)
        └── coprimality_argument    -- gcd(k,n) = 1
```

Each node is a single algebraic manipulation or logical deduction.
-/

import Mathlib

set_option maxHeartbeats 800000

namespace NormQuotientDAG

open Finset Fintype

/-! ## Layer 0: Foundations (from Mathlib/Type Theory) -/

/-- The Kasami exponent d(k) = 2^{2k} - 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Frobenius map x ↦ x^{2^k}. -/
def frob (k : ℕ) {F : Type*} [CommRing F] (x : F) : F := x ^ (2 ^ k)

/-- The relative norm N_k(x) = x^{q+1} where q = 2^k. -/
def relNorm (k : ℕ) {F : Type*} [CommRing F] (x : F) : F := x ^ (2 ^ k + 1)

/-- The linearized polynomial L_k(x) = x^{2^k} + x. -/
def linPolyL (k : ℕ) (F : Type*) [Field F] [CharP F 2] (x : F) : F :=
  x ^ (2 ^ k) + x

/-- The cross form Cross(s, P) = s · P^{2^k} + s^{2^k} · P. -/
def crossForm (k : ℕ) {F : Type*} [CommRing F] (s P : F) : F :=
  s * P ^ (2 ^ k) + s ^ (2 ^ k) * P

/-! ## Layer 1: Basic Algebraic Identities (single manipulations) -/

section BasicAlgebra

variable {F : Type*} [Field F] [CharP F 2]

/-- **L1.1** Freshman's dream: (a+b)^{2^k} = a^{2^k} + b^{2^k} in char 2. -/
theorem frob_add (k : ℕ) (a b : F) :
    (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) :=
  add_pow_expChar_pow a b 2 k

/-- **L1.2** Frobenius is multiplicative: (ab)^{2^k} = a^{2^k} · b^{2^k}. -/
theorem frob_mul (k : ℕ) (a b : F) :
    (a * b) ^ (2 ^ k) = a ^ (2 ^ k) * b ^ (2 ^ k) :=
  mul_pow a b (2 ^ k)

/-- **L1.3** Norm is multiplicative: N_k(ab) = N_k(a) · N_k(b). -/
theorem relNorm_mul (k : ℕ) (a b : F) :
    relNorm k (a * b) = relNorm k a * relNorm k b := by
  simp [relNorm, mul_pow]

/-- **L1.4** In char 2: x + x = 0. -/
theorem add_self_char2 (x : F) : x + x = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have : x + x = 2 * x := by ring
  rw [this, h2, zero_mul]

/-- **L1.5** In char 2: -x = x. -/
theorem neg_eq_self_char2 (x : F) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_char2 x)

/-- **L1.6** L_k(0) = 0. -/
theorem linPolyL_zero (k : ℕ) : linPolyL k F 0 = 0 := by
  simp [linPolyL]

/-- **L1.7** L_k(1) = 0 in char 2. -/
theorem linPolyL_one (k : ℕ) : linPolyL k F 1 = 0 := by
  simp [linPolyL, one_pow, add_self_char2]

/-- **L1.8** L_k is additive. -/
theorem linPolyL_add (k : ℕ) (x y : F) :
    linPolyL k F (x + y) = linPolyL k F x + linPolyL k F y := by
  simp [linPolyL, frob_add]; ring

end BasicAlgebra

/-! ## Layer 2: Ratio and Product Lemmas -/

section RatioLemmas

variable {F : Type*} [Field F] [CharP F 2]

/-- **L2.1** Definition: lam = P/s, so P = lam · s. -/
theorem lam_def_as_ratio (s P : F) (hs : s ≠ 0) :
    P = (P / s) * s := by
  field_simp

/-- **L2.2** Norm of the ratio: N_k(P) = N_k(lam) · N_k(s). -/
theorem norm_of_ratio (k : ℕ) (s P : F) (hs : s ≠ 0) :
    relNorm k P = relNorm k (P / s) * relNorm k s := by
  rw [← relNorm_mul, div_mul_cancel₀ P hs]

/-- **L2.3** Cross via linearized polynomial:
    Cross(s, P) = s^{q+1} · L_k(P/s). -/
theorem cross_via_linPoly (k : ℕ) (s P : F) (hs : s ≠ 0) :
    crossForm k s P = relNorm k s * linPolyL k F (P / s) := by
  simp only [crossForm, linPolyL, relNorm]
  rw [div_pow, mul_add]
  congr 1 <;> (field_simp; ring)

/-- **L2.4** Cross = 0 iff ratio in kernel. -/
theorem cross_zero_iff_kernel (k : ℕ) (s P : F) (hs : s ≠ 0) :
    crossForm k s P = 0 ↔ linPolyL k F (P / s) = 0 := by
  rw [cross_via_linPoly k s P hs]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hs)
  · intro h; rw [h, mul_zero]

end RatioLemmas

/-! ## Layer 3: Norm Expansion Equations -/

section NormExpansion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**L3.1** Gold derivative identity:
    (t+c)^{q³+1} + t^{q³+1} = t^{q³}·c + c^{q³}·t + c^{q³+1}.
-/
theorem gold_derivative (t c : F) (k : ℕ) :
    (t + c) ^ (2 ^ (3 * k) + 1) + t ^ (2 ^ (3 * k) + 1) =
      t ^ (2 ^ (3 * k)) * c + c ^ (2 ^ (3 * k)) * t + c ^ (2 ^ (3 * k) + 1) := by
  grind +suggestions

/-
**L3.2** Norm expansion identity:
    (A+B)^{q+1} = A^{q+1} + B^{q+1} + cross(A, B).
-/
theorem norm_expansion (A B : F) (k : ℕ) :
    (A + B) ^ (2 ^ k + 1) = A ^ (2 ^ k + 1) + B ^ (2 ^ k + 1) +
      crossForm k A B := by
  rw [ pow_succ, pow_succ, pow_succ ];
  rw [ frob_add ] ; ring!;
  unfold crossForm; ring;

/-
**L3.3** s-norm equation: s^{q+1} expressed via t₁.
-/
theorem s_norm_expanded (k : ℕ) (t₁ : F) :
    let s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
    let A := (t₁ + 1) ^ kasamiExp k
    s ^ (2 ^ k + 1) = t₁ ^ (2 ^ (3 * k)) + t₁ + 1 +
      s * A ^ (2 ^ k) + s ^ (2 ^ k) * A := by
  have h_gold : ∀ t₁ : F, (t₁ + 1) ^ (2 ^ (3 * k) + 1) + t₁ ^ (2 ^ (3 * k) + 1) = t₁ ^ (2 ^ (3 * k)) + t₁ + 1 := by
    intro t₁
    have := gold_derivative t₁ 1 k
    simp_all +decide [ pow_add, pow_mul ];
  have h_kasami : ∀ t₁ : F, (t₁ + 1) ^ (2 ^ (3 * k) + 1) = (t₁ + 1) ^ (kasamiExp k * (2 ^ k + 1)) ∧ t₁ ^ (2 ^ (3 * k) + 1) = t₁ ^ (kasamiExp k * (2 ^ k + 1)) := by
    intro t₁
    constructor <;> congr 1
    simp [kasamiExp];
    · zify ; ring;
      rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
    · zify [ kasamiExp ] ; ring;
      rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
  simp_all +decide [ mul_comm, pow_mul ];
  grind +suggestions

/-
**L3.4** P-norm equation: P^{q+1} expressed via t₁, c.
-/
theorem p_norm_expanded (k : ℕ) (t₁ c : F) :
    let P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
    let B := t₁ ^ kasamiExp k
    P ^ (2 ^ k + 1) =
      t₁ ^ (2 ^ (3 * k)) * c + c ^ (2 ^ (3 * k)) * t₁ + c ^ (2 ^ (3 * k) + 1) +
      P * B ^ (2 ^ k) + P ^ (2 ^ k) * B := by
  simp +decide [ crossForm, pow_add, pow_mul ] ; ring;
  simp +decide [ add_pow_char_pow, mul_assoc, mul_comm, mul_left_comm ] ; ring;
  simp +decide [ ← pow_add, add_comm, add_left_comm, add_assoc ];
  rw [ show kasamiExp k + kasamiExp k * 2 ^ k = 8 ^ k + 1 by
        unfold kasamiExp;
        zify;
        rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
        norm_num [ pow_mul' ] ] ; ring;
  rw [ show ( 8 ^ k : ℕ ) = 2 ^ ( 3 * k ) by rw [ pow_mul ] ; norm_num ] ; simp +decide [ add_pow_char_pow, mul_assoc, mul_comm, mul_left_comm ] ; ring;

end NormExpansion

/-! ## Layer 4: The Norm Quotient Equation -/

section NormQuotient

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L4.1** The tautological norm quotient: P^{q+1} = lam^{q+1} · s^{q+1}. -/
theorem norm_quotient_tautology (k : ℕ) (s P : F) (hs : s ≠ 0) :
    relNorm k P = relNorm k (P / s) * relNorm k s :=
  norm_of_ratio k s P hs

/-- **L4.2** Substituting s-norm and P-norm expansions into the quotient:
    [P-norm RHS] = lam^{q+1} · [s-norm RHS].
    After expansion this gives an equation in lam. -/
theorem norm_quotient_expanded (k : ℕ) (t₁ c : F)
    (hs : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k ≠ 0)
    (hP : t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k ≠ 0) :
    let s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
    let P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
    let lam := P / s
    relNorm k P = relNorm k lam * relNorm k s := by
  intro s P lam
  exact norm_quotient_tautology k s P hs

end NormQuotient

/-! ## Layer 5: Cross Substitution via Key Equation -/

section CrossSubstitution

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**L5.1** The key equation: c^{q³} + c = cross (under collision).
-/
theorem key_equation (k : ℕ) (t₁ c : F)
    (heq : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k =
           (t₁ + c + 1) ^ kasamiExp k + (t₁ + c) ^ kasamiExp k) :
    let s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
    let P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
    c ^ (2 ^ (3 * k)) + c = crossForm k s P := by
  -- Expand $s^{q+1}$ using the definition of $s$ and the norm_expansion lemma.
  have hs_exp : ((t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k) ^ (2 ^ k + 1) =
    (t₁ + 1) ^ (2 ^ (3 * k) + 1) + t₁ ^ (2 ^ (3 * k) + 1) + crossForm k ((t₁ + 1) ^ kasamiExp k) (t₁ ^ kasamiExp k) := by
      convert norm_expansion _ _ _ using 2;
      · rw [ ← pow_mul, ← pow_mul ];
        rw [ show kasamiExp k * ( 2 ^ k + 1 ) = 2 ^ ( 3 * k ) + 1 from ?_ ];
        unfold kasamiExp;
        zify;
        rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
      · infer_instance;
      · infer_instance;
      · infer_instance;
  simp_all +decide [ crossForm ];
  grind +suggestions

/-- **L5.2** The norm difference is tautologically zero. -/
theorem norm_diff_zero (k : ℕ) (s P : F) (hs : s ≠ 0) :
    relNorm k P - relNorm k (P / s) * relNorm k s = 0 := by
  simp [norm_quotient_tautology k s P hs]

end CrossSubstitution

/-! ## Layer 6: Factoring out L_k(lam) -/

section LinPolyFactor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L6.1** The cross form factors through the linearized polynomial.
    Cross(s, P) = N_k(s) · L_k(P/s). -/
theorem cross_factored (k : ℕ) (s P : F) (hs : s ≠ 0) :
    crossForm k s P = relNorm k s * linPolyL k F (P / s) :=
  cross_via_linPoly k s P hs

/-- **L6.2** Norm expansion minus lam-scaled norm expansion gives
    an equation involving L_k(lam). After substituting the key equation,
    all terms involving c^{q³}+c are replaced by cross = N_k(s)·L_k(lam).
    The remaining equation is divisible by L_k(lam). -/
theorem norm_equation_linPoly_divisible (k : ℕ) (t₁ c : F)
    (heq : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k =
           (t₁ + c + 1) ^ kasamiExp k + (t₁ + c) ^ kasamiExp k)
    (hs : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k ≠ 0)
    (hP : t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k ≠ 0) :
    let s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
    let P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
    let lam := P / s
    -- The norm equations, after expansion and cross substitution,
    -- produce an equation where L_k(lam) is a factor
    ∃ (g : F), crossForm k s P = relNorm k s * g * linPolyL k F lam ∨
               linPolyL k F lam = 0 := by
  intro s P lam
  by_cases h : linPolyL k F lam = 0
  · exact ⟨0, Or.inr h⟩
  · sorry

end LinPolyFactor

/-! ## Layer 7: Coprimality Forces L_k(lam) = 0 -/

section CoprimeFinal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L7.1** Kernel of L_k in GF(2^n) has 2^{gcd(k,n)} elements. -/
theorem kernel_card (k n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    Fintype.card { x : F // linPolyL k F x = 0 } = 2 ^ Nat.gcd k n := by
  sorry

/-- **L7.2** When gcd(k,n) = 1, kernel = {0, 1}. -/
theorem kernel_trivial (k n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime k n) :
    ∀ x : F, linPolyL k F x = 0 → x = 0 ∨ x = 1 := by
  sorry

/-- **L7.3** lam ∉ {0, 1} under collision constraints. -/
theorem lam_not_trivial (k : ℕ) (t₁ c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hs : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k ≠ 0)
    (hP : t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k ≠ 0) :
    let s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
    let P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
    let lam := P / s
    lam ≠ 0 ∧ lam ≠ 1 := by
  sorry

end CoprimeFinal

/-! ## Layer 8: Assembly — lam_forced_trivial via Norm Quotient -/

section Assembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Master Assembly**: All layers compose to derive False from cross ≠ 0.

    Layer 2: cross ≠ 0 ⟹ lam ∉ ker(L_k)
    Layer 7: ker(L_k) = {0, 1} (coprimality)
    Layer 7: lam ∉ {0, 1} (collision constraints)
    Layer 6: norm equations force L_k(lam) = 0
    ⟹ contradiction -/
theorem cross_nonzero_impossible_normquot
    (k n : ℕ) (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hcop : Nat.Coprime k n)
    (t₁ c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (heq : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k =
           (t₁ + c + 1) ^ kasamiExp k + (t₁ + c) ^ kasamiExp k)
    (hs : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k ≠ 0)
    (hP : t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k ≠ 0)
    (hcross : crossForm k
      ((t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k)
      (t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k) ≠ 0) :
    False := by
  set s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k with hs_def
  set P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k with hP_def
  set lam := P / s
  -- Step 1 (Layer 2): cross ≠ 0 means lam ∉ ker(L_k)
  have h_not_ker : linPolyL k F lam ≠ 0 := by
    intro h; exact hcross ((cross_zero_iff_kernel k s P hs).mpr h)
  -- Step 2 (Layer 7): lam ∉ {0, 1}
  have ⟨hlam0, hlam1⟩ := lam_not_trivial k t₁ c hc0 hc1 hs hP
  -- Step 3 (Layer 7): kernel = {0, 1}
  have h_ker := kernel_trivial k n hcard hcop
  -- Step 4 (Layer 6): norm equations force L_k(lam) = 0
  -- (This is where Layers 3-6 compose)
  -- TODO: complete using norm_equation_linPoly_divisible
  sorry

end Assembly

/-! ## DAG Dependency Summary

```
Layer 0: Definitions (kasamiExp, frob, relNorm, linPolyL, crossForm)
    ↑ Grounded in: Mathlib.FieldTheory.Finite, Mathlib.RingTheory.Polynomial

Layer 1: Basic algebra (frob_add, frob_mul, relNorm_mul, add_self_char2, ...)
    ↑ Grounded in: Mathlib.CharP, add_pow_expChar_pow, mul_pow

Layer 2: Ratio lemmas (lam_def, norm_of_ratio, cross_via_linPoly)
    ↑ Uses: Layer 1 + Mathlib.Algebra.Field.Basic (div_mul_cancel)

Layer 3: Norm expansions (gold_derivative, norm_expansion, s_norm, p_norm)
    ↑ Uses: Layer 1 + ring arithmetic in char 2

Layer 4: Norm quotient tautology (P^{q+1} = lam^{q+1} · s^{q+1})
    ↑ Uses: Layer 2

Layer 5: Key equation + cross substitution
    ↑ Uses: Layer 3 + Layer 4 + collision hypothesis

Layer 6: L_k(lam) factored out of norm difference
    ↑ Uses: Layer 5 + Layer 1 (char 2 simplification)

Layer 7: Coprimality + kernel classification
    ↑ Uses: Mathlib.FieldTheory.Finite.GaloisField + Frobenius theory

Layer 8: Assembly — contradiction
    ↑ Uses: Layer 2 (cross ↔ kernel) + Layer 6 + Layer 7
```
-/

end NormQuotientDAG