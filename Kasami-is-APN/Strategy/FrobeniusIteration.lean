/-
# Strategy C: Frobenius Iteration DAG

## Attack on `lam_forced_trivial` via Iterated Frobenius & Trace

### DAG Overview

```
lam_forced_trivial
├── key_equation_base              -- c^{q³}+c = cross (base)
├── key_equation_frob_iter         -- apply Frob^k iteratively
│   ├── key_eq_shift1              -- c^{q⁴}+c^q = cross^q
│   ├── key_eq_shift2              -- c^{q⁵}+c^{q²} = cross^{q²}
│   └── key_eq_shift_general       -- c^{q^{i+3}}+c^{q^i} = cross^{q^i}
├── telescoping_sum                -- sum of shifted equations telescopes
│   ├── key_eq_shift_general
│   └── telescope_cancellation     -- adjacent terms cancel in char 2
├── trace_of_cross                 -- Tr_{n/gcd(3k,n)}(cross) = 0
│   ├── telescoping_sum
│   └── periodicity_frob_n         -- c^{2^n} = c (Fermat)
├── trace_expansion                -- expand Tr(cross) = Tr(N_k(s)·L_k(lam))
│   ├── trace_of_cross
│   └── cross_factored             -- cross = N_k(s) · L_k(lam)
├── trace_forces_linpoly           -- Tr conditions force L_k(lam) = 0
│   ├── trace_expansion
│   ├── s_norm_structure           -- structure of N_k(s)
│   └── independence_argument      -- linear independence over GF(2)
└── linPolyL_zero                  -- L_k(lam) = 0
    └── trace_forces_linpoly
```
-/

import Mathlib

set_option maxHeartbeats 800000

namespace FrobeniusIterationDAG

open Finset Fintype

/-! ## Layer 0: Shared Definitions -/

def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

def frob (k : ℕ) {F : Type*} [CommRing F] (x : F) : F := x ^ (2 ^ k)

def relNorm (k : ℕ) {F : Type*} [CommRing F] (x : F) : F := x ^ (2 ^ k + 1)

def linPolyL (k : ℕ) (F : Type*) [Field F] [CharP F 2] (x : F) : F :=
  x ^ (2 ^ k) + x

def crossForm (k : ℕ) {F : Type*} [CommRing F] (s P : F) : F :=
  s * P ^ (2 ^ k) + s ^ (2 ^ k) * P

/-- Iterated Frobenius: Frob^{ik}(x) = x^{2^{ik}}. -/
def frobIter (k i : ℕ) {F : Type*} [CommRing F] (x : F) : F := x ^ (2 ^ (i * k))

/-- The relative trace: Σ_{i=0}^{m-1} x^{2^{ik}}. -/
noncomputable def relTr (k m : ℕ) {F : Type*} [CommRing F] (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ (i * k))

/-! ## Layer 1: Frobenius Iteration Basics -/

section FrobBasics

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L1.1** Frobenius commutes with addition (Freshman's dream). -/
theorem frob_add_comm (k : ℕ) (x y : F) :
    frob k (x + y) = frob k x + frob k y := by
  simp [frob]; exact add_pow_expChar_pow x y 2 k

/-- **L1.2** Frobenius commutes with multiplication. -/
theorem frob_mul_comm (k : ℕ) (x y : F) :
    frob k (x * y) = frob k x * frob k y := by
  simp [frob, mul_pow]

/-- **L1.3** Iterated Frobenius: Frob^i ∘ Frob^j = Frob^{i+j}. -/
theorem frobIter_compose (k i j : ℕ) (x : F) :
    frobIter k i (frobIter k j x) = frobIter k (i + j) x := by
  simp [frobIter, ← pow_mul, ← pow_add, Nat.add_mul]
  ring_nf

/-- **L1.4** Fermat's little theorem: x^{2^n} = x in GF(2^n). -/
theorem fermat_finite_field (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ n) = x := by
  rw [← hcard]; exact FiniteField.pow_card x

/-- **L1.5** Frobenius is periodic: Frob^n = id on GF(2^n). -/
theorem frob_periodic (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (x : F) :
    frobIter 1 n x = x := by
  simp only [frobIter, mul_one]
  exact fermat_finite_field n hcard x

/-- **L1.6** Applying Frob^k to both sides of an equation preserves it. -/
theorem frob_preserves_eq (k : ℕ) (a b : F) (h : a = b) :
    frob k a = frob k b := by rw [h]

end FrobBasics

/-! ## Layer 2: Key Equation and its Frobenius Shifts -/

section KeyEquationShifts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L2.1** The base key equation: c^{q³} + c = cross. -/
theorem key_equation_base (k : ℕ) (t₁ c : F)
    (heq : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k =
           (t₁ + c + 1) ^ kasamiExp k + (t₁ + c) ^ kasamiExp k) :
    let s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
    let P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
    c ^ (2 ^ (3 * k)) + c = crossForm k s P := by
  sorry

/-
**L2.2** First Frobenius shift: Frob^k applied to key equation.
    c^{q⁴} + c^q = Frob^k(cross).
-/
theorem key_eq_shift1 (k : ℕ) (c cross : F)
    (hbase : c ^ (2 ^ (3 * k)) + c = cross) :
    c ^ (2 ^ (4 * k)) + c ^ (2 ^ k) = frob k cross := by
  rw [ ← hbase, frob ];
  rw [ add_pow_char_pow ] ; ring

/-- **L2.3** Second Frobenius shift: c^{q⁵} + c^{q²} = Frob^{2k}(cross). -/
theorem key_eq_shift2 (k : ℕ) (c cross : F)
    (hbase : c ^ (2 ^ (3 * k)) + c = cross) :
    c ^ (2 ^ (5 * k)) + c ^ (2 ^ (2 * k)) = frobIter k 2 cross := by
  sorry

/-- **L2.4** General Frobenius shift: apply Frob^{ik} to get
    c^{q^{i+3}} + c^{q^i} = Frob^{ik}(cross). -/
theorem key_eq_shift_general (k i : ℕ) (c cross : F)
    (hbase : c ^ (2 ^ (3 * k)) + c = cross) :
    c ^ (2 ^ ((i + 3) * k)) + c ^ (2 ^ (i * k)) = frobIter k i cross := by
  sorry

end KeyEquationShifts

/-! ## Layer 3: Telescoping Sum -/

section TelescopingSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L3.1** Sum of shifted equations: each term equals a Frobenius iterate. -/
theorem telescoping_sum_general (k m : ℕ) (c cross : F)
    (hbase : c ^ (2 ^ (3 * k)) + c = cross) :
    ∑ i ∈ Finset.range m, frobIter k i cross =
    ∑ i ∈ Finset.range m, (c ^ (2 ^ ((i + 3) * k)) + c ^ (2 ^ (i * k))) := by
  congr 1; ext i; exact (key_eq_shift_general k i c cross hbase).symm

/-- **L3.2** The sum splits by distributivity. -/
theorem telescoping_sum_split (k m : ℕ) (c : F) :
    ∑ i ∈ Finset.range m, (c ^ (2 ^ ((i + 3) * k)) + c ^ (2 ^ (i * k))) =
    ∑ i ∈ Finset.range m, c ^ (2 ^ ((i + 3) * k)) +
    ∑ i ∈ Finset.range m, c ^ (2 ^ (i * k)) := by
  rw [Finset.sum_add_distrib]

/-
**L3.3** The first sum is a reindexing of Frobenius iterates.
-/
theorem shifted_sum_reindex (k m : ℕ) (c : F) :
    ∑ i ∈ Finset.range m, c ^ (2 ^ ((i + 3) * k)) =
    ∑ j ∈ Finset.Ico 3 (m + 3), c ^ (2 ^ (j * k)) := by
  rw [ Finset.sum_Ico_eq_sum_range ] ; simp +decide [ add_comm, add_left_comm, add_assoc ] ;

end TelescopingSum

/-! ## Layer 4: Trace of Cross = 0 -/

section TraceOfCross

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L4.1** The relative trace of cross vanishes.
    After telescoping and using Fermat (c^{2^n} = c), boundary terms cancel. -/
theorem relative_trace_of_cross (k n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (c cross : F) (hbase : c ^ (2 ^ (3 * k)) + c = cross) :
    relTr k (n / Nat.gcd k n) cross = 0 := by
  sorry

/-- **L4.2** Full trace of cross is zero. -/
theorem full_trace_of_cross (k n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (c cross : F) (hbase : c ^ (2 ^ (3 * k)) + c = cross) :
    ∑ i ∈ Finset.range n, cross ^ (2 ^ (k * i)) = 0 := by
  sorry

/-- **L4.3** Writing cross = N_k(s) · L_k(lam), the trace condition becomes
    a sum of products of Frobenius iterates. -/
theorem trace_of_factored_cross (k n : ℕ) (s lam : F) (hs : s ≠ 0)
    (hcard : Fintype.card F = 2 ^ n)
    (c : F) (hbase : c ^ (2 ^ (3 * k)) + c = relNorm k s * linPolyL k F lam) :
    relTr k (n / Nat.gcd k n) (relNorm k s * linPolyL k F lam) = 0 := by
  exact relative_trace_of_cross k n hcard c _ hbase

end TraceOfCross

/-! ## Layer 5: Trace Forces L_k(lam) = 0 -/

section TraceForces

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L5.1** Frobenius distributes over products. -/
theorem frobIter_distributes (k i : ℕ) (a b : F) :
    frobIter k i (a * b) = frobIter k i a * frobIter k i b := by
  simp [frobIter, mul_pow]

/-- **L5.2** Frobenius commutes with the norm. -/
theorem frobIter_norm (k i : ℕ) (s : F) :
    frobIter k i (relNorm k s) = relNorm k (frobIter k i s) := by
  simp [frobIter, relNorm, ← pow_mul]; congr 1; ring

/-
**L5.3** Frobenius commutes with L_k.
-/
theorem frobIter_linPoly (k i : ℕ) (lam : F) :
    frobIter k i (linPolyL k F lam) = linPolyL k F (frobIter k i lam) := by
  unfold frobIter linPolyL;
  rw [ add_pow_char_pow ] ; ring

/-
**L5.4** The trace condition expanded:
    Σ_i N_k(s^{q^i}) · L_k(lam^{q^i}) = 0.
    Since N_k(s^{q^i}) ≠ 0 for all i (because s ≠ 0),
    this constrains L_k(lam).
-/
theorem trace_expanded (k n : ℕ) (s lam : F) (hs : s ≠ 0)
    (hcard : Fintype.card F = 2 ^ n)
    (c : F) (hbase : c ^ (2 ^ (3 * k)) + c = relNorm k s * linPolyL k F lam) :
    ∑ i ∈ Finset.range (n / Nat.gcd k n),
      relNorm k (frobIter k i s) * linPolyL k F (frobIter k i lam) = 0 := by
  convert relative_trace_of_cross k n hcard c _ hbase using 1;
  unfold relTr; simp +decide [ *, relNorm, linPolyL, frobIter ] ; ring;
  refine' Finset.sum_congr rfl fun x hx => _;
  rw [ add_pow_char_pow ] ; ring

/-- **L5.5** Dedekind's independence of characters:
    Frobenius conjugates of a nonzero element are linearly independent.
    A weighted sum with nonzero weights cannot vanish. -/
theorem dedekind_independence (k n : ℕ) (hn0 : n ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hcop : Nat.Coprime k n)
    (s : F) (hs : s ≠ 0) (w : F) (hw : w ≠ 0)
    (hsum : ∑ i ∈ Finset.range (n / Nat.gcd k n),
      relNorm k (frobIter k i s) * frobIter k i w = 0) :
    False := by
  sorry

/-- **L5.6** Therefore L_k(lam) = 0. -/
theorem linPolyL_zero_from_trace (k n : ℕ) (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hcop : Nat.Coprime k n)
    (s lam : F) (hs : s ≠ 0)
    (c : F) (hbase : c ^ (2 ^ (3 * k)) + c = relNorm k s * linPolyL k F lam)
    (htrace : ∑ i ∈ Finset.range (n / Nat.gcd k n),
      relNorm k (frobIter k i s) * linPolyL k F (frobIter k i lam) = 0) :
    linPolyL k F lam = 0 := by
  sorry

end TraceForces

/-! ## Layer 6: Assembly — Frobenius Iteration Path -/

section Assembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
Cross = 0 iff ratio in kernel.
-/
theorem cross_zero_iff_kernel (k : ℕ) (s P : F) (hs : s ≠ 0) :
    crossForm k s P = 0 ↔ linPolyL k F (P / s) = 0 := by
  simp +decide only [crossForm, linPolyL];
  field_simp;
  simp +decide [ hs, mul_add, mul_assoc, mul_left_comm, pow_add, mul_div_cancel₀, add_eq_zero_iff_eq_neg ];
  rw [ div_pow, mul_div, div_eq_iff ] <;> ring_nf ; aesop

/-- **The Master Assembly via Frobenius Iteration** -/
theorem cross_nonzero_impossible_frobiter
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
  -- Step 1: Get key equation
  have hkey := key_equation_base k t₁ c heq
  -- Step 2: cross = N_k(s) · L_k(lam) (factorization bridge)
  have hfact : crossForm k s P = relNorm k s * linPolyL k F lam := by
    sorry
  -- Step 3: cross ≠ 0 means L_k(lam) ≠ 0
  have h_not_ker : linPolyL k F lam ≠ 0 := by
    intro h; rw [h, mul_zero] at hfact; exact hcross hfact
  -- Step 4: Key equation in factored form
  have hkey_fact : c ^ (2 ^ (3 * k)) + c = relNorm k s * linPolyL k F lam := by
    rw [hkey, hfact]
  -- Step 5: Trace of cross = 0 (from Frobenius iteration)
  have htrace := trace_of_factored_cross k n s lam hs hcard c hkey_fact
  -- Step 6: Trace expanded
  have htrace_exp := trace_expanded k n s lam hs hcard c hkey_fact
  -- Step 7: L_k(lam) = 0 from trace (contradicts Step 3)
  have h_ker := linPolyL_zero_from_trace k n hk hn hn0 hcard hcop s lam hs c hkey_fact htrace_exp
  exact h_not_ker h_ker

end Assembly

/-! ## DAG Dependency Summary — Frobenius Iteration Path

```
Layer 0: Definitions (shared)
    ↑ Grounded in: Mathlib.FieldTheory.Finite

Layer 1: Frobenius basics (additivity, periodicity, Fermat)
    ↑ Grounded in: FiniteField.pow_card, add_pow_expChar_pow, mul_pow

Layer 2: Key equation shifts (each is one Frobenius application)
    ↑ Uses: Layer 1 (frob is ring hom)

Layer 3: Telescoping sum
    ↑ Uses: Layer 2 + Finset.sum_add_distrib (Mathlib)

Layer 4: Trace = 0
    ↑ Uses: Layer 3 + Layer 1 (Fermat / periodicity)

Layer 5: Dedekind independence + L_k(lam) = 0
    ↑ Uses: Layer 4 + Mathlib.LinearAlgebra.LinearIndependent

Layer 6: Assembly — contradiction
    ↑ Uses: Layer 5 + factorization bridge (cross = N·L)
```
-/

end FrobeniusIterationDAG