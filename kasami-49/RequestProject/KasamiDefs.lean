import Mathlib

/-!
# Kasami Almost Bent (AB) Functions — Definitions

This file defines the core objects for the Kasami AB formalization using the
Canteaut–Charpin–Dobbertin (CCD) approach.

## Main Definitions

* `kasamiExp` — The Kasami exponent d = 2^{2k} − 2^k + 1.
* `linPolyL` — The linearized polynomial L_k(z) = z^{2^{2k}} + z^{2^k} + z.
* `linPolyM` — The companion polynomial M_k(z) = z^{2^k} + z.
* `frobIter` — Shorthand for x ↦ x^{2^k}, the k-th Frobenius iterate.

## Setup

We work over a finite field `F` of characteristic 2 with `|F| = 2^n`.
-/

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-! ### Finite field setup -/

/-- The Kasami exponent: d = 2^{2k} − 2^k + 1. Since we work in ℕ and
    2^{2k} ≥ 2^k for all k, the subtraction is safe. -/
noncomputable def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The k-th Frobenius iterate applied to an element: x ↦ x^{2^k}. -/
noncomputable def frobIter {F : Type*} [CommSemiring F] [ExpChar F 2] (k : ℕ) (z : F) : F :=
  z ^ (2 ^ k)

/-- The linearized polynomial L_k(z) = z^{2^{2k}} + z^{2^k} + z. -/
noncomputable def linPolyL {F : Type*} [CommSemiring F] [ExpChar F 2] (k : ℕ) (z : F) : F :=
  z ^ (2 ^ (2 * k)) + z ^ (2 ^ k) + z

/-- The companion polynomial M_k(z) = z^{2^k} + z. -/
noncomputable def linPolyM {F : Type*} [CommSemiring F] [ExpChar F 2] (k : ℕ) (z : F) : F :=
  z ^ (2 ^ k) + z

/-! ### Basic identities -/

section BasicIdents

variable {F : Type*} [CommRing F] [CharP F 2] (k : ℕ) (z : F)

/-- L_k can be rewritten using M_k: L_k(z) = frobIter(2k, z) + M_k(z). -/
lemma linPolyL_eq_frob_add_M :
    linPolyL k z = frobIter (2 * k) z + linPolyM k z := by
  simp only [linPolyL, linPolyM, frobIter, add_assoc]

/-- M_k(z) = frobIter(k, z) + z -/
lemma linPolyM_eq : linPolyM k z = frobIter k z + z := by
  simp [linPolyM, frobIter]

/-- frobIter distributes over addition in char 2 (Frobenius is a ring hom). -/
lemma frobIter_add (x y : F) :
    frobIter k (x + y) = frobIter k x + frobIter k y := by
  simp only [frobIter]
  exact add_pow_expChar_pow x y 2 k

/-- frobIter distributes over multiplication. -/
lemma frobIter_mul (x y : F) :
    frobIter k (x * y) = frobIter k x * frobIter k y := by
  simp only [frobIter, mul_pow]

/-- frobIter of 0 is 0. -/
@[simp] lemma frobIter_zero : frobIter k (0 : F) = 0 := by
  simp [frobIter]

/-- frobIter of 1 is 1. -/
@[simp] lemma frobIter_one : frobIter k (1 : F) = 1 := by
  simp [frobIter]

/-- Composing Frobenius iterates: frobIter(a, frobIter(b, z)) = frobIter(a+b, z). -/
lemma frobIter_comp (a b : ℕ) (z : F) :
    frobIter a (frobIter b z) = frobIter (a + b) z := by
  simp only [frobIter, ← pow_mul, pow_add]
  ring

end BasicIdents

/-! ### Kernel definitions -/

section Kernels

variable {F : Type*} [CommRing F] [CharP F 2]

/-- The kernel of L_k: elements z with L_k(z) = 0. -/
def kerL (k : ℕ) : Set F := {z : F | linPolyL k z = 0}

/-- The kernel of M_k: elements z with M_k(z) = 0. -/
def kerM (k : ℕ) : Set F := {z : F | linPolyM k z = 0}

/-- The fixed-point set of the m-th Frobenius iterate: {z | z^{2^m} = z}. -/
def frobFixedPts (m : ℕ) : Set F := {z : F | frobIter m z = z}

/-- Elements of GF(2) embedded in F, i.e., {0, 1}. -/
def gf2Set : Set F := {0, 1}

end Kernels
