/-
# Kasami P₃ Triple Count — Shared Definitions

Core mathematical objects for the Kasami P₃ proof pipeline.
Every subsequent phase imports only this file for base definitions.

## Mathematical Setup
- F = 𝔽_{2^n}, n ≥ 3 odd, with the Gold parameter k satisfying gcd(k,n) = 1
- Tr : F → 𝔽₂ is the absolute trace
- The Gold function is g(x) = Tr(x^(2^k+1))
- The Walsh transform W_g(a) = ∑_x (-1)^(g(x) + Tr(ax))
-/
import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators

/-! ## Trace Character -/

/-- The additive character χ : ZMod 2 → ℤ, mapping 0 ↦ 1 and 1 ↦ -1. -/
def traceChar : ZMod 2 → ℤ :=
  fun t => if t = 0 then 1 else -1

@[simp] lemma traceChar_zero : traceChar 0 = 1 := by simp [traceChar]
@[simp] lemma traceChar_one : traceChar 1 = -1 := by simp [traceChar]

lemma traceChar_sq (t : ZMod 2) : traceChar t ^ 2 = 1 := by
  fin_cases t <;> simp [traceChar]

lemma traceChar_add (s t : ZMod 2) :
    traceChar (s + t) = traceChar s * traceChar t := by
  fin_cases s <;> fin_cases t <;> simp [traceChar]
  decide

lemma traceChar_values (t : ZMod 2) : traceChar t = 1 ∨ traceChar t = -1 := by
  fin_cases t <;> simp [traceChar]

lemma traceChar_abs (t : ZMod 2) : |traceChar t| = 1 := by
  rcases traceChar_values t with h | h <;> simp [h]

/-! ## Field Parameters -/

/-- `KasamiData` bundles the parameters for a Kasami-function analysis. -/
structure KasamiData where
  n : ℕ
  k : ℕ
  hn : n ≥ 3
  hk : Nat.Coprime k n
  hk_pos : k ≥ 1
  hk_lt : k < n
  hn_odd : ¬ 2 ∣ n

namespace KasamiData

variable (K : KasamiData)

lemma n_ne_zero : K.n ≠ 0 := by have := K.hn; omega
lemma n_pos : 0 < K.n := by have := K.hn; omega

/-- The finite field 𝔽_{2^n}. -/
abbrev F : Type := GaloisField 2 K.n

noncomputable instance instFieldF : Field K.F := inferInstance
noncomputable instance instFiniteF : Finite K.F := inferInstance
instance instCharPF : CharP K.F 2 := inferInstance
instance instExpCharF : ExpChar K.F 2 := inferInstance
noncomputable instance instFintypeF : Fintype K.F := Fintype.ofFinite K.F
noncomputable instance instAlgebraF : Algebra (ZMod 2) K.F := inferInstance

/-- |F| = 2^n. -/
lemma card_F : Fintype.card K.F = 2 ^ K.n := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 K.n K.n_ne_zero

/-- The algebraic trace Tr : F → 𝔽₂. -/
noncomputable def Tr : K.F →ₗ[ZMod 2] (ZMod 2) :=
  Algebra.trace (ZMod 2) K.F

/-- The Gold exponent d = 2^k + 1. -/
def goldExp : ℕ := 2 ^ K.k + 1

/-! ## Frobenius -/

/-- The k-th Frobenius: x ↦ x^(2^k). -/
noncomputable def frob (x : K.F) : K.F := x ^ (2 ^ K.k)

lemma frob_def (x : K.F) : K.frob x = x ^ (2 ^ K.k) := rfl

lemma frob_add (x y : K.F) : K.frob (x + y) = K.frob x + K.frob y := by
  simp only [frob_def]; exact add_pow_expChar_pow x y 2 K.k

lemma frob_mul (x y : K.F) : K.frob (x * y) = K.frob x * K.frob y := by
  simp [frob_def, mul_pow]

@[simp] lemma frob_zero : K.frob 0 = 0 := by simp [frob_def]
@[simp] lemma frob_one : K.frob 1 = 1 := by simp [frob_def]

/-- The conjugate Frobenius: x → x^(2^(n-k)). -/
noncomputable def frobConj (x : K.F) : K.F := x ^ (2 ^ (K.n - K.k))

lemma frobConj_def (x : K.F) : K.frobConj x = x ^ (2 ^ (K.n - K.k)) := rfl

lemma frobConj_add (x y : K.F) : K.frobConj (x + y) = K.frobConj x + K.frobConj y := by
  simp only [frobConj_def]; exact add_pow_expChar_pow x y 2 (K.n - K.k)

/-! ## Linearized Map (Differential Kernel) -/

/-- The linearized map L_a(x) = a^(2^k)·x + a·x^(2^k).
    This arises from the derivative of the Gold function f(x) = x^(2^k+1):
    f(x + a) + f(x) + f(a) = L_a(x). -/
noncomputable def linMap (a x : K.F) : K.F :=
  K.frob a * x + a * K.frob x

/-! ## Quadratic Form and Bilinear Form -/

/-- The Gold quadratic form Q_a(x) = Tr(a · x^(2^k + 1)). -/
noncomputable def goldQuad (a x : K.F) : ZMod 2 :=
  K.Tr (a * x ^ K.goldExp)

/-- The associated bilinear form B_a(x,y) = Tr(a · (x^(2^k)·y + x·y^(2^k))).
    This is the polar form: B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y). -/
noncomputable def goldBilin (a x y : K.F) : ZMod 2 :=
  K.Tr (a * (K.frob x * y + x * K.frob y))

/-! ## Walsh–Hadamard Transform -/

/-- The Gold Boolean function: g(x) = Tr(x^(2^k+1)). -/
noncomputable def goldBool (x : K.F) : ZMod 2 := K.Tr (x ^ K.goldExp)

/-- Walsh–Hadamard transform of a Boolean function g : F → 𝔽₂:
    W_g(a) = ∑_{x ∈ F} χ(g(x) + Tr(a·x)). -/
noncomputable def walsh (g : K.F → ZMod 2) (a : K.F) : ℤ :=
  ∑ x : K.F, traceChar (g x + K.Tr (a * x))

/-- Walsh transform of the Gold Boolean function. -/
noncomputable def goldWalsh (a : K.F) : ℤ := K.walsh K.goldBool a

/-! ## Triple Count -/

/-- The ordered triple count: |{(x, y, z) ∈ F³ | g(x)+g(y)+g(z) = g(x+y+z)}|. -/
noncomputable def orderedTripleCount : ℕ :=
  Finset.card (Finset.univ.filter fun t : K.F × K.F × K.F =>
    K.goldBool t.1 + K.goldBool t.2.1 + K.goldBool t.2.2 =
    K.goldBool (t.1 + t.2.1 + t.2.2))

/-- The normalized triple count P₃ = orderedTripleCount / 8. -/
noncomputable def tripleCount : ℕ := K.orderedTripleCount / 8

end KasamiData
