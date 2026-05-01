/-
# Almost Bent Functions and the Kasami Power Function

This file contains the core definitions for the formalization of the
P₃ completeness analysis of the Kasami power function over GF(2^n).

## Main definitions

- `KasamiContext`: bundled parameters for the Kasami function analysis
- `traceForm`: the quadratic form Q_a(x) = Tr(a · x^d)
- `polarForm`: the associated bilinear form B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y)
- `radicalSubspace`: the radical of the quadratic form
- `linearizedPoly`: the linearized polynomial L_a
- `walshTransform`: the Walsh-Hadamard transform
-/
import Mathlib

noncomputable section

open scoped BigOperators
open Finset

/-! ## Finite Field Setup -/

/-- The context for Kasami function analysis.
  We work over F = GF(2^n) where n = 2k+1 is odd,
  and the Kasami exponent is d = 2^(2k) - 2^k + 1. -/
structure KasamiContext where
  /-- The parameter k, so n = 2k+1 -/
  k : ℕ
  /-- k is positive -/
  hk : 0 < k

namespace KasamiContext

variable (ctx : KasamiContext)

/-- The extension degree n = 2k + 1 -/
def n : ℕ := 2 * ctx.k + 1

/-- n is at least 3 -/
lemma n_ge_three : 3 ≤ ctx.n := by unfold n; have := ctx.hk; omega

/-- n is positive -/
lemma n_pos : 0 < ctx.n := by unfold n; omega

/-- n is odd -/
lemma n_odd : ¬ 2 ∣ ctx.n := by
  unfold n
  omega

/-- The Kasami exponent d = 2^(2k) - 2^k + 1 -/
def d : ℕ := 2 ^ (2 * ctx.k) - 2 ^ ctx.k + 1

end KasamiContext

/-! ## Abstract Quadratic Form Theory over GF(2)

We work abstractly with a finite field F that is a finite extension of ZMod 2,
equipped with the field trace. The key results are:
1. The trace is a nondegenerate bilinear pairing
2. For a quadratic form Q_a(x) = Tr(a·x^d), the polar form is B_a(x,y) = Tr(x·L_a(y))
3. The radical of Q_a equals the kernel of L_a
-/

/-- The radical of a function Q : F → ZMod 2 defined via its polar form.
    rad(Q) = {y | ∀ x, Q(x+y) + Q(x) + Q(y) = 0} -/
def radicalSet (F : Type*) [Field F] [CharP F 2]
    (Q : F → ZMod 2) : Set F :=
  {y | ∀ x, Q (x + y) + Q x + Q y = 0}

/-- The kernel of a function L : F → F.
    ker(L) = {y | L(y) = 0} -/
def kernelSet (F : Type*) [Field F] (L : F → F) : Set F :=
  {y | L y = 0}

/-! ## Trace Non-Degeneracy

The trace form Tr : GF(2^n) → GF(2) is nondegenerate in the sense that
for any z ∈ GF(2^n), if Tr(x·z) = 0 for all x, then z = 0.
-/

/-- A trace-like bilinear pairing is nondegenerate if
    ∀ z, (∀ x, f(x * z) = 0) → z = 0 -/
def TraceNondegenerate (F : Type*) [Field F] (K : Type*) [Field K]
    (f : F → K) : Prop :=
  ∀ z : F, (∀ x : F, f (x * z) = 0) → z = 0

/-! ## The Bridge: Radical equals Kernel

The key structural theorem: if we have a quadratic form Q where
the polar form B(x,y) = Tr(x · L(y)) for some function L, and the
trace is nondegenerate, then rad(Q) = ker(L).
-/

/-
The bridge theorem stated abstractly: if Q's polar form satisfies
    Q(x+y) + Q(x) + Q(y) = f(x * L(y)) for a nondegenerate pairing f,
    then rad(Q) = ker(L).
-/
theorem radical_eq_kernel_of_polar_form
    (F : Type*) [Field F]
    (K : Type*) [Field K]
    (f : F → K) (Q : F → K) (L : F → F)
    (hpolar : ∀ x y, Q (x + y) + Q x + Q y = f (x * L y))
    (hnd : TraceNondegenerate F K f)
    (hf0 : f 0 = 0) :
    {y : F | ∀ x, Q (x + y) + Q x + Q y = 0} = {y : F | L y = 0} := by
  ext y;
  constructor <;> intro hy <;> specialize hnd ( L y ) <;> aesop

/-! ## Walsh Transform -/

/-- The Walsh-Hadamard transform of a function f : F → ZMod 2,
    evaluated at a ∈ F. This counts the "imbalance" of f with
    respect to the character x ↦ (-1)^{Tr(ax)}.
    W_f(a) = ∑_{x ∈ F} (-1)^{f(x) + Tr(ax)} -/
def walshTransform (F : Type*) [Fintype F] [Field F]
    (Tr : F → ZMod 2) (f : F → ZMod 2) (a : F) : ℤ :=
  ∑ x : F, if (f x + Tr (a * x)).val = 0 then 1 else -1

/-! ## Almost Bent Property

A function f : GF(2^n) → GF(2) is Almost Bent (AB) if its
Walsh transform takes only the values 0, ±2^((n+1)/2).
-/

/-- A function is Almost Bent if its Walsh spectrum is {0, ±2^((n+1)/2)} -/
def IsAlmostBent (F : Type*) [Fintype F] [Field F]
    (Tr : F → ZMod 2) (f : F → ZMod 2) (halfDim : ℕ) : Prop :=
  ∀ a : F, walshTransform F Tr f a = 0 ∨
            walshTransform F Tr f a = 2 ^ halfDim ∨
            walshTransform F Tr f a = -(2 ^ halfDim : ℤ)

/-! ## P₃ Triple Count -/

/-- The triple count: the number of triples (x, y) such that
    f(x) = f(y) = f(x+y) = 1, expressible via the Walsh transform as
    TripleCount = 2^{-3n} ∑_a W_f(a)³ -/
def tripleCount (F : Type*) [Fintype F] [Field F]
    (_Tr : F → ZMod 2) (f : F → ZMod 2) : ℤ :=
  ∑ x : F, ∑ y : F,
    if (f x).val = 1 ∧ (f y).val = 1 ∧ (f (x + y)).val = 1 then 1 else 0

end