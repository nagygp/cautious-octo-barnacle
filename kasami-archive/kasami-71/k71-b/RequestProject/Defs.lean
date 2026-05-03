/-
  Definitions for the Bracken-McGuire Theorem 3 formalization.
  Based on arXiv:0803.3781.
-/
import Mathlib

set_option maxHeartbeats 800000

open Polynomial Finset

noncomputable section

/-! ## Basic definitions for APN functions over F_{2^n} -/

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The linearized derivative Δ_u f(x) = f(x+u) + f(x) + f(u).
    In characteristic 2, subtraction equals addition, so this is the
    standard discrete derivative for power functions. -/
def deltaDerivative (f : F → F) (u x : F) : F :=
  f (x + u) + f x + f u

/-- The Gold power function g(x) = x^(2^k + 1). -/
def goldFunction (k : ℕ) (x : F) : F :=
  x ^ (2 ^ k + 1)

/-- The Bracken-McGuire binomial f(x) = x^(2^k+1) + ω · x^(2^(ik) + 2^(tk+s)). -/
def brackenMcGuireBinomial (k i t s : ℕ) (ω : F) (x : F) : F :=
  x ^ (2 ^ k + 1) + ω * x ^ (2 ^ (i * k) + 2 ^ (t * k + s))

/-- The kernel of the linearized derivative: {x | Δ_u f(x) = 0}. -/
def deltaKernel (f : F → F) (u : F) : Set F :=
  {x : F | deltaDerivative f u x = 0}

/-- A function is APN (Almost Perfect Nonlinear) if for every nonzero u,
    the equation Δ_u f(x) = 0 has at most 2 solutions (kernel dimension ≤ 1). -/
def isAPN (f : F → F) : Prop :=
  ∀ u : F, u ≠ 0 → (deltaKernel f u).Finite ∧
    ∀ (S : Finset F), (↑S : Set F) ⊆ deltaKernel f u → S.card ≤ 2

end

