/-
  BinomialParams.lean

  Defines the BinomialParams structure that encapsulates all parameters
  for the Bracken-McGuire Theorem 3 and provides a clean interface.
-/
import Mathlib
import Theorem3.Defs

set_option maxHeartbeats 800000

open Polynomial Finset

noncomputable section

/-! ## BinomialParams: primary interface for the Bracken-McGuire theorem -/

/-- Parameters for the Bracken-McGuire binomial APN construction.
    The binomial is f(x) = x^(2^k+1) + ω · x^(2^(ik) + 2^(tk+s))
    over F_{2^n}, where ω has multiplicative order 2^(2k) + 2^k + 1. -/
structure BinomialParams (F : Type*) [Field F] [Fintype F] [CharP F 2] where
  /-- The primary exponent parameter -/
  k : ℕ
  /-- The first exponent multiplier -/
  i : ℕ
  /-- The second exponent multiplier -/
  t : ℕ
  /-- The exponent shift -/
  s : ℕ
  /-- The field size parameter: |F| = 2^n -/
  n : ℕ
  /-- The coefficient of the second monomial -/
  ω : F
  /-- k is positive -/
  hk : 0 < k
  /-- n is positive -/
  hn : 0 < n
  /-- The field has cardinality 2^n -/
  hcard : Fintype.card F = 2 ^ n
  /-- ω has the correct multiplicative order -/
  hω_order : orderOf ω = 2 ^ (2 * k) + 2 ^ k + 1

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The binomial function associated to parameters. -/
def BinomialParams.toFunc (p : BinomialParams F) : F → F :=
  brackenMcGuireBinomial p.k p.i p.t p.s p.ω

/-- The delta kernel for the binomial. -/
def BinomialParams.kernel (p : BinomialParams F) (u : F) : Set F :=
  deltaKernel p.toFunc u

/-- The APN property for the binomial. -/
def BinomialParams.isAPNProp (p : BinomialParams F) : Prop :=
  isAPN p.toFunc

/-- ω is nonzero (follows from having order > 1). -/
lemma BinomialParams.ω_ne_zero (p : BinomialParams F) : p.ω ≠ 0 := by
  intro h
  have ho := p.hω_order
  simp [h] at ho

end
