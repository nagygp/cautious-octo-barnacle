/-
# Almost Bent Functions and the Kasami Power Function — Core Definitions

This file contains the core definitions for the formalization of the
P₃ completeness analysis of the Kasami power function over GF(2^n).

## Main definitions

- `walshTransform`: the Walsh-Hadamard transform
- `IsAlmostBent`: Almost Bent function property
- `tripleCount`: the P₃ triple count
- `tripleCorrelation`: the triple correlation function
-/
import Mathlib

noncomputable section

open scoped BigOperators
open Finset

/-! ## Walsh Transform -/

/-- The Walsh-Hadamard transform of a function f : F → ZMod 2,
    evaluated at a ∈ F. This counts the "imbalance" of f with
    respect to the character x ↦ (-1)^{Tr(ax)}.
    W_f(a) = ∑_{x ∈ F} (-1)^{f(x) + Tr(ax)} -/
def walshTransform (F : Type*) [Fintype F] [Field F]
    (Tr : F → ZMod 2) (f : F → ZMod 2) (a : F) : ℤ :=
  ∑ x : F, if (f x + Tr (a * x)).val = 0 then 1 else -1

/-! ## Almost Bent Property -/

/-- A function is Almost Bent if its Walsh spectrum is {0, ±2^((n+1)/2)} -/
def IsAlmostBent (F : Type*) [Fintype F] [Field F]
    (Tr : F → ZMod 2) (f : F → ZMod 2) (halfDim : ℕ) : Prop :=
  ∀ a : F, walshTransform F Tr f a = 0 ∨
            walshTransform F Tr f a = 2 ^ halfDim ∨
            walshTransform F Tr f a = -(2 ^ halfDim : ℤ)

/-! ## P₃ Triple Count -/

/-- The triple count: the number of pairs (x, y) such that
    f(x) = f(y) = f(x+y) = 1. -/
def tripleCount (F : Type*) [Fintype F] [Field F]
    (_Tr : F → ZMod 2) (f : F → ZMod 2) : ℤ :=
  ∑ x : F, ∑ y : F,
    if (f x).val = 1 ∧ (f y).val = 1 ∧ (f (x + y)).val = 1 then 1 else 0

/-! ## Triple Correlation -/

/-- The triple correlation function C₃ = ∑_{x,y} (-1)^{f(x)+f(y)+f(x+y)}. -/
def tripleCorrelation (F : Type*) [Fintype F] [Field F]
    (f : F → ZMod 2) : ℤ :=
  ∑ x : F, ∑ y : F,
    (if (f x).val = 0 then (1 : ℤ) else -1) *
    (if (f y).val = 0 then 1 else -1) *
    (if (f (x + y)).val = 0 then 1 else -1)

end
