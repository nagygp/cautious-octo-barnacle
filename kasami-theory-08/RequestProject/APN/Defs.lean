/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# APN and Almost Bent Functions — Core Definitions

This module defines the fundamental objects of the theory of Almost Perfect Nonlinear (APN)
and Almost Bent (AB) functions over finite fields / elementary abelian 2-groups.

## Main Definitions

* `APN.diffEqSolutions` — the set of solutions to F(x + a) - F(x) = b
* `APN.differentialUniformity` — δ(F), the maximum of |{x : F(x+a)-F(x) = b}| over a ≠ 0, b
* `APN.IsAPN` — a function is APN iff δ(F) ≤ 2
* `APN.innerProductF2` — inner product over GF(2)^n
* `APN.walshCoeff` — Walsh transform coefficient W_F(a,b)
* `APN.IsAlmostBent` — AB property: all Walsh coefficients in {0, ±2^((n+1)/2)}

## References

* Carlet, C. "Vectorial Boolean Functions for Cryptography"
* Nyberg, K. "Differentially uniform mappings for cryptography"
* Chabaud, F. and Vaudenay, S. "Links between differential and linear cryptanalysis"
-/

import Mathlib

open Finset BigOperators

namespace APN

/-! ### Differential Uniformity -/

section DifferentialUniformity

variable {α : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

/-- The set of solutions to the differential equation `F(x + a) - F(x) = b`. -/
def diffEqSolutions (F : α → α) (a b : α) : Finset α :=
  Finset.univ.filter (fun x => F (x + a) - F (x) = b)

/-- The number of solutions to `F(x + a) - F(x) = b`. This is sometimes called
    the *entry* `Δ_F(a, b)` of the difference distribution table. -/
def delta (F : α → α) (a b : α) : ℕ :=
  (diffEqSolutions F a b).card

/-- A function `F` is **APN** (Almost Perfect Nonlinear) if for every nonzero `a`,
    the equation `F(x + a) - F(x) = b` has at most 2 solutions for every `b`.
    Equivalently, the differential uniformity is at most 2. -/
def IsAPN (F : α → α) : Prop :=
  ∀ (a : α), a ≠ 0 → ∀ (b : α), delta F a b ≤ 2

/-- The **differential uniformity** of `F`, defined as
    `max_{a ≠ 0, b} |{x : F(x + a) - F(x) = b}|`.
    Returns 0 if the domain has at most one element. -/
noncomputable def differentialUniformity (F : α → α) : ℕ :=
  (Finset.univ.filter (· ≠ (0 : α)) ×ˢ Finset.univ).sup
    (fun p => (diffEqSolutions F p.1 p.2).card)

/-
A function is APN if and only if its differential uniformity is at most 2.
-/
theorem isAPN_iff_differentialUniformity_le (F : α → α) :
    IsAPN F ↔ differentialUniformity F ≤ 2 := by
      constructor;
      · exact fun h => Finset.sup_le fun p hp => by aesop;
      · simp +decide [ IsAPN, differentialUniformity ];
        exact fun h a ha b => h a b ha

end DifferentialUniformity

/-! ### Walsh Transform over GF(2)^n -/

section WalshTransform

/-- The inner product of two vectors over `GF(2)^n`, i.e., `∑ᵢ aᵢ · bᵢ` in `ZMod 2`. -/
def innerProductF2 {n : ℕ} (a b : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, a i * b i

/-- `(-1)^x` where `x : ZMod 2`, returning an integer.
    Maps `0 ↦ 1` and `1 ↦ -1`. -/
def signF2 (x : ZMod 2) : ℤ :=
  if x = 0 then 1 else -1

/-- The **Walsh transform** of a vectorial function `F : GF(2)^n → GF(2)^n`,
    evaluated at `(a, b)`. This is defined as
    `W_F(a, b) = ∑_x (-1)^{⟨b, F(x)⟩ + ⟨a, x⟩}`. -/
def walshCoeff {n : ℕ} (F : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (a b : Fin n → ZMod 2) : ℤ :=
  ∑ x : Fin n → ZMod 2, signF2 (innerProductF2 b (F x) + innerProductF2 a x)

/-- A vectorial function `F : GF(2)^n → GF(2)^n` is **Almost Bent** (AB) if
    for every `b ≠ 0`, every Walsh coefficient `W_F(a, b)` lies in `{0, ±2^((n+1)/2)}`. -/
def IsAlmostBent {n : ℕ} (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) : Prop :=
  ∀ (a b : Fin n → ZMod 2), b ≠ 0 →
    walshCoeff F a b = 0 ∨
    walshCoeff F a b = 2 ^ ((n + 1) / 2) ∨
    walshCoeff F a b = -(2 ^ ((n + 1) / 2))

end WalshTransform

/-! ### Component Functions -/

section ComponentFunctions

/-- The **component function** `F_b` of a vectorial Boolean function `F`,
    defined as `F_b(x) = ⟨b, F(x)⟩` (the inner product of `b` with `F(x)` over GF(2)).
    For `b ≠ 0`, these are the nontrivial components. -/
def componentFunction {n : ℕ} (F : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (b : Fin n → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 :=
  fun x => innerProductF2 b (F x)

/-- The **Walsh–Hadamard transform** of a Boolean function `f : GF(2)^n → GF(2)`,
    evaluated at `a ∈ GF(2)^n`:
    `W_f(a) = ∑_x (-1)^{f(x) + ⟨a,x⟩}`. -/
def walshHadamard {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (a : Fin n → ZMod 2) : ℤ :=
  ∑ x : Fin n → ZMod 2, signF2 (f x + innerProductF2 a x)

/-- The Walsh coefficient of a vectorial function equals the Walsh–Hadamard
    transform of its component function. -/
theorem walshCoeff_eq_walshHadamard {n : ℕ}
    (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (a b : Fin n → ZMod 2) :
    walshCoeff F a b = walshHadamard (componentFunction F b) a := by
  simp [walshCoeff, walshHadamard, componentFunction]

end ComponentFunctions

/-! ### Nonlinearity -/

section Nonlinearity

/-- The **nonlinearity** of a Boolean function `f : GF(2)^n → GF(2)` is
    `NL(f) = 2^(n-1) - (1/2) max_a |W_f(a)|`.
    We define it as a natural number (the formula always gives a non-negative integer). -/
noncomputable def boolNonlinearity {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) : ℕ :=
  2 ^ (n - 1) - (Finset.univ.sup (fun a => (walshHadamard f a).natAbs)) / 2

/-- The **nonlinearity** of a vectorial function `F : GF(2)^n → GF(2)^n` is
    the minimum nonlinearity over all nontrivial component functions.
    Returns `0` when `n = 0` (vacuously). -/
noncomputable def vecNonlinearity {n : ℕ}
    (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) : WithTop ℕ :=
  (Finset.univ.filter (· ≠ (0 : Fin n → ZMod 2))).inf
    (fun b => (boolNonlinearity (componentFunction F b) : WithTop ℕ))

end Nonlinearity

end APN