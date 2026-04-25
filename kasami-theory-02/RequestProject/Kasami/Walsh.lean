/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Walsh Transform

This file defines the Walsh transform of a function on `GF(2^n)` and
the Walsh transform of a subset, along with Parseval's identity.
-/
import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.Trace

open scoped BigOperators
open Finset
noncomputable section

namespace Kasami

variable {n : ℕ} [NeZero n]

/-- The Walsh transform of a function `f : GF(2^n) → GF(2^n)` at point `a`:
`W_f(a) = Σ_x (-1)^{Tr(ax + f(x))}` -/
def walshTransform [Fintype (GaloisField 2 n)]
    (f : GaloisField 2 n → GaloisField 2 n)
    (a : GaloisField 2 n) : ℤ :=
  ∑ x : GaloisField 2 n, traceLift (a * x + f x)

/-- The Walsh transform of a finite set `S ⊆ GF(2^n)` at point `a`:
`Ŝ(a) = Σ_{x ∈ S} (-1)^{Tr(ax)}` -/
def walshTransformSet [Fintype (GaloisField 2 n)]
    (S : Finset (GaloisField 2 n))
    (a : GaloisField 2 n) : ℤ :=
  ∑ x ∈ S, traceLift (a * x)

/-
Parseval's identity: `Σ_a W_f(a)^2 = 2^{2n}`.
This is a standard result for Walsh transforms.
-/
theorem walshTransform_parseval [Fintype (GaloisField 2 n)]
    (f : GaloisField 2 n → GaloisField 2 n) :
    ∑ a : GaloisField 2 n, (walshTransform f a) ^ 2 =
      (Fintype.card (GaloisField 2 n) : ℤ) ^ 2 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : GaloisField 2 n, (∑ x : GaloisField 2 n, traceLift (a * x + f x)) ^ 2 = ∑ x : GaloisField 2 n, ∑ y : GaloisField 2 n, traceLift (f x + f y) * ∑ a : GaloisField 2 n, traceLift (a * (x + y)) := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => _ ) );
    simp +decide [ mul_add, add_mul, traceLift_add ];
    grind;
  -- Consider the inner sum $\sum_{a \in \mathbb{F}_{2^n}} \chi(ax + f(x))$.
  have h_inner : ∀ x y : GaloisField 2 n, x ≠ y → ∑ a : GaloisField 2 n, traceLift (a * (x + y)) = 0 := by
    intro x y hxy;
    convert traceLift_sum_eq_zero ( x + y ) _ using 1;
    · ac_rfl;
    · grind;
  convert h_fubini using 1;
  rw [ Finset.sum_congr rfl fun x hx => Finset.sum_eq_single x ( fun y hy => ?_ ) ( ?_ ) ] <;> simp_all +decide [ sq ];
  · simp_all +decide [ ← two_mul, charTwo_add_self ];
    simp_all +decide [ show ( 2 : GaloisField 2 n ) = 0 by exact? ];
  · exact fun h => Or.inr <| h_inner x y <| Ne.symm h

end Kasami

end