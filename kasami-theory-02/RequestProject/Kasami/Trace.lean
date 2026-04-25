/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trace Function and Additive Characters

This file defines the absolute trace `Tr: GF(2^n) → GF(2)` and the
associated additive character `χ(x) = (-1)^{Tr(x)}` used in Walsh transforms.
-/
import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.CharTwo

open scoped BigOperators
noncomputable section

namespace Kasami

variable {n : ℕ} [NeZero n]

/-- The absolute trace function `Tr: GF(2^n) → ZMod 2`.
This is the `(ZMod 2)`-algebra trace. -/
abbrev absoluteTrace (n : ℕ) [NeZero n] : GaloisField 2 n →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) (GaloisField 2 n)

/-- The additive character of `GF(2)`: maps `0 ↦ 1` and `1 ↦ -1`. -/
def chi (x : ZMod 2) : ℤ :=
  if x = 0 then 1 else -1

@[simp]
theorem chi_zero : chi (0 : ZMod 2) = 1 := by simp [chi]

@[simp]
theorem chi_one : chi (1 : ZMod 2) = -1 := by
  simp [chi]

theorem chi_sq (x : ZMod 2) : chi x ^ 2 = 1 := by
  simp only [chi]
  split <;> ring

theorem chi_mul (x y : ZMod 2) : chi (x + y) = chi x * chi y := by
  fin_cases x <;> fin_cases y <;> simp [chi] <;> decide

/-- The lifted trace character: `χ(Tr(x)) = (-1)^{Tr(x)}` as an integer. -/
def traceLift [Fintype (GaloisField 2 n)] (x : GaloisField 2 n) : ℤ :=
  chi (absoluteTrace n x)

@[simp]
theorem traceLift_zero [Fintype (GaloisField 2 n)] :
    traceLift (0 : GaloisField 2 n) = 1 := by
  simp [traceLift, absoluteTrace]

theorem traceLift_sq [Fintype (GaloisField 2 n)] (x : GaloisField 2 n) :
    traceLift x ^ 2 = 1 := chi_sq _

theorem traceLift_val [Fintype (GaloisField 2 n)] (x : GaloisField 2 n) :
    traceLift x = 1 ∨ traceLift x = -1 := by
  unfold traceLift chi
  by_cases h : absoluteTrace n x = 0 <;> simp [h]

theorem traceLift_add [Fintype (GaloisField 2 n)] (x y : GaloisField 2 n) :
    traceLift (x + y) = traceLift x * traceLift y := by
  simp [traceLift, absoluteTrace]
  exact chi_mul _ _

/-
Orthogonality of the additive character: `Σ_x χ(Tr(ax)) = 0` for `a ≠ 0`.
-/
theorem traceLift_sum_eq_zero [Fintype (GaloisField 2 n)]
    (a : GaloisField 2 n) (ha : a ≠ 0) :
    ∑ x : GaloisField 2 n, traceLift (a * x) = 0 := by
  -- By Lemma 25, $Tr(ax)$ is a nontrivial additive character sum over a finite field, which equals 0 by character orthogonality.
  have h_sum_zero : ∑ x : GaloisField 2 n, (if absoluteTrace n (a * x) = 0 then 1 else -1) = 0 := by
    have h_trace_distri : Function.Bijective (fun x : GaloisField 2 n => a * x) := by
      exact ⟨ mul_right_injective₀ ha, mul_left_surjective₀ ha ⟩;
    have h_trace_distri : ∑ x : GaloisField 2 n, (if absoluteTrace n x = 0 then 1 else -1) = 0 := by
      have h_trace_distri : Function.Surjective (absoluteTrace n) := by
        exact LinearMap.surjective_of_ne_zero ( show Algebra.trace ( ZMod 2 ) ( GaloisField 2 n ) ≠ 0 from by exact? )
      have h_trace_distri : Finset.card (Finset.filter (fun x => absoluteTrace n x = 0) Finset.univ) = Finset.card (Finset.filter (fun x => absoluteTrace n x = 1) Finset.univ) := by
        exact?;
      simp_all +decide [ Finset.sum_ite ];
      rw [ show ( Finset.filter ( fun x => ¬ ( absoluteTrace n ) x = 0 ) Finset.univ : Finset ( GaloisField 2 n ) ) = Finset.filter ( fun x => ( absoluteTrace n ) x = 1 ) Finset.univ from Finset.filter_congr fun x hx => by have := Fin.exists_fin_two.mp ⟨ ( absoluteTrace n ) x, rfl ⟩ ; aesop ] ; linarith;
    rw [ ← h_trace_distri, eq_comm ];
    conv_lhs => rw [ ← Equiv.sum_comp ( Equiv.ofBijective _ ‹_› ) ] ;
    rfl;
  exact?

/-- The character sum over all elements: `Σ_x χ(Tr(0·x)) = 2^n`. -/
theorem traceLift_sum_zero [Fintype (GaloisField 2 n)] :
    ∑ x : GaloisField 2 n, traceLift (0 * x) =
      (Fintype.card (GaloisField 2 n) : ℤ) := by
  simp [traceLift]

end Kasami

end