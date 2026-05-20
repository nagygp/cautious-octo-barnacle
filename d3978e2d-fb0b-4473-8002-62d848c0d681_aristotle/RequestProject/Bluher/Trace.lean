/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Generalized Trace and the Telescoping Principle

This file formalizes the **generalized trace** associated to a ring endomorphism σ,
and proves its fundamental structural properties. The key insight is the
**telescoping lemma**: the trace of the Artin-Schreier operator `x - σ(x)` collapses
to `x - σ^m(x)`. This single identity is the engine behind additive Hilbert 90
and connects to Galois cohomology via the coboundary interpretation.

## Mathematical Context

Given a ring endomorphism `σ : R →+* R`, the generalized trace is:

  `T_m^σ(x) = ∑_{j=0}^{m-1} σ^j(x)`

When `σ` is the Frobenius `x ↦ x^q` on `F̄_p`, this recovers the classical
finite field trace `T_m(x) = ∑ x^{q^j}`.

## Big Ideas

1. **Telescoping as Coboundary**: The map `x ↦ x - σ(x)` is a 1-cocycle for the
   additive group action. The telescoping lemma says trace kills coboundaries —
   this is the heart of `H¹(⟨σ⟩, R⁺) = 0` (additive Hilbert 90).

2. **Category Theory**: The trace is the norm map for the additive group in the
   category of modules over the group ring `ℤ[σ]/(σ^m - 1)`. The telescoping
   identity is the factorization `(1 + σ + ... + σ^{m-1})(1 - σ) = 1 - σ^m`
   in this ring — a multiplicative identity masquerading as additive cancellation.

3. **Linearized Polynomials**: When σ is Frobenius, the trace is a linearized
   (additive) polynomial. These form a non-commutative ring under composition,
   isomorphic to the Ore polynomial ring `F_q[x; Frob]`. This connects finite
   field combinatorics to non-commutative algebra and D-modules.
-/

import Mathlib

open Finset Function BigOperators

set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

/-! ## Generalized Trace -/

/-- The generalized trace `T_m^σ(x) = ∑_{j=0}^{m-1} σ^j(x)`, where `σ` is a
    ring endomorphism. This simultaneously generalizes:
    - The finite field trace `∑ x^{q^j}` (when σ = Frobenius)
    - The norm map for additive group actions
    - The Reynolds operator in invariant theory -/
noncomputable def sigmaTrace (σ : R →+* R) (m : ℕ) (x : R) : R :=
  ∑ j ∈ range m, (σ ^ j) x

/-! ## Basic Properties -/

lemma sigmaTrace_zero (σ : R →+* R) (x : R) : sigmaTrace σ 0 x = 0 := by
  simp [sigmaTrace]

lemma sigmaTrace_one (σ : R →+* R) (x : R) : sigmaTrace σ 1 x = x := by
  simp [sigmaTrace]

lemma sigmaTrace_succ (σ : R →+* R) (m : ℕ) (x : R) :
    sigmaTrace σ (m + 1) x = sigmaTrace σ m x + (σ ^ m) x := by
  simp [sigmaTrace, Finset.sum_range_succ]

/-
The trace is additive: `T_m(x + y) = T_m(x) + T_m(y)`. This is immediate from
    σ being a ring homomorphism. In characteristic p for the Frobenius, this is the
    deep "freshman's dream" `(x+y)^p = x^p + y^p`.
-/
lemma sigmaTrace_add (σ : R →+* R) (m : ℕ) (x y : R) :
    sigmaTrace σ m (x + y) = sigmaTrace σ m x + sigmaTrace σ m y := by
  unfold sigmaTrace;
  simp +decide [ Finset.sum_add_distrib, map_add ]

/-
The trace commutes with σ application.
-/
lemma sigmaTrace_map (σ : R →+* R) (m : ℕ) (x : R) :
    σ (sigmaTrace σ m x) = sigmaTrace σ m (σ x) := by
  unfold sigmaTrace;
  induction m <;> simp_all +decide [ Function.iterate_succ_apply', Finset.sum_range_succ' ]

/-! ## The Telescoping Lemma — The Key Structural Identity -/

/-
**The Telescoping Lemma** (Heart of Additive Hilbert 90).

    `T_m(x - σ(x)) = x - σ^m(x)`

    This is the factorization `(1 + σ + ⋯ + σ^{m-1})(1 - σ) = 1 - σ^m`
    in the group ring `ℤ[σ]`. It says the trace annihilates the image of
    the Artin-Schreier operator, and is the core engine behind:
    - Additive Hilbert 90
    - The vanishing of `H¹(Gal, 𝔽⁺)` in Galois cohomology
    - Lang's theorem for the additive group over finite fields
-/
theorem sigmaTrace_sub_sigma (σ : R →+* R) (m : ℕ) (x : R) :
    sigmaTrace σ m (x - σ x) = x - (σ ^ m) x := by
  induction' m with m ih;
  · simp +decide [ sigmaTrace ];
  · convert congr_arg ( fun y => y + ( σ ^ m ) ( x - σ x ) ) ih using 1 <;> ring!;
    · rw [ add_comm, sigmaTrace_succ ];
    · simp +decide [ add_comm, pow_add ]

/-! ## Consequences for Fixed Points -/

/-
If `σ^r(u) = u` (i.e., u is in the fixed field of σ^r), and `x = u - σ(u)`,
    then `T_r(x) = 0`. This is one direction of additive Hilbert 90.

    **Cohomological reading**: Every coboundary is in the kernel of the trace.
    `H¹(⟨σ⟩, R⁺) ↪ ker(T_r) / im(1 - σ)`, and the easy direction says `im ⊆ ker`.
-/
theorem trace_of_artinSchreier_eq_zero (σ : R →+* R) (r : ℕ) (u : R)
    (hfixed : (σ ^ r) u = u) :
    sigmaTrace σ r (u - σ u) = 0 := by
  grind +suggestions

/-
The trace of a fixed point is just multiplication by m.
    If `σ(x) = x`, then `T_m(x) = m • x`.
-/
lemma sigmaTrace_of_fixed (σ : R →+* R) (m : ℕ) (x : R) (hfixed : σ x = x) :
    sigmaTrace σ m x = m • x := by
  unfold sigmaTrace;
  induction' m with m ih <;> simp_all +decide [ pow_succ', mul_add ];
  simp +decide [ *, Finset.sum_range_succ, add_mul ];
  exact Function.iterate_fixed hfixed m

/-! ## Shift Relation -/

/-
The shift relation: `T_m(σ(x)) = T_m(x) - x + σ^m(x)`.
    This captures how the trace transforms under σ-application.
-/
lemma sigmaTrace_sigma (σ : R →+* R) (m : ℕ) (x : R) :
    sigmaTrace σ m (σ x) = sigmaTrace σ m x - x + (σ ^ m) x := by
  unfold sigmaTrace;
  induction' m with m ih <;> simp_all +decide [ Finset.sum_range_succ, pow_succ' ];
  erw [ Function.iterate_succ_apply' ] ; ring;

/-! ## Frobenius Specialization -/

section Frobenius

variable {F : Type*} [CommRing F] {p : ℕ} [ExpChar F p]

/-
In characteristic p, the iterated Frobenius satisfies `Frob^j(x) = x^{p^j}`.
-/
lemma frobenius_iterate_eq_pow (x : F) (j : ℕ) :
    ((frobenius F p) ^ j) x = x ^ (p ^ j) := by
  induction' j with j ih;
  · simp +decide [ pow_zero ];
  · convert map_pow ( frobenius F p ) x ( p ^ j ) using 1;
    · convert congr_arg ( frobenius F p ) ih using 1;
      exact Nat.recOn j ( by simp +decide ) fun n ih => by simp +decide [ *, pow_succ', mul_assoc ] ;
    · simp +decide [ pow_succ', pow_mul, frobenius_def ]

/-
The Frobenius trace `T_m(x) = ∑_{j=0}^{m-1} x^{p^j}` as a sum of powers,
    connecting the abstract endomorphism formulation to the explicit polynomial.
-/
theorem sigmaTrace_frobenius_eq_sum_pow (x : F) (m : ℕ) :
    sigmaTrace (frobenius F p) m x = ∑ j ∈ range m, x ^ (p ^ j) := by
  exact Finset.sum_congr rfl fun i hi => frobenius_iterate_eq_pow x i

end Frobenius