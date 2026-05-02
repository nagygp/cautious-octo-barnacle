/-
Copyright (c) 2025. All rights reserved.
Formalization of Almost Perfect Nonlinear (APN) and Almost Bent (AB) functions
over finite fields of characteristic 2, following Budaghyan et al. (arXiv:0803.3781).
-/
import Mathlib

/-! # APN and AB Functions over Finite Fields of Characteristic 2

This file defines the core concepts from the theory of cryptographic Boolean functions:
- **APN (Almost Perfect Nonlinear)** functions
- **Walsh Transform**
- **AB (Almost Bent)** functions
- **Absolute Trace** from 𝔽_{2^n} to 𝔽_2

These definitions are used in the formalization of Theorem 23 from
"Construction and Analysis of Cryptographic Functions" by Budaghyan et al.
-/

open Finset BigOperators

noncomputable section

/-! ## Differential Properties -/

/-- The derivative of a function `f : F → F` in direction `a`.
  In characteristic 2 this is `f(x + a) + f(x)` (since subtraction equals addition). -/
def derivative {F : Type*} [AddCommGroup F] (f : F → F) (a : F) : F → F :=
  fun x => f (x + a) - f x

/-- A function `f : F → F` is **Almost Perfect Nonlinear (APN)** if for every nonzero `a`,
  the derivative `x ↦ f(x + a) - f(x)` is at most 2-to-1, i.e., for every `b`,
  the equation `f(x + a) - f(x) = b` has at most 2 solutions.

  In characteristic 2, subtraction equals addition, so this is equivalent to:
  `#{x | f(x+a) + f(x) = b} ≤ 2` for all `a ≠ 0` and all `b`. -/
def IsAPN {F : Type*} [Field F] [Fintype F] [DecidableEq F] (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F, (Finset.univ.filter (fun x => f (x + a) - f x = b)).card ≤ 2

/-! ## The Absolute Trace Function -/

/-- The absolute trace from `GaloisField 2 n` to `ZMod 2`, defined as the
  field-theoretic trace `Tr_{𝔽_{2^n}/𝔽_2}`. This is the Mathlib `Algebra.trace`. -/
abbrev absoluteTrace (n : ℕ) [Fact (Nat.Prime 2)] :
    GaloisField 2 n →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) (GaloisField 2 n)

/-! ## Walsh Transform -/

/-- Auxiliary: convert an element of `ZMod 2` to a sign `{-1, 1}` in `ℤ`.
  Maps `0 ↦ 1` and `1 ↦ -1`, i.e., computes `(-1)^x`. -/
def signOfZMod2 (x : ZMod 2) : ℤ :=
  if x = 0 then 1 else -1

/-- The **Walsh Transform** of `f : F → F` at `(a, b)`, defined as
  `W_f(a, b) = Σ_{x ∈ F} (-1)^{Tr(b·f(x) + a·x)}`.

  Here `F = GaloisField 2 n` and `Tr` is the absolute trace to `ZMod 2`. -/
def walshTransform (n : ℕ) [hprime : Fact (Nat.Prime 2)] (hn : n ≠ 0)
    (f : GaloisField 2 n → GaloisField 2 n)
    (a b : GaloisField 2 n) : ℤ :=
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  ∑ x : GaloisField 2 n,
    signOfZMod2 (absoluteTrace n (b * f x + a * x))

/-- A function `f` on `GaloisField 2 n` is **Almost Bent (AB)** if its Walsh spectrum
  takes values only in `{0, 2^{(n+1)/2}, -2^{(n+1)/2}}`.

  AB functions exist only when `n` is odd. -/
def IsAB (n : ℕ) [Fact (Nat.Prime 2)] (hn : n ≠ 0)
    (f : GaloisField 2 n → GaloisField 2 n) : Prop :=
  ∀ a b : GaloisField 2 n,
    walshTransform n hn f a b = 0 ∨
    walshTransform n hn f a b = (2 ^ ((n + 1) / 2) : ℤ) ∨
    walshTransform n hn f a b = -(2 ^ ((n + 1) / 2) : ℤ)

/-! ## Basic Properties -/

/-
AB implies APN: any Almost Bent function is Almost Perfect Nonlinear.
  This is a classical result in Boolean function theory.
-/
theorem IsAB.isAPN (n : ℕ) [Fact (Nat.Prime 2)] (hn : n ≠ 0)
    (f : GaloisField 2 n → GaloisField 2 n) (hf : IsAB n hn f) :
    @IsAPN (GaloisField 2 n) (instFieldGaloisField 2 n)
      (Fintype.ofFinite _) (Classical.decEq _) f := by
  unfold IsAPN IsAB at *;
  contrapose! hf;
  obtain ⟨ a, ha, b, hb ⟩ := hf; use 0, 0; simp_all +decide [ walshTransform ] ;
  erw [ Fintype.card_eq_nat_card ] ; erw [ GaloisField.card ] ; norm_num [ signOfZMod2 ];
  · rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.div_le_self ];
    · contrapose! hb;
      have h_card : Nat.card (GaloisField 2 1) = 2 := by
        simp +decide [ GaloisField.card ];
      have h_card : Fintype (GaloisField 2 1) := by
        exact Fintype.ofFinite _;
      exact lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by norm_num [ show Fintype.card ( GaloisField 2 1 ) = 2 by simpa [ Nat.card_eq_fintype_card ] using ‹Nat.card ( GaloisField 2 1 ) = 2› ] );
    · exact ⟨ by omega, by positivity ⟩;
  · assumption

/-
`signOfZMod2` only takes values in `{-1, 1}`.
-/
theorem signOfZMod2_sq (x : ZMod 2) : signOfZMod2 x ^ 2 = 1 := by
  fin_cases x <;> rfl

/-
In characteristic 2, subtraction equals addition.
-/
theorem char2_sub_eq_add {F : Type*} [Ring F] [CharP F 2] (a b : F) : a - b = a + b := by
  rw [ sub_eq_add_neg, neg_eq_of_add_eq_zero_right ( CharTwo.add_self_eq_zero b ) ]

end