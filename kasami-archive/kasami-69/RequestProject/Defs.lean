/-
Copyright (c) 2025. All rights reserved.

# Fourier Spectra of Binomial APN Functions

Formalization of definitions and preliminary results from:
  "Fourier Spectra of Binomial APN Functions"
  by C. Bracken, E. Byrne, N. Markin, G. McGuire (arXiv:0803.3781)

This file contains:
  - The absolute trace map Tr : F_{2^n} → F_2
  - The canonical additive character χ(t) = (-1)^t
  - The Walsh (Fourier) transform W_f(a,b)
  - The Almost Perfect Nonlinear (APN) property
  - The Almost Bent (AB) property
  - The derivative operator D_u
-/
import Mathlib

noncomputable section

open scoped BigOperators
open Finset Classical

/-! ## Basic Setup -/

/-- The absolute trace from `GaloisField 2 n` to `ZMod 2`.
    This is `Tr(x) = x + x^2 + x^{2^2} + ⋯ + x^{2^{n-1}}`. -/
def absTr (n : ℕ) [NeZero n] : GaloisField 2 n →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) (GaloisField 2 n)

/-- The canonical sign character on `ZMod 2`: maps `0 ↦ 1` and `1 ↦ -1`.
    This is `χ(t) = (-1)^t`, the unique nontrivial additive character of `F_2`
    when composed with the trace. (Definition 2 of the paper.) -/
def chi (t : ZMod 2) : ℤ := (-1) ^ ZMod.val t

@[simp] lemma chi_zero : chi 0 = 1 := by native_decide
@[simp] lemma chi_one : chi 1 = -1 := by native_decide

/-- `chi` is multiplicative in the sense that `chi(a + b) = chi(a) * chi(b)`,
    since `(-1)^(a+b) = (-1)^a · (-1)^b` in `ZMod 2`. -/
lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> decide

/-- `chi(t)` takes values in `{-1, 1}`. -/
lemma chi_sq (t : ZMod 2) : chi t ^ 2 = 1 := by
  fin_cases t <;> decide

/-- `chi(t) ∈ {-1, 1}`. -/
lemma chi_eq_one_or_neg_one (t : ZMod 2) : chi t = 1 ∨ chi t = -1 := by
  fin_cases t <;> decide

/-! ## Walsh Transform (Definition 2) -/

variable {n : ℕ} [NeZero n]

attribute [local instance] Fintype.ofFinite

/-- The Walsh (Fourier) transform of a function `f : GaloisField 2 n → GaloisField 2 n`.

    Following Definition 2 of the paper:
    `W_f(a, b) = ∑_{x ∈ F_{2^n}} (-1)^{Tr(ax + b·f(x))}`

    where `Tr` is the absolute trace from `F_{2^n}` to `F_2`. -/
def walshTransform (f : GaloisField 2 n → GaloisField 2 n)
    (a b : GaloisField 2 n) : ℤ :=
  ∑ x : GaloisField 2 n, chi (absTr n (a * x + b * f x))

/-- Notation-friendly version. -/
notation "𝒲" => walshTransform

/-! ## APN and AB Properties -/

/-- The derivative of `f` at direction `u`:
    `D_u f(x) = f(x + u) + f(x)`.

    In characteristic 2, addition equals subtraction, so this is the standard
    difference operator. -/
def derivative (f : GaloisField 2 n → GaloisField 2 n)
    (u : GaloisField 2 n) : GaloisField 2 n → GaloisField 2 n :=
  fun x => f (x + u) + f x

notation "D_" => derivative

/-- The *linearized derivative* (used in Section 2 of the paper):
    `Δ_u f(x) = f(x + u) + f(x) + f(u)`.

    When `f` is a power function or quadratic, `Δ_u f` is `F_2`-linear in `x`. -/
def linDerivative (f : GaloisField 2 n → GaloisField 2 n)
    (u : GaloisField 2 n) : GaloisField 2 n → GaloisField 2 n :=
  fun x => f (x + u) + f x + f u

notation "Δ_" => linDerivative

/-- A function `f : F_{2^n} → F_{2^n}` is **Almost Perfect Nonlinear (APN)** if
    for every nonzero `u` and every `v`, the equation `D_u f(x) = v` has at most
    2 solutions.

    Equivalently (in char 2), the linearized derivative `Δ_u f` has kernel of
    dimension at most 1 for all nonzero `u`. -/
def IsAPN (f : GaloisField 2 n → GaloisField 2 n) : Prop :=
  ∀ u : GaloisField 2 n, u ≠ 0 →
    ∀ v : GaloisField 2 n,
      Nat.card {x : GaloisField 2 n // derivative f u x = v} ≤ 2

/-- A function `f : F_{2^n} → F_{2^n}` is **Almost Bent (AB)** if its Walsh
    spectrum takes only the values `0` and `±2^{(n+1)/2}`.

    This implies `n` must be odd (for `(n+1)/2` to be an integer giving the
    correct magnitude). -/
def IsAB (f : GaloisField 2 n → GaloisField 2 n) : Prop :=
  ∀ a b : GaloisField 2 n,
    walshTransform f a b = 0 ∨
    walshTransform f a b = (2 ^ ((n + 1) / 2) : ℤ) ∨
    walshTransform f a b = -(2 ^ ((n + 1) / 2) : ℤ)

/-- AB implies APN (well-known; see e.g. Chabaud–Vaudenay). -/
theorem IsAB.isAPN (f : GaloisField 2 n → GaloisField 2 n) (hf : IsAB f) :
    IsAPN f := by
  sorry

/-! ## Key identity: `chi` distributes over the trace -/

/-- The trace is `F_2`-linear, so `(-1)^{Tr(a + b)} = (-1)^{Tr(a)} · (-1)^{Tr(b)}`. -/
lemma chi_absTr_add (a b : GaloisField 2 n) :
    chi (absTr n (a + b)) = chi (absTr n a) * chi (absTr n b) := by
  rw [map_add]
  exact chi_add _ _

/-! ## Orthogonality of characters -/

/-- Character sum orthogonality: `∑_x (-1)^{Tr(ax)} = 0` when `a ≠ 0`,
    and equals `|F_{2^n}|` when `a = 0`. This is the fundamental Fourier identity
    over `F_{2^n}`. -/
lemma character_sum_eq (a : GaloisField 2 n) :
    ∑ x : GaloisField 2 n, chi (absTr n (a * x)) =
      if a = 0 then (Nat.card (GaloisField 2 n) : ℤ) else 0 := by
  sorry

end
