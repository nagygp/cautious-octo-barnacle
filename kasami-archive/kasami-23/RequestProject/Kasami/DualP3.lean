/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dual of P₃ for the Kasami Exponent

We formalize the dual (spectral / Fourier-analytic) formulation of P₃ and prove its
equivalence to the original combinatorial statement.

## Setup
- 𝔽 is a finite field of characteristic 2 with |𝔽| = 2^n.
- F(b) = b^d where d = 4^k − 2^k + 1 is the Kasami exponent.
- Δ = { F(b) + F(b+1) + 1 | b ∈ 𝔽 }.

## P₃ (combinatorial)
For gcd(k,n) = 1 and all v₁, v₂ ∈ 𝔽* with v₁ ≠ v₂:
  |{ (x,y,z) ∈ Δ³ : v₁·x + v₂·y + (v₁+v₂)·z = 0 }| = 2^(2n−3).

## Dual P₃ (spectral)
For gcd(k,n) = 1 and all v₁, v₂ ∈ 𝔽* with v₁ ≠ v₂:
  ∑_{ψ ∈ 𝔽̂} Ŝ_ψ(v₁) · Ŝ_ψ(v₂) · Ŝ_ψ(v₁+v₂) = 2^(3n−3)
where Ŝ_ψ(c) = ∑_{x ∈ Δ} ψ(c·x) and the sum is over all additive characters ψ : 𝔽 → ℂ.

## Equivalence
The two formulations are equivalent via the character orthogonality relation:
  δ(s=0) = (1/|𝔽|) ∑_ψ ψ(s),
which gives: count = (1/|𝔽|) · spectral_sum.

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Canteaut, Charpin, Dobbertin (2000)][canteaut2000]
-/
import Mathlib

open scoped BigOperators Pointwise
open Finset

attribute [local instance] Fintype.ofFinite

noncomputable section

/-! ## 1. Definitions over a finite field of characteristic 2 -/

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

/-- The Kasami exponent: d = 4^k − 2^k + 1. -/
def DualP3.kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- F(b) = b^d, the Kasami power function. -/
def DualP3.kasF (k : ℕ) (b : 𝔽) : 𝔽 := b ^ DualP3.kasamiExp k

/-- Δ = { F(b) + F(b+1) + 1 | b ∈ 𝔽 }, the second-order derivative image. -/
def DualP3.kasDelta (k : ℕ) : Finset 𝔽 :=
  Finset.univ.image (fun b : 𝔽 => DualP3.kasF k b + DualP3.kasF k (b + 1) + 1)

/-! ## 2. Triple count and spectral triple product -/

/-- The number of triples (x,y,z) ∈ S³ satisfying v₁·x + v₂·y + (v₁+v₂)·z = 0. -/
def DualP3.tripleCount (S : Finset 𝔽) (v₁ v₂ : 𝔽) : ℕ :=
  ((S ×ˢ (S ×ˢ S)).filter fun xyz : 𝔽 × 𝔽 × 𝔽 =>
    v₁ * xyz.1 + v₂ * xyz.2.1 + (v₁ + v₂) * xyz.2.2 = 0).card

/-- The spectral sum Ŝ_ψ(c) = ∑_{x ∈ S} ψ(c·x). -/
def DualP3.charSum (ψ : AddChar 𝔽 ℂ) (S : Finset 𝔽) (c : 𝔽) : ℂ :=
  ∑ x ∈ S, ψ (c * x)

/-- The spectral triple product: ∑_ψ Ŝ_ψ(v₁) · Ŝ_ψ(v₂) · Ŝ_ψ(v₁+v₂). -/
def DualP3.spectralTriple (S : Finset 𝔽) (v₁ v₂ : 𝔽) : ℂ :=
  ∑ ψ : AddChar 𝔽 ℂ,
    DualP3.charSum ψ S v₁ * DualP3.charSum ψ S v₂ * DualP3.charSum ψ S (v₁ + v₂)

/-! ## 3. P₃ and Dual P₃ statements -/

/-- **P₃** (combinatorial formulation). -/
def DualP3.P3 (n k : ℕ) : Prop :=
  Nat.Coprime k n ∧
  ∀ v₁ v₂ : 𝔽, v₁ ≠ 0 → v₂ ≠ 0 → v₁ ≠ v₂ →
    DualP3.tripleCount (DualP3.kasDelta (𝔽 := 𝔽) k) v₁ v₂ = 2 ^ (2 * n - 3)

/-- **Dual P₃** (spectral formulation). -/
def DualP3.DualP3Statement (n k : ℕ) : Prop :=
  Nat.Coprime k n ∧
  ∀ v₁ v₂ : 𝔽, v₁ ≠ 0 → v₂ ≠ 0 → v₁ ≠ v₂ →
    DualP3.spectralTriple (DualP3.kasDelta (𝔽 := 𝔽) k) v₁ v₂ =
      ↑(2 ^ (2 * n - 3)) * ↑(Fintype.card 𝔽)

/-! ## 4. The connecting identity: count · |𝔽| = spectral sum -/

/-- Key identity: the spectral triple product equals the triple count times |𝔽|.
    This follows from character orthogonality: ∑_ψ ψ(s) = |𝔽| if s=0, else 0. -/
theorem DualP3.spectral_eq_count_mul_card (S : Finset 𝔽) (v₁ v₂ : 𝔽) :
    DualP3.spectralTriple S v₁ v₂ =
    ↑(DualP3.tripleCount S v₁ v₂) * ↑(Fintype.card 𝔽) := by
  have h_expand : ∑ ψ : AddChar 𝔽 ℂ, (∑ x ∈ S, ψ (v₁ * x)) * (∑ y ∈ S, ψ (v₂ * y)) *
      (∑ z ∈ S, ψ ((v₁ + v₂) * z)) =
    ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ∑ ψ : AddChar 𝔽 ℂ,
      ψ (v₁ * x + v₂ * y + (v₁ + v₂) * z) := by
    simp +decide only [sum_mul _ _ _, mul_sum]
    simp +decide only [← sum_product']
    refine' Finset.sum_bij (fun x _ => (x.2.1, x.2.2.1, x.2.2.2, x.1)) _ _ _ _ <;>
      simp +decide
    · aesop
    · tauto
    · simp +decide [AddChar.map_add_eq_mul]
  have h_ortho : ∀ x y z : 𝔽,
    ∑ ψ : AddChar 𝔽 ℂ, ψ (v₁ * x + v₂ * y + (v₁ + v₂) * z) =
    if v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
    exact fun x y z => AddChar.sum_apply_eq_ite (v₁ * x + v₂ * y + (v₁ + v₂) * z)
  simp_all +decide [Finset.sum_ite]
  convert h_expand using 1
  simp +decide [← Finset.sum_mul _ _ _, DualP3.tripleCount]
  simp +decide only [card_filter, sum_product]
  norm_cast

/-! ## 5. Equivalence P₃ ↔ Dual P₃ -/

/-- P₃ and its dual are equivalent: they differ only by a factor of |𝔽| = 2^n. -/
theorem DualP3.P3_iff_DualP3 (n k : ℕ) (hcard : Fintype.card 𝔽 = 2 ^ n) (_hn : 3 ≤ n) :
    DualP3.P3 (𝔽 := 𝔽) n k ↔ DualP3.DualP3Statement (𝔽 := 𝔽) n k := by
  constructor <;> intro h <;> refine ⟨h.1, fun v₁ v₂ hv₁ hv₂ hv => ?_⟩ <;>
    have := h.2 v₁ v₂ hv₁ hv₂ hv <;>
    simp_all +decide [DualP3.spectral_eq_count_mul_card]
  exact_mod_cast this

end
