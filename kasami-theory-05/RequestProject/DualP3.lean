/-
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
-/
import Mathlib

open scoped BigOperators Pointwise
open Finset

attribute [local instance] Fintype.ofFinite

noncomputable section

/-! ## 1. Definitions over a finite field of characteristic 2 -/

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

/-- The Kasami exponent: d = 4^k − 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- F(b) = b^d, the Kasami power function. -/
def kasF (k : ℕ) (b : 𝔽) : 𝔽 := b ^ kasamiExp k

/-- Δ = { F(b) + F(b+1) + 1 | b ∈ 𝔽 }, the second-order derivative image. -/
def kasDelta (k : ℕ) : Finset 𝔽 :=
  Finset.univ.image (fun b : 𝔽 => kasF k b + kasF k (b + 1) + 1)

/-! ## 2. Triple count and spectral triple product -/

/-- The number of triples (x,y,z) ∈ S³ satisfying v₁·x + v₂·y + (v₁+v₂)·z = 0. -/
def tripleCount (S : Finset 𝔽) (v₁ v₂ : 𝔽) : ℕ :=
  ((S ×ˢ (S ×ˢ S)).filter fun xyz : 𝔽 × 𝔽 × 𝔽 =>
    v₁ * xyz.1 + v₂ * xyz.2.1 + (v₁ + v₂) * xyz.2.2 = 0).card

/-- The spectral sum Ŝ_ψ(c) = ∑_{x ∈ S} ψ(c·x). -/
def charSum (ψ : AddChar 𝔽 ℂ) (S : Finset 𝔽) (c : 𝔽) : ℂ :=
  ∑ x ∈ S, ψ (c * x)

/-- The spectral triple product: ∑_ψ Ŝ_ψ(v₁) · Ŝ_ψ(v₂) · Ŝ_ψ(v₁+v₂). -/
def spectralTriple (S : Finset 𝔽) (v₁ v₂ : 𝔽) : ℂ :=
  ∑ ψ : AddChar 𝔽 ℂ,
    charSum ψ S v₁ * charSum ψ S v₂ * charSum ψ S (v₁ + v₂)

/-! ## 3. P₃ and Dual P₃ statements -/

/-- **P₃** (combinatorial formulation):
    gcd(k,n)=1 and the triple count over Δ is 2^(2n−3) for all valid coefficient pairs. -/
def P3 (n k : ℕ) : Prop :=
  Nat.Coprime k n ∧
  ∀ v₁ v₂ : 𝔽, v₁ ≠ 0 → v₂ ≠ 0 → v₁ ≠ v₂ →
    tripleCount (kasDelta (𝔽 := 𝔽) k) v₁ v₂ = 2 ^ (2 * n - 3)

/-- **Dual P₃** (spectral formulation):
    gcd(k,n)=1 and the spectral triple product over Δ equals 2^(2n−3) · |𝔽|
    for all valid coefficient pairs. -/
def DualP3 (n k : ℕ) : Prop :=
  Nat.Coprime k n ∧
  ∀ v₁ v₂ : 𝔽, v₁ ≠ 0 → v₂ ≠ 0 → v₁ ≠ v₂ →
    spectralTriple (kasDelta (𝔽 := 𝔽) k) v₁ v₂ =
      ↑(2 ^ (2 * n - 3)) * ↑(Fintype.card 𝔽)

/-! ## 4. The connecting identity: count · |𝔽| = spectral sum -/

/-
Key identity: the spectral triple product equals the triple count times |𝔽|.
    This follows from character orthogonality: ∑_ψ ψ(s) = |𝔽| if s=0, else 0.
-/
omit [CharP 𝔽 2] in
theorem spectral_eq_count_mul_card (S : Finset 𝔽) (v₁ v₂ : 𝔽) :
    spectralTriple S v₁ v₂ = ↑(tripleCount S v₁ v₂) * ↑(Fintype.card 𝔽) := by
  -- Expand the products of sums using the distributive property.
  have h_expand : ∑ ψ : AddChar 𝔽 ℂ, (∑ x ∈ S, ψ (v₁ * x)) * (∑ y ∈ S, ψ (v₂ * y)) * (∑ z ∈ S, ψ ((v₁ + v₂) * z)) = ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ∑ ψ : AddChar 𝔽 ℂ, ψ (v₁ * x + v₂ * y + (v₁ + v₂) * z) := by
    simp +decide only [sum_mul _ _ _, mul_sum];
    simp +decide only [← sum_product'];
    refine' Finset.sum_bij ( fun x _ => ( x.2.1, x.2.2.1, x.2.2.2, x.1 ) ) _ _ _ _ <;> simp +decide;
    · aesop;
    · tauto;
    · simp +decide [ AddChar.map_add_eq_mul ];
  -- Apply character orthogonality to the inner sum.
  have h_ortho : ∀ x y z : 𝔽, ∑ ψ : AddChar 𝔽 ℂ, ψ (v₁ * x + v₂ * y + (v₁ + v₂) * z) = if v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
    exact fun x y z => AddChar.sum_apply_eq_ite (v₁ * x + v₂ * y + (v₁ + v₂) * z);
  simp_all +decide [ Finset.sum_ite ];
  convert h_expand using 1;
  simp +decide [ ← Finset.sum_mul _ _ _, tripleCount ];
  simp +decide only [card_filter, sum_product];
  norm_cast

/-! ## 5. Equivalence P₃ ↔ Dual P₃ -/

/-
P₃ and its dual are equivalent: they differ only by a factor of |𝔽| = 2^n.
-/
omit [CharP 𝔽 2] in
theorem P3_iff_DualP3 (n k : ℕ) (hcard : Fintype.card 𝔽 = 2 ^ n) (_hn : 3 ≤ n) :
    P3 (𝔽 := 𝔽) n k ↔ DualP3 (𝔽 := 𝔽) n k := by
  constructor <;> intro h <;> refine ⟨h.1, fun v₁ v₂ hv₁ hv₂ hv => ?_⟩ <;> have := h.2 v₁ v₂ hv₁ hv₂ hv <;> simp_all +decide [ spectral_eq_count_mul_card ];
  exact_mod_cast this

/-! ## 6. P₃ holds for the Kasami exponent -/

/-- **Main theorem**: P₃ holds for the Kasami exponent when gcd(k,n) = 1.
    This is a deep result from the theory of APN (Almost Perfect Nonlinear) functions. -/
theorem P3_holds (n k : ℕ) (hcard : Fintype.card 𝔽 = 2 ^ n) (hn : 3 ≤ n)
    (hcoprime : Nat.Coprime k n) :
    P3 (𝔽 := 𝔽) n k := by
  sorry

/-- **Corollary**: The dual of P₃ also holds. -/
theorem DualP3_holds (n k : ℕ) (hcard : Fintype.card 𝔽 = 2 ^ n) (hn : 3 ≤ n)
    (hcoprime : Nat.Coprime k n) :
    DualP3 (𝔽 := 𝔽) n k :=
  (P3_iff_DualP3 n k hcard hn).mp (P3_holds n k hcard hn hcoprime)

end