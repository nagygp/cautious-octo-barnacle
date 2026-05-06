/-
  KasamiDefs.lean

  Core definitions for the Kasami triple-count formalization.

  Defines:
  - The Kasami exponent 4^k − 2^k + 1
  - The Kasami function F(b) = b^(4^k − 2^k + 1)
  - The differential set Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}
  - The triple set {(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}

  Reference: Budaghyan, "Construction and Analysis of Cryptographic Functions"
-/
import Mathlib

noncomputable section

open Finset BigOperators

variable {n k : ℕ}
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Kasami Function -/

/-- The Kasami exponent: `4^k − 2^k + 1 = 2^(2k) − 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The Kasami function: `F(b) = b ^ (4^k − 2^k + 1)`. -/
def kasamiFun (k : ℕ) (b : F) : F := b ^ kasamiExp k

/-! ## The Differential Set Δ -/

/-- The differential set:
    `Δ = {F(b) + F(b + 1) + 1 : b ∈ GF(2^n)}`. -/
def kasamiDelta (k : ℕ) : Finset F :=
  Finset.univ.image fun b => kasamiFun F k b + kasamiFun F k (b + 1) + 1

/-! ## The Triple Count -/

/-- The set of triples `(x, y, z) ∈ Δ³` satisfying `v₁·x + v₂·y + (v₁+v₂)·z = 0`. -/
def tripleSet (k : ℕ) (v₁ v₂ : F) : Finset (F × F × F) :=
  (kasamiDelta F k ×ˢ kasamiDelta F k ×ˢ kasamiDelta F k).filter fun ⟨x, y, z⟩ =>
    v₁ * x + v₂ * y + (v₁ + v₂) * z = 0

end
