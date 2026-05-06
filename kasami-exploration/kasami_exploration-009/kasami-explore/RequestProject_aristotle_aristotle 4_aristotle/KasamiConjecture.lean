/-
  KasamiConjecture.lean

  Formal statement of the Kasami triple-count conjecture over GF(2^n).

  This file defines:
  - The Kasami exponent 4^k − 2^k + 1
  - The Kasami function F(b) = b^(4^k − 2^k + 1)
  - The differential set Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}
  - The triple-count conjecture: for distinct nonzero v₁, v₂,
    |{(x, y, z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}| = 2^(2n−3)

  NOTE: The existing files (Normalization.lean, Factorization.lean, Counting.lean,
  Kasami_Final_Theorem.lean) prove related but distinct results — namely that
  AB functions are APN, and that Walsh supports have size 2^(n−1). They do NOT
  prove this conjecture. See ANALYSIS.md for a detailed gap analysis.
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

/-! ## The Conjecture -/

/-- **Kasami Triple-Count Conjecture.**

    Let `k` be coprime with `n`, and `|F| = 2^n`. For every pair of distinct
    nonzero elements `v₁, v₂ ∈ F`:

      |{(x, y, z) ∈ Δ³ : v₁·x + v₂·y + (v₁ + v₂)·z = 0}| = 2^(2n − 3)

    where `Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}` and `F(b) = b^(4^k − 2^k + 1)`.

    STATUS: **OPEN** — not proved by the current formalization. See ANALYSIS.md.

    The proof pathway is: this follows from `KasamiHelpers.kasami_triple_count_from_helpers`,
    which reduces to `tripleSet_card_eq_pair_filter` + `pair_filter_count`. -/
theorem kasami_triple_count_conjecture
    (hn : 3 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (tripleSet F k v₁ v₂).card = 2 ^ (2 * n - 3) := by
  sorry

end
