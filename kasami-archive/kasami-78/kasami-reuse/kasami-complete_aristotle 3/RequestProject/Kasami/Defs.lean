/-
  Kasami/Defs.lean

  Basic definitions for the Kasami exponent and associated constructions.

  The Kasami exponent is d = 2^{2k} - 2^k + 1 = 4^k - 2^k + 1.
  The Kasami function is F(x) = x^d over GF(2^n).
  The differential set is Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}.

  Reference: Budaghyan, "Construction and Analysis of Cryptographic Functions", §5.2
             Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions", Theorem 3
-/
import Mathlib

noncomputable section

open Finset Classical

/-! ### The Kasami exponent -/

/-- The Kasami exponent: `d = 2^{2k} - 2^k + 1 = 4^k - 2^k + 1`.
    We define it as a natural number; note `2^{2k} - 2^k + 1 ≥ 1` for all `k ≥ 0`. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The Kasami exponent equals `2^{2k} - 2^k + 1`. -/
lemma kasamiExp_eq (k : ℕ) : kasamiExp k = 2 ^ (2 * k) - 2 ^ k + 1 := by
  unfold kasamiExp
  congr 1
  have : 4 ^ k = (2 ^ 2) ^ k := by norm_num
  rw [this, ← pow_mul]

/-- The Kasami exponent is positive. -/
lemma kasamiExp_pos (k : ℕ) : 0 < kasamiExp k := by
  unfold kasamiExp; omega

/-- For k ≥ 1, 2^k ≤ 4^k. -/
lemma pow2_le_pow4 (k : ℕ) : 2 ^ k ≤ 4 ^ k := by
  calc 2 ^ k ≤ (2 ^ 2) ^ k := by
        apply Nat.pow_le_pow_left; omega
       _ = 4 ^ k := by ring

/-! ### The Kasami function -/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The Kasami function: `f(x) = x^{4^k - 2^k + 1}`. -/
def kasamiFun (k : ℕ) (x : F) : F := x ^ kasamiExp k

/-- The Kasami derivative: `Δ_a f(x) = f(x + a) + f(x)`. -/
def kasamiDelta (k : ℕ) (a x : F) : F :=
  kasamiFun F k (x + a) + kasamiFun F k x

/-! ### The differential set Δ -/

/-- The differential set:
    `Δ = {F(b) + F(b + 1) + 1 : b ∈ GF(2^n)}`.
    This is the image of `b ↦ f(b) + f(b + 1) + 1` over the whole field.

    In characteristic 2, note that `+1` and `-1` are the same, and
    `f(b+1) + f(b) = Δ_1 f(b)`, so elements of Δ are of the form
    `Δ_1 f(b) + 1`. -/
def kasamiDeltaSet (k : ℕ) : Finset F :=
  Finset.univ.image (fun b : F => kasamiFun F k b + kasamiFun F k (b + 1) + 1)

end