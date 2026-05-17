/-
# Quadratic Form Bridge for the Kasami Function

This module establishes the connection between the Kasami power function
and the Gold quadratic form, which is the correct Layer 2 bridge.

## Architecture

The Kasami exponent d = 4^k - 2^k + 1 satisfies d·(2^k+1) = 2^{3k}+1.
The Gold exponent g = 2^k + 1 gives a QUADRATIC form Q(x) = Tr(a·x^g).
The Walsh transform of x^d reduces to an exponential sum involving
the Gold function, enabling quadratic form / Gauss sum analysis.

## Key distinction

* `Tr(a·x^d)` is NOT a quadratic form over GF(2) for k ≥ 2
  (the Kasami exponent has > 2 nonzero binary digits).
* `Tr(a·x^{2^k+1})` IS a quadratic form over GF(2)
  (the Gold exponent has exactly 2 nonzero binary digits).

The proof route reduces the Kasami to the Gold case.

## References

* Canteaut, Charpin, Dobbertin (2000), §3
* Carlet, *Boolean Functions for Cryptography and Coding Theory*, §6.4
* Dobbertin (1999), *Almost Perfect Nonlinear Power Functions*
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.WalshHadamard

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ### §1 The Gold Quadratic Form -/

/-- The Gold exponent g = 2^k + 1. -/
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1

/-- The Gold quadratic form: Q_a(x) = Tr(a · x^{2^k+1}). -/
def goldQF (n k : ℕ) (a : F2n n) : F2n n → ZMod 2 :=
  fun x => tr2 n (a * x ^ goldExp k)

/-- The cross term for the Gold function: (x+y)^{2^k+1} + x^{2^k+1} + y^{2^k+1}. -/
def goldCross (k : ℕ) (x y : F2n n) : F2n n :=
  (x + y) ^ goldExp k + x ^ goldExp k + y ^ goldExp k

/-
The Gold cross term equals x^{2^k}·y + x·y^{2^k}.
-/
theorem goldCross_eq (k : ℕ) (x y : F2n n) :
    goldCross k x y = x ^ (2 ^ k) * y + x * y ^ (2 ^ k) := by
  unfold goldCross goldExp
  have hfresh : (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
    add_pow_char_pow x y 2 k
  have : (x + y) ^ (2 ^ k + 1) = (x ^ (2 ^ k) + y ^ (2 ^ k)) * (x + y) := by
    rw [pow_succ, hfresh]
  rw [this]
  grind

/-- The Gold cross term is symmetric. -/
theorem goldCross_symm (k : ℕ) (x y : F2n n) :
    goldCross k x y = goldCross k y x := by
  simp [goldCross_eq]; ring

/-- The Gold bilinear form B_a(x,y) = Tr(a·goldCross(x,y)). -/
def goldBF (n k : ℕ) (a : F2n n) : F2n n → F2n n → ZMod 2 :=
  fun x y => tr2 n (a * goldCross k x y)

/-- Gold bilinear form is GF(2)-bilinear in the first argument. -/
theorem goldBF_add_left (n k : ℕ) (a x₁ x₂ y : F2n n) :
    goldBF n k a (x₁ + x₂) y = goldBF n k a x₁ y + goldBF n k a x₂ y := by
  simp only [goldBF, goldCross_eq]
  rw [← map_add (tr2 n)]
  congr 1
  rw [add_pow_char_pow x₁ x₂ 2 k]
  ring

/-- Gold bilinear form is symmetric. -/
theorem goldBF_symm (n k : ℕ) (a x y : F2n n) :
    goldBF n k a x y = goldBF n k a y x := by
  unfold goldBF; rw [goldCross_symm]

/-- Gold bilinear form is GF(2)-bilinear in the second argument. -/
theorem goldBF_add_right (n k : ℕ) (a x y₁ y₂ : F2n n) :
    goldBF n k a x (y₁ + y₂) = goldBF n k a x y₁ + goldBF n k a x y₂ := by
  rw [goldBF_symm, goldBF_add_left, goldBF_symm _ _ _ y₁, goldBF_symm _ _ _ y₂]

/-! ### §2 The Gold-Kasami Connection -/

/-- Key identity: kasamiExp k * goldExp k = 2^(3*k) + 1. -/
theorem kasami_gold_identity (k : ℕ) :
    kasamiExp k * goldExp k = 2 ^ (3 * k) + 1 := by
  unfold kasamiExp goldExp
  have h4 : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]; ring_nf
  have h3k : (2 : ℕ) ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; ring_nf
  have h2k : 2 ^ k ≤ 4 ^ k := by nlinarith [Nat.one_le_pow k 2 (by omega)]
  rw [h4] at h2k ⊢; rw [h3k]; zify [h2k]; ring

/-- The Kasami-Gold norm relation: (x^d)^{2^k+1} = x^{2^{3k}+1}. -/
theorem kasami_gold_norm (k : ℕ) (x : F2n n) :
    (x ^ kasamiExp k) ^ goldExp k = x ^ (2 ^ (3 * k) + 1) := by
  rw [← pow_mul, kasami_gold_identity]

/-! ### §3 Radical of the Gold Bilinear Form -/

/-- The radical of the Gold bilinear form. -/
def goldRadical (n k : ℕ) (a : F2n n) : Set (F2n n) :=
  { x | ∀ y, goldBF n k a x y = 0 }

/-- 0 is in the Gold radical. -/
theorem goldRadical_zero_mem (n k : ℕ) (a : F2n n) :
    (0 : F2n n) ∈ goldRadical n k a := by
  intro y; simp [goldBF, goldCross_eq]

/-- The Gold radical is closed under addition. -/
theorem goldRadical_add_mem (n k : ℕ) (a : F2n n)
    {x₁ x₂ : F2n n} (h₁ : x₁ ∈ goldRadical n k a) (h₂ : x₂ ∈ goldRadical n k a) :
    x₁ + x₂ ∈ goldRadical n k a := by
  intro y; rw [goldBF_add_left, h₁ y, h₂ y, add_zero]

/-- x is in the Gold radical iff a·(x^{2^k}·y + x·y^{2^k}) has trace 0 for all y.
    By trace surjectivity, this is equivalent to a·x^{2^k}·y + a·x·y^{2^k} = 0 for all y
    (the "linearized polynomial" condition). -/
theorem goldRadical_iff_trace (n k : ℕ) (a x : F2n n) :
    x ∈ goldRadical n k a ↔ ∀ y, tr2 n (a * (x ^ (2 ^ k) * y + x * y ^ (2 ^ k))) = 0 := by
  simp [goldRadical, goldBF, goldCross_eq]

/-! ### §4 Walsh Transform Connection -/

/-- The WHT of f(x) = x^d at parameter a equals ∑_x χ(ax + x^d). -/
theorem wht_kasamiF_eq (n k : ℕ) (a : F2n n) :
    wht (kasamiF n k) a =
      ∑ x : F2n n, chi n (a * x + x ^ kasamiExp k) := by
  rfl

end
end Kasami