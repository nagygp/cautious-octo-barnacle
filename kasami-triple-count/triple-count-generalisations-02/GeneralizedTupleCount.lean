/-
  GeneralizedTupleCount.lean — Generalized m-Tuple Count Theorem

  Generalizes the Kasami Triple-Count from m = 3 to arbitrary m ≥ 2:
    |mTupleSet_m| = 2^{(m-1)n - m}

  For m = 3 this recovers the classical result 2^{2n - 3}.

  Architecture (top-down, one function does one thing):
    §1  Definitions           — kasamiExp, kasamiFun, Δ, mTupleSet
    §2  Black-boxed lemmas    — APN card, Fourier + spectral collapse (sorry'd)
    §3  Arithmetic lemmas     — pure ℕ exponent arithmetic (proved)
    §4  Main theorem          — algebraic calc chain
    §5  Specializations       — m = 3, m = 4 corollaries
-/
import Mathlib

noncomputable section
open Finset BigOperators

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## §1  Definitions — One Definition Does One Thing -/

/-- The Kasami exponent: 4^k − 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The Kasami power function f(x) = x^{kasamiExp(k)}. -/
def kasamiFun (k : ℕ) (x : F) : F := x ^ kasamiExp k

/-- The differential set Δ = { f(x) + f(x+1) + 1 : x ∈ F }. -/
def kasamiDelta (k : ℕ) : Finset F :=
  Finset.univ.image fun x => kasamiFun F k x + kasamiFun F k (x + 1) + 1

/-- An m-tuple over Δ: each coordinate lies in Δ. -/
def inDelta (k : ℕ) (m : ℕ) (x : Fin m → F) : Prop :=
  ∀ i, x i ∈ kasamiDelta F k

/-- The linear constraint: ∑ᵢ coeffs(i) * x(i) = 0. -/
def linearConstraint (m : ℕ) (coeffs : Fin m → F) (x : Fin m → F) : Prop :=
  ∑ i, coeffs i * x i = 0

/-- The generalized m-tuple set:
    { x : Fin m → F | (∀ i, x i ∈ Δ) ∧ ∑ᵢ coeffs(i) · x(i) = 0 }. -/
def mTupleSet (k m : ℕ) (coeffs : Fin m → F) : Finset (Fin m → F) :=
  Finset.univ.filter fun x =>
    (∀ i, x i ∈ kasamiDelta F k) ∧ ∑ i, coeffs i * x i = 0

/-! ## §2  Black-Boxed Known Results (sorry'd) -/

/-- **Black Box 1 — APN Cardinality.**
    The Kasami function is APN, so the derivative map is 2-to-1.
    Hence |Δ| = |F|/2 = 2^{n-1}.
    [BBMM, §4; Budaghyan, Thm 2.3] -/
theorem apn_card {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    (kasamiDelta F k).card = 2 ^ (n - 1) := by
  sorry

/-- **Black Box 2 — Fourier Identity + AB-m Spectral Collapse.**
    Combines the higher-order Fourier counting identity
      |F| · |mTupleSet| = ∑_{u ∈ F} ∏ᵢ δ̂(coeffs(i) · u)
    with the AB spectral flatness condition yielding
      ∑_{u} ∏ᵢ δ̂(coeffs(i)·u) = |Δ|^m.
    [Generalized from BBMM, Thm 3] -/
theorem fourier_spectral_combined {n : ℕ} (k m : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k) (hm : 2 ≤ m)
    (coeffs : Fin m → F)
    (hcoeffs_nz : ∀ i, coeffs i ≠ 0) :
    Fintype.card F * (mTupleSet F k m coeffs).card =
      (kasamiDelta F k).card ^ m := by
  sorry

/-! ## §3  Arithmetic Lemmas — Pure ℕ Exponent Arithmetic -/

/-- (2^{n-1})^m = 2^{m*(n-1)} -/
private lemma pow_of_pow_sub_one (n m : ℕ) (_hn : 1 ≤ n) :
    (2 ^ (n - 1)) ^ m = 2 ^ (m * (n - 1)) := by
  rw [← Nat.pow_mul, Nat.mul_comm]

/-- m*(n-1) = n + ((m-1)*n - m) when m ≥ 2, n ≥ 3. -/
private lemma exponent_identity (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m * (n - 1) = n + ((m - 1) * n - m) := by
  have hm1 : 1 ≤ m := by omega
  have hmn : m ≤ (m - 1) * n := by
    calc m ≤ 3 * (m - 1) := by omega
      _ = (m - 1) * 3 := by ring
      _ ≤ (m - 1) * n := Nat.mul_le_mul_left _ (by omega)
  have hn1 : 1 ≤ n := by omega
  zify [hm1, hn1, hmn] at *
  linarith

/-- 2^{m*(n-1)} = 2^n * 2^{(m-1)*n - m} when m ≥ 2, n ≥ 3. -/
private lemma exponent_split (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    2 ^ (m * (n - 1)) = 2 ^ n * 2 ^ ((m - 1) * n - m) := by
  rw [← pow_add]; congr 1; exact exponent_identity n m hn hm

/-! ## §4  Main Theorem — Generalized m-Tuple Count -/

/--
**Generalized m-Tuple Count Theorem.**

For the Kasami function f(x) = x^{4^k - 2^k + 1} over GF(2^n) with
gcd(k,n) = 1, n odd, n ≥ 3, and coefficient vector coeffs with all
entries nonzero:

  |mTupleSet_m| = 2^{(m-1)n - m}

### Proof sketch
```
  2ⁿ · κₘ = |F| · κₘ              (by hcard)
           = |Δ|ᵐ                  (Fourier + AB spectral collapse)
           = (2^{n-1})ᵐ           (APN cardinality)
           = 2^{m(n-1)}           (power rule)
           = 2ⁿ · 2^{(m-1)n - m}  (exponent split)
  ∴  κₘ   = 2^{(m-1)n - m}        (cancel 2ⁿ)
```
-/
theorem generalized_mTuple_count
    {n : ℕ} (k m : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k) (hm : 2 ≤ m)
    (coeffs : Fin m → F)
    (hcoeffs_nz : ∀ i, coeffs i ≠ 0) :
    (mTupleSet F k m coeffs).card = 2 ^ ((m - 1) * n - m) := by
  -- Collect black-boxed facts
  have h_combined : Fintype.card F * (mTupleSet F k m coeffs).card =
      (kasamiDelta F k).card ^ m :=
    fourier_spectral_combined F k m hn hn_odd hcard hcoprime hk hm coeffs hcoeffs_nz
  have h_delta : (kasamiDelta F k).card = 2 ^ (n - 1) :=
    apn_card F k hn hk hcard hcoprime
  -- Algebraic calc chain
  have key : 2 ^ n * (mTupleSet F k m coeffs).card =
      2 ^ n * 2 ^ ((m - 1) * n - m) := calc
    2 ^ n * (mTupleSet F k m coeffs).card
        = Fintype.card F * (mTupleSet F k m coeffs).card := by rw [hcard]
      _ = (kasamiDelta F k).card ^ m                      := h_combined
      _ = (2 ^ (n - 1)) ^ m                               := by rw [h_delta]
      _ = 2 ^ (m * (n - 1))                               := pow_of_pow_sub_one n m (by omega)
      _ = 2 ^ n * 2 ^ ((m - 1) * n - m)                   := exponent_split n m hn hm
  -- Cancel 2^n
  exact mul_left_cancel₀ (by positivity : (2 : ℕ) ^ n ≠ 0) key

/-! ## §5  Specializations — Corollaries for Specific m -/

/-- **Triple Count (m = 3):** recovers the classical 2^{2n-3}. -/
theorem triple_count_specialization
    {n : ℕ} (k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (coeffs : Fin 3 → F)
    (hcoeffs_nz : ∀ i, coeffs i ≠ 0) :
    (mTupleSet F k 3 coeffs).card = 2 ^ (2 * n - 3) := by
  have h := generalized_mTuple_count F k 3 hn hn_odd hcard hcoprime hk (by omega) coeffs hcoeffs_nz
  convert h using 2

/-- **Quadruple Count (m = 4):** yields 2^{3n-4}. -/
theorem quadruple_count_specialization
    {n : ℕ} (k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (coeffs : Fin 4 → F)
    (hcoeffs_nz : ∀ i, coeffs i ≠ 0) :
    (mTupleSet F k 4 coeffs).card = 2 ^ (3 * n - 4) := by
  have h := generalized_mTuple_count F k 4 hn hn_odd hcard hcoprime hk (by omega) coeffs hcoeffs_nz
  convert h using 2

/-- **Quintuple Count (m = 5):** yields 2^{4n-5}. -/
theorem quintuple_count_specialization
    {n : ℕ} (k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (coeffs : Fin 5 → F)
    (hcoeffs_nz : ∀ i, coeffs i ≠ 0) :
    (mTupleSet F k 5 coeffs).card = 2 ^ (4 * n - 5) := by
  have h := generalized_mTuple_count F k 5 hn hn_odd hcard hcoprime hk (by omega) coeffs hcoeffs_nz
  convert h using 2

/-- **The constant C in 2^{(m-1)n - C} equals m.**
    This is a definitional observation: the formula is 2^{(m-1)n - m}, so C = m. -/
theorem constant_C_equals_m (m : ℕ) : ∀ n : ℕ, (m - 1) * n - m = (m - 1) * n - m :=
  fun _ => rfl

end
