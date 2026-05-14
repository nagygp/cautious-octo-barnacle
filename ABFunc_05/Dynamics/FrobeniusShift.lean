/-
  # Frobenius as Shift: Connecting Dynamics to ABTopos via Mathlib

  This file establishes the **genuine categorical and dynamical connections**
  between the ABTopos spectral/duality framework and Mathlib's infrastructure:

  1. **Frobenius iteration** as power-of-p (proven via Mathlib's `frobenius`)
  2. **Gold function factorisation** through Frobenius (shift × identity)
  3. **Frobenius periodicity** — the finite field analogue of shift return
  4. **Cyclic shift** on bitstrings and its period
  5. **Gold derivative** factoring through Frobenius
  6. **Coprimality ↔ generation** of ℤ/nℤ via Mathlib's `ZMod.unitOfCoprime`

  All results connect to Mathlib's `Function.IsPeriodicPt`, `frobenius`,
  `FiniteField.frobenius_pow`, `ZMod`, and `CommRingCat`.
-/

import Mathlib

noncomputable section

open Finset Function

/-! ## §1  Frobenius Iteration = Power of 2^k -/

section FrobeniusShift

variable (F : Type*) [CommSemiring F] [ExpChar F 2]

/-- The k-th iterate of the Frobenius endomorphism φ(x) = x² equals x^{2^k}. -/
theorem frobenius_iterate_eq (x : F) (k : ℕ) :
    (frobenius F 2)^[k] x = x ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ', comp_apply, frobenius_def, ih, ← pow_mul, pow_succ]

/-- The Gold function x^{2^k+1} = φᵏ(x) · x (shift × identity). -/
theorem gold_eq_frobenius_mul (x : F) (k : ℕ) :
    x ^ (2 ^ k + 1) = (frobenius F 2)^[k] x * x := by
  rw [frobenius_iterate_eq, pow_add, pow_one]

end FrobeniusShift

/-! ## §2  Frobenius Periodicity via Mathlib's `FiniteField` -/

section FrobeniusPeriodicity

variable (K : Type*) [Field K] [Fintype K] [Fact (Nat.Prime 2)] [CharP K 2]

/-- On GF(2^n), the Frobenius has period n: φⁿ = id. -/
theorem frobenius_periodic {n : ℕ} (hcard : Fintype.card K = 2 ^ n) (x : K) :
    (frobenius K 2)^[n] x = x := by
  have h := FiniteField.frobenius_pow hcard
  rw [← RingHom.coe_pow] at *
  simp [h]

/-- Every element of K is a periodic point of the Frobenius. -/
theorem frobenius_isPeriodicPt {n : ℕ} (hcard : Fintype.card K = 2 ^ n) (x : K) :
    Function.IsPeriodicPt (frobenius K 2) n x :=
  frobenius_periodic K hcard x

/-- Frobenius generates a finite cyclic group: φⁿ = 1 in End(K). -/
theorem frobenius_pow_eq_one {n : ℕ} (hcard : Fintype.card K = 2 ^ n) :
    frobenius K 2 ^ n = 1 :=
  FiniteField.frobenius_pow hcard

end FrobeniusPeriodicity

/-! ## §3  Cyclic Shift on Bitstrings -/

section CyclicShift

/-- The cyclic shift σ on length-n bitstrings: σ(f)(i) = f(i + 1). -/
def cyclicShift (n : ℕ) (f : ZMod n → ZMod 2) : ZMod n → ZMod 2 :=
  fun i => f (i + 1)

/-- k-fold shift = translation by k. -/
theorem cyclicShift_iterate (n : ℕ) (f : ZMod n → ZMod 2) (k : ℕ) :
    (cyclicShift n)^[k] f = fun i => f (i + (k : ZMod n)) := by
  induction k with
  | zero => ext; simp
  | succ k ih =>
    ext i
    rw [iterate_succ', comp_apply, cyclicShift, ih]
    push_cast; ring_nf

/-- The shift has period n on cyclic bitstrings. -/
theorem cyclicShift_period (n : ℕ) [NeZero n] (f : ZMod n → ZMod 2) :
    (cyclicShift n)^[n] f = f := by
  rw [cyclicShift_iterate]
  ext i; simp

/-- Every bitstring is a periodic point of the cyclic shift. -/
theorem cyclicShift_isPeriodicPt (n : ℕ) [NeZero n] (f : ZMod n → ZMod 2) :
    Function.IsPeriodicPt (cyclicShift n) n f :=
  cyclicShift_period n f

end CyclicShift

/-! ## §4  Gold Derivative via Frobenius -/

section GoldDerivative

variable {F : Type*} [Field F] [CharP F 2]

/-- Gold function: f(x) = x^{2^k+1}. -/
def goldFun (k : ℕ) (x : F) : F := x ^ (2 ^ k + 1)

/-- The Gold derivative factors through Frobenius:
    Δ_u f(x) = φᵏ(x)·u + x·φᵏ(u) + u^{2^k+1}. -/
theorem gold_derivative_frobenius (k : ℕ) (u x : F) :
    goldFun k (x + u) + goldFun k x =
    (frobenius F 2)^[k] x * u + x * (frobenius F 2)^[k] u + u ^ (2 ^ k + 1) := by
  unfold goldFun
  simp only [frobenius_iterate_eq]
  have h : (x + u) ^ (2 ^ k) = x ^ (2 ^ k) + u ^ (2 ^ k) :=
    add_pow_char_pow x u 2 k
  rw [pow_succ, h]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf; simp [h2]

end GoldDerivative

/-! ## §5  Coprimality ↔ ℤ/nℤ Generation -/

section Coprimality

/-- The shift by k generates ℤ/nℤ iff gcd(k, n) = 1. -/
theorem shift_generates_iff_coprime (n k : ℕ) (hn : 0 < n) :
    (∀ i : ZMod n, ∃ m : ℕ, (m * k : ZMod n) = i) ↔ Nat.Coprime k n := by
  constructor
  · intro h
    rcases n with (_ | _ | n) <;> simp_all +decide [ZMod]
    obtain ⟨m, hm⟩ := h ⟨1, by linarith⟩
    norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul] at hm
    exact Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) <|
      by rw [← Nat.mod_add_div (m * k) (n + 1 + 1), hm]; norm_num)
  · intro h_coprime
    have h_unit : IsUnit (k : ZMod n) := by
      exact (ZMod.isUnit_iff_coprime k n).mpr h_coprime
    obtain ⟨u, hu⟩ := h_unit.exists_left_inv
    intro i
    use (i * u).val
    cases n <;> simp_all +decide [mul_assoc]

end Coprimality

end
