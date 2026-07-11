import Mathlib

/-!
# Gadget C — cyclotomic-coset / exponent bookkeeping

The third primitive LEGO brick: the arithmetic of exponents modulo `2ⁿ − 1`.
Where gadget F cycles a *point* (`x^{2ⁿ} = x`), gadget C cycles an *exponent*:
multiplication by `2` permutes `ℤ/(2ⁿ−1)`, its orbits are the **cyclotomic
cosets**, and the two facts the Kasami argument actually consumes are:

* `mersenne_coprime` — `gcd(2^k − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1`, so `k ⟂ n`
  forces `2^k − 1 ⟂ 2ⁿ − 1`;
* `inv_mod_exists`   — hence `2^k − 1` is invertible mod `2ⁿ − 1` (the inverse
  `k'` of the "step" `k` in coset arithmetic);
* `powMap_bijective` — the power map `x ↦ xᵃ` is a permutation of a finite field
  exactly when `a ⟂ |F| − 1` (a bijection read off coset arithmetic).

Depends only on `Mathlib`; reusable and upstreamable on its own.
-/

namespace Kasami.Gadgets

open Finset

/-! ## Mersenne / coset arithmetic -/

/-- Since `gcd(2^k − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1`, coprimality of the steps
`k` and `n` makes the Mersenne numbers `2^k − 1` and `2ⁿ − 1` coprime. -/
theorem mersenne_coprime {k n : ℕ} (h : Nat.Coprime k n) :
    Nat.Coprime (2 ^ k - 1) (2 ^ n - 1) := by
  unfold Nat.Coprime at *
  rw [Nat.pow_sub_one_gcd_pow_sub_one]
  simp [h]

/-- The multiplicative inverse `k' = (2^k − 1)⁻¹ (mod 2ⁿ − 1)` exists whenever
`gcd(k, n) = 1` (and `1 < 2ⁿ − 1`).  This `k'` is the coset-arithmetic inverse of
the step used throughout the Kasami argument. -/
theorem inv_mod_exists {k n : ℕ} (h : Nat.Coprime k n) (hn : 1 < 2 ^ n - 1) :
    ∃ b, (2 ^ k - 1) * b % (2 ^ n - 1) = 1 := by
  obtain ⟨b, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime (mersenne_coprime h) hn
  exact ⟨b, hb.2⟩

/-! ## Power maps from coset coprimality -/

variable {F : Type*} [Field F] [Fintype F]

/-- **A power map is a permutation iff its exponent is coprime to `|F| − 1`.**
The map `x ↦ xᵃ` on a finite field is a bijection when `a ⟂ |F| − 1` — the
coset-arithmetic reason the various Kasami exponents give permutations. -/
theorem powMap_bijective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a)
    (ha_pos : 0 < a) :
    Function.Bijective (fun x : F => x ^ a) := by
  obtain ⟨b, hb⟩ : ∃ b, a * b ≡ 1 [MOD (Fintype.card F - 1)] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime ha.symm
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;>
      simp_all +decide [ Nat.ModEq, Nat.mod_one ]
    grind +splitIndPred
  have h_exp : ∀ x : F, x ≠ 0 → x ^ (a * b) = x := by
    intro x hx
    rw [ ← Nat.mod_add_div ( a * b ) ( Fintype.card F - 1 ), hb ]
    simp +decide [ pow_add, pow_mul ]
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ]
    · have := FiniteField.pow_card_sub_one_eq_one x; aesop
    · have := FiniteField.pow_card_sub_one_eq_one x; simp_all +decide [ pow_succ' ]
  have h_inj : Function.Injective (fun x : F => x ^ a) := by
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ pow_mul ]
    · rw [ zero_pow ha_pos.ne', eq_comm ] at hxy ; aesop
    · cases a <;> simp_all +decide
    · rw [ ← h_exp x hx, ← h_exp y hy, hxy ]
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

end Kasami.Gadgets
