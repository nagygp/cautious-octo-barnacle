import Mathlib
import RequestProject.FrobAlg
import RequestProject.ExpArith

/-!
# Foundational Layer: Norm Map and Fixed-Field Power Theory

Theory of the field norm and elements "fixed by GF(q)-Frobenius".

## Key results

1. **Norm divisibility ⟹ Frobenius-fixed** (`pow_frob_fixed_of_norm_dvd`)
2. **Char 2: x^b = 1 for nonzero x** (`pow_eq_one_of_frob_fixed_char2`)
3. **Bijection with twist (char 2)** (`bij_of_additive_pow_twist_char2`)

## DAG

```
  FrobAlg (F1) + ExpArith (F3)
    │
    ├──► NP.1 norm ⟹ Frobenius-fixed
    ├──► NP.2 power factorization
    └──► NP.3 char 2 twist (fully proved)
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- NP.1 : Norm divisibility ⟹ Frobenius-fixed
-- ═══════════════════════════════════════════

/-- Norm exponent divides ⟹ power is Frobenius-fixed. -/
lemma pow_frob_fixed_of_norm_dvd
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (b : ℕ) (N : ℕ) (hN : N = (p ^ n - 1) / (p - 1))
    (hbN : N ∣ b) {x : F} (hx : x ≠ 0) :
    (x ^ b) ^ p = x ^ b := by
      have h_div : (p ^ n - 1) ∣ b * (p - 1) := by
        rw [ hN, Nat.div_dvd_iff_dvd_mul ] at hbN;
        · rwa [ mul_comm ];
        · zify;
          cases p <;> cases n <;> simp_all +decide [ ← geom_sum_mul, mul_comm ];
        · exact Nat.sub_pos_of_lt hp.1.one_lt;
      have h_exp : x ^ (b * (p - 1)) = 1 := by
        obtain ⟨ k, hk ⟩ := h_div;
        rw [ hk, pow_mul, show x ^ ( p ^ n - 1 ) = 1 from by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx ] ] ; simp +decide;
      cases p <;> simp_all +decide [ pow_succ, pow_mul ]

-- ═══════════════════════════════════════════
-- NP.2 : Power addition factorization
-- ═══════════════════════════════════════════

/-- `x^{k+b} = x^k · x^b`. -/
lemma pow_add_split (x : F) (k b : ℕ) :
    x ^ (k + b) = x ^ k * x ^ b :=
  pow_add x k b

/-- `L(x) · x^{k+b} = (L(x) · x^k) · x^b`. -/
lemma mul_pow_add_factor (L : F → F) (k b : ℕ) (x : F) :
    L x * x ^ (k + b) = L x * x ^ k * x ^ b := by
  rw [pow_add, mul_assoc]

-- ═══════════════════════════════════════════
-- NP.3a : Char 2 specialization (fully proved)
-- ═══════════════════════════════════════════

/-- **In char 2, x^b = 1 for nonzero x when (x^b)^2 = x^b.**
    GF(2)* = {1}, so any nonzero element of GF(2) is 1. -/
lemma pow_eq_one_of_frob_fixed_char2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {x : F} (hx : x ≠ 0) (b : ℕ) (hb : (x ^ b) ^ 2 = x ^ b) :
    x ^ b = 1 := by
  have h' : x ^ b * (x ^ b - 1) = 0 := by
    rw [mul_sub, mul_one, ← sq, hb, sub_self]
  rcases mul_eq_zero.mp h' with h | h
  · exact absurd h (pow_ne_zero b hx)
  · exact sub_eq_zero.mp h

/-- **Bijection with twist (char 2).** In char 2, x^b = 1 for all nonzero x,
    so L(x)·x^{k+b} = L(x)·x^k, which is bijective by assumption. -/
lemma bij_of_additive_pow_twist_char2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (k b : ℕ)
    (hbij_P : Function.Bijective (fun x : F => L x * x ^ k))
    (hb_fixed : ∀ x : F, x ≠ 0 → (x ^ b) ^ 2 = x ^ b) :
    Function.Bijective (fun x : F => L x * x ^ (k + b)) := by
  have hL0 : L 0 = 0 := by have := hL_add 0 0; simp at this; exact this
  have heq : (fun x : F => L x * x ^ (k + b)) = (fun x : F => L x * x ^ k) := by
    ext x
    by_cases hx : x = 0
    · subst hx; simp [hL0]
    · rw [pow_add]; simp [pow_eq_one_of_frob_fixed_char2 hx b (hb_fixed x hx)]
  rw [heq]; exact hbij_P

-- ═══════════════════════════════════════════
-- NP.3b : General characteristic — FALSE
-- ═══════════════════════════════════════════

/- **⚠ FALSE STATEMENT (commented out).**
   The original `bij_of_additive_pow_twist` claimed that for general char p,
   if `L(x)·x^k` is bijective, `(x^b)^p = x^b` for x ≠ 0, and `gcd(b+1, |F|-1) = 1`,
   then `L(x)·x^{k+b}` is bijective.

   **Counterexample:** F = GF(13), p = 13, L = id, k = 4, b = 4.
   - f(x) = x^5 is bijective (gcd(5, 12) = 1)
   - (x^4)^13 = x^4 ✓ (x^12 = 1 in GF(13)*)
   - gcd(5, 12) = 1 ✓
   - g(x) = x^9 is NOT bijective (gcd(9, 12) = 3, x^9 takes only 5 values on GF(13))

   **Root cause:** For general char p, the GF(p)*-homogeneity of the map
   (f(cx) = c^{k+1}·f(x) for c ∈ GF(p)*) requires gcd(k+1, p-1) = 1
   for f to be bijective, and gcd(k+b+1, p-1) = 1 for g to be bijective.
   The hypothesis gcd(b+1, |F|-1) = 1 does NOT guarantee gcd(k+b+1, p-1) = 1.

   In char 2, p-1 = 1 so gcd(anything, 1) = 1, which is why the char 2
   version (`bij_of_additive_pow_twist_char2`) works unconditionally.
   The char 2 version suffices for the Dempwolff-Müller paper. -/

-- lemma bij_of_additive_pow_twist
--     (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
--     (k b : ℕ)
--     (hbij_P : Function.Bijective (fun x : F => L x * x ^ k))
--     (hb_fixed : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
--     (hcop : Nat.Coprime (b + 1) (Fintype.card F - 1)) :
--     Function.Bijective (fun x : F => L x * x ^ (k + b)) := by sorry

end DempwolffMueller
