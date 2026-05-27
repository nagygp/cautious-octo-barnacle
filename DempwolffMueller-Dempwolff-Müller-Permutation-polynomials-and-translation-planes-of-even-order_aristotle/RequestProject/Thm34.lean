import Mathlib
import RequestProject.Thm32
import RequestProject.ExpArith
import RequestProject.NormPower

/-!
# Theorem 3.4 — Simple Construction

Formalization of Theorem 3.4 from Dempwolff & Müller (2013).

## Statement

If `L(X)·X^k` is a permutation polynomial on `GF(q^n)` and
`b` is a multiple of `N = (q^n - 1)/(q - 1)` with `gcd(b·ℓ + 1, q - 1) = 1`,
then `L(X)·X^{k+b}` is also a permutation polynomial.

## Note on correctness

The general-characteristic version of this theorem (with arbitrary prime p)
is false — see the counterexample documented in `NormPower.lean`.
The characteristic 2 version holds trivially because `x^b = 1` for all
nonzero x (since `GF(2)* = {1}`).

## DAG structure

```
  Thm32 + ExpArith (F3)
    │
    ├──► Norm map N computation
    │
    ├──► Power map factorization
    │
    └──► Theorem 3.4 (char 2)
```

**Dependencies:** Thm32 (`Thm32.lean`), ExpArith (`ExpArith.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F]

-- ═══════════════════════════════════════════
-- T4.1 : Norm map definition
-- ═══════════════════════════════════════════

/-- The field norm `N_{q^n/q}(x) = x^{(q^n - 1)/(q - 1)}`.
    When `q = |GF(q)|` is the base field size, `N` maps `GF(q^n)* → GF(q)*`. -/
noncomputable def fieldNorm (q_size : ℕ) (n_ext : ℕ) (x : F) : F :=
  x ^ ((q_size ^ n_ext - 1) / (q_size - 1))

/-- **Norm is multiplicative.** `N(x·y) = N(x)·N(y)`. -/
lemma fieldNorm_mul (q_size n_ext : ℕ) (x y : F) :
    fieldNorm q_size n_ext (x * y) = fieldNorm q_size n_ext x * fieldNorm q_size n_ext y := by
  simp [fieldNorm, mul_pow]

-- ═══════════════════════════════════════════
-- T4.2 : Power map shift lemma
-- ═══════════════════════════════════════════

/-- **Power shift.** If `b` is a multiple of `N = (q^n-1)/(q-1)`,
    then `x^b ∈ GF(q)` for all `x ∈ GF(q^n)*`.

    This means `x^b` commutes with all `GF(q)`-linear operations. -/
lemma pow_multiple_of_norm_in_base (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]
    {n_ext : ℕ} (hn : Fintype.card F = p ^ n_ext)
    (b : ℕ) (N : ℕ) (hN : N = (p ^ n_ext - 1) / (p - 1))
    (hbN : N ∣ b) {x : F} (hx : x ≠ 0) :
    (x ^ b) ^ p = x ^ b := by
  have hn1 : 1 ≤ n_ext := by
    by_contra h; push_neg at h; interval_cases n_ext
    simp at hn; exact absurd hn (by have := Fintype.one_lt_card (α := F); omega)
  exact pow_frob_fixed_of_norm_dvd p hn hn1 b N hN hbN hx

-- ═══════════════════════════════════════════
-- T4.3 : Theorem 3.4 — general statement FALSE
-- ═══════════════════════════════════════════

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

/- **⚠ FALSE for general characteristic (commented out).**
   Same issue as `bij_of_additive_pow_twist` in NormPower.lean.
   The general-char version fails because GF(p)*-homogeneity of x ↦ L(x)·x^k
   requires gcd(k+b+1, p-1) = 1 for the twisted version, which is not
   guaranteed by the hypotheses. See counterexample in NormPower.lean. -/

-- theorem thm_3_4_abstract
--     (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
--     (k b : ℕ)
--     (hbij : Function.Bijective (fun x : F => L x * x ^ k))
--     (hb_norm : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
--     (hcop : Nat.Coprime (b + 1) (Fintype.card F - 1)) :
--     Function.Bijective (fun x : F => L x * x ^ (k + b)) := by sorry

/-- **Theorem 3.4 (characteristic 2).** In char 2, the twist is trivial
    since `x^b = 1` for all nonzero x whenever `(x^b)^2 = x^b`. -/
theorem thm_3_4_char2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (k b : ℕ)
    (hbij : Function.Bijective (fun x : F => L x * x ^ k))
    (hb_norm : ∀ x : F, x ≠ 0 → (x ^ b) ^ 2 = x ^ b) :
    Function.Bijective (fun x : F => L x * x ^ (k + b)) :=
  bij_of_additive_pow_twist_char2 L hL_add k b hbij hb_norm

end DempwolffMueller
