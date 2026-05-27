import Mathlib
import RequestProject.FrobAlg
import RequestProject.ExpArith

/-!
# Skeleton: bij_of_additive_pow_twist — Sub-lemma DAG

Decomposes `bij_of_additive_pow_twist` (NormPower.lean:115) into tiny lemmas.

## Goal
If `L(x)·x^k` is bijective, `(x^b)^p = x^b` for x ≠ 0,
and `gcd(b+1, |F|−1) = 1`, then `L(x)·x^{k+b}` is bijective.

## Key Insight
Since `(x^b)^p = x^b`, we have `x^b ∈ GF(p)`. The map `L(x)·x^{k+b}`
factors as `(L(x)·x^k) · x^b`. Since `x^b` is a GF(p)-scalar and `L` is
GF(p)-linear, the scalar can be "absorbed" into the argument of `L` or
treated as a bijective twist on the multiplicative structure.

## DAG

```
  NPT.1 (x^b ∈ GF(p))              [easy]
    │
    ├──► NPT.2 (x^b commutes with L) [meh]
    │
    ├──► NPT.3 (factored form)       [easy]
    │
    ├──► NPT.4 (scalar-twisted inj)  [hard]
    │      │
    │      └──► NPT.5 (assembly)      [meh]
    │
    └──► bij_of_additive_pow_twist
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- NPT.1 [easy]: x^b is in GF(p) for nonzero x
-- ═══════════════════════════════════════════

/-- If (x^b)^p = x^b then x^b is fixed by Frobenius, hence in GF(p). -/
lemma pow_b_in_gfp {b : ℕ} {x : F} (hx : x ≠ 0) (hfixed : (x ^ b) ^ p = x ^ b) :
    x ^ (b * p) = x ^ b := by sorry
-- Difficulty: easy
-- Proof: (x^b)^p = x^{bp} = x^b. Just rewrite pow_mul.

-- ═══════════════════════════════════════════
-- NPT.2 [meh]: x^b commutes with GF(p)-linear L
-- ═══════════════════════════════════════════

/-- If L is additive and commutes with GF(p)-scalars, and x^b ∈ GF(p),
    then L(x^b · y) = x^b · L(y). -/
lemma L_commutes_with_pow_b
    (L : F → F) (hL_add : ∀ a c, L (a + c) = L a + L c)
    (b : ℕ) {x : F} (hx : x ≠ 0) (hfixed : (x ^ b) ^ p = x ^ b)
    -- We need L to commute with GF(p)-scalars:
    (hL_frob : ∀ y : F, L (y ^ p) = (L y) ^ p) :
    ∀ y : F, L (x ^ b * y) = x ^ b * L y := by sorry
-- Difficulty: meh
-- Proof: Since x^b satisfies c^p = c (i.e., c ∈ GF(p)), and L is
-- a sum of Frobenius powers (each fixing GF(p)), L(c·y) = c·L(y).
-- This follows from additive_frob_is_gfp_linear.

-- ═══════════════════════════════════════════
-- NPT.3 [easy]: Factored form of L(x)·x^{k+b}
-- ═══════════════════════════════════════════

/-- `L(x) · x^{k+b} = L(x) · x^k · x^b`. -/
lemma factored_form (L : F → F) (k b : ℕ) (x : F) :
    L x * x ^ (k + b) = L x * x ^ k * x ^ b := by sorry
-- Difficulty: easy
-- Proof: pow_add, mul_assoc.

-- ═══════════════════════════════════════════
-- NPT.4a [meh]: Injectivity on zero
-- ═══════════════════════════════════════════

/-- L(0) = 0 for any additive map. -/
lemma additive_map_zero (L : F → F) (hL_add : ∀ a c, L (a + c) = L a + L c) :
    L 0 = 0 := by sorry
-- Difficulty: easy
-- Proof: L(0) = L(0+0) = L(0) + L(0), so L(0) = 0.

-- ═══════════════════════════════════════════
-- NPT.4b [meh]: Zero case for twist
-- ═══════════════════════════════════════════

/-- If L(0) = 0 and k+b > 0, then L(0)·0^{k+b} = 0. -/
lemma twist_at_zero (L : F → F) (hL0 : L 0 = 0) (k b : ℕ) (hkb : 0 < k + b) :
    L 0 * (0 : F) ^ (k + b) = 0 := by sorry
-- Difficulty: easy

-- ═══════════════════════════════════════════
-- NPT.5 [hard]: Core injectivity argument
-- ═══════════════════════════════════════════

/-- **Core injectivity.** If L(x)·x^k is injective, (x^b)^p = x^b for x ≠ 0,
    and gcd(b+1, |F|−1) = 1, then L(x)·x^{k+b} is injective.

    Key argument: Suppose L(x)·x^{k+b} = L(y)·y^{k+b} for x ≠ y.
    Case 1: x = 0. Then L(0)·0^{k+b} = 0 = L(y)·y^{k+b}, so either y = 0 or L(y)·y^k = 0 and y^b = 0.
    Case 2: x, y both nonzero. Then L(x)·x^k·x^b = L(y)·y^k·y^b.
      Since x^b ∈ GF(p)* and y^b ∈ GF(p)*, we can use the bijection of x ↦ x^{b+1}...

    Actually, the cleaner argument is:
    Define g(x) = x^{b+1} for x ≠ 0, g(0) = 0. Since gcd(b+1, |F|-1) = 1,
    g is bijective. Then L(x)·x^{k+b} = L(x)·x^{k-1}·x^{b+1} (when k ≥ 1).
    Hmm, this doesn't directly work either.

    Alternative approach: The map x ↦ L(x)·x^{k+b} is the composition
    of x ↦ (L(x)·x^k, x^b) followed by multiplication.
    Since x^b ∈ GF(p)*, and |GF(p)*| = p-1, we can partition F* by the
    value of x^b and show injectivity on each fiber...

    Actually, the simplest correct argument is:
    For p = 2 (char 2): x^b ∈ {0, 1}, and for x ≠ 0, x^b = 1 (since GF(2)* = {1}).
    So L(x)·x^{k+b} = L(x)·x^k·1 = L(x)·x^k for x ≠ 0. Already proved as char 2 case.

    For general p: x^b ∈ GF(p)* for x ≠ 0. The key is that the map
    x ↦ x^b : F* → GF(p)* is a group homomorphism, and its kernel has
    index dividing p-1 in F*. The fibers are cosets.
    On each coset (where x^b = c is constant), L(x)·x^{k+b} = c·L(x)·x^k,
    and since c ≠ 0, injectivity of L(x)·x^k on the coset gives injectivity
    of c·L(x)·x^k. The coprimality gcd(b+1, |F|-1) = 1 ensures that
    distinct cosets map to distinct values.
-/
lemma twist_injective
    (L : F → F) (hL_add : ∀ a c, L (a + c) = L a + L c)
    (k b : ℕ)
    (hbij_P : Function.Bijective (fun x : F => L x * x ^ k))
    (hb_fixed : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
    (hcop : Nat.Coprime (b + 1) (Fintype.card F - 1)) :
    Function.Injective (fun x : F => L x * x ^ (k + b)) := by sorry
-- Difficulty: hard
-- After proving injective, convert to bijective on Fintype.

-- ═══════════════════════════════════════════
-- NPT.6 [easy]: Injective ⟹ bijective on Fintype
-- ═══════════════════════════════════════════

/-- On a finite type, injective ⟹ bijective. -/
lemma fintype_inj_bij (f : F → F) (hf : Function.Injective f) :
    Function.Bijective f :=
  ⟨hf, Finite.injective_iff_surjective.mp hf⟩

end DempwolffMueller
