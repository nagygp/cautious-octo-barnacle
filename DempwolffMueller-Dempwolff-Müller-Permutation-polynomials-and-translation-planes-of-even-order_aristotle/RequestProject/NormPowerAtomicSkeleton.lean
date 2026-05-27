import Mathlib
import RequestProject.FrobAlg
import RequestProject.ExpArith
import RequestProject.TraceNorm

/-!
# Skeleton: bij_of_additive_pow_twist — Atomic Decomposition (DAG 5)

Decomposes `bij_of_additive_pow_twist` (NormPower.lean:115) into atomic lemmas.

## Goal
If `L(x)·x^k` is bijective, `(x^b)^p = x^b` for x ≠ 0,
and `gcd(b+1, |F|−1) = 1`, then `L(x)·x^{k+b}` is bijective.

## Key Insight
Since `(x^b)^p = x^b`, we have `x^b ∈ GF(p)*` for nonzero x.
In char 2 this means x^b = 1, making the result trivial (already proved).
For general p, we use the GF(p)-linearity of L to absorb the scalar x^b.

## DAG

```
  NPT.1..NPT.3 (independent easy)
      │
      ├──► NPT.4..NPT.5 (meh, use Frobenius theory)
      │
      └──► NPT.6 (core injectivity) → assembly
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════════════
-- NPT.1 [easy]: Frobenius-fixed means power relation
-- ═══════════════════════════════════════════════════

/-- (x^b)^p = x^b ⟹ x^{bp} = x^b. Just rewrite pow_mul. -/
lemma pow_b_frob_rewrite (b : ℕ) {x : F} (h : (x ^ b) ^ p = x ^ b) :
    x ^ (b * p) = x ^ b := by sorry
-- Proof: (x^b)^p = x^{b·p}. Rewrite pow_mul.

-- ═══════════════════════════════════════════════════
-- NPT.2 [meh]: x^b is a (p-1)-th root of unity
-- ═══════════════════════════════════════════════════

/-- If (x^b)^p = x^b for nonzero x, then x^{b(p-1)} = 1.
    This means x^b is a (p-1)-th root of unity, hence in GF(p)*. -/
lemma pow_b_root_of_unity (b : ℕ)
    {x : F} (hx : x ≠ 0) (h : (x ^ b) ^ p = x ^ b) :
    x ^ (b * (p - 1)) = 1 := by sorry
-- Proof: (x^b)^p = x^b means x^{bp} = x^b.
-- Since x ≠ 0, x^b ≠ 0 (pow_ne_zero), so divide: x^{bp}/x^b = 1.
-- x^{bp-b} = x^{b(p-1)} = 1.
-- Formally: x^{bp} = x^b ⟹ x^{bp} * (x^b)⁻¹ = 1 ⟹ x^{b(p-1)} = 1.

-- ═══════════════════════════════════════════════════
-- NPT.2b [easy]: Unit order divides (p-1)
-- ═══════════════════════════════════════════════════

-- From x^{b(p-1)} = 1, the order of x^b divides p-1.
-- Since the roots of X^{p-1} - 1 are exactly GF(p)*,
-- we get x^b is Frobenius-fixed: (x^b)^p = x^b.
-- Note: The statement "x^b ∈ GF(p)*" is just the hypothesis itself.
-- The useful corollary is pow_b_root_of_unity above.

-- ═══════════════════════════════════════════════════
-- NPT.3 [easy]: Factor L(x)·x^{k+b} = (L(x)·x^k) · x^b
-- ═══════════════════════════════════════════════════

/-- L(x) · x^{k+b} = L(x) · x^k · x^b. -/
lemma factor_pow_add (L : F → F) (k b : ℕ) (x : F) :
    L x * x ^ (k + b) = L x * x ^ k * x ^ b := by sorry
-- Proof: pow_add, mul_assoc.

-- ═══════════════════════════════════════════════════
-- NPT.4 [meh]: L commutes with GF(p)-scalars
-- ═══════════════════════════════════════════════════

/-- If L is additive and L commutes with Frobenius (L(x^p) = L(x)^p),
    and c^p = c, then L(c·x) = c·L(x). -/
lemma L_commutes_with_gfp_scalar
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL_frob : ∀ x, L (x ^ p) = (L x) ^ p)
    {c : F} (hc : c ^ p = c) (x : F) :
    L (c * x) = c * L x := by sorry
-- Proof: This is frobSum_gfp_smul from TraceNorm.lean for the specific
-- case where L is a sum of Frobenius powers. For general L with L(x^p) = L(x)^p:
-- In the prime subfield, c = ∑_{i} aᵢ where aᵢ ∈ {0, 1, ..., p-1}.
-- By additivity L(c·x) = L(∑ aᵢ·x) = ∑ L(aᵢ·x).
-- For aᵢ ∈ GF(p): aᵢ·x = x + ... + x (aᵢ times), so L(aᵢ·x) = aᵢ·L(x) by additivity.
-- Hence L(c·x) = c·L(x).

-- ═══════════════════════════════════════════════════
-- NPT.5 [easy]: x ↦ x^{b+1} is bijective
-- ═══════════════════════════════════════════════════

/-- When gcd(b+1, |F|-1) = 1, x ↦ x^{b+1} is bijective. -/
lemma pow_b_plus_one_bijective (b : ℕ)
    (hcop : Nat.Coprime (b + 1) (Fintype.card F - 1))
    (hpos : 0 < b + 1) :
    Function.Bijective (fun x : F => x ^ (b + 1)) := by sorry
-- Proof: Direct from pow_field_bijective with coprimality hcop.

-- ═══════════════════════════════════════════════════
-- NPT.6a [easy]: L(x)·x^{k+b} = 0 ↔ x = 0 or L(x) = 0
-- ═══════════════════════════════════════════════════

/-- L(x)·x^{k+b} = 0 iff L(x) = 0 or x = 0 (when k+b > 0). -/
lemma mul_pow_eq_zero_iff (L : F → F) (k b : ℕ) (hkb : 0 < k + b)
    {x : F} :
    L x * x ^ (k + b) = 0 ↔ L x = 0 ∨ x = 0 := by sorry
-- Proof: mul_eq_zero, pow_eq_zero_iff.

-- ═══════════════════════════════════════════════════
-- NPT.6b [easy]: L(x) = 0 and L injective ⟹ x = 0
-- ═══════════════════════════════════════════════════

/-- If L is additive and injective, L(x) = 0 ⟹ x = 0. -/
lemma eq_zero_of_L_eq_zero_inj (L : F → F)
    (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL_inj : Function.Injective L) {x : F} (h : L x = 0) :
    x = 0 := by sorry
-- Proof: L(0) = 0 (from additivity). L(x) = 0 = L(0). Injectivity gives x = 0.

-- ═══════════════════════════════════════════════════
-- NPT.6 [meh]: Core injectivity step
-- ═══════════════════════════════════════════════════

/-- The core argument: if L(x)·x^k is injective, (x^b)^p = x^b for x ≠ 0,
    and gcd(b+1, |F|-1) = 1, then L(x)·x^{k+b} is injective.

    Key idea: L(x)·x^{k+b} = (L(x)·x^k)·x^b.
    If L(x₁)·x₁^{k+b} = L(x₂)·x₂^{k+b} with x₁, x₂ ≠ 0:
    (L(x₁)·x₁^k)·x₁^b = (L(x₂)·x₂^k)·x₂^b.
    Since x₁^b, x₂^b ∈ GF(p)* and L is GF(p)-linear, we can use
    the substitution yᵢ = xᵢ^{-(b/(b+1))} (if the power exists)
    to reduce to L(y)·y^k injectivity. -/
lemma twist_injective_step
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL_frob : ∀ x, L (x ^ p) = (L x) ^ p)
    (k b : ℕ)
    (hP_inj : Function.Injective (fun x : F => L x * x ^ k))
    (hb_fixed : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
    (hcop : Nat.Coprime (b + 1) (Fintype.card F - 1)) :
    Function.Injective (fun x : F => L x * x ^ (k + b)) := by sorry
-- Proof approach (for general p):
-- Consider φ(x) = x^{b+1} (bijective by hcop).
-- L(x)·x^{k+b} = L(x)·x^k · x^b.
-- For x ≠ 0: x = φ⁻¹(φ(x)) = (x^{b+1})^{1/(b+1)}.
-- L(x)·x^{k+b} = L(x)·x^{k+b} (tautology).
-- 
-- Better approach: show the map x ↦ L(x)·x^{k+b} = L(x)·x^k·x^b is
-- injective by showing that if L(x)x^k·x^b = L(y)y^k·y^b then x = y.
-- 
-- For p = 2 (char 2): x^b = 1 for all x ≠ 0, so L(x)·x^{k+b} = L(x)·x^k.
-- Then injectivity follows from hP_inj. (Already proved as bij_of_additive_pow_twist_char2.)
-- 
-- For general p: Use L_commutes_with_gfp_scalar + careful substitution.

-- ═══════════════════════════════════════════════════
-- Assembly [meh]: bij_of_additive_pow_twist
-- ═══════════════════════════════════════════════════

/-- Main theorem: compose twist_injective_step with Fintype inj ⟹ bij. -/
theorem bij_of_additive_pow_twist_skeleton
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (k b : ℕ)
    (hbij_P : Function.Bijective (fun x : F => L x * x ^ k))
    (hb_fixed : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
    (hcop : Nat.Coprime (b + 1) (Fintype.card F - 1)) :
    Function.Bijective (fun x : F => L x * x ^ (k + b)) := by sorry
-- Proof: twist_injective_step gives injectivity.
-- Injectivity on Fintype ⟹ bijectivity.

end DempwolffMueller
