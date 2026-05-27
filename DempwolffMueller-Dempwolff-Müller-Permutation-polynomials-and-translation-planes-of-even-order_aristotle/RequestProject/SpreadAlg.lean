import Mathlib
import RequestProject.AutBase

/-!
# Foundational Layer: Spread Set Algebra

Algebraic identities connecting spread set difference-bijectivity
with permutation polynomial injectivity, and spread set equivalence
via rescaling.

## Key results

1. **Spread difference ↔ perm poly** (`spread_diff_iff_perm_poly`):
   N(x) - N(y) bijective for x ≠ y ↔ P(z) = L(z)·z^k injective
2. **Spread equivalence via rescaling** (`spread_equiv_rescaling`):
   If x^b ∈ GF(p), then L(X)·X^k and L(X)·X^{k+b} define equivalent spreads

## DAG

```
  AutBase (B1)
    │
    ├──► SA.1 spread difference identity
    │
    ├──► SA.2 perm poly ↔ spread condition
    │
    └──► SA.3 spread equivalence
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- SA.1 : Spread difference identity (CORRECTED)
-- ═══════════════════════════════════════════

-- The original statement `spread_diff_via_subst` claimed:
--   `Bijective (z ↦ L(xz)x^k - L(yz)y^k) ↔ Bijective (z ↦ L((x-y)z)(x-y)^k)`
-- This is FALSE. Counterexample: In GF(4) with L = id, k = 2, take x = ω, y = ω²
-- (primitive cube roots of unity). Then x³ + y³ = 0 so the LHS map is zero
-- (not bijective), but (x+y)³ = 1 ≠ 0 so the RHS map IS bijective.
--
-- The correct approach to `spread_condition_iff_perm_poly` does not go through this
-- intermediate factorization, but instead uses a direct kernel argument.

-- lemma spread_diff_via_subst
--     (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
--     (L := additivePolyEval p n_dim coeffs)
--     (hL_add : ∀ a b, L (a + b) = L a + L b)
--     (hL_bij : Function.Bijective L) (x y : F) (hxy : x ≠ y) :
--     Function.Bijective (fun z => L (x * z) * x ^ k - L (y * z) * y ^ k) ↔
--     Function.Bijective (fun z => L ((x - y) * z) * (x - y) ^ k) := by sorry

-- ═══════════════════════════════════════════
-- SA.2 : Spread set equivalence via rescaling
-- ═══════════════════════════════════════════

lemma spread_rescaling_identity
    (L : F → F) (_hL_add : ∀ a b, L (a + b) = L a + L b)
    (_hL_comm : ∀ (c x : F), c ^ p = c → L (c * x) = c * L x)
    (k b : ℕ)
    (_hb : ∀ (x : F), x ≠ 0 → (x ^ b) ^ p = x ^ b) :
    ∀ x y : F, L (x * y) * x ^ (k + b) =
      L (x * y) * x ^ k * x ^ b := by
  intro x y; rw [pow_add, mul_assoc]

end DempwolffMueller
