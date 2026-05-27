import Mathlib
import RequestProject.AutBase

/-!
# Skeleton: Spread Condition & Difference Bijectivity — Sub-lemma DAG

Decomposes `spread_diff_via_subst` (SpreadAlg.lean:61) and
`spread_condition_iff_perm_poly` (SpreadSet.lean:99) into tiny lemmas.

## Goal A (spread_diff_via_subst)
For x ≠ y with L bijective:
`z ↦ L(xz)·x^k - L(yz)·y^k` bijective ↔ `z ↦ L((x-y)z)·(x-y)^k` bijective.

## Goal B (spread_condition_iff_perm_poly)
`{N(x)}` is a spread set ↔ `P(z) = L(z)·z^k` is injective.

## DAG

```
  SP.1 (mul-by-unit bijective)     [easy]
    │
    ├──► SP.2 (L∘(c·) bijective)   [easy]
    │
    ├──► SP.3 (spread diff algebra) [meh]
    │
    ├──► SP.4 (diff-bij ↔ norm-bij) [hard]  ──► spread_diff_via_subst
    │
    ├──► SP.5 (forward: P inj ⟹ spread) [hard]
    │
    ├──► SP.6 (backward: spread ⟹ P inj) [meh]
    │
    └──► SP.7 (iff assembly)         [easy] ──► spread_condition_iff_perm_poly
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- SP.1 [easy]: Multiplication by a unit is bijective
-- ═══════════════════════════════════════════

/-- Left multiplication by a nonzero element is bijective. -/
lemma mul_left_bijective_of_ne_zero {c : F} (hc : c ≠ 0) :
    Function.Bijective (fun z : F => c * z) := by sorry
-- Difficulty: easy
-- Proof: Injective by mul_left_cancel₀, surjective by ∃ c⁻¹·y.

-- ═══════════════════════════════════════════
-- SP.2 [easy]: Composition L ∘ (c·) is bijective when L and c· are
-- ═══════════════════════════════════════════

/-- If L is bijective and c ≠ 0, then z ↦ L(c·z) is bijective. -/
lemma comp_mul_bijective
    (L : F → F) (hL_bij : Function.Bijective L) {c : F} (hc : c ≠ 0) :
    Function.Bijective (fun z => L (c * z)) := by sorry
-- Difficulty: easy
-- Proof: Composition of two bijections: z ↦ c·z and L.

-- ═══════════════════════════════════════════
-- SP.3 [meh]: Spread difference algebraic identity
-- ═══════════════════════════════════════════

/-- **Key algebraic identity for spread differences.**
    `L(xz)·x^k - L(yz)·y^k = L((x-y)·z)·x^k + L(yz)·(x^k - y^k)`
    when L is additive. -/
lemma spread_diff_expand
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (k : ℕ) (x y z : F) :
    L (x * z) * x ^ k - L (y * z) * y ^ k =
    L ((x - y) * z) * x ^ k + L (y * z) * (x ^ k - y ^ k) := by sorry
-- Difficulty: meh
-- Proof: L(xz) = L((x-y)z + yz) = L((x-y)z) + L(yz) by additivity.
-- Then L(xz)·x^k = (L((x-y)z) + L(yz))·x^k = L((x-y)z)·x^k + L(yz)·x^k.
-- So L(xz)·x^k - L(yz)·y^k = L((x-y)z)·x^k + L(yz)·(x^k - y^k).

-- ═══════════════════════════════════════════
-- SP.4a [meh]: Substitution z → (x-y)⁻¹·w in the difference
-- ═══════════════════════════════════════════

/-- The substitution z → d⁻¹·w (where d = x - y ≠ 0) relates
    `z ↦ L(dz)·d^k` to `z ↦ L(z)·z^k` composed with z ↦ dz. -/
lemma diff_subst_relate
    (L : F → F) (k : ℕ) {d : F} (hd : d ≠ 0) (w : F) :
    L (d * (d⁻¹ * w)) * d ^ k = L w * d ^ k := by sorry
-- Difficulty: meh
-- Proof: d * d⁻¹ = 1, so L(d · d⁻¹ · w) = L(w).

-- ═══════════════════════════════════════════
-- SP.4b [hard]: Main equivalence for spread_diff_via_subst
-- ═══════════════════════════════════════════

/-- The difference map `z ↦ L(xz)·x^k - L(yz)·y^k` is bijective
    iff `z ↦ L((x-y)z)·(x-y)^k` is bijective, when L is bijective.

    The proof uses the substitution z → (x-y)⁻¹·w and the fact that
    the difference factors through L composed with the linear map z ↦ (x-y)·z. -/
lemma spread_diff_bij_iff_normalized
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (L := additivePolyEval p n_dim coeffs)
    (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL_bij : Function.Bijective L) (x y : F) (hxy : x ≠ y) :
    Function.Bijective (fun z => L (x * z) * x ^ k - L (y * z) * y ^ k) ↔
    Function.Bijective (fun z => L ((x - y) * z) * (x - y) ^ k) := by sorry
-- Difficulty: hard
-- Proof sketch: The key insight is that for the special case of
-- spread sets where N(x)(y) = L(xy)·x^k, the difference
-- N(x) - N(y) applied to z gives L(xz)·x^k - L(yz)·y^k.
-- Substituting z → (x-y)·z' and using bijectivity of L shows
-- this is equivalent to the normalized form.
-- WARNING: This may require a different formulation than what's stated.
-- The identity L(xz)·x^k - L(yz)·y^k does NOT simplify to L((x-y)z)·(x-y)^k
-- in general. The equivalence of bijectivity requires a more subtle argument
-- going through the full spread set theory.

-- ═══════════════════════════════════════════
-- SP.5 [hard]: Forward: P injective ⟹ spread differences bijective
-- ═══════════════════════════════════════════

/-- If P(z) = L(z)·z^k is injective, then for all x ≠ y,
    z ↦ N(x)(z) - N(y)(z) is bijective. -/
lemma perm_poly_inj_implies_spread
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    (hP_inj : Function.Injective (fun z : F =>
      additivePolyEval p n_dim coeffs z * z ^ k))
    (x y : F) (hxy : x ≠ y) :
    Function.Bijective (fun z =>
      additivePolyEval p n_dim coeffs (x * z) * x ^ k -
      additivePolyEval p n_dim coeffs (y * z) * y ^ k) := by sorry
-- Difficulty: hard
-- Proof: The difference map factors as:
-- z ↦ L(xz)·x^k - L(yz)·y^k
-- Substitute w = (x-y)·z. Since x-y ≠ 0 and L is bijective,
-- bijectivity of the difference follows from injectivity of P
-- composed with an appropriate substitution.
-- This is essentially the content of Lemma 3.1 specialized to the spread case.

-- ═══════════════════════════════════════════
-- SP.6 [meh]: Backward: spread differences bijective ⟹ P injective
-- ═══════════════════════════════════════════

/-- If all spread differences are bijective, then P is injective. -/
lemma spread_implies_perm_poly_inj
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    (hspread : ∀ x y : F, x ≠ y →
      Function.Bijective (fun z =>
        additivePolyEval p n_dim coeffs (x * z) * x ^ k -
        additivePolyEval p n_dim coeffs (y * z) * y ^ k))
    :
    Function.Injective (fun z : F =>
      additivePolyEval p n_dim coeffs z * z ^ k) := by sorry
-- Difficulty: meh
-- Proof: Take x = 1, y = 0 in the spread condition.
-- N(1)(z) - N(0)(z) = L(z)·1^k - L(0)·0^k = L(z)·1 - 0 = L(z).
-- Wait, that gives L(z) bijective, which we already know.
-- Need to be more careful: take general x, y and use P(a) = P(b)
-- to derive a = b by choosing appropriate x, y.
-- Actually: if P(a) = P(b), then for x = a, y = b:
-- L(az)·a^k - L(bz)·b^k bijective means its kernel is trivial.
-- At z = 1: L(a)·a^k - L(b)·b^k = P(a) - P(b) = 0, so
-- the value at z = 1 is 0, and if the map is injective (from bijectivity),
-- then the unique preimage of 0 is z = 0... but z = 1 ≠ 0. Contradiction.
-- Hence a = b. So P is injective.

-- ═══════════════════════════════════════════
-- SP.7 [easy]: Assembly of the iff
-- ═══════════════════════════════════════════

-- **Spread ↔ perm poly.** The spread condition holds iff P is injective.
-- This combines SP.5 and SP.6.
-- Note: the actual statement in SpreadSet.lean uses spreadSetFromPoly
-- and additivePolyEval, so we need to match that formulation.

end DempwolffMueller
