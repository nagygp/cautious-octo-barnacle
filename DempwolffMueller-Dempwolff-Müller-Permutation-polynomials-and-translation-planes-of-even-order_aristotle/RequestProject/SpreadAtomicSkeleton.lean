import Mathlib
import RequestProject.AutBase
import RequestProject.LinPoly

/-!
# Skeleton: Spread Substitution — Atomic Decomposition (DAGs 6-7)

Decomposes:
- `spread_diff_via_subst` (SpreadAlg.lean:61) — DAG 6
- `spread_condition_iff_perm_poly` (SpreadSet.lean:99) — DAG 7

## Key Insight for spread_diff_via_subst

The RHS `z ↦ L((x-y)z)·(x-y)^k` is ALWAYS bijective when L is bijective
and x ≠ y (it's a composition of bijections: multiply by x-y, apply L,
multiply by (x-y)^k ≠ 0).

So the iff decomposes as:
- Forward: LHS bij ⟹ True (trivially true, RHS always bij)
- Backward: True ⟹ LHS bij (must prove LHS is always bij when L is bij)

Actually, the backward direction (RHS bij ⟹ LHS bij) is the substantive claim.

## DAG Structure

```
  SD.A..SD.C (independent easy/meh)
      │
      ├──► SD.D (forward, trivial)
      │
      ├──► SD.E (backward, core content)
      │      │
      │      ├──► SD.E.1 (diff additive) [easy]
      │      │
      │      ├──► SD.E.2 (kernel analysis) [meh]
      │      │
      │      └──► SD.E.3 (additive ker bij) [easy]
      │
      └──► SD.F (iff assembly)
               │
               └──► spread_diff_via_subst
```

For `spread_condition_iff_perm_poly`:
```
  spread_diff_via_subst
      │
      ├──► SC.4 (forward: P inj ⟹ spread bij) [meh]
      │
      ├──► SC.5 (backward: spread bij ⟹ P inj) [meh]
      │
      └──► spread_condition_iff_perm_poly [easy]
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════════════════
-- DAG 6: spread_diff_via_subst
-- ═══════════════════════════════════════════════════════

-- ─── SD.A [easy]: Multiplication by nonzero is bijective ──────────

/-- z ↦ c·z is bijective when c ≠ 0. -/
lemma mul_left_bijective' {c : F} (hc : c ≠ 0) :
    Function.Bijective (fun z : F => c * z) := by sorry
-- Proof: Injective: c·z₁ = c·z₂ ⟹ z₁ = z₂ (mul_left_cancel₀ hc).
-- Bijective: injective on Fintype ⟹ bijective.

-- ─── SD.B [easy]: Multiplying output by nonzero preserves bijectivity ───

/-- If f is bijective and c ≠ 0, then z ↦ f(z)·c is bijective. -/
lemma mul_right_const_bij (f : F → F) (hf : Function.Bijective f)
    {c : F} (hc : c ≠ 0) :
    Function.Bijective (fun z => f z * c) := by sorry
-- Proof: Injective: f(z₁)·c = f(z₂)·c ⟹ f(z₁) = f(z₂) (cancel c) ⟹ z₁ = z₂.
-- Surjective: given w, find z with f(z)·c = w, i.e., f(z) = w·c⁻¹.
-- Since f is surjective, ∃ z.

-- ─── SD.C [meh]: RHS is always bijective ──────────────────────────

/-- z ↦ L((x-y)·z) · (x-y)^k is always bijective when L is bijective and x ≠ y. -/
lemma rhs_always_bijective
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    {x y : F} (hxy : x ≠ y) :
    Function.Bijective (fun z => additivePolyEval p n_dim coeffs ((x - y) * z) * (x - y) ^ k) := by sorry
-- Proof:
-- 1. x - y ≠ 0 (sub_ne_zero.mpr hxy).
-- 2. z ↦ (x-y)·z is bijective (mul_left_bijective').
-- 3. L ∘ (mul by x-y) is bijective (composition of bijections).
-- 4. (x-y)^k ≠ 0 (pow_ne_zero, sub_ne_zero).
-- 5. z ↦ (L ∘ mul_{x-y})(z) · (x-y)^k is bijective (mul_right_const_bij).

-- ─── SD.D [easy]: Forward direction (trivial) ────────────────────

/-- Forward: LHS bijective ⟹ RHS bijective (trivially, since RHS always bij). -/
lemma spread_diff_forward
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    {x y : F} (hxy : x ≠ y)
    (_hLHS : Function.Bijective (fun z =>
      additivePolyEval p n_dim coeffs (x * z) * x ^ k -
      additivePolyEval p n_dim coeffs (y * z) * y ^ k)) :
    Function.Bijective (fun z =>
      additivePolyEval p n_dim coeffs ((x - y) * z) * (x - y) ^ k) :=
  rhs_always_bijective p n_dim coeffs k hL_bij hxy

-- ─── SD.E.1 [easy]: Difference map is additive in z ──────────────

/-- The spread difference z ↦ L(xz)·x^k - L(yz)·y^k is additive in z. -/
lemma spread_diff_additive
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (x y a b : F) :
    (additivePolyEval p n_dim coeffs (x * (a + b)) * x ^ k -
     additivePolyEval p n_dim coeffs (y * (a + b)) * y ^ k) =
    (additivePolyEval p n_dim coeffs (x * a) * x ^ k -
     additivePolyEval p n_dim coeffs (y * a) * y ^ k) +
    (additivePolyEval p n_dim coeffs (x * b) * x ^ k -
     additivePolyEval p n_dim coeffs (y * b) * y ^ k) := by sorry
-- Proof: Use mul_add on x*(a+b) and y*(a+b).
-- additivePolyEval_add gives L(x(a+b)) = L(xa) + L(xb).
-- Distribute x^k, y^k. Ring.

-- ─── SD.E.2 [meh]: Kernel analysis ───────────────────────────────

/-- If L is bijective and x ≠ y, then the kernel of
    z ↦ L(xz)·x^k - L(yz)·y^k is trivial. -/
lemma spread_diff_ker_trivial
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    {x y : F} (hxy : x ≠ y)
    {z : F} (hz : additivePolyEval p n_dim coeffs (x * z) * x ^ k -
                   additivePolyEval p n_dim coeffs (y * z) * y ^ k = 0) :
    z = 0 := by sorry
-- Proof: From hz: L(xz)·x^k = L(yz)·y^k.
-- If z = 0: done.
-- If z ≠ 0: Need to derive contradiction.
-- Since L is bijective (hence injective and additive):
--   L(xz) = L(yz) · y^k / x^k (if x ≠ 0).
-- But L(xz) - L(yz) = L((x-y)z) (additivity).
-- So L((x-y)z)·x^k = L(yz)·(y^k - x^k)... hmm complicated.
-- 
-- Hmm, actually this is NOT true in general. Consider L = id, k = 0:
-- L(xz)·1 - L(yz)·1 = (x-y)z = 0 ⟹ z = 0 (since x ≠ y). ✓
-- 
-- For k > 0 and L = id: xz·x^k - yz·y^k = x^{k+1}z - y^{k+1}z = (x^{k+1}-y^{k+1})z.
-- This is 0 iff z = 0 or x^{k+1} = y^{k+1}. The latter can happen!
-- So the statement is FALSE for general k unless we add hypotheses.
-- 
-- WAIT: The hypotheses include hL_bij. For L = additivePolyEval which is NOT
-- the identity in general. The statement has L bijective. Let me re-examine.
-- The spread difference L(xz)·x^k - L(yz)·y^k is NOT just (x^{k+1}-y^{k+1})·L(z).
-- Because L is additive but NOT multiplicative in general.
-- So L(xz) ≠ x·L(z) unless L is a scalar multiplication.
-- 
-- This means the kernel analysis is more subtle. The statement may actually be
-- that the iff holds precisely because the two maps have the same kernel structure
-- (both trivial when L is bijective), but proving it requires showing that
-- z ↦ L(xz)·x^k - L(yz)·y^k has trivial kernel.
--
-- For the RHS: ker(z ↦ L((x-y)z)·(x-y)^k) = {z : L((x-y)z) = 0}
-- = {z : (x-y)z ∈ ker L} = {0} since L is injective and x-y ≠ 0.
-- 
-- For the LHS: We need L(xz)·x^k = L(yz)·y^k ⟹ z = 0.
-- This is genuinely harder and may require additional structure (e.g., that
-- x ↦ L(x)·x^k is a permutation polynomial, which is exactly what we're trying to prove).
-- 
-- CONCLUSION: The iff as stated may be wrong, or may require the hypothesis
-- that z ↦ L(z)·z^k is a PP (which would be circular for the intended application).
-- 
-- ALTERNATIVE INTERPRETATION: Perhaps the iff is used in the opposite direction:
-- we have that z ↦ L(z)·z^k is a PP (proved separately), and from that we
-- derive the spread condition. Then the forward direction is what matters,
-- and it follows from the fact that the spread difference is a "twist" of the PP.

-- ─── SD.E.3 [easy]: Additive + trivial kernel ⟹ bijective ───────

/-- On Fintype: additive, kernel trivial ⟹ bijective. -/
lemma additive_trivial_ker_bij
    (f : F → F) (hf_add : ∀ a b, f (a + b) = f a + f b)
    (hker : ∀ x, f x = 0 → x = 0) :
    Function.Bijective f := by sorry
-- Proof: ker trivial + additive ⟹ injective. Injective on Fintype ⟹ bijective.

-- ─── SD.E [meh]: Backward direction ──────────────────────────────

/-- Backward: RHS bijective ⟹ LHS bijective.
    Since RHS is always bijective (SD.C), this says LHS is always bijective
    when L is bijective and x ≠ y. -/
lemma spread_diff_backward
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_add : ∀ a b, additivePolyEval p n_dim coeffs (a + b) =
                      additivePolyEval p n_dim coeffs a +
                      additivePolyEval p n_dim coeffs b)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    {x y : F} (hxy : x ≠ y)
    (_hRHS : Function.Bijective (fun z =>
      additivePolyEval p n_dim coeffs ((x - y) * z) * (x - y) ^ k)) :
    Function.Bijective (fun z =>
      additivePolyEval p n_dim coeffs (x * z) * x ^ k -
      additivePolyEval p n_dim coeffs (y * z) * y ^ k) := by sorry
-- Proof: Show the LHS map is additive (SD.E.1) with trivial kernel (SD.E.2),
-- hence bijective (SD.E.3).
-- 
-- NOTE: SD.E.2 (kernel triviality) is the hard part.
-- The proof may need to use the specific structure of additivePolyEval
-- or additional hypotheses not currently stated.

-- ─── SD.F [easy]: Iff assembly ────────────────────────────────────

/-- Combine forward and backward into iff. -/
theorem spread_diff_via_subst_skeleton
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (L := additivePolyEval p n_dim coeffs)
    (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL_bij : Function.Bijective L) (x y : F) (hxy : x ≠ y) :
    Function.Bijective (fun z => L (x * z) * x ^ k - L (y * z) * y ^ k) ↔
    Function.Bijective (fun z => L ((x - y) * z) * (x - y) ^ k) := by sorry
-- Proof: ⟨spread_diff_forward, spread_diff_backward⟩.
-- Actually: both sides are always true (given L bij, x ≠ y),
-- so the iff is trivially True ↔ True.
-- The backward direction shows LHS is bij (the interesting part).
-- The forward direction is trivial (RHS is always bij).

-- ═══════════════════════════════════════════════════════
-- DAG 7: spread_condition_iff_perm_poly
-- ═══════════════════════════════════════════════════════

-- ─── SC.1 [easy]: Spread operator unfold ──────────────────────────

/-- N(x)(z) = L(xz) · x^k by definition. -/
lemma spread_N_unfold (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ) (x z : F) :
    additivePolyEval p n_dim coeffs (x * z) * x ^ k =
    additivePolyEval p n_dim coeffs (x * z) * x ^ k := rfl

-- ─── SC.2 [easy]: N(x)(z) - N(y)(z) expressed ────────────────────

/-- The spread difference is L(xz)·x^k - L(yz)·y^k. -/
lemma spread_diff_expressed (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ) (x y z : F) :
    additivePolyEval p n_dim coeffs (x * z) * x ^ k -
    additivePolyEval p n_dim coeffs (y * z) * y ^ k =
    additivePolyEval p n_dim coeffs (x * z) * x ^ k -
    additivePolyEval p n_dim coeffs (y * z) * y ^ k := rfl

-- ─── SC.3a [easy]: P(z) = L(z)·z^k ──────────────────────────────

-- P(z) = L(z)·z^k = N(z)(1)... no. P(z) = L(z)·z^k.
-- N(x)(z) = L(xz)·x^k. So N(1)(z) = L(z)·1 = L(z). Not P(z).
-- Actually: P relates to the spread via the substitution in spread_diff_via_subst.
-- (This is just a note; the actual connection goes through the iff.)

-- ─── SC.4 [meh]: Forward: P injective ⟹ spread differences bijective ──

/-- If P(z) = L(z)·z^k is injective, then all spread differences are bijective. -/
lemma spread_forward
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    (hP_inj : Function.Injective (fun z : F =>
      additivePolyEval p n_dim coeffs z * z ^ k))
    (x y : F) (hxy : x ≠ y) :
    Function.Bijective (fun z =>
      additivePolyEval p n_dim coeffs (x * z) * x ^ k -
      additivePolyEval p n_dim coeffs (y * z) * y ^ k) := by sorry
-- Proof: The RHS of spread_diff_via_subst is always bijective (SD.C).
-- The iff gives LHS is bijective too.
-- (Or prove directly from P injective + substitution.)

-- ─── SC.5 [meh]: Backward: spread differences bijective ⟹ P injective ──

/-- If all spread differences are bijective, then P is injective. -/
lemma spread_backward
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs))
    (hSpread : ∀ x y : F, x ≠ y →
      Function.Bijective (fun z =>
        additivePolyEval p n_dim coeffs (x * z) * x ^ k -
        additivePolyEval p n_dim coeffs (y * z) * y ^ k))  :
    Function.Injective (fun z : F =>
      additivePolyEval p n_dim coeffs z * z ^ k) := by sorry
-- Proof: Suppose P(a) = P(b) with a ≠ b.
-- Then L(a)·a^k = L(b)·b^k, i.e., L(a)·a^k - L(b)·b^k = 0.
-- Take x = a, y = b, z = 1:
-- N(a)(1) - N(b)(1) = L(a)·a^k - L(b)·b^k = 0.
-- But the map z ↦ N(a)(z) - N(b)(z) is bijective (by hypothesis, since a ≠ b).
-- Bijective maps send distinct elements to distinct elements, and are injective.
-- In particular, the map evaluated at z = 1 gives 0 only if there exists z' = 1 in ker.
-- Since the map is additive and bijective (hence injective), 1 is sent to
-- N(a)(1) - N(b)(1) = 0. But injective + additive means ker = {0}, so 1 = 0. ⊥.
-- Wait, that gives 1 = 0 which is a contradiction in a field.
-- Actually: the map IS bijective so it IS injective. If it maps 1 to 0,
-- and it's additive with L bijective, then... it maps 0 to 0 too.
-- So map(1) = map(0) = 0, hence 1 = 0 by injectivity. ⊥.
-- So P(a) ≠ P(b), i.e., P is injective.

-- ─── SC.6 [easy]: Assembly ────────────────────────────────────────

/-- Combine forward and backward into the iff. -/
theorem spread_condition_iff_perm_poly_skeleton
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs)) :
    (∀ x y : F, x ≠ y →
      Function.Bijective (fun z =>
        additivePolyEval p n_dim coeffs (x * z) * x ^ k -
        additivePolyEval p n_dim coeffs (y * z) * y ^ k)) ↔
    Function.Injective (fun z : F =>
      additivePolyEval p n_dim coeffs z * z ^ k) := by sorry
-- Proof: ⟨spread_backward, spread_forward⟩.

end DempwolffMueller
