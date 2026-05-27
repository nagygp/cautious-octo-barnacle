import Mathlib

/-!
# Skeleton: Proposition 3.5 — Atomic Decomposition (DAG 8)

Decomposes `prop_3_5_abstract` (Prop35.lean:78).

## Goal
If `x^b ∈ GF(p)` for all nonzero x, and L commutes with GF(p) scalars,
then `L(X)·X^k` and `L(X)·X^{k+b}` define equivalent spread sets.

## Key Insight
The spread set `N₂(x)(y) = L(xy)·x^{k+b} = L(xy)·x^k · x^b = x^b · N₁(x)(y)`.
Since `x^b ∈ GF(p)*` for x ≠ 0, `N₂(x) = c_x · N₁(x)` with `c_x` a GF(p)-scalar.
The rescaling φ must satisfy `N₂(φ(x))(y) = N₁(x)(y)` for all y.

So: `L(φ(x)·y) · φ(x)^{k+b} = L(x·y) · x^k`.
Equivalently: `L(φ(x)·y) · φ(x)^k · φ(x)^b = L(x·y) · x^k`.

We need φ(x) such that φ(x)^b · L(φ(x)y) · φ(x)^k = L(xy) · x^k.
If φ(x) = x · d(x) where d(x) is chosen to cancel the b-th power:
φ(x)^b = (x·d(x))^b = x^b · d(x)^b.
Need: x^b · d(x)^b · L(x·d(x)·y) · (x·d(x))^k = L(xy) · x^k.
Using L(c·z) = c·L(z) for c ∈ GF(p):
= x^b · d(x)^b · d(x) · L(xy) · x^k · d(x)^k    [if d(x) ∈ GF(p)]
= x^b · d(x)^{b+k+1} · L(xy) · x^k.
Need: x^b · d(x)^{b+k+1} = 1, i.e., d(x)^{b+k+1} = (x^b)^{-1}.

If gcd(b+k+1, |F*|) = gcd(b+k+1, p-1) = 1 (since d(x) ∈ GF(p)* has order dividing p-1),
then d(x) = ((x^b)^{-1})^{1/(b+k+1)} exists.

But we need to verify this works and that φ is bijective.

## Alternative simpler approach for char 2

In char 2: x^b = 1 for all x ≠ 0 (since GF(2)* = {1}).
So N₂(x)(y) = N₁(x)(y) for all x ≠ 0.
For x = 0: both N₁(0) and N₂(0) are the zero operator.
So φ = id works. φ is bijective (identity).

## DAG Structure

```
  P5.1 (φ definition) [easy]
    │
    ├──► P5.2 (φ bijective) [easy]
    │
    ├──► P5.3 (power identity) [meh]
    │
    └──► P5.4 (spread element eq) [meh]
           │
           └──► prop_3_5_abstract [meh]
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════════════
-- P5.0 [easy]: SpreadSetsEquivalent definition reminder
-- ═══════════════════════════════════════════════════

-- SpreadSetsEquivalent N₁ N₂ = ∃ φ, bij φ ∧ ∀ x y, N₂(φ(x))(y) = N₁(x)(y).

-- ═══════════════════════════════════════════════════
-- P5.1a [easy]: N₂(x)(y) = x^b · N₁(x)(y)
-- ═══════════════════════════════════════════════════

/-- The shifted spread operator differs by a scalar: N₂(x)(y) = x^b · N₁(x)(y). -/
lemma spread_shift_scalar
    (L : F → F) (k b : ℕ) (x y : F) :
    L (x * y) * x ^ (k + b) = (L (x * y) * x ^ k) * x ^ b := by sorry
-- Proof: pow_add, mul_assoc.

-- ═══════════════════════════════════════════════════
-- P5.1b [easy]: x^b commutes with L(xy)·x^k when x^b ∈ GF(p)
-- ═══════════════════════════════════════════════════

/-- Since x^b ∈ GF(p)*, it commutes with everything (being a scalar). -/
lemma gfp_scalar_commutes {c : F} (hc : c ^ p = c) (a : F) :
    c * a = a * c :=
  mul_comm c a
-- (Trivially true since F is commutative. But noting it for documentation.)

-- ═══════════════════════════════════════════════════
-- P5.1 [easy]: Define φ
-- ═══════════════════════════════════════════════════

/-- **Definition of the rescaling bijection φ.**

For char 2: φ = id (since x^b = 1 for all x ≠ 0).
For general p: φ(x) = x · d(x) where d(x) = (x^b)^{-1/(b+k+1)}.

For the general case, define φ using noncomputable inverse: -/
noncomputable def phi_rescale (L : F → F) (k b : ℕ)
    (hcop : Nat.Coprime (b + k + 1) (p - 1))
    (hb : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b) : F → F := by sorry
-- For char 2: fun x => x (identity).
-- For general p: needs more care.

-- ═══════════════════════════════════════════════════
-- P5.2 [easy]: φ is bijective
-- ═══════════════════════════════════════════════════

/-- φ is bijective. For char 2: identity is bijective.
    For general p: φ(x) = x · d(x) where x ↦ d(x) is a power map, so
    φ(x) = x^{1 + some_power}, which is bijective by coprimality. -/
lemma phi_rescale_bijective (L : F → F) (k b : ℕ)
    (hcop : Nat.Coprime (b + k + 1) (p - 1))
    (hb : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b) :
    Function.Bijective (phi_rescale p L k b hcop hb) := by sorry

-- ═══════════════════════════════════════════════════
-- P5.3 [meh]: Power identity for φ
-- ═══════════════════════════════════════════════════

/-- The key power identity: φ(x)^{k+b} = x^k / x^0 = x^k (after rescaling). -/
-- This is the heart: we need L(φ(x)y)·φ(x)^{k+b} = L(xy)·x^k.
-- Which means: φ(x)^{k+b} · L(φ(x)y) = x^k · L(xy).
-- If L is GF(p)-linear and φ(x) = x·d with d ∈ GF(p):
-- L(φ(x)y) = L(x·d·y) = d·L(xy) (GF(p)-linearity).
-- φ(x)^{k+b} = (xd)^{k+b} = x^{k+b}·d^{k+b}.
-- So LHS = d^{k+b+1}·x^{k+b}·L(xy) = d^{k+b+1}·x^k·x^b·L(xy).
-- Need d^{k+b+1}·x^b = 1, i.e., d = (x^b)^{-1/(k+b+1)}.
-- This is well-defined when gcd(k+b+1, p-1) = 1 (since d ∈ GF(p)*).

-- For char 2: d = 1 (since x^b = 1), and 1^{k+b+1} · 1 = 1. ✓

lemma phi_power_identity (L : F → F) (k b : ℕ)
    (hL_comm : ∀ (c x : F), c ^ p = c → L (c * x) = c * L x)
    (hb : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
    (hcop : Nat.Coprime (b + k + 1) (p - 1))
    (x y : F) (hx : x ≠ 0) :
    L (phi_rescale p L k b hcop hb x * y) * (phi_rescale p L k b hcop hb x) ^ (k + b) =
    L (x * y) * x ^ k := by sorry

-- ═══════════════════════════════════════════════════
-- P5.4 [meh]: Spread element equality (including x = 0)
-- ═══════════════════════════════════════════════════

/-- For all x (including 0) and all y:
    N₂(φ(x))(y) = N₁(x)(y). -/
lemma spread_element_equality (L : F → F)
    (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL_comm : ∀ (c x : F), c ^ p = c → L (c * x) = c * L x)
    (k b : ℕ)
    (hb : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
    (hcop : Nat.Coprime (b + k + 1) (p - 1))
    (x y : F) :
    L (phi_rescale p L k b hcop hb x * y) * (phi_rescale p L k b hcop hb x) ^ (k + b) =
    L (x * y) * x ^ k := by sorry
-- Proof: If x ≠ 0: phi_power_identity.
-- If x = 0: φ(0) = 0 (or whatever φ is defined to be at 0),
-- and both sides are 0 (L(0·y) = L(0) = 0, 0^k = 0).

-- ═══════════════════════════════════════════════════
-- Assembly [meh]: prop_3_5_abstract
-- ═══════════════════════════════════════════════════

-- Note: The statement in Prop35.lean uses SpreadSetsEquivalent which
-- requires ∃ φ bij ∧ ∀ x y, N₂(φ(x))(y) = N₁(x)(y).
-- We provide φ = phi_rescale, prove it's bij (P5.2), and prove
-- the element equality (P5.4).

-- **Proposition 3.5 (abstract).** Spread sets from L·X^k and L·X^{k+b} are equivalent.
--
-- Note: The existing statement in Prop35.lean does NOT include the coprimality
-- hypothesis on b+k+1. This may need to be added, or the proof may work
-- with a different choice of φ that avoids this condition.
-- theorem prop_3_5_abstract_skeleton : ... := by sorry

-- ═══════════════════════════════════════════════════
-- CHAR 2 SPECIALIZATION [easy]: Much simpler
-- ═══════════════════════════════════════════════════

/-- **Char 2 specialization.** In char 2, x^b = 1 for all nonzero x (since GF(2)* = {1}).
    So N₂(x)(y) = N₁(x)(y) for all x, y. Take φ = id. -/
lemma prop_3_5_char2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (k b : ℕ) (hk_pos : 0 < k) (hb_pos : 0 < b)
    (hb : ∀ x : F, x ≠ 0 → (x ^ b) ^ 2 = x ^ b) :
    ∃ φ : F → F, Function.Bijective φ ∧
      ∀ x y, L (φ x * y) * (φ x) ^ (k + b) = L (x * y) * x ^ k := by sorry
-- Proof: Take φ = id. Bijective: trivially.
-- For x = 0: both sides are 0.
-- For x ≠ 0: x^b = 1 (pow_eq_one_of_frob_fixed_char2).
-- L(xy)·x^{k+b} = L(xy)·x^k·x^b = L(xy)·x^k·1 = L(xy)·x^k. ✓

end DempwolffMueller
