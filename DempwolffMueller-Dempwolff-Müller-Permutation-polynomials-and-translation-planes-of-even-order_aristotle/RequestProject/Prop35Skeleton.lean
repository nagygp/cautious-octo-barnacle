import Mathlib

/-!
# Skeleton: Proposition 3.5 — Spread Set Equivalence — Sub-lemma DAG

Decomposes `prop_3_5_abstract` (Prop35.lean:78) into tiny lemmas.

## Goal
If `x^b ∈ GF(p)` for all nonzero x, and L commutes with GF(p)-scalars,
then `L(X)·X^k` and `L(X)·X^{k+b}` define equivalent spread sets.

## Proof Sketch
The spread set from P(x) = L(x)·x^k has operators N(x)(y) = L(xy)·x^k.
The spread set from P'(x) = L(x)·x^{k+b} has N'(x)(y) = L(xy)·x^{k+b}.
We need φ : F → F bijective with N'(φ(x))(y) = N(x)(y) for all x, y.

Since x^b ∈ GF(p), we have N'(x)(y) = L(xy)·x^k·x^b = N(x)(y)·x^b.
The idea is: set φ(x) = x·(x^b)^{-1/(k+1)} or similar rescaling.
But more precisely, we want L(φ(x)·y)·φ(x)^{k+b} = L(xy)·x^k.

If we set φ(x) = x·c(x)⁻¹ where c(x) = (x^b)^{1/(k+1)}, then
φ(x)^{k+b} = x^{k+b}·c(x)^{-(k+b)} and
L(φ(x)·y) = L(x·c(x)⁻¹·y) = c(x)⁻¹·L(xy) (GF(p)-linearity).
So N'(φ(x))(y) = c(x)⁻¹·L(xy)·x^{k+b}·c(x)^{-(k+b)}.
For this to equal N(x)(y) = L(xy)·x^k, we need:
c(x)⁻¹·x^{k+b}·c(x)^{-(k+b)} = x^k, i.e., c(x)^{-(k+b+1)} = x^{-b}.
So c(x)^{k+b+1} = x^b, i.e., c(x) = (x^b)^{1/(k+b+1)}.
But x^b ∈ GF(p), so c(x) ∈ GF(p)^{1/(k+b+1)}.
For this to be well-defined, we need k+b+1 coprime to p-1 = |GF(p)*|.

Actually, there's a much simpler argument: since x^b ∈ GF(p)* for x ≠ 0,
define φ(x) = x · g(x) where g(x) is chosen so that the equation works out.
But actually the simplest construction is:

For the SAME spread set (not just equivalent), we note that
N'(x)(y) = L(xy)·x^{k+b} = L(xy)·x^k · x^b = N(x)(y) · x^b.
So N'(x) = x^b · N(x) (scalar multiplication by x^b ∈ GF(p)).
Since multiplying by a nonzero scalar is a bijection that preserves
the spread condition, we get isomorphic spread sets.

More precisely: φ = id, and A = multiplication by x^b, B = id satisfies
A(N(x)(y)) = x^b · N(x)(y) = N'(x)(y).

Wait, but that's not quite right because x^b depends on x, not on y.
The SpreadSetsEquivalent condition asks for ∃ φ : F → F bijective with
N₂(φ(x))(y) = N₁(x)(y) for all x, y.

So we need: L(φ(x)·y)·φ(x)^{k+b} = L(xy)·x^k.

Let's try φ(x) = x·(x^{-b})^{1/(k+1)} when k+1 is coprime to |F|-1...
This is getting complex. Let's decompose.

## DAG

```
  P35.1 (scalar factorization)       [easy]
    │
    ├──► P35.2 (GF(p)-linearity)      [easy]
    │
    ├──► P35.3 (power map root)       [meh]
    │
    ├──► P35.4 (rescaling definition) [meh]
    │
    └──► P35.5 (verify spread equiv)  [hard]
           │
           └──► prop_3_5_abstract
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- P35.1 [easy]: Factorization L(xy)·x^{k+b} = L(xy)·x^k · x^b
-- ═══════════════════════════════════════════

lemma spread_shift_factor (L : F → F) (k b : ℕ) (x y : F) :
    L (x * y) * x ^ (k + b) = L (x * y) * x ^ k * x ^ b := by sorry
-- Difficulty: easy
-- Proof: pow_add, mul_assoc.

-- ═══════════════════════════════════════════
-- P35.2 [easy]: x^b · L(z) = L(x^b · z) when x^b ∈ GF(p)
-- ═══════════════════════════════════════════

lemma gfp_scalar_comm_L (L : F → F)
    (hL_comm : ∀ (c x : F), c ^ p = c → L (c * x) = c * L x)
    {c : F} (hc : c ^ p = c) (z : F) :
    L (c * z) = c * L z := hL_comm c z hc
-- Difficulty: easy (literally the hypothesis)

-- ═══════════════════════════════════════════
-- P35.3 [meh]: For nonzero x, x^{b·p} = x^b
-- ═══════════════════════════════════════════

lemma pow_b_frob_eq (b : ℕ) {x : F} (hx : x ≠ 0)
    (hfixed : (x ^ b) ^ p = x ^ b) :
    x ^ (b * p) = x ^ b := by sorry
-- Difficulty: meh
-- Proof: rewrite pow_mul, then hfixed.

-- ═══════════════════════════════════════════
-- P35.4 [meh]: The rescaling map definition and bijectivity
-- ═══════════════════════════════════════════

-- The rescaling φ depends on being able to solve c^{k+1} = x^{-b} in GF(p).
-- This requires gcd(k+1, p-1) = 1 (or similar coprimality).
-- For the abstract formulation, we may need to add this as a hypothesis,
-- OR use a different construction.

-- Alternative simpler approach: show that there EXISTS some bijection φ
-- making the identity work, without constructing it explicitly.
-- This uses the fact that both spread sets define the same translation plane.

-- ═══════════════════════════════════════════
-- P35.5 [hard]: Main spread equivalence
-- ═══════════════════════════════════════════

/-- The identity `N'(φ(x))(y) = N(x)(y)` for the appropriate φ.

    For the actual proof, we may need to construct φ explicitly or
    argue indirectly. The key identity to verify is:
    L(φ(x)·y) · φ(x)^{k+b} = L(x·y) · x^k.

    With the substitution φ(x) = x · (x^b)^{-1/(k+b+1)} (when this root exists):
    - L(φ(x)·y) = L(x·c⁻¹·y) = c⁻¹·L(xy) where c = (x^b)^{1/(k+b+1)}
    - φ(x)^{k+b} = (x·c⁻¹)^{k+b} = x^{k+b}·c^{-(k+b)}
    - Product: c⁻¹·L(xy)·x^{k+b}·c^{-(k+b)} = L(xy)·x^{k+b}·c^{-(k+b+1)}
    - We need c^{k+b+1} = x^b, which is exactly the definition of c.
    - So the product = L(xy)·x^{k+b}·x^{-b} = L(xy)·x^k. ✓
-/
lemma spread_equiv_construction
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (k b : ℕ)
    (hb : ∀ (x : F), x ≠ 0 → (x ^ b) ^ p = x ^ b)
    (hL_comm : ∀ (c x : F), c ^ p = c → L (c * x) = c * L x)
    -- Additional hypothesis needed: existence of (k+b+1)-th root in GF(p)
    -- or alternatively gcd(k+b+1, p-1) divides certain things
    :
    ∃ φ : F → F, Function.Bijective φ ∧
      ∀ x y, L (φ x * y) * φ x ^ (k + b) = L (x * y) * x ^ k := by sorry
-- Difficulty: hard

end DempwolffMueller
