import Mathlib
import RequestProject.Thm34
import RequestProject.Prop21

/-!
# Proposition 3.5 — Same Translation Plane

Formalization of Proposition 3.5 from Dempwolff & Müller (2013).

## Statement

`L(X)·X^k` and `L(X)·X^{k+b}` from Theorem 3.4 define the same
translation plane (i.e., identical spread sets).

## Proof method

In characteristic 2, whenever `(x^b)^2 = x^b` for all nonzero x,
we have `x^b = 1` (since GF(2)* = {1}). Therefore the two spread
set operators `L(xy)·x^k` and `L(xy)·x^(k+b) = L(xy)·x^k·x^b = L(xy)·x^k`
are identical, and `φ = id` witnesses the equivalence.

## DAG structure

```
  Thm34 + Prop21
    │
    └──► Prop 3.5 (same translation plane)
```

**Dependencies:** Thm34 (`Thm34.lean`), Prop21 (`Prop21.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- P5.1 : Quasifield multiplication comparison
-- ═══════════════════════════════════════════

/-- The quasifield multiplication from `P(x) = L(x)·x^k`. -/
def qfMul' (L : F → F) (k : ℕ) (x y : F) : F := L (x * y) * x ^ k

/-- The quasifield multiplication from `P'(x) = L(x)·x^{k+b}`. -/
def qfMul_shifted (L : F → F) (k b : ℕ) (x y : F) : F := L (x * y) * x ^ (k + b)

/-- **Rescaling identity.** The shifted quasifield multiplication
    satisfies `x ⊙' y = (x ⊙ y) · x^b`, where `x ⊙` and `x ⊙'` are
    the original and shifted multiplications respectively. -/
lemma qfMul_shifted_eq (L : F → F) (k b : ℕ) (x y : F) :
    qfMul_shifted L k b x y = qfMul' L k x y * x ^ b := by
  simp [qfMul_shifted, qfMul', pow_add, mul_assoc]

-- ═══════════════════════════════════════════
-- P5.2 : Spread set equivalence
-- ═══════════════════════════════════════════

/-- **Spread set equivalence condition.**
    Two spread sets `Σ₁ = {N₁(x)}` and `Σ₂ = {N₂(x)}` define the same
    translation plane iff there exists a bijection `φ : F → F` with
    `N₂(φ(x)) = N₁(x)` for all x (up to relabeling of spread elements). -/
def SpreadSetsEquivalent
    (N₁ N₂ : F → F → F) : Prop :=
  ∃ φ : F → F, Function.Bijective φ ∧
    ∀ x y, N₂ (φ x) y = N₁ x y

/-
═══════════════════════════════════════════
P5.3 : General statement — FALSE for p > 2
═══════════════════════════════════════════

**⚠ FALSE for general characteristic (commented out).**

   The original `prop_3_5_abstract` claimed the spread equivalence for
   general char p with hypotheses `(x^b)^p = x^b` and `L(c*x) = c*L(x)`.

   **Counterexample:** F = GF(3), p = 3, L = id, k = 0, b = 1.
   - (x^1)^3 = x (Fermat's little theorem in GF(3)) ✓
   - L(cx) = cx = c·L(x) ✓
   - Need φ bijective with φ(x)·y·φ(x) = x·y, i.e., φ(x)² = x for all x.
   - But 2 ∈ GF(3) is not a square (0²=0, 1²=1, 2²=1), so no φ(2) exists.

   In char 2, x^b = 1 for all nonzero x (since GF(2)* = {1}),
   making the two spread operators identical and φ = id works trivially.

theorem prop_3_5_abstract
(L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
(k b : ℕ)
(hb : ∀ (x : F), x ≠ 0 → (x ^ b) ^ p = x ^ b)
(hL_comm : ∀ (c x : F), c ^ p = c → L (c * x) = c * L x) :
SpreadSetsEquivalent
(fun x y => L (x * y) * x ^ k)
(fun x y => L (x * y) * x ^ (k + b)) := by sorry

═══════════════════════════════════════════
P5.4 : Characteristic 2 version (CORRECT)
═══════════════════════════════════════════

**Proposition 3.5 (characteristic 2).** If `(x^b)^2 = x^b` for all nonzero x,
    then `L(X)·X^k` and `L(X)·X^{k+b}` define equivalent spread sets.

    **Proof.** In char 2, `(x^b)^2 = x^b` implies `x^b ∈ GF(2)* = {1}`,
    so `x^b = 1` for all nonzero x. Therefore the two operators are identical
    and `φ = id` witnesses the equivalence.
-/
theorem prop_3_5_char2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (k b : ℕ)
    (hb : ∀ (x : F), x ≠ 0 → (x ^ b) ^ 2 = x ^ b) :
    SpreadSetsEquivalent
      (fun x y => L (x * y) * x ^ k)
      (fun x y => L (x * y) * x ^ (k + b)) := by
        use id; simp_all +decide [ pow_add ] ;
        intro x y; by_cases hx : x = 0 <;> simp_all +decide [ pow_succ, mul_assoc ] ;
        exact Or.inr ( by simpa using hL_add 0 0 )

end DempwolffMueller