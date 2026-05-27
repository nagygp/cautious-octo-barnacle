import Mathlib
import RequestProject.LinPoly
import RequestProject.Prop21
import RequestProject.TraceNorm

/-!
# Foundational Layer F5: Spread Set and Translation Plane Theory

The formal theory of spread sets and their associated translation planes,
specialized to the `L(X)·X^k` construction.

## Main results

1. **Spread set definition** (F5.1): `Σ = {N(x) | x ∈ F}` where
   `N(x)(y) = L(x·y) · x^k`.
2. **Spread condition** (F5.2): `Σ` is a spread set iff `N(x) - N(y)`
   is invertible for all `x ≠ y`.
3. **Dual spread** (F5.3): `Σ* = {N(x)* | x ∈ F}`.
4. **Isomorphism criterion** (F5.4): Classification of isomorphisms
   between spread sets.

## DAG structure

```
  LinPoly (F4) + Prop21 + TraceNorm (F2)
    │
    ├──► F5.1 (spread set definition)
    │      │
    │      └──► F5.2 (spread condition)
    │
    ├──► F5.3 (dual spread)
    │
    └──► F5.4 (isomorphism criterion)
```

**Dependencies:** LinPoly, Prop21, TraceNorm, Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- F5.1 : Spread set definition
-- ═══════════════════════════════════════════

/-- A **spread set** is a collection of GF(p)-linear endomorphisms `{N(x) | x ∈ F}`
    indexed by `F`, satisfying certain regularity conditions. -/
structure SpreadSet where
  /-- The indexed family of operators `N(x) : F → F`. -/
  N : F → F → F
  /-- Each `N(x)` is additive. -/
  N_add : ∀ x a b, N x (a + b) = N x a + N x b
  /-- `N(0) = 0` (the zero operator). -/
  N_zero : ∀ y, N 0 y = 0
  /-- For `x ≠ y`, `N(x) - N(y)` is bijective. -/
  N_diff_bij : ∀ x y, x ≠ y →
    Function.Bijective (fun z => N x z - N y z)

/-- The spread set from the `L(X)·X^k` construction.
    `N(x)(y) = L(x·y) · x^k`. -/
noncomputable def spreadSetFromPoly
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ) : F → F → F :=
  fun x y => additivePolyEval p n_dim coeffs (x * y) * x ^ k

/-- The spread set operator is additive in y (since L is additive). -/
lemma spreadSetFromPoly_add (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (x a b : F) :
    spreadSetFromPoly p n_dim coeffs k x (a + b) =
    spreadSetFromPoly p n_dim coeffs k x a +
    spreadSetFromPoly p n_dim coeffs k x b := by
  simp [spreadSetFromPoly, mul_add, additivePolyEval_add, add_mul]

/-- N(0)(y) = 0. -/
lemma spreadSetFromPoly_zero (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (y : F) (hk : 0 < k) :
    spreadSetFromPoly p n_dim coeffs k 0 y = 0 := by
  simp [spreadSetFromPoly, zero_mul, additivePolyEval_zero, zero_pow hk.ne']

/-
═══════════════════════════════════════════
F5.2 : Spread condition
═══════════════════════════════════════════

**Spread condition.**
    `{N(x)}` is a spread set iff `L(X)·X^k` is a permutation polynomial.
    More precisely, `N(x) - N(y)` bijective for all `x ≠ y` is equivalent to
    `P(z) = L(z)·z^k` being injective.
-/
lemma spread_condition_iff_perm_poly
    (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ)
    (hL_bij : Function.Bijective (additivePolyEval p n_dim coeffs)) :
    (∀ x y : F, x ≠ y →
      Function.Bijective (fun z =>
        spreadSetFromPoly p n_dim coeffs k x z -
        spreadSetFromPoly p n_dim coeffs k y z)) ↔
    Function.Injective (fun z : F =>
      additivePolyEval p n_dim coeffs z * z ^ k) := by
        constructor <;> intro h;
        · intro z₁ z₂ h_eq;
          by_contra h_neq;
          have := h z₁ z₂ h_neq;
          have := this.1 ( show spreadSetFromPoly p n_dim coeffs k z₁ 1 - spreadSetFromPoly p n_dim coeffs k z₂ 1 = spreadSetFromPoly p n_dim coeffs k z₁ 0 - spreadSetFromPoly p n_dim coeffs k z₂ 0 from ?_ ) ; simp_all +decide [ spreadSetFromPoly ] ;
          unfold spreadSetFromPoly; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
          rw [ additivePolyEval_zero' ] ; ring;
        · intro x y hxy
          have h_diff : ∀ z : F, spreadSetFromPoly p n_dim coeffs k x z - spreadSetFromPoly p n_dim coeffs k y z = additivePolyEval p n_dim coeffs (x * z) * x ^ k - additivePolyEval p n_dim coeffs (y * z) * y ^ k := by
            exact fun z => rfl;
          have h_inj : ∀ z : F, z ≠ 0 → additivePolyEval p n_dim coeffs (x * z) * x ^ k - additivePolyEval p n_dim coeffs (y * z) * y ^ k ≠ 0 := by
            intro z hz h_eq
            have h_contra : additivePolyEval p n_dim coeffs (x * z) * (x * z) ^ k = additivePolyEval p n_dim coeffs (y * z) * (y * z) ^ k := by
              convert congr_arg ( · * z ^ k ) ( eq_of_sub_eq_zero h_eq ) using 1 <;> ring;
            have := @h ( x * z ) ( y * z ) ; simp_all +decide [ mul_pow, sub_eq_iff_eq_add ] ;
          have h_inj : Function.Injective (fun z : F => additivePolyEval p n_dim coeffs (x * z) * x ^ k - additivePolyEval p n_dim coeffs (y * z) * y ^ k) := by
            intro z₁ z₂ h_eq
            by_contra h_neq
            have h_neq' : z₁ - z₂ ≠ 0 := by
              exact sub_ne_zero_of_ne h_neq
            have h_neq'' : additivePolyEval p n_dim coeffs (x * (z₁ - z₂)) * x ^ k - additivePolyEval p n_dim coeffs (y * (z₁ - z₂)) * y ^ k = 0 := by
              have := additivePolyEval_add' p n_dim coeffs ( x * z₂ ) ( x * ( z₁ - z₂ ) ) ; have := additivePolyEval_add' p n_dim coeffs ( y * z₂ ) ( y * ( z₁ - z₂ ) ) ; simp_all +decide [ mul_sub, sub_mul ] ;
              grind
            exact h_inj (z₁ - z₂) h_neq' h_neq'';
          exact ⟨ by simpa only [ h_diff ] using h_inj, Finite.injective_iff_surjective.mp ( by simpa only [ h_diff ] using h_inj ) ⟩

-- ═══════════════════════════════════════════
-- F5.3 : Dual spread (trace-adjoint)
-- ═══════════════════════════════════════════

/-- The **dual spread** is obtained by taking the trace-adjoint of each operator. -/
noncomputable def dualSpreadSet {n_dim : ℕ}
    (hn : Fintype.card F = p ^ n_dim)
    (N : F → F → F)
    (Nadj : F → F → F)
    (_hAdj : ∀ x w z, frobSum p n_dim (N x w * z) = frobSum p n_dim (w * Nadj x z)) :
    F → F → F :=
  Nadj

-- ═══════════════════════════════════════════
-- F5.4 : Isomorphism of spread sets
-- ═══════════════════════════════════════════

/-- Two spread sets are **isomorphic** if there exist bijective
    semilinear operators relating them. -/
def SpreadSetIsomorphic (N₁ N₂ : F → F → F) : Prop :=
  ∃ (A B : F → F),
    Function.Bijective A ∧ Function.Bijective B ∧
    (∀ a b, A (a + b) = A a + A b) ∧
    (∀ a b, B (a + b) = B a + B b) ∧
    ∃ φ : F → F, Function.Bijective φ ∧
      ∀ x y, A (N₁ x y) = N₂ (φ x) (B y)

end DempwolffMueller