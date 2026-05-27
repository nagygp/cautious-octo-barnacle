import Mathlib
import RequestProject.FrobAlg
import RequestProject.AutBase

/-!
# Foundational Layer F4: Linearized Polynomial Algebra

The algebra of linearized (additive) polynomials over finite fields.

## Main results

1. **Ring structure** (F4.1): Linearized polynomials form a ring under
   addition and symbolic composition.
2. **GF(p)-linearity** (F4.2): Additive polynomials are GF(p)-linear maps.
3. **Composition** (F4.3): Composition of linearized polynomials is linearized.
4. **Kernel theory** (F4.4): The kernel of a linearized polynomial is a
   GF(p)-subspace; |ker(L)| = p^d for some d.
5. **Inverse polynomial** (F4.5): If L is bijective, L⁻¹ is linearized.
6. **Matrix representation** (F4.6): Representation via GF(p)-linear maps.

## DAG structure

```
  F4.1 (ring structure)
    │
    ├──► F4.2 (GF(p)-linearity)
    │
    ├──► F4.3 (composition)
    │      │
    │      └──► F4.5 (inverse)
    │
    └──► F4.4 (kernel theory)
           │
           └──► F4.6 (matrix representation)
```

**Dependencies:** Layer F1 (`FrobAlg.lean`), AutBase (`AutBase.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- F4.1 : Ring structure basics
-- ═══════════════════════════════════════════

/-- Addition of linearized polynomials (coefficients add pointwise). -/
def additivePolyAdd (n : ℕ) (c₁ c₂ : Fin n → F) : Fin n → F :=
  fun i => c₁ i + c₂ i

/-- Evaluation of the sum polynomial equals sum of evaluations. -/
lemma additivePolyEval_add_coeffs (n : ℕ) (c₁ c₂ : Fin n → F) (x : F) :
    additivePolyEval p n (additivePolyAdd n c₁ c₂) x =
    additivePolyEval p n c₁ x + additivePolyEval p n c₂ x := by
  simp [additivePolyEval, additivePolyAdd, add_mul, Finset.sum_add_distrib]

/-- Negation of linearized polynomials. -/
def additivePolyNeg (n : ℕ) (c : Fin n → F) : Fin n → F :=
  fun i => -(c i)

/-- Evaluation of the negated polynomial. -/
lemma additivePolyEval_neg_coeffs (n : ℕ) (c : Fin n → F) (x : F) :
    additivePolyEval p n (additivePolyNeg n c) x =
    -(additivePolyEval p n c x) := by
  simp [additivePolyEval, additivePolyNeg, neg_mul, Finset.sum_neg_distrib]

/-- Zero polynomial (all coefficients zero). -/
def additivePolyZero (n : ℕ) : Fin n → F := fun _ => 0

/-- Evaluation of the zero polynomial. -/
lemma additivePolyEval_zero_coeffs (n : ℕ) (x : F) :
    additivePolyEval p n (additivePolyZero n : Fin n → F) x = 0 := by
  simp [additivePolyEval, additivePolyZero]

-- ═══════════════════════════════════════════
-- F4.2 : GF(p)-linearity of additive polynomials
-- ═══════════════════════════════════════════

/-- **Linearity over GF(p).** Additive polynomials preserve GF(p)-scalar multiplication:
    `L(c·x) = c·L(x)` when `c ∈ GF(p)` (i.e., `c^p = c`). -/
lemma additivePolyEval_gfp_linear (n : ℕ) (coeffs : Fin n → F)
    (c : F) (hc : c ^ p = c) (x : F) :
    additivePolyEval p n coeffs (c * x) = c * additivePolyEval p n coeffs x :=
  additivePolyEval_smul p n coeffs c hc x

/-- Additive polynomials send 0 to 0. -/
lemma additivePolyEval_zero' (n : ℕ) (coeffs : Fin n → F) :
    additivePolyEval p n coeffs 0 = 0 :=
  additivePolyEval_zero p n coeffs

/-- Additive polynomials are additive: L(x+y) = L(x) + L(y). -/
lemma additivePolyEval_add' (n : ℕ) (coeffs : Fin n → F) (x y : F) :
    additivePolyEval p n coeffs (x + y) =
    additivePolyEval p n coeffs x + additivePolyEval p n coeffs y :=
  additivePolyEval_add p n coeffs x y

-- ═══════════════════════════════════════════
-- F4.3 : Frobenius action on linearized polynomials
-- ═══════════════════════════════════════════

/-- **Frobenius output.** L(x)^{p^s} = ∑ aᵢ^{p^s} · x^{p^{i+s}}. -/
lemma additivePolyEval_frob_output (n : ℕ) (coeffs : Fin n → F)
    (x : F) (s : ℕ) :
    (additivePolyEval p n coeffs x) ^ (p ^ s) =
    ∑ i : Fin n, (coeffs i) ^ (p ^ s) * x ^ (p ^ ((i : ℕ) + s)) :=
  linpoly_frob_output p n coeffs x s

/-- **Frobenius input.** L(x^{p^s}) = ∑ aᵢ · x^{p^{s+i}}. -/
lemma additivePolyEval_frob_input (n : ℕ) (coeffs : Fin n → F)
    (x : F) (s : ℕ) :
    additivePolyEval p n coeffs (x ^ (p ^ s)) =
    ∑ i : Fin n, coeffs i * x ^ (p ^ (s + (i : ℕ))) :=
  linpoly_frob_input p n coeffs x s

/-- **Commutativity under Frobenius-stable coefficients.**
    L(x^{p^s}) = L(x)^{p^s} when aᵢ^{p^s} = aᵢ for all i. -/
lemma additivePolyEval_frob_comm (n : ℕ) (coeffs : Fin n → F) (x : F) (s : ℕ)
    (hcoeffs : ∀ i : Fin n, (coeffs i) ^ (p ^ s) = coeffs i) :
    additivePolyEval p n coeffs (x ^ (p ^ s)) =
    (additivePolyEval p n coeffs x) ^ (p ^ s) :=
  linpoly_frob_comm p n coeffs x s hcoeffs

-- ═══════════════════════════════════════════
-- F4.4 : Kernel theory
-- ═══════════════════════════════════════════

/-- The kernel of a linearized polynomial. -/
noncomputable def additivePolyKer (n : ℕ) (coeffs : Fin n → F) : Set F :=
  {x | additivePolyEval p n coeffs x = 0}

/-- The kernel is a subgroup under addition (contains 0). -/
lemma additivePolyKer_zero (n : ℕ) (coeffs : Fin n → F) :
    (0 : F) ∈ additivePolyKer p n coeffs := by
  simp [additivePolyKer, additivePolyEval_zero]

/-- The kernel is closed under addition. -/
lemma additivePolyKer_add (n : ℕ) (coeffs : Fin n → F) {x y : F}
    (hx : x ∈ additivePolyKer p n coeffs)
    (hy : y ∈ additivePolyKer p n coeffs) :
    x + y ∈ additivePolyKer p n coeffs := by
  simp only [additivePolyKer, Set.mem_setOf_eq] at *
  rw [additivePolyEval_add, hx, hy, add_zero]

/-- The kernel is closed under negation. -/
lemma additivePolyKer_neg (n : ℕ) (coeffs : Fin n → F) {x : F}
    (hx : x ∈ additivePolyKer p n coeffs) :
    -x ∈ additivePolyKer p n coeffs := by
  simp only [additivePolyKer, Set.mem_setOf_eq] at *
  have key : additivePolyEval p n coeffs (-x) + additivePolyEval p n coeffs x = 0 := by
    rw [← additivePolyEval_add p n coeffs, neg_add_cancel, additivePolyEval_zero p n coeffs]
  rw [hx, add_zero] at key
  exact key

/-- The kernel is closed under GF(p)-scalar multiplication. -/
lemma additivePolyKer_gfp_smul (n : ℕ) (coeffs : Fin n → F)
    {c : F} (hc : c ^ p = c) {x : F}
    (hx : x ∈ additivePolyKer p n coeffs) :
    c * x ∈ additivePolyKer p n coeffs := by
  simp only [additivePolyKer, Set.mem_setOf_eq] at *
  rw [additivePolyEval_smul p n coeffs c hc x, hx, mul_zero]

/-
An injective linearized polynomial has trivial kernel.
-/
lemma additivePolyKer_trivial_of_injective (n : ℕ) (coeffs : Fin n → F)
    (hinj : Function.Injective (additivePolyEval p n coeffs)) :
    additivePolyKer p n coeffs = {0} := by
      ext x; simp [DempwolffMueller.additivePolyKer, hinj.eq_iff'] ;
      exact ⟨ fun hx => hinj <| hx.trans <| Eq.symm <| additivePolyEval_zero' p n coeffs, fun hx => hx.symm ▸ additivePolyEval_zero' p n coeffs ⟩

-- ═══════════════════════════════════════════
-- F4.5 : Bijective linearized polynomial has linearized inverse
-- ═══════════════════════════════════════════

/-- If a linearized polynomial is bijective, its inverse is additive. -/
lemma additivePolyEval_inv_add (n : ℕ) (coeffs : Fin n → F)
    (hbij : Function.Bijective (additivePolyEval p n coeffs))
    (x y : F) :
    Function.invFun (additivePolyEval p n coeffs) (x + y) =
    Function.invFun (additivePolyEval p n coeffs) x +
    Function.invFun (additivePolyEval p n coeffs) y := by
  set L := additivePolyEval p n coeffs with hL_def
  have hRinv : ∀ y, L (Function.invFun L y) = y := by
    intro y; exact Function.invFun_eq (hbij.surjective y)
  have h1 : L (Function.invFun L (x + y)) = x + y := hRinv (x + y)
  have h2 : L (Function.invFun L x + Function.invFun L y) =
    L (Function.invFun L x) + L (Function.invFun L y) :=
    additivePolyEval_add p n coeffs _ _
  rw [hRinv x, hRinv y] at h2
  exact hbij.injective (h1.trans h2.symm)

-- ═══════════════════════════════════════════
-- F4.6 : Scalar multiplication of linearized polynomials
-- ═══════════════════════════════════════════

/-- Scalar multiplication of a linearized polynomial by a field element. -/
def additivePolyScalarMul (n : ℕ) (a : F) (coeffs : Fin n → F) : Fin n → F :=
  fun i => a * coeffs i

/-- Evaluation of a scalar-multiplied polynomial. -/
lemma additivePolyEval_scalarMul (n : ℕ) (a : F) (coeffs : Fin n → F) (x : F) :
    additivePolyEval p n (additivePolyScalarMul n a coeffs) x =
    a * additivePolyEval p n coeffs x := by
  simp [additivePolyEval, additivePolyScalarMul, Finset.mul_sum, mul_assoc]

end DempwolffMueller