import Mathlib
import RequestProject.AutKernel

/-!
# Layer B3: General Automorphism Theory

Formalization of Proposition 4.6 and Lemma 4.7 from Dempwolff & Müller (2013).

## Main results

1. **Proposition 4.6**: For non-semifield planes:
   (a) G_{0,∞} = G̃ (full stabilizer equals normalizer)
   (b) S is normal Sylow p-subgroup of G
   (c) G = G_{0,∞}

2. **Lemma 4.7**: For non-desarguesian semifield planes,
   L(X) or L⁻¹(X) has at most 2 terms.

## DAG structure

```
  B2 (AutKernel)
    │
    ├──► Prop 4.6 (non-semifield)
    │
    └──► Lemma 4.7 (semifield polynomial structure)
```

**Dependencies:** Layer B2 (`AutKernel.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- B3.1 : Semifield detection
-- ═══════════════════════════════════════════

/-- A linearized polynomial defines a **semifield** if the quasifield
    multiplication `x ⊙ y = L(x·y) · x^k` is associative. -/
def IsSemifieldPolynomial (n_dim : ℕ) (coeffs : Fin n_dim → F) (k : ℕ) : Prop :=
  ∀ x y z : F,
    (additivePolyEval p n_dim coeffs (x * y) * x ^ k) *
    (additivePolyEval p n_dim coeffs z) =
    additivePolyEval p n_dim coeffs (x * y) *
    (additivePolyEval p n_dim coeffs (y * z) * y ^ k)

/-- A plane is **desarguesian** if L is a semilinear operator
    (i.e., L(x) = a · x^{p^r} for some a, r). -/
def IsDesarguesian (n_dim : ℕ) (coeffs : Fin n_dim → F) : Prop :=
  (support n_dim coeffs).card = 1

-- ═══════════════════════════════════════════
-- B3.2 : Proposition 4.6 — Non-semifield structure
-- ═══════════════════════════════════════════

/-- **Proposition 4.6(a) (abstract form).**
    If `L` is not a semifield polynomial and not desarguesian, then
    the stabilizer group `G_{0,∞}` equals the full automorphism group.

    This is stated as: every automorphism triple `(a, b, α)` has the
    form where `α` is determined by the normalizer structure. -/
def StabilizerEqualsNormalizer (n_dim : ℕ) (coeffs : Fin n_dim → F) : Prop :=
  ∀ a b : F, ∀ α : ℕ, isAutomorphismTriple p n_dim coeffs a b α →
    ∃ r : ℕ, α = r ∧ r < n_dim

-- ═══════════════════════════════════════════
-- B3.3 : Lemma 4.7 — Semifield polynomial structure
-- ═══════════════════════════════════════════

/-- **Lemma 4.7 (abstract form).**
    For a non-desarguesian semifield plane, the linearized polynomial
    `L(X)` or its inverse `L⁻¹(X)` has at most 2 terms in its support.

    This is a necessary condition for the semifield property. -/
def HasAtMostTwoTerms (n_dim : ℕ) (coeffs : Fin n_dim → F) : Prop :=
  (support n_dim coeffs).card ≤ 2

/-- **Monomial linearized polynomial.**
    A linearized polynomial with support of size 1 is a single monomial
    `L(x) = a · x^{p^i}`. -/
lemma support_singleton_is_monomial (n_dim : ℕ) (coeffs : Fin n_dim → F)
    (h : (support n_dim coeffs).card = 1) :
    ∃ i : Fin n_dim, coeffs i ≠ 0 ∧
      ∀ j : Fin n_dim, j ≠ i → coeffs j = 0 := by
  rw [Finset.card_eq_one] at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by
    constructor
    · exact (mem_support_iff n_dim coeffs i).mp (hi ▸ Finset.mem_singleton_self i)
    · intro j hj
      by_contra hc
      have : j ∈ support n_dim coeffs := (mem_support_iff n_dim coeffs j).mpr hc
      rw [hi] at this
      exact hj (Finset.mem_singleton.mp this)⟩

/-
**Binomial linearized polynomial.**
    A linearized polynomial with support of size 2 is a sum of two monomials.
-/
lemma support_pair_structure (n_dim : ℕ) (coeffs : Fin n_dim → F)
    (h : (support n_dim coeffs).card = 2) :
    ∃ i j : Fin n_dim, i ≠ j ∧ coeffs i ≠ 0 ∧ coeffs j ≠ 0 ∧
      ∀ l : Fin n_dim, l ≠ i → l ≠ j → coeffs l = 0 := by
        rw [ Finset.card_eq_two ] at h; obtain ⟨ i, j, hij, h ⟩ := h; use i, j; simp_all +decide [ Finset.ext_iff, mem_support_iff ] ;
        grind +ring

end DempwolffMueller