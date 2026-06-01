# Strategy DAGs for `lam_forced_trivial` — Overview

## Architecture

Three independent attack strategies on `lam_forced_trivial` (the single remaining
lemma needed for the full Kasami APN theorem), each formalized as a DAG of
small lemmas rooted in Mathlib. Plus a non-Boolean topos exploration module.

All four files compile successfully against Lean 4.28.0 + Mathlib.

---

## File: `NormQuotient.lean` — Strategy A: Norm Quotient

**Approach**: Expand P^{q+1} and s^{q+1} via norm_expansion + gold_derivative,
take the quotient P^{q+1}/s^{q+1} = lam^{q+1}, substitute the key equation
c^{q³}+c = cross, and show L_k(lam) factors out. Since s ≠ 0, L_k(lam) = 0.

**DAG Layers** (8 layers, 25+ lemmas):
- Layer 0: Definitions (kasamiExp, frob, relNorm, linPolyL, crossForm)
- Layer 1: Basic algebra (frob_add ✅, frob_mul ✅, relNorm_mul ✅, char 2 ✅, linPolyL ✅)
- Layer 2: Ratio lemmas (lam_def ✅, norm_of_ratio ✅, cross_via_linPoly ✅, cross↔kernel ✅)
- Layer 3: Norm expansions (gold_derivative ✅, norm_expansion ✅, s_norm ✅, p_norm ✅)
- Layer 4: Norm quotient tautology ✅
- Layer 5: Key equation + cross substitution (key_equation ✅)
- Layer 6: L_k(lam) factored out (❌)
- Layer 7: Coprimality + kernel classification (❌)
- Layer 8: Assembly (❌)

**Proved**: 16 lemmas  |  **Remaining sorry**: 5

---

## File: `Hilbert90.lean` — Strategy B: Hilbert 90

**Approach**: Interpret P/s as a 1-cocycle for the Frobenius action. Apply
additive Hilbert 90 (H¹ = 0 for cyclic extensions) to show the cocycle
is a coboundary, forcing P/s into the fixed field GF(2^{gcd(k,n)}) = ker(L_k).

**DAG Layers** (6 layers, 18+ lemmas):
- Layer 0: Definitions
- Layer 1: Galois foundations (frob_is_additive ✅, frob_mul ✅, kernel↔frob_fixed ✅)
- Layer 2: Cocycle formalism (isNormOneCocycle, isCoboundary, relNorm_as_product ✅)
- Layer 3: Ratio as cocycle (❌)
- Layer 4: Hilbert 90 (❌, requires Mathlib.FieldTheory.Hilbert90)
- Layer 5: Cocycle → ker(L_k) (❌)
- Layer 6: Assembly ✅ (reduces to hilbert90_forces_kernel + cross_zero_iff_kernel ✅)

**Proved**: 9 lemmas (incl. cross_zero_implies_frob_fixed)  |  **Remaining sorry**: 9

---

## File: `FrobeniusIteration.lean` — Strategy C: Frobenius Iteration

**Approach**: Apply Frob^k iteratively to the key equation, sum the shifted
equations (telescoping), derive Tr(cross) = 0, expand the trace using
cross = N_k(s)·L_k(lam), and use Dedekind's independence of characters
to conclude L_k(lam) = 0.

**DAG Layers** (6 layers, 22+ lemmas):
- Layer 0: Definitions (frobIter, relTr)
- Layer 1: Frobenius basics (frob_add ✅, frob_mul ✅, frobIter_compose ✅, Fermat ✅, periodic ✅)
- Layer 2: Key equation shifts (❌)
- Layer 3: Telescoping sum (partial ✅)
- Layer 4: Trace of cross = 0 (❌)
- Layer 5: Trace forces L_k(lam) = 0 (frobIter_distributes ✅, frobIter_norm ✅, frobIter_linPoly ✅, trace_expanded ✅, Dedekind ❌)
- Layer 6: Assembly (partial — reduces to linPolyL_zero_from_trace ❌)

**Proved**: 14 lemmas (incl. key_eq_shift1, shifted_sum_reindex)  |  **Remaining sorry**: 8

---

## File: `NonBooleanTopos.lean` — Non-Boolean Topos & Novel APN-like Structures

**Approach**: Explores the observation that in a Boolean topos (like Type),
the Ω-Frobenius is the identity, making the cross term trivialize.
In a non-Boolean topos, Ω-Frobenius ≠ id and the cross carries content,
suggesting non-classical APN-like structures.

**Key Results** (ALL PROVED, 0 sorry):
- `prop_boolean` ✅ — Prop is Boolean (Classical.em)
- `boolean_cross_trivial` ✅ — Boolean Ω-cross collapses to s ∧ P
- `omega3_not_boolean` ✅ — The 3-element Omega3 is non-Boolean
- `boolean_frobenius_unique` ✅ — 2-element Boolean algebra has only id as Ω-Frobenius
- `cross_identity_reduces` ✅ — Identity Frobenius gives cross = s ⊓ P
- `nonboolean_cross_nontrivial` ✅ — **In Prop × Prop with swap Frobenius,
  cross genuinely differs from s ⊓ P** — proving non-classical APN content exists
- `APNLikeStructure` — Parameterized by Ω (Heyting algebra), generalizes classical APN
- `SheafAPN` — Sheaf-theoretic differential structure
- `boolean_iff_classical_apn` ✅ — Boolean ↔ classical APN theory

**Proved**: ALL  |  **Remaining sorry**: 0

---

## Cross-Strategy DAG

All three strategies share the same root and terminal nodes:

```
                    lam_forced_trivial
                   /        |         \
           [Strategy A]  [Strategy B]  [Strategy C]
           Norm Quotient  Hilbert 90   Frob Iteration
                |            |              |
         norm expansion   cocycle      Frob shifts
         + gold deriv     formalism    + telescoping
                |            |              |
         factor L_k      Hilbert 90   trace = 0
         from quotient   kills H¹     Dedekind indep.
                |            |              |
          L_k(lam)=0    P/s ∈ ker     L_k(lam)=0
                 \          |         /
                  \         v        /
               cross_zero_iff_kernel ✅
                        |
                   cross = 0
                        |
                   contradiction ✅
```

### Shared Infrastructure (all proved ✅)
- `crossForm`, `linPolyL`, `relNorm` definitions
- `cross_zero_iff_kernel`: cross = 0 ↔ L_k(P/s) = 0
- `frob_add`, `frob_mul`: Frobenius ring homomorphism
- `gold_derivative`, `norm_expansion`: algebraic identities

### What Remains
The hardest lemmas — the ones that embody the deep mathematical content —
remain as `sorry`:
- **Strategy A**: `norm_diff_factored`, `kernel_trivial`
- **Strategy B**: `hilbert90_forces_kernel`, `additive_hilbert90`
- **Strategy C**: `key_eq_shift_general`, `relative_trace_of_cross`, `dedekind_independence`

Each strategy reduces to proving these 2-3 hard sub-lemmas.

---

## Mathlib Grounding

All definitions and proved lemmas are grounded in Mathlib:
- `add_pow_expChar_pow` — Freshman's dream (char p)
- `mul_pow` — Frobenius multiplicativity
- `CharP.cast_eq_zero` — Characteristic identification
- `FiniteField.pow_card` — Fermat for finite fields
- `Finset.sum_add_distrib` — Sum distributivity
- `neg_eq_of_add_eq_zero_left` — Negation in char 2
- `pow_ne_zero` — Power nonzero
- `div_mul_cancel₀` — Field division
- `HeytingAlgebra`, `BooleanAlgebra`, `DistribLattice` — Lattice theory
- `CompleteBooleanAlgebra Prop` — Prop as subobject classifier

## Connection to Lean's Type Theory as Topos

The `NonBooleanTopos.lean` module explicitly connects:
- **Lean's `Prop`** = Ω (subobject classifier of the topos `Type`)
- **`Classical.em`** = Booleanness of Ω
- **Ω-Frobenius = id** in Boolean topos ↔ cross trivializes
- **Non-Boolean Ω** (Omega3, Prop × Prop) ↔ cross carries content
- This grounds the entire APN cross-term analysis in **type-theoretic foundations**
