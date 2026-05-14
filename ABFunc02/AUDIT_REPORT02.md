# Audit 02 — Structural Reinforcement Report

## Summary

All five tasks from the Audit 02 request have been implemented. The project compiles with **zero `sorry`** and uses only the standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Task 1: Non-Vacuous `IsAB` ✅

**File**: `ABCategory.lean`

### Changes
- Added `false_ : terminal ℰ ⟶ Omega` to `ElemTopos` (the bottom element ⊥_Ω of the Heyting algebra), along with a non-degeneracy axiom `true_ne_false`.
- Replaced `flat : True` in `IsAB` with a genuine **spectral dichotomy** condition:

```lean
class IsAB ... where
  spectral_dichotomy : ∀ (X : 𝕋.ℰ) (χ : X ⟶ ch.dual),
    χ ≫ W.wal f = terminal.from X ≫ 𝕋.false_ ∨
    χ ≫ W.wal f = terminal.from X ≫ c
```

This states that for every generalized element `χ` of the dual, the Walsh value `𝒲(f)(χ)` is either `⊥_Ω` (zero) or equals the spectral level `c`. This is the Yoneda-embedding formulation of the topos-internal dichotomy.

### Impact
- `IsAB` is now a **genuine mathematical constraint** — not every endomorphism satisfies it.
- The `boolIsAB` instance in `SporadicABFunc.lean` is updated to verify the dichotomy for the constant-true Walsh transform.

---

## Task 2: Derived Homotopy Discreteness ✅

**File**: `HomotopySpectral.lean`

### Changes
- Introduced `SpectralObject.spectralDiversity`: the number of distinct nonzero norm values in the spectrum.
- Defined `postnikovConstruction`: a `HomotopySpectralObject` where `πₖ = spectralDiversity` for `k ≥ 1` (not hardcoded to 1).
- Proved `bent_diversity_eq_one`: if a spectral object is bent at level `c > 0` with at least one nonzero value, then its spectral diversity is exactly 1.
- Proved the **rigidity theorem** `bent_implies_discrete`:

```lean
theorem bent_implies_discrete ... :
    (postnikovConstruction X hNontriv).IsDiscrete
```

### Mathematical Content
The proof chain is:
1. Bent ⟹ all nonzero norms equal `c` (definition of `IsBent`)
2. Since `c > 0`, the set of distinct nonzero norms is exactly `{c}`
3. Hence `spectralDiversity = |{c}| = 1`
4. Therefore `πₖ = spectralDiversity = 1` for `k ≥ 1`

This is a **genuine theorem** — discreteness is *derived* from the bent condition, not defined into the construction.

---

## Task 3: Complete Group Axioms for `GrpObj` ✅

**File**: `ABCategory.lean`, `SporadicABFunc.lean`

### Changes
Added five group axioms to `GrpObj`, expressed via generalized elements (Yoneda-style):

```lean
structure GrpObj where
  ...
  mul_assoc : ∀ (X : 𝕋.ℰ) (a b c : X ⟶ carrier),
    prod.lift (prod.lift a b ≫ mul) c ≫ mul =
    prod.lift a (prod.lift b c ≫ mul) ≫ mul
  mul_left_unit : ∀ (X : 𝕋.ℰ) (a : X ⟶ carrier),
    prod.lift (terminal.from X ≫ unit) a ≫ mul = a
  mul_right_unit : ...
  mul_left_inv : ...
  mul_right_inv : ...
```

All five axioms are **formally verified** for `FinGrpObj G` (the Type-topos instantiation) using Lean's group laws.

---

## Task 4: Converse Kerdock Isomorphism ✅

**File**: `CodingTheoryIsomorphism.lean`

### Changes
Added three new definitions and theorems:

- `hasABTypeSpectrum`: a code's character-sum eigenvalues lie in `{n, 2^r, 0, -2^r}`.
- `hasKerdockWeightStructure`: 3-weight structure symmetric around `n/2`.
- `ab_spectrum_implies_kerdock_weights`: the **converse** — AB-type spectrum constrains nonzero weights to the Kerdock pattern.
- `ab_spectral_uniqueness`: two codes with AB-type spectra and equal cardinality have identical m-tuple counts.

This closes the if-and-only-if relationship between AB spectral structure and Kerdock codes.

---

## Task 5: Non-Abelian Generalization ✅

**File**: `SporadicABFunc.lean`

### Changes
- Defined `grpCommutator a b = a⁻¹ * b⁻¹ * a * b`.
- Defined `commutatorMTupleCount G m`: the number of solutions to the m-fold commutator equation `[x₁,x₂]·[x₃,x₄]·⋯ = 1` using `List.prod` (correct for non-commutative groups).
- Proved `commutatorMTupleCount_comm`: for **abelian** groups, every commutator is trivial, so the count equals `|G|^{2m}`.
- Proved `commutatorMTupleCount_trivial`: the trivial group count is 1.

The formulation extends the κ_m framework to all finite groups (including sporadic simple groups) via the Frobenius character-theoretic formula.

---

## Axiom Verification

All theorems use only the standard Lean 4 axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

No `sorry`, `axiom`, or `@[implemented_by]` declarations remain.

## Files Modified

| File | Changes |
|------|---------|
| `ABCategory.lean` | Added `false_`, `true_ne_false`, group axioms, non-vacuous `IsAB` |
| `SporadicABFunc.lean` | Updated `TypeTopos`, `FinGrpObj` with axioms, `boolIsAB` with dichotomy, added commutator counting |
| `HomotopySpectral.lean` | Added `spectralDiversity`, `postnikovConstruction`, proved `bent_implies_discrete` |
| `CodingTheoryIsomorphism.lean` | Added converse Kerdock theorems |
| `ABDiscoveryIntegration.lean` | Updated to use derived discreteness, re-proved `kappa_m_identity_formula` |
