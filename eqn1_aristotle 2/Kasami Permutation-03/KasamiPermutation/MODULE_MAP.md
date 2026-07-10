# KasamiPermutation — module map

A functional re-organisation of Dobbertin's 1999 paper skeleton ("Kasami Power
Functions, Permutation Polynomials and Cyclic Difference Sets").  Modules and
declarations are named by **role / function / structural pattern**, not by the
paper's theorem numbers.  The subtree is self-contained: nothing outside it
depends on it, and everything is `sorry`-free (standard axioms only).

Import the whole theory with `import RequestProject.KasamiPermutation`.

## Foundations — `FiniteField/` (namespace `FiniteFieldCharTwo`)

A reusable char-2 finite-field toolbox (formerly `DempwolffMueller`).

| Module | Role |
| --- | --- |
| `FiniteField/FrobAlg.lean` | Frobenius endomorphism algebra (`frob_cycle`, `frob_bijective`, …). |
| `FiniteField/TraceNorm.lean` | Additive trace `frobSum`, its additivity and nondegeneracy. |
| `FiniteField/ExpArith.lean` | Power maps `x ↦ xᵃ` and their bijectivity from coprimality. |
| `FiniteField/AdjointBijection.lean` | Adjoint/trace-adjoint bijectivity. |
| `FiniteField/LinearizedBijection.lean` | Dempwolff–Müller: `L(X)·Xᵏ` is a permutation (`linearizedTimesPow_bijective`). |
| `FiniteField/DerivativeBijection.lean` | Bare derivative-map bijection criterion (Lemma 3.1 core). |

## Recurrence machinery

| Module (namespace) | Role |
| --- | --- |
| `Casoratian.lean` (`KasamiPerm.Casoratian`) | Discrete Wronskian / conserved cross-invariant of a two-step linear recurrence. |
| `InverseRecurrence.lean` (`KasamiPerm.InverseRec`) | The `A/B/C` sequence families and the driving equation (Eqn 10). |
| `InverseCubicEquation.lean` (`KasamiPerm.InverseCubic`) | The cubic equation satisfied by the inverse polynomial. |

## Permutation criteria

| Module (namespace) | Role |
| --- | --- |
| `TraceFreeCriterion.lean` (`KasamiPerm.TraceFree`) | The trace-free map `q₀ = qeps`; `qeps_bijective_iff`. |
| `TraceVersionInfra.lean` (`KasamiPerm.TraceCore`) | Trace-version infrastructure: `qPoly`, Artin–Schreier surjectivity, derivative-image ↔ trace characterization (`derivImage_iff_trace_zero`). |
| `TraceVersionBase.lean` (`KasamiPerm.TraceParityCase`) | The trace-version map `gmap` and its bijectivity in the base parity case (`derivImage_iff_trace_zero_evenCase`). |
| `Headlines/TraceVersionCriterion.lean` (`KasamiPerm.TraceCriterion`) | Parity-general trace-version criterion `gmap_bijective_iff`. |

## MCM → APN — `MCM/` and `Core/`

| Module (namespace) | Role |
| --- | --- |
| `MCM/Permutation.lean` (`KasamiPerm.MCM`) | Müller–Cohen–Matthews permutation polynomial engine. |
| `MCM/ToAPN.lean` (`KasamiPerm.MCMtoAPN`) | Bridge from MCM permutation to the APN property. |
| `Core/KasamiAPN.lean` (`KasamiAPN`) | Direct proof that Kasami power functions are APN. |

## Headlines — `Headlines/`

| Module (namespace) | Role |
| --- | --- |
| `Headlines/PermutationCriterionAndAPN.lean` (`KasamiPerm.Headlines`) | Theorem 1 (`qKasami_bijective_iff`) and Corollary 2 (`kasami_isAPN`), plus the engine-free invariant `qKasami_bijective_imp_parity`. |
| `Headlines/InvariantAndClassifier.lean` (`KasamiPerm.Headlines.Bridge`) | The value-at-1 invariant, the headline proof space as a connected `SimpleGraph`, and the contexts groupoid with parity functor. |

## Structural distillation — `Structural/`

| Module (namespace) | Role |
| --- | --- |
| `Structural/Obstruction.lean` (`KasamiPerm.Obstruction`) | The engine-free permutation obstruction for **arbitrary self-maps**: a bijection fixing `0` never vanishes off `0`. Upstreamable. |
| `Structural/ContextClassifier.lean` (`KasamiPerm.Headlines.Bridge`) | The Kasami headline necessary-direction as a one-liner (`qKasami_bijective_imp_parity_v2`); the parity functor upgraded to an equivalence of categories `contextClassifier : Context ≌ Discrete (ZMod 2)`, with `iso_iff_par`, `contextSelfDual`, and the criterion read off the classifier. |

## Field-level bridges — `Bridge/`

Small structural re-derivations (units functor, Artin–Schreier telescoping,
forgetful `Field ⤳ AddGroup` two-to-one), collected in `Bridge.lean`.
