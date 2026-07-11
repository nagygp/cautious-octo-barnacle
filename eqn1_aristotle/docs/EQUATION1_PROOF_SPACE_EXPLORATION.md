# Equation (1): proof-space exploration and context bridge

This note records what the exploration of `Equation1.zip` produced. All claims
below are backed by the machine-checked, `sorry`-free file

* `RequestProject/Kasami/Equation1ProofSpace.lean`
  (builds via `lake build RequestProject.Kasami.Equation1ProofSpace`; every
  headline declaration rests only on `propext`, `Classical.choice`, `Quot.sound`).

## What `Equation1.zip` contains

`Equation1.zip` is the self-contained MVP for **equation (1)** in Dobbertin's
Theorem 1, `c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`. Its headline
statements are `theorem_1` (`Bijective (qKasami …) ↔ (k' + α·n) % 2 = 1`),
`eqn2_of_eqn1` (the step (1) ⟹ (2)), and the two case counts
`theorem_1_case1 / theorem_1_case2`. The heavy content lives in
`Theorem5.lean` (Artin–Schreier telescoping) and `Theorem8C1.lean` (trace
facts); `DAG_eqn1_to_eqn2.md` records the dependency DAG.

## Finding 1 — the proof space is one connected graph

`§3` of the Lean file transcribes the module-level dependency DAG as a genuine
`SimpleGraph` on the modules `{mathlib, defs, ffp, thm5, thm8c1, equation1}`
(`depGraph`), and proves `depGraph_connected`: every module is linked, through
its dependency chain, down to the common Mathlib base. This is the "mapping the
proof space with `SimpleGraph`" request, made into a checkable theorem.

## Finding 2 — a small invariant that propagates Mathlib → headline (the shortcut)

The single number `k' + α·n (mod 2)` controls the whole headline. The
`Equation1.zip` proof of the **necessary** direction of `theorem_1` routes
through the finite-field engine, but that direction needs none of it:

* `qKasami_zero` : `q_α(0) = 0` (the `0/0 = 0` convention);
* `qKasami_one`  : `q_α(1) = k' + α·n`;
* hence if `k' + α·n` is even then `q_α(1) = 0 = q_α(0)`, so an injective —
  a fortiori bijective — `q_α` forces `1 = 0` in the field.

This is `qKasami_bijective_imp_parity` (§2): `Bijective (qKasami …) → (k'+α·n)%2 = 1`,
proved from two evaluations plus injectivity, **engine-free**. It is the
"small elegant invariant that propagates from foundations to a headline".

## Finding 3 — the two Kasami contexts as a Morita-style bridge

The `α = 0` (trace-free) and `α = 1` (trace) forms of the Kasami map are the two
"equivalent contexts" of Dobbertin's proof (in `Equation1.zip` they are matched
to the library polynomials `qeps` and `gmap` by the bridge lemmas
`qKasami_zero_eq_qeps` / `qKasami_one_eq_gmap`). §4 packages *all* parameter
tuples `(n,k,k',α)` as objects of a `CategoryTheory` groupoid `Context`, where a
morphism is a proof of equal parity invariant:

* `instance : Groupoid Context` — connected components = parity classes;
* `hom_nonempty_iff` — a morphism exists iff the contexts share the invariant;
* `parFunctor : Context ⥤ Discrete (ZMod 2)` — the invariant as a functor
  ("one invariant, many contexts");
* `bridge_transports_nonvanishing` and `bridge_transports_bijective_necessary` —
  the value-at-`1` criterion and the headline necessary condition **transport**
  along the morphisms of the bridge, i.e. one may move a proof freely between the
  `α = 0` and `α = 1` contexts.

## Composable proof-arrow summary

```
Mathlib  ──(injective + q(0)=0, q(1)=k'+α·n)──▶  qKasami_bijective_imp_parity   (§2 shortcut)
                                                        │  parFunctor / f : c ⟶ d
                                                        ▼
                              bridge_transports_bijective_necessary            (§4 transport)
                              (same arrow, now valid in every linked context)
```

The full *sufficient* direction of `theorem_1` (and the `(1) ⟹ (2)` /
case-count headlines) still require the finite-field engine in `Theorem5.lean` /
`Theorem8C1.lean`; the bridge does not eliminate that work, but it isolates the
part of the headline that is context-independent and elementary, and gives a
checked mechanism for carrying results between the equivalent contexts.
