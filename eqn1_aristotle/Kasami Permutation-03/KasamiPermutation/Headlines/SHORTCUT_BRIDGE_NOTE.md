# Dobbertin (1999), Sections 1–2 — shortcut / bridge refactor

This note records the refactoring of the paper-skeleton headlines
(`PaperSkeleton/Sections1and2.lean`) and the bridge exploration
(`PaperSkeleton/ShortcutBridge.lean`). Everything referenced below builds as part
of the `RequestProject` library and is `sorry`-free, resting only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound` (the proof-space graph uses
only `propext`).

## The small structural invariant (the shortcut)

The single number `k' + α·n (mod 2)` — the value of the generalized Kasami map
`q_α` at `1` — controls the whole of Theorem 1. Three elementary facts, none of
which touch the finite-field engine, now live in `Sections1and2.lean`:

* `qKasami_zero` : `q_α(0) = 0` (the `0/0 = 0` convention makes the numerator
  vanish);
* `qKasami_one`  : `q_α(1) = k' + α·n`;
* `qKasami_bijective_imp_parity` : `Bijective q_α → (k' + α·n) % 2 = 1`, proved
  from the two evaluations above plus injectivity alone.

## Refactor of `theorem_1`

`theorem_1` (`Bijective (qKasami …) ↔ (k' + α·n) % 2 = 1`) is now split along the
shortcut:

* the **necessary** direction is discharged by the engine-free
  `qKasami_bijective_imp_parity`;
* only the **sufficient** direction calls the heavy engine (`Theorem5.theorem_5`
  for `α = 0`, `Q1General.gmap_bijective_iff` for `α = 1`), via `.mpr`.

This isolates the context-independent, elementary half of the headline from the
finite-field machinery. `theorem_1_q0`, `theorem_1_q1`, `theorem_1_case2`,
`corollary_2` are unchanged and still verify.

## The bridge (`ShortcutBridge.lean`)

* **Proof space as a `SimpleGraph`.** `Node`/`dep`/`depGraph` transcribe the
  dependency structure of the headlines (`theorem_1`, `routine_computation`,
  `frob_shift_two_to_one`, `kasamiDeriv_two_to_one`, `corollary_2`) over a common
  engine/Mathlib base; `depGraph_connected` proves the space is one connected
  component.

* **Equivalent contexts as a groupoid (Morita/Caramello).** `Context` bundles the
  parameters `(n,k,k',α)`; morphisms are proofs of equal parity invariant
  `Context.par : ZMod 2`. This is a `Groupoid`; `hom_nonempty_iff` characterises
  when two contexts are linked, and `contextIso` upgrades a shared invariant to an
  `Iso` (the Morita equivalence of the two contexts as objects).

* **The invariant as a functor.** `parFunctor : Context ⥤ Discrete (ZMod 2)`
  realises the parity as a functor to the (self-dual, "MacLane dual") discrete
  category — one invariant, many contexts.

* **Transport.** `bridge_transports_nonvanishing` and
  `bridge_transports_bijective_necessary` carry the value-at-`1` criterion and the
  headline necessary condition along morphisms of the bridge, so a proof obtained
  in the easiest context (e.g. trace-free `α = 0`) moves to the trace context
  `α = 1`.

* **Mapping back to the paper.** `headline_in_context` restates Theorem 1 itself
  in the bridge language: for admissible parameters,
  `Bijective (qKasami … c.α) ↔ c.par ≠ 0`. This closes the loop from the
  categorical invariant back onto the true Dobbertin headline.

## Conjectures explored

* *Established.* The parity invariant is the exact obstruction to `q_α` being a
  permutation (`headline_in_context`), it is constant on the connected components
  of the context groupoid (`bridge_transports_*`), and the two headline contexts
  `α ∈ {0,1}` are isomorphic objects precisely when they share it (`contextIso`).
* *Not pursued as a shortcut for the sufficient direction.* The bridge relocates
  and transports the headline criterion but does not eliminate the finite-field
  engine behind the *sufficient* direction of Theorem 1 (the Artin–Schreier
  telescoping in `Theorem5`/`Theorem8C1`); that remains the genuine analytic core.
