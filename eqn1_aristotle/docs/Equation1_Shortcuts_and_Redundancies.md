# Equation (1): structural shortcuts, the classifier, and redundant parity restrictions

This note records the exploration/refactor of the "proof space" layer that sits on
top of the Kasami permutation-criterion library. Everything referenced here builds
and is `sorry`-free on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.

New/changed modules:

| file | role |
|------|------|
| `KasamiPermutations/Equation1ProofSpace.lean` | the **context groupoid** and the analytic↔combinatorial bridge |
| `KasamiPermutations/Equation1Classifier.lean` | the **engine-free obstruction**, the **classifier equivalence**, and the **parity graph** |
| `KasamiPermutations/SpecialValues.lean` | now also carries the engine-free necessary direction `qKasami_bijective_imp_parity` |
| `KasamiPermutations/PermutationCriterion.lean` | headline `qKasami_bijective_iff` refactored to use the shortcut for `→` |

## 1. The one-invariant, engine-free shortcut (and where it is now used)

The whole **necessary** ("only if") direction of Dobbertin's Theorem 1 is a single
fact about *any* self-map of *any* pointed type, with **no field, no finiteness, no
Frobenius**:

> a bijection that fixes `0` cannot send the distinct point `1` to `0`
> (that would collide two points), so `q_α(1) ≠ 0`.

This is distilled in `Equation1Classifier` §1 as three general lemmas
(`not_injective_of_collision`, `not_injective_of_zero_collision`,
`apply_ne_zero_of_bijective_fixing_zero`) and instantiated in one line as
`qKasami_bijective_imp_parity_v2`.

The same argument, stated directly for the Kasami map, is now a first-class lemma of
the main library, `Kasami.qKasami_bijective_imp_parity` (in `SpecialValues`). The
headline `qKasami_bijective_iff` was **refactored** so its `→` direction is exactly
this lemma; only the `←` (sufficiency) direction still invokes the finite-field
engine (`qeps_bijective_iff` / `gmap_bijective_iff`). Previously both directions were
proved together through the engine via `convert`.

**Consequence for "which parity restrictions are redundant".** The arithmetic
hypotheses of the headline — `hn`, `hk`, `hcop`, `hk'`, `hk0`, `hexp`, `hα` — are
*all* load-bearing for the combined `↔` (verified by hypothesis-minimization), **but
only because of the `←` direction.** The `→` direction needs *none* of them: it holds
for every `n, k, k', α` and over every characteristic-2 field, finite or not. So the
"parity restriction" `k' + α·n ≡ 1 (mod 2)` is *forced* unconditionally by
bijectivity; the numeric side conditions are purely about *realising* it.

## 2. Redundancies found in the parity bookkeeping

* **`1 % n` vs `1`.** The headline takes `hk' : k * k' % n = 1 % n`, but `hk0 : 0 < k`
  and `hk : k < n` force `n ≥ 2`, hence `1 % n = 1`. The proof now derives
  `hkk1 : k * k' % n = 1` once and reuses it. The hypothesis could be stated directly
  as `k * k' % n = 1` with no loss of generality (kept as `1 % n` to preserve the
  existing public statement).

* **The necessary direction was proved three times.** It is embedded (as a
  `by_contra` collision at `q(0) = q(1) = 0`) inside *both* `qeps_bijective_iff` and
  `gmap_bijective_iff`, and again at the `qKasami` level. Factoring it out as
  `qKasami_bijective_imp_parity` removes the third copy from the headline; the two
  copies inside the engine lemmas remain (they are stated over the `qeps`/`gmap`
  representations and are internal to those proofs).

* **Two names, one statement.** `Kasami.qKasami_bijective_imp_parity` and
  `Equation1ProofSpace.qKasami_bijective_imp_parity_v2` prove the identical fact. The
  `_v2` is retained deliberately as the *pedagogical* instance showing it as one
  application of the general §1 obstruction; the un-suffixed lemma is the one wired
  into the headline.

## 3. The classifier: one invariant, three equivalent views

`Context` bundles `(n, k, k', α)`; its only relevant invariant is
`Context.par = k' + α·n (mod 2) : ZMod 2`. Making "same parity" the hom-relation
turns `Context` into a thin groupoid, and the single-invariant record is the functor
`parFunctor : Context ⥤ Discrete (ZMod 2)`. `Equation1Classifier` §3 shows it is
full + faithful + essentially surjective, hence an **equivalence**
`contextClassifier : Context ≌ Discrete (ZMod 2)` (and, being a groupoid,
`contextSelfDual : Context ≌ Contextᵒᵖ`).

The same two-class partition then appears in three guises, proved mutually
equivalent:

* **combinatorial** — `c.par = d.par`;
* **categorical** — `Nonempty (c ≅ d)` (`iso_iff_par`);
* **graph-theoretic** — `parGraph.Reachable c d`, i.e. a *walk* = a composite of proof
  arrows (`parGraph_reachable_iff`, `parGraph_reachable_iff_iso`).

The `SimpleGraph` view (§5) answers the "composed proof arrows / reachability"
question: the parity graph has exactly two connected components, and reachability is
literally the transitive closure of single parity-preserving edges.

The analytic hinge tying this back to the map is `qKasami_one_eq_zero_iff_par`
(`q_α(1) = 0 ↔ Context.par c = 0`), from which
`qKasami_one_eq_zero_iff_classifier` and `bijective_imp_classifier_one` read the
criterion off the classifier's object map.

## 4. Other approaches / Mathlib reuse considered

* The `→` obstruction is a special case of the standard pigeonhole/injective facts
  (`Function.Bijective.injective`); no bespoke counting is needed. The abstract §1
  lemmas are stated generically so they are reusable for any "fixes 0, misses 0 off
  the base point" argument.
* The thin-category machinery reuses Mathlib's `Discrete`, `Functor.Full/Faithful/
  EssSurj`, `Functor.asEquivalence`, `Discrete.opposite`, and the `SimpleGraph`
  reachability API (`reachable_iff_reflTransGen`, `Relation.ReflTransGen`) rather than
  hand-rolled partitions.
* The `←` (sufficiency) direction is the genuinely deep part and is *not* shortcut-
  able by these structural moves: it rests on the finite-field engine (Frobenius/
  Fermat `pow_card`, `add_pow_char_pow`, the Mersenne gcd, and
  `Finite.injective_iff_surjective`). The structural refactor cleanly isolates that
  depth to a single direction.
