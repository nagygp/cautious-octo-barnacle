# Upstreaming: linear codes, minimum distance, and the Singleton bound

This folder packages the foundational linear-coding-theory results from
`CodeTheoryCryptoEquiv/CodingTheory/LinearCode.lean` into a **Mathlib-PR-ready** form,
following the ordering and process recommended in the assistant's reply: *raise
it on Zulip first, then open a focused PR around the most attractive standalone
contribution.*

Contents:

* `LinearCode.lean` — the contribution candidate, written to Mathlib conventions
  (copyright header, module docstring with Main definitions / Main results /
  References / Tags, full per-declaration docstrings, dot-notation API).
* `Dual.lean` — the **dual code** layer (the recommended next step from
  `../../CODING_THEORY_DIRECTIONS.md`), built on Mathlib's general
  orthogonal-complement theory for bilinear forms. It contains two genuinely
  general, reusable "pearls" about the standard dot-product form
  (`Matrix.dotProductBilin_isSymm`, `Matrix.dotProductBilin_nondegenerate`) plus
  the dual-code API (`LinearCode.dual`, `mem_dual_iff`, `dim_add_dim_dual`,
  `dim_dual`, `dual_dual`, `dual_antitone`, `dual_bot`/`dual_top`, and the
  self-orthogonal / self-dual predicates).
* `GeneratorParityCheck.lean` — the **generator/parity-check matrix duality**
  layer (the next sub-step after the dual code in
  `../../CODING_THEORY_DIRECTIONS.md`): a code as the row space `LinearCode.gen G`
  of a generator matrix and as the kernel `LinearCode.parityCheck H` of a
  parity-check matrix, with `dual_gen` (`(gen G)ᗮ = parityCheck G`),
  `dual_parityCheck` (`(parityCheck H)ᗮ = gen H`), the dimension identities
  `dim_gen` (`= rank Gᵀ`) and `dim_parityCheck` (`= n - rank H`), and
  `eq_parityCheck_iff_dual_eq_gen`.
* `MDS.lean` — the **MDS-duality** layer (the next step, §1.1 of
  `../../CODING_THEORY_DIRECTIONS.md`). The `IsMDS` predicate already lives in
  `LinearCode.lean`; this file adds the *information-set* machinery
  (`LinearCode.vanishingOn`, `mem_vanishingOn_iff`, `dim_vanishingOn`,
  `dual_vanishingOn`, `dual_disjoint`, `dual_sup`) and the characterization
  `isMDS_iff_forall_disjoint_vanishing`, culminating in the headline
  MacWilliams–Sloane Ch. 11, Thm 2: `LinearCode.IsMDS.dual` (the dual of an MDS
  code is MDS) and the biconditional `isMDS_dual_iff`.
* `SpherePacking.lean` — the **sphere-packing (Hamming) bound** layer (§1.3 of
  `../../CODING_THEORY_DIRECTIONS.md`, MacWilliams–Sloane Ch. 1, Thm 6): the
  Hamming ball `LinearCode.hammingBall` and its explicit volume
  `hammingBallVolume`, the exact sphere count `card_filter_hammingDist_eq`, the
  ball count `hammingBall_card` and translation invariance
  `hammingBall_card_eq_zero`, the ball disjointness `disjoint_hammingBall_of_mem`,
  and the bound in abstract (`sphere_packing_bound`) and explicit
  (`sphere_packing_bound_volume`) form.
* `GilbertVarshamov.lean` — the **Gilbert–Varshamov bound** layer (§1.4 of
  `../../CODING_THEORY_DIRECTIONS.md`, MacWilliams–Sloane Ch. 1, Thm 12): the
  `LinearCode.IsSeparated` predicate, existence of a maximum-cardinality
  separated finset (`exists_maximal_separated`), the maximal-packing covering
  lemma (`gilbert_varshamov_covering`), and the bound in abstract
  (`gilbert_varshamov_bound_card`) and explicit (`gilbert_varshamov_bound`) form.
* `WeightEnumerator.lean` — the **weight enumerator** layer (§2, item 6 of
  `../../CODING_THEORY_DIRECTIONS.md`, MacWilliams–Sloane Ch. 5), the gateway to
  the MacWilliams identity: the weight distribution `LinearCode.weightDistribution`
  (`A_i`) and the bivariate enumerator `LinearCode.weightEnumerator`
  (`W_C(X, Y) = Σ_c X^{n-wt c} Y^{wt c}`), with `weightDistribution_zero`
  (`A_0 = 1`), `sum_weightDistribution` (`Σ_i A_i = |C|`),
  `weightEnumerator_eq_sum_weightDistribution` (`W_C = Σ_i A_i X^{n-i} Y^i`) and
  `weightEnumerator_eval_one_one` (`W_C(1,1) = |C|`).
* `Krawtchouk.lean` — the **Krawtchouk polynomial** layer (§2, item 8 of
  `../../CODING_THEORY_DIRECTIONS.md`, MacWilliams–Sloane Ch. 5, §2), the discrete
  orthogonal-polynomial transform kernel that turns a weight enumerator into its
  MacWilliams dual: `LinearCode.krawtchouk`
  (`K_k(x;n,q) = Σ_j (-1)^j (q-1)^{k-j} C(x,j) C(n-x,k-j)`), with the basic
  evaluations `krawtchouk_zero` (`K_0 = 1`), `krawtchouk_eval_zero`
  (`K_k(0) = C(n,k)(q-1)^k`), the degree-vanishing `krawtchouk_eq_zero_of_lt`,
  the coefficient bridge `krawtchouk_eq_coeff`, and the headline
  **generating function** `krawtchouk_generating_function`
  (`Σ_k K_k(x) X^k = (1 + (q-1)X)^{n-x} (1-X)^x`). The reusable polynomial pearl
  `coeff_linear_pow` (`((C b + C a · X)^m).coeff k = C(m,k) a^k b^{m-k}`) is the
  combinatorial heart of the proof.

The file builds in this project and every declaration is `sorry`-free, resting
only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

---

## Step 0 — raise it on Zulip *before* doing anything else

The right first move is a short post in **#mathlib4** (or **#new members**)
describing the gap and asking whether linear-code minimum-distance / Singleton
theory already exists under names that weren't searched. Frame it as *"I didn't
find it"* rather than *"it's absent"*: maintainers will say quickly whether it is
wanted and how they'd want it organized.

Draft Zulip message:

> **Linear codes: minimum distance + Singleton bound**
> I'm looking at formalizing basic linear-code theory on top of
> `Mathlib.InformationTheory.Hamming` — modelling a code as a
> `Submodule F (ι → F)` and proving (a) for a linear code, minimum distance =
> minimum weight, and (b) the Singleton bound `d ≤ n − k + 1`. I searched and
> didn't find existing minimum-distance / Singleton API; could someone confirm
> whether this already exists under a name I missed, and if it's wanted, how
> you'd like it organized (a `LinearCode` abstraction vs. working directly over
> `Submodule F (ι → F)`, file location, naming)? I have a `sorry`-free draft.

Do **not** assert "no existing theory" in the PR description; verify it with the
maintainers on Zulip instead.

## What a PR will likely be asked to provide

Based on the assistant's reply, expect requests for:

* **A general API, not just the headlines.** Provided here: `length`, `dim`,
  `weightSet`, `distSet`, `minWeight`, `minDist`, the lower-bound /
  attainment / positivity lemmas (`minWeight_le`, `exists_eq_minWeight`,
  `minWeight_pos`, `minWeight_le_length`, `minDist_le`, `exists_eq_minDist`), the
  puncturing lemma, and the `IsMDS` predicate with its basic lemmas.
* **Integration with existing `hammingDist` / `hammingNorm`.** The file builds
  directly on `Mathlib.InformationTheory.Hamming`; weights and distances are
  *not* redefined — `weightSet`/`minWeight` use `hammingNorm`,
  `distSet`/`minDist` use `hammingDist`, and `minDist_eq_minWeight` is exactly
  the bridge `d(x,y) = wt(x − y)`.
* **A `LinearCode` abstraction (or working over `Submodule F (ι → F)`).**
  Provided as the reducible abbreviation `LinearCode ι F := Submodule F (ι → F)`,
  which keeps the entire `Submodule` API available while giving a named home for
  dot-notation (`C.minDist`, `C.length`, …). If maintainers prefer plain
  `Submodule F (ι → F)`, the abbreviation can be inlined with no proof changes.
* **Full docstrings.** Every definition and theorem is documented; the module
  docstring lists Main definitions, Main results, References, and Tags.

The **`minDist_eq_minWeight`** result is the most attractive standalone
contribution; the **Singleton bound** (`singleton_bound` / `singleton_bound_dist`)
is the natural companion, and `IsMDS` sets up the maximum-distance-separable
follow-ups.

## Ordering: upstream first

Upstreaming first is the sensible order. It pins down the canonical definitions,
gets a maintainer review of correctness and generality, and means any later
writeup can cite landed Mathlib code rather than a moving private file. A short
expository "pearl" note reads better describing an *accepted* contribution.

Don't overclaim novelty: this is textbook material (MacWilliams–Sloane, Ch. 1,
Thms 2 and 11), so pitch it as a clean, reusable foundation rather than a new
result, and let the maintainers — not the PR text — settle the "no existing
theory" question.

## Suggested PR scope and follow-ups

* **PR 1 (`LinearCode.lean`):** `LinearCode` abstraction + Hamming-based
  `minWeight` / `minDist` API + `minDist_eq_minWeight` + Singleton bound +
  `IsMDS` predicate.
* **PR 3 (`GeneratorParityCheck.lean`):** the generator/parity-check matrix
  duality (`gen`, `parityCheck`, `dual_gen`, `dual_parityCheck`, `dim_gen`,
  `dim_parityCheck`, `eq_parityCheck_iff_dual_eq_gen`), built on the dual code
  of PR 2.
* **PR 4 (`MDS.lean`):** MDS duality — the information-set characterization
  (`vanishingOn`, `dual_vanishingOn`, `dim_vanishingOn`, `dual_disjoint`,
  `isMDS_iff_forall_disjoint_vanishing`) and the headline `IsMDS.dual` /
  `isMDS_dual_iff` (MacWilliams–Sloane, Ch. 11, Thm 2), built on the dual code
  of PR 2 and the `IsMDS` predicate of PR 1.
* **PR 2 (`Dual.lean`):** the two dot-product-form pearls
  (`dotProductBilin_isSymm`, `dotProductBilin_nondegenerate` — candidates for
  `Mathlib/LinearAlgebra/Matrix/DotProduct.lean`) and the dual-code API on top of
  `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`. The dual is the gateway to
  parity-check matrices, self-dual codes, and the MacWilliams identity.
* **Natural follow-ups** (see `../../CODING_THEORY_DIRECTIONS.md` for the full
  dependency-ordered roadmap): MDS characterizations and MDS-duality;
  Reed–Solomon codes as the cleanest MDS instance; the sphere-packing and
  Gilbert–Varshamov bounds; and, longer term, weight enumerators and the
  MacWilliams identity.

For the actual PR, minimise the blanket `import Mathlib` at the top of
`LinearCode.lean` (e.g. with `shake`) down to the modules actually used.
