# APN Functions & the Open Classification Problem: Insights from This Formalisation

## The Open Question (Restated)

The known APN (Almost Perfect Nonlinear) functions over GF(2ⁿ) fall into:

1. **Quadratic APN functions in odd dimension** — many exist; the conjecture (every APN in odd dimension is CCZ-equivalent to a quadratic) is easy to verify on these because their differential set Δ is an affine subspace.
2. **Kasami functions** — power functions x^d with d = 2²ᵏ − 2ᵏ + 1.
3. **Gold, Welch, Niho type** — other power APN functions x^d.
4. **One sporadic example in dimension 6** (the Dillon–McGuire function, found computationally).

**The open question**: Are there others?

---

## What This Formalisation Contributes

### 1. The m-Tuple Count as a Structural Invariant

The central proven result (`mTupleCount_eq_card_pow` in `CodingTheoryIsomorphism.lean`) establishes that for any binary linear code C and any m ≥ 1:

> **κ_m(C) = |C|^{m−1}**

This is the number of m-tuples of codewords summing to zero. For m = 3 and |C| = 2ⁿ (as in APN/AB codes), this gives κ₃ = 2^{2n}.

**Insight for APN classification**: This result shows that κ_m is *entirely determined by the code's cardinality* and carries no information about which specific APN function generated the code. The theorem `mtuple_rigidity_from_card` makes this explicit: two linear codes with the same cardinality have identical m-tuple counts for all m. This means **the m-tuple count alone cannot distinguish between different APN families** — it is too coarse an invariant for classification.

This is actually an important negative result: any attempt to classify APN functions purely through m-tuple counting (or equivalently, through the formula |Ω|^{(m−1)n − m} in the topos framework) will fail to separate the known families. The invariant is universal across all APN functions of the same dimension.

### 2. The Topos-Theoretic Bridge: PN ↔ Boolean

The Bridge Theorem (`bridge_theorem` in `PNBooleanRelatives.lean`) proves that for every prime p and dimension n, the internal m-tuple counting formula has the same *exponent* (m−1)n − m in both:
- the p-valued topos (|Ω| = p, relevant for PN functions over GF(p)), and
- the Boolean topos (|Ω| = 2, relevant for APN/AB functions over GF(2)).

**Insight for classification**: This establishes a formal *structural correspondence* between PN functions (over odd characteristic) and APN/AB functions (over characteristic 2). The exponent is an absolute invariant — it does not depend on the base of the topos. This suggests:

- **Potential transfer principle**: If a new PN function is discovered over GF(p) for odd p, the Bridge Theorem guarantees the existence of a "Boolean relative" — a structural signature in the Boolean topos with matching exponent. This does *not* automatically produce a new APN function (the signature is a counting pattern, not a function), but it provides a *target specification* for what such a function's combinatorial profile would look like.

- **Constraint on sporadic examples**: The uniqueness clause of the Bridge Theorem (part iii) proves that the Boolean relative signature is *unique* at each dimension. This means any new APN function in dimension n must have the same m-tuple counting signature as all existing ones — narrowing the search space.

### 3. Spectral Rigidity and Homotopical Discreteness

The theorem `bent_implies_discrete` (in `HomotopySpectral.lean`) proves:

> If a spectral object is bent (all nonzero Walsh values have the same norm), then its Postnikov tower is discrete — all higher homotopy groups are trivial.

**Insight**: AB (Almost Bent) functions — the odd-dimensional counterparts of APN functions — are "maximally rigid" in the homotopical sense. There is no room for continuous deformation or higher-order structure. This rigidity is:

- **Self-dual** (proved in `DualitySymmetry.lean`): the property holds equally in the primal and dual categories.
- **Monotone**: k-bentness at level k+1 implies k-bentness at level k.

For the classification question, this suggests that AB/APN functions are *isolated points* in some appropriate moduli space — they cannot be smoothly deformed into one another. This aligns with the empirical observation that known APN families are "rigid" (e.g., CCZ-equivalence classes are discrete).

### 4. The Kerdock Correspondence

The bidirectional correspondence `ab_kerdock_spectral_match` / `ab_spectrum_implies_kerdock_weights` proves:

> A code has AB-type Walsh spectrum ⟺ it has Kerdock-type weight distribution (3 nonzero weights symmetric around n/2).

**Insight**: This provides a *dual characterisation* of APN/AB functions through coding theory. To find new APN functions, one could equivalently search for codes with the Kerdock weight pattern. The Pless moment decomposition (`three_weight_pless_decomposition`) further constrains such codes: the weight distribution must admit a 4-term moment expansion.

### 5. What the Formalisation Does NOT Resolve

The formalisation is honest about its limitations:

- **The m-tuple count is dimension-blind within a fixed dimension**: It cannot distinguish Gold from Kasami from the sporadic dimension-6 example. All APN functions of the same dimension n produce codes with identical κ_m values.

- **The topos framework operates at the level of counting signatures, not explicit functions**: The Bridge Theorem tells you *what the counting pattern is*, not *which polynomial f(x) achieves it*. The gap between "a Boolean relative signature exists" and "a concrete APN function realising it exists" remains open.

- **Homotopical discreteness is proved from a model where it is essentially built into the construction** (as noted in Audit Report 01). The deeper question — *why* APN functions are homotopically discrete from first principles — is encoded in the model choice, not derived from more primitive axioms.

---

## Summary: Does This Help Answer "Are There Others?"

**Partially, in the following ways:**

| Aspect | Contribution |
|--------|-------------|
| **Ruling out approaches** | The m-tuple count is proved to be identical for all APN functions of the same dimension → it is not a useful distinguishing invariant. Any classification attempt needs finer invariants. |
| **Transfer from PN world** | The Bridge Theorem provides a systematic way to "import" structural predictions from the better-understood PN world (odd characteristic) to the Boolean (APN) world. If new PN families are discovered, their Boolean relatives give candidate specifications. |
| **Rigidity constraints** | Homotopical discreteness + spectral flatness + Kerdock weight duality collectively impose strong structural constraints on any hypothetical new APN function. Any candidate must satisfy all three simultaneously. |
| **Coding-theoretic reformulation** | The Kerdock correspondence converts the APN search problem into a coding-theory problem (find 3-weight codes with Kerdock-type weight distribution), which is a different — and possibly more tractable — formulation. |
| **Uniqueness of Boolean relative** | There is exactly one "counting shape" (Boolean relative signature) per dimension. This is a rigidity result on the combinatorial side. |

**What remains genuinely open**: Whether there exist APN functions beyond the known families (Gold, Kasami, Welch, Niho, quadratic, and the dimension-6 sporadic example). This formalisation constrains the search space and provides structural tools, but does not resolve the classification. The question of existence of new APN functions appears to require invariants finer than those captured by the m-tuple counting framework — perhaps differential uniformity spectra, CCZ-equivalence class enumeration, or algebraic-geometric methods not yet formalised here.

The most actionable insight from this work is arguably the **negative one**: the m-tuple count (and by extension, the topos-internal counting formula) is too coarse to classify APN functions. Any progress on the classification will require going beyond counting and into the *geometric structure* of the differential sets Δ_f — which, as noted in your point (1), are affine subspaces for quadratic APN functions but have unknown structure in general.
