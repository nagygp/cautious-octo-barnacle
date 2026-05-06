# Kasami Triple Count — Formal Proof

## The Theorem

Let k be coprime with n. For every b ∈ GF(2^n), let F(b) = b^{4^k − 2^k + 1} (the **Kasami function**). Define:

$$\Delta = \{F(b) + F(b+1) + 1 : b \in GF(2^n)\}$$

Then, for every distinct nonzero v₁, v₂ ∈ GF(2^n):

$$|\{(x, y, z) \in \Delta^3 : v_1 x + v_2 y + (v_1 + v_2) z = 0\}| = 2^{2n-3}$$

## Key Mathematical Insight

The proof rests on a beautiful connection between **cryptographic function theory** and **additive combinatorics**, revealed through a "crystallographic" lens:

### The Hyperplane Structure

The Kasami function F(b) = b^{4^k - 2^k + 1} is known to be:
- **APN** (Almost Perfect Nonlinear) when gcd(k,n) = 1
- **AB** (Almost Bent) when additionally n is odd
- **Crooked** when AB (every quadratic AB permutation with F(0) = 0 is crooked)

The **crooked property** means: for every nonzero a ∈ GF(2^n), the set {F(x+a) + F(x) : x ∈ GF(2^n)} is the complement of a hyperplane (codimension-1 additive subspace).

Since F(1) = 1, we have:
$$\Delta = \{F(b+1) + F(b) + F(1) : b\} = \text{Im}(\Delta_1 F) + 1$$

where Im(Δ₁F) = GF(2^n) \ H for some hyperplane H. Adding 1 either maps the complement back to H (if 1 ∉ H) or keeps it as the complement (if 1 ∈ H). **In either case, Δ is a hyperplane or the complement of a hyperplane.**

For the Gold function (k=1), this can be verified directly: Δ = {b² + b : b ∈ GF(2^n)} = ker(Tr), which is the trace-zero hyperplane.

### The Combinatorial Heart: Coset Geometry

The triple count for a hyperplane H ⊂ GF(2^n) is computed purely through **coset geometry**:

**Step 1: Reduce to pairs.** Since v₁ ≠ 0, x is determined by (y,z): x = c·y + (1+c)·z where c = v₂/v₁.

**Step 2: Coset analysis.** H has index 2, so F = H ∪ (F\H). The condition c·y + (1+c)·z ∈ H decomposes:
- Both c·y ∈ H and (1+c)·z ∈ H → sum ∈ H ✓
- Both c·y ∉ H and (1+c)·z ∉ H → sum ∈ H ✓ (index-2 complement sum property)
- Mixed → sum ∉ H ✗

**Step 3: The key non-invariance lemma.** For ANY hyperplane H in a field of char 2, and any c ∉ {0,1}:
$$c \cdot H \neq H$$

*Proof:* If c·H ⊆ H, then (c+1)·H ⊆ H (since (c+1)h = ch + h). For a ∉ H, both c·a and a are ∉ H (c maps complement to complement by bijectivity). So (c+1)·a = c·a + a ∈ H (complement sum property). But (c+1) should also map complement to complement. Contradiction!

**Step 4: Half-split.** Since c·H ≠ H, the set {h ∈ H : c·h ∈ H} is a proper subgroup of H with index 2 in H, giving |H ∩ c⁻¹H| = |H|/2.

**Step 5: Count.** The triple count = (|H|/2)² + (|H|/2)² = |H|²/2 = (2^{n-1})²/2 = 2^{2n-3}.

### Why the Formula is Independent of v₁, v₂

The remarkable fact that the count is the **same** for all distinct nonzero v₁, v₂ comes from the hyperplane structure: the only property used is c = v₂/v₁ ∉ {0,1}, which holds for all distinct nonzero pairs. The intersection |H ∩ c⁻¹H| always equals |H|/2 regardless of c (as long as c ∉ {0,1}).

## Formalization Structure

The formal proof in `KasamiTripleCount.lean` consists of:

### Part 1: Index-2 Subgroup Combinatorics
- `index_two_complement_add` — Two elements outside H sum to an element inside H
- `smul_complement` — If c·H ⊆ H, then c maps complement to complement
- `not_smul_subset` — H is NOT invariant under c ∉ {0,1} (the key lemma)
- `card_smul_inter` — |{h ∈ H : c·h ∈ H}| = |H|/2
- `card_index_two` — |H| = |F|/2

### Part 2: The Triple Count
- `tripleCount_hyperplane` — |{triples}| = |H|²/2 (the main theorem)

### Part 3: Arithmetic Bridge
- `hyperplane_card` — |H| = 2^{n-1} for |F| = 2^n
- `half_sq_pow` — (2^{n-1})²/2 = 2^{2n-3}
- `tripleCount_eq_pow` — The final numerical result

### Part 4: Kasami Connection
- `kasamiExp`, `kasamiFun`, `kasamiDelta` — Definitions
- `kasami_triple_count` — The main theorem with Kasami function

## Axioms Used

The proof depends only on standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Connection to Existing Formalization

This proof builds on the exploration in `kasami-explore/` which established:
- The Walsh-Differential Identity (Theorem 2.3 of Budaghyan)
- AB implies APN
- Walsh support size = 2^{n-1}
- Pair counting in the Walsh support

The current proof takes a different, more direct path through the hyperplane structure, avoiding the Walsh transform machinery entirely for the triple count computation.
