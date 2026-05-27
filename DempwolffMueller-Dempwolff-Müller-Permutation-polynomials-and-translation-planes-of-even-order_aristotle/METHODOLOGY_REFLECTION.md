# Methodology Reflection: DAG Decomposition for Lean 4 Formalization

## What Worked in This Session

### The DAG decomposition approach proved highly effective for the critical path

The **Foundational Layer FL-A** (Bare-Function Lemma 3.1) was the key:
- **17 atomic lemmas** decomposed from 1 hard sorry (`adjoint_swap_bij`)
- **10 easy** (🟢): all proved on first attempt by automation
- **5 meh** (🟡): all proved on first attempt with proof sketches
- **2 assembly** (🟡): both proved, completing the layer
- **0 hard remaining**: every "hard" was decomposed away

This single foundational layer collapsed **4 sorries** in a chain:
`adjoint_swap_bij` → `adjoint_swap_bijective` → `LxXk'_bijective_v2` → `LxXk'_bijective`

### The "sorry audit → abstraction" cycle was measurable

The methodology question *"What single theorem would make 5+ sorries disappear?"*  
led directly to FL-A. The answer was: "A bare-function version of Lemma 3.1 that  
works with additive `F → F` functions and `frobSum` instead of LinearMap."

### Structural labels outperformed subjective difficulty

The classification into:
- **atomic/library** (already in Mathlib: `mul_pow`, `Finite.injective_iff_surjective`)
- **rewrite-only** (1-3 tactics: `additive_zero`, `DeltaBare_is_additive'`)
- **composite-local** (glue 2+ lemmas: `P_inj_imp_DeltaBare_sub_bij'`)
- **core-theorem** (new invariant: `adjoint_swap_bij_bare`)

...was more predictive than easy/meh/hard. Every "rewrite-only" lemma was proved  
instantly. Every "composite-local" lemma was proved in one attempt with a good  
sketch. The "core-theorem" required careful assembly but worked because all  
sub-components were verified.

### The topological level strategy worked

```
Level 0: mul_pow, Finite.injective_iff_surjective (Mathlib)
Level 1: DeltaBare' (definition), additive_zero, additive_neg, ...
Level 2: PBare_mul_eq', DeltaBare_sub_additive', ...
Level 3: DeltaBare_sub_zero_imp_zero', P_inj_imp_DeltaBare_sub_bij', ...
Level 4: DeltaBare_trace_adjoint', additive_bij_iff_adj_bij'
Level 5: DeltaBare_sub_bij_iff_adj'
Level 6: adjoint_swap_bij_bare (assembly)
```

Proving bottom-up by topological level ensured every dependency was available  
when needed. No backtracking was required.

## What Almost Failed

### The exponent matching subtlety

In `LxXk'_bijective_v2`, my initial approach was:
1. Use `adjoint_swap_bijective` to get bijectivity of `truncTrace m x * x^l`  
   where `l` is the modular inverse of `k`
2. Match `x^l = x^{k'}` using `exp_k'_eq_on_units`

**Problem**: `exp_k'_eq_on_units` gives `x^l = x^{k' * 2^{n-m+1}}`, not `x^l = x^{k'}`.  
So the adjoint swap gives bijectivity of `truncTrace m x * x^{k' * 2^{n-m+1}}`,  
not `truncTrace m x * x^{k'}`.

**Solution**: Pass `l = k'` directly to `adjoint_swap_bijective` instead of using  
`exists_pow_inverse'`. The modular condition `(k * 2^{n-m+1}) * k' ≡ 1 mod (2^n-1)`  
follows from `k * k' ≡ 2^{m-1}` via `exp_mod_chain`.

**Lesson**: The DAG decomposition exposed this subtlety early, because each  
node had a clear interface. In a monolithic proof, this bug would have been  
buried in a long tactic chain.

### The type-level mismatch between truncTrace and frobSum

`truncTrace m x = ∑ x^{2^i}` (CommSemiring) vs `frobSum 2 m x = ∑ x^{2^i}` (Field).  
Definitionally equal but Lean distinguishes the type classes.

**Solution**: A `simp` lemma: `truncTrace n f = frobSum 2 n f`.

**Lesson**: The "Type Boundary Principle" from the methodology document is  
essential. Define foundational layers at the most general type, then specialize  
at the boundary.

## Methodology Assessment

### Is this approach effective for THIS project?

**Yes, strongly.** Evidence:
- 4 of 9 sorries eliminated in one session
- 17/17 atomic lemmas proved without backtracking
- The proof of the main theorem (Theorem 3.2 k' part) fell out as a clean  
  10-step assembly of pre-verified components
- No false lemmas were discovered (the DAG structure caught the exponent  
  mismatch before wasting proof attempts)

### Comparison with other approaches

| Approach | Would it work here? | Why / Why not |
|----------|-------------------|---------------|
| **Monolithic automation** | Partially | The final assembly (adjoint_swap_bij_bare) was proved in one shot, but only because all 16 sub-lemmas were available. Without decomposition, the 500-line proof would be beyond any current tactic. |
| **Proof planning (Edinburgh)** | Partially | The "rippling" technique could handle the rewrite-only lemmas, but the trace adjoint argument requires domain-specific insight that automated planners lack. |
| **Refinement (Event-B)** | Partially | Good for the type refinement (frobSum → truncTrace), but overkill for the algebraic steps. |
| **HTN planning** | Yes | The decomposition IS an HTN plan. The "methods" are: "decompose via Lemma 3.1 structure", "prove additivity", "prove kernel triviality", "compose via trace adjoint". |

### When does decomposition have diminishing returns?

The remaining 5 sorries fall into two categories:

1. **Would benefit from further decomposition**: `spread_diff_via_subst` and  
   `spread_condition_iff_perm_poly` — these share the spread substitution  
   infrastructure and would benefit from a shared foundational layer.

2. **Better served by monolithic proving**: `typeI_inverse_GF2_coeffs` — this  
   is a single-concept lemma (Frobenius commutativity of the inverse) that  
   should be a 3-line proof once the correct statement is identified.

3. **Uncertain**: `bij_of_additive_pow_twist` and `prop_3_5_abstract` —  
   the char 2 cases are trivial (already proved), but the general-p cases  
   may need deeper Galois theory infrastructure.

## Key Takeaways

1. **The sorry audit is the highest-leverage activity.** Finding that one  
   foundational layer (FL-A) collapsed 4 sorries saved ~10x the effort  
   of proving them individually.

2. **Bottom-up proving with topological ordering eliminates backtracking.**  
   Every lemma was proved on the first attempt because its dependencies  
   were verified.

3. **Difficulty labels are less useful than structural labels.** "Easy" and  
   "hard" depend on automation quality. "Rewrite-only" and "composite-local"  
   are intrinsic properties of the proof.

4. **The compression score κ (dependencies collapsed) is the right metric.**  
   FL-A had κ = 4 (collapsed 4 sorries). The individual spread lemmas  
   have κ = 1 each. Prioritize by κ.

5. **The type boundary principle prevents boilerplate explosion.**  
   Defining FL-A at the `frobSum` level (general p, Field constraint)  
   and specializing at the `truncTrace` boundary (p=2, CommSemiring)  
   kept the layer clean and the specialization trivial.
