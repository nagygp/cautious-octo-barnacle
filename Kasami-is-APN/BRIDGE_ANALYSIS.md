# Kasami Cross-Term Bridge Analysis — Status Report

## What This Is

`KasamiCrossBridge.lean` explores `kasami_cross_nonzero_impossible` (KasamiCore.lean:107)
through 7 categorical/topos-theoretic lenses following Caramello's bridge technique.

**This is NOT the topological conjugacy / symbolic dynamics bridge.** These are
algebraic/categorical bridges: linearized polynomial kernels, Galois cohomology,
projective geometry, Ω-logic, and Heyting algebra perspectives.

## The Key Discovery: The Factorization Bridge

The central result (fully proved, no sorry):

```
Cross(s, P) = s^{q+1} · L_k(P/s)
            = N_k(s)  · Tr_k(P/s)
```

This factorizes the cross term into:
- **Norm** N_k(s) = s^{q+1} (multiplicative structure)
- **Linearized polynomial** L_k(P/s) = (P/s)^q + P/s (additive structure)

### Consequence (fully proved):

```
Cross = 0  ⟺  P/s ∈ ker(L_k) = GF(2^{gcd(k,n)})
```

When gcd(k,n) = 1: ker(L_k) = {0, 1}, so Cross = 0 ⟺ P = 0 or P = s.

## Does Full Formalization Give a Proof?

**The theorem reduces to one open lemma:**

```lean
theorem lam_forced_trivial : ... linPolyL k F (P / s) = 0 := by sorry
```

This says: "the Kasami collision constraints force P/s ∈ ker(L_k)."

If proved → `cross_nonzero_impossible_bridge` follows (3 lines) →
equivalent to `kasami_cross_nonzero_impossible` → Kasami APN theorem.

**But `lam_forced_trivial` IS the hard part.** The bridge *reformulates*
the problem more cleanly, but doesn't yet solve it.

## Proved vs. Open

### Fully Proved (7 lemmas, no sorry)
- `crossForm_via_linearized` — The factorization bridge
- `cross_zero_iff_ratio_in_kernel` — Cross = 0 ↔ ratio in kernel
- `cross_eq_norm_trace` — Cross = Norm × Trace
- `key_equation_norm_trace` — Key equation in norm-trace form
- `cross_zero_iff_frob_fixed` — Projective fixed-point equivalence
- `norm_expansion_bb` — Norm expansion identity
- `gold_derivative_bb` — Gold derivative identity
- `s_norm_equation_bb` — s-norm equation

### Blackboxed (proved in KasamiAPN project, imported as sorry)
- `frobenius_fixed_bb`, `kernel_theorem_bb`, `key_equation_bb`, `H_ne_one_collision_bb`

### Open
- **`lam_forced_trivial`** — THE key open question
- `linPolyL_kernel_card` — Frobenius kernel cardinality (deep, established)
- `p_norm_equation_bb` — P-norm equation (straightforward)

## Most Promising Proof Path for `lam_forced_trivial`

**Strategy A (Norm Quotient):**
1. P^{q+1} = lam^{q+1} · s^{q+1} (tautology)
2. Expand both via norm_expansion
3. After cancellation: equation in lam with L_k(lam) as factor
4. Conclude L_k(lam) = 0

**Strategy B (Hilbert 90):**
- The ratio P/s defines a Galois cocycle
- Hilbert 90 says H¹ = 0 for cyclic extensions
- Therefore the cocycle is a coboundary → P/s ∈ GF(q)

**Strategy C (Frobenius Iteration):**
- Sum the key equation and its Frobenius iterates
- Derive a trace condition forcing cross = 0
