# Summary of changes for run f83307eb-2609-4941-b3fa-28a8e45aa328
## Formalization: AB implies APN and Kasami is APN

I have formalized the theorem that **Almost Bent (AB) functions are Almost Perfect Nonlinear (APN)** over finite fields of characteristic 2, following the proof strategy from Chabaud-Vaudenay (EUROCRYPT '94), and derived the corollary that **Kasami functions are APN**.

### Files created

1. **`RequestProject/Defs.lean`** — Core definitions:
   - `chi`: The additive character χ(x) = (−1)^{Tr(x)} using the absolute trace
   - `walshTransform`: The Walsh-Hadamard transform W_f(a,b) = ∑_x χ(bf(x) + ax)
   - `deltaCount`: The differential count δ_f(a,b) = |{x : f(x+a) + f(x) = b}|
   - `IsAPN`: Almost Perfect Nonlinear — δ_f(a,b) ≤ 2 for all a ≠ 0, b
   - `IsAB`: Almost Bent — W_f(a,b)² ∈ {0, 2|F|} for all a and b ≠ 0
   - `kasamiExponent`: The exponent d = 2^{2k} − 2^k + 1
   - `kasamiFunction`: The power map f(x) = x^d

2. **`RequestProject/ABImpliesAPN.lean`** — Proofs (~386 lines):

   **Fully machine-verified theorems** (no sorry):
   - `chi_add`, `chi_sq`, `chi_values` — Character arithmetic
   - `sum_chi_mul` — Character orthogonality: ∑_x χ(ax) = |F|·[a=0]
   - `walsh_b_zero` — W_f(a,0) = |F|·[a=0]
   - `parseval_walsh` — Parseval's identity: ∑_a W_f(a,b)² = |F|²
   - `delta_sum`, `delta_at_zero`, `delta_even` — Properties of differential counts
   - `fourth_moment_identity` — **The global identity**: ∑_{a,b} W_f(a,b)⁴ = |F|² · ∑_{a,b} δ_f(a,b)²
   - `ab_walsh_fourth_per_b`, `ab_total_fourth_moment` — AB fourth moment computation
   - `delta_sq_lower_bound` — Lower bound: ∑_b δ² ≥ 2|F| (from solution pairing)
   - `delta_sq_eq_implies_apn` — Equality ∑_b δ² = 2|F| forces δ ≤ 2
   - **`ab_implies_apn`** — **Main theorem: AB ⟹ APN** ✓

   **Kasami corollaries:**
   - `kasami_is_ab` — Kasami functions are AB (stated with `sorry`; this is a deep number-theoretic result from Kasami 1971 / Dillon-Dobbertin 1999 involving cross-correlation of m-sequences)
   - `kasami_is_apn` — **Kasami is AB ⟹ Kasami is APN** — follows immediately from `ab_implies_apn` applied to `kasami_is_ab`

### Proof strategy

The proof of AB ⟹ APN follows Chabaud-Vaudenay's approach using Fourier analysis over GF(2^n):

1. Establish the **global fourth moment identity** connecting Walsh coefficients to differential uniformity via double character orthogonality
2. For AB functions, compute the total fourth moment as |F|³(3|F| − 2) using the AB spectrum constraint and Parseval
3. Derive that ∑_{a≠0} ∑_b δ(a,b)² = 2|F|(|F|−1)
4. Combine with the **combinatorial lower bound** ∑_b δ² ≥ 2|F| (from the pairing of solutions x ↔ x+a in characteristic 2) to conclude each inner sum equals exactly 2|F|, forcing δ(a,b) ∈ {0,2} — i.e., APN

### Axiom status

- `ab_implies_apn`: depends only on `propext`, `Classical.choice`, `Quot.sound` — **fully verified, no sorry**
- `kasami_is_apn`: depends on `sorryAx` (via the deep `kasami_is_ab` assumption)