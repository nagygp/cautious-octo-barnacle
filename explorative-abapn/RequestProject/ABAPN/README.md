# AB/APN Function Theory — Lean 4 Foundations

A bottom-up, sorry-free foundation for Almost Perfect Nonlinear (APN) and Almost Bent (AB) function theory over finite fields, built entirely on existing Mathlib infrastructure.

## Module Structure (11 files, ~107 lemmas, 0 sorries)

### Core (`Defs.lean`)
- **Definitions**: `diffMap`, `deltaSet`, `deltaCount`, `diffUniformity`, `IsAPN`, `IsPN`, `IsDiffUniform`
- **API**: membership, bounds, PN ⟹ APN, identity function counts
- **Mathlib building blocks**: `Finset.filter`, `Finset.card`, `Function.Injective`

### Characteristic 2 (`CharTwo.lean`)
- `add_self_eq_zero`, `neg_eq_self`, `sub_eq_add` — char 2 arithmetic
- `add_sq`, `add_pow_two_pow` — Frobenius identity (x+y)^(2^n) = x^(2^n) + y^(2^n)
- `frobenius_eq_sq`, `iterateFrobenius_eq` — connecting to Mathlib's `frobenius`
- `frobenius_add`, `iterateFrobenius_add` — additivity via `map_add`
- **Mathlib building blocks**: `CharP`, `frobenius`, `iterateFrobenius`

### Discrete Derivative (`Derivative.lean`)
- Zero direction: `diffMap_zero`, `deltaCount_zero_zero/ne`
- Linearity: `diffMap_add`, `diffMap_smul`, `diffMap_const`, `diffMap_id`
- Second order: `diffMap₂_eq`, `diffMap₂_comm` (symmetry)
- Direction additivity: `diffMap_add_dir`
- Composition: `diffMap_comp_addHom`
- Counting: `sum_deltaCount_eq_card` (partition of unity)
- **Mathlib building blocks**: `AddMonoidHom`, `Finset.sum`, `Pi.add`

### Walsh Transform (`Walsh.lean`)
- **Definitions**: `walshTransform`, `autoCorr`
- Boundary values: `walshTransform_zero_zero/left/right`
- **Parseval's theorem**: `∑_{a,b} ‖W_f(a,b)‖² = |F|³` (fully proved!)
- `autoCorr_eq_sum_deltaCount` — connecting autocorrelation to delta counts
- `walshTransform_of_additive` — Walsh spectrum of linear functions is {0, |F|}
- **Mathlib building blocks**: `AddChar`, `Finset.sum`, `Complex.norm`, `AddChar.sum_eq_ite`

### Power Functions (`Power.lean`)
- `powerFn`, `cubeFn`, `inverseFn` — definitions
- `cube_diff_char2`, `cube_diff_linear_part`, `cube_linear_part_additive` — cube analysis
- **Gold exponent identity**: `gold_diff_char2` — (x+a)^(2^k+1) - x^(2^k+1) = a^(2^k+1) + a·x^(2^k) + a^(2^k)·x
- `gold_linear_part_additive` — linearized part is F₂-linear
- **Mathlib building blocks**: `HPow`, `frobenius`, `add_pow_char_pow`

### Morphisms & Equivalences (`Morphism.lean`)
- `AffineMap` structure, `IsEAEquiv`, `IsCCZEquiv`, `graphSet` — definitions
- **Preservation theorems**: `isAPN_add_const`, `isAPN_translate`, `isAPN_comp_ringHom`, `isAPN_smul_pre/post`, `isAPN_add_linear`
- Frobenius: `isAPN_frobenius_comp`, `isAPN_comp_frobenius`, `isAPN_power_double_iff`
- `isAPN_of_bijective_inverse` — inverses of APN permutations are APN
- **Mathlib building blocks**: `RingHom`, `Function.Bijective`, `Equiv.Perm`, `frobenius`

### Permutations & Fibers (`Perm.lean`)
- `IsAtMostTwoToOne` — definition
- `isAPN_iff_diffMap_atMost2to1` — equivalent characterization
- `fiber_card_of_perm`, `bijective_isAtMostTwoToOne`
- **Pairing theorem**: `deltaSet_pair` — in char 2, solutions come in pairs {x, x+a}
- `deltaCount_even` — consequence: delta counts are always even
- `isAPN_iff_deltaCount_zero_or_two` — the sharp char 2 characterization
- `powerFn_apn_normalize` — normalization for power functions
- **Mathlib building blocks**: `Equiv.Perm`, `Finset.card_eq_one`

### Linear Algebra (`LinearAlgebra.lean`)
- `IsF2Linear` — F₂-linearity predicate
- Closure: `frobenius_isF2Linear`, `iterFrob_isF2Linear`, `isF2Linear_comp/add/smul/zero/id`
- `f2Kernel`, `f2Kernel_card_pow_two` — kernel is always a power of 2
- `f2Linear_injective_iff_kernel_trivial`
- **Gold kernel**: `goldLinearPart`, `goldLinearPart_isF2Linear`, `goldLinearPart_self/zero`
- `f2Linear_image_card` — |image| × |kernel| = |F|
- **Mathlib building blocks**: `Module`, `LinearMap`, `Submodule`, `ZMod`

### Coding Theory (`Coding.lean`)
- `graphCode` — graph code definition, `graphCode_card`
- `diffMultiset` — difference multiset
- `apn_diff_bound` — code-theoretic interpretation
- **Mathlib building blocks**: `Finset.image`, `Prod`

### Topology & Dynamics (`Topology.lean`)
- `frobOrbit` — Frobenius orbit
- `frobenius_fixedPt_iff`, `frobFixedPts_eq` — fixed points are {0, 1}
- `IsFrobConj` — Frobenius conjugacy, `isFrobConj_refl`, `isFrobConj_symm_of_pow_two`
- `isAPN_of_frobConj` — conjugate exponents give same APN property
- `perm_implies_periodic` — elements are periodic under permutations
- **`power_fixed_points_card`** — |{x : x^d = x}| = gcd(d-1, |F|-1) + 1 (fully proved!)
- **Mathlib building blocks**: `frobenius`, `Equiv.Perm`, `orderOf`, `IsCyclic`

### Polynomials (`Polynomial.lean`)
- `exists_poly_of_fun` — Lagrange interpolation (fully proved!)
- `linearizedPoly`, `linearizedPoly_eval`, `linearizedPoly_additive`
- `IsDOPolynomial`, `gold_is_DO` — Gold exponents are DO polynomials
- `not_isAPN_of_degree_one`, `not_isAPN_zero` — non-APN results (|F| > 2)
- **Mathlib building blocks**: `Polynomial`, `Polynomial.eval`, `Finset.sum`

## Design Principles

1. **Each lemma proves one identity** — tiny, composable building blocks
2. **Uses simple Mathlib patterns** — no deep infrastructure beyond what's available
3. **Diverse Mathlib dependencies**: `CharP`, `AddChar`, `frobenius`, `Polynomial`, `Equiv.Perm`, `RingHom`, `AddMonoidHom`, `Module`, `Finset`, `Function.Injective/Bijective`, `Complex.norm`, `orderOf`, `IsCyclic`, `Subgroup.zpowers`
4. **Bottom-up**: core definitions → char 2 identities → derivative algebra → Walsh transform → power functions → morphisms → applications
5. **Statements verified against counterexamples**: false conjectures (like "permutation conjugation preserves APN" or "periodic under any function") were detected and corrected

## Future Directions

- AB (Almost Bent) definition via Walsh spectrum values {0, ±2^((n+1)/2)}
- AB ⟹ APN theorem
- Concrete APN proofs: cubing over GF(2^n) with n odd
- Kasami exponent APN proof
- Walsh fourth moment / deltaCount² identity
- Algebraic geometry: varieties defined by APN conditions
- Group cohomology connections
