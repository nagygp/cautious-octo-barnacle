# Summary of changes for run b142f7fc-5f92-4c0a-a944-272c74d612fb
## AB/APN Function Theory — Lean 4 Foundations

Built a comprehensive, **sorry-free** foundation for Almost Perfect Nonlinear (APN) and Almost Bent (AB) function theory across **11 Lean files** with **~107 fully proved lemmas**.

### Files created (all under `RequestProject/ABAPN/`)

| File | Content | Key Mathlib building blocks |
|------|---------|----------------------------|
| `Defs.lean` | Core definitions: `IsAPN`, `deltaSet`, `deltaCount`, `diffUniformity` | `Finset.filter`, `Finset.card` |
| `CharTwo.lean` | Char 2 identities: `sub = add`, `(x+y)^(2^n) = x^(2^n) + y^(2^n)`, Frobenius | `CharP`, `frobenius`, `iterateFrobenius` |
| `Derivative.lean` | Discrete derivative algebra: linearity, symmetry, partition of unity | `AddMonoidHom`, `Finset.sum` |
| `Walsh.lean` | Walsh transform, **Parseval's theorem**, autocorrelation-deltaCount link, spectrum of linear functions | `AddChar`, `Complex.norm`, `AddChar.sum_eq_ite` |
| `Power.lean` | Power functions, Gold/Kasami exponents, Gold difference identity | `HPow`, `add_pow_char_pow` |
| `Morphism.lean` | EA/CCZ equivalence, APN preservation under translations/scalings/Frobenius/inverse | `RingHom`, `Function.Bijective`, `Equiv.Perm` |
| `Perm.lean` | Fiber structure: pairing theorem, `deltaCount` is always even in char 2, sharp APN characterization | `Equiv.Perm`, `Finset.card` |
| `LinearAlgebra.lean` | F₂-linearity, kernel is power-of-2, Gold kernel analysis, image-kernel formula | `Module`, `Submodule`, `ZMod` |
| `Coding.lean` | Graph codes, difference multisets | `Finset.image`, `Prod` |
| `Topology.lean` | Frobenius dynamics, fixed points = {0,1}, Frobenius conjugacy, `|{x^d=x}| = gcd(d-1,|F|-1)+1` | `orderOf`, `IsCyclic`, `Subgroup.zpowers` |
| `Polynomial.lean` | Lagrange interpolation, linearized polynomials, DO polynomials, Gold is DO | `Polynomial`, `Polynomial.eval` |

### Highlights
- **Parseval's theorem** for Walsh transforms — fully proved
- **Pairing theorem**: in char 2, APN solutions come in pairs, giving `deltaCount ∈ {0, 2}`
- **Gold exponent identity**: `(x+a)^(2^k+1) - x^(2^k+1) = a^(2^k+1) + a·x^(2^k) + a^(2^k)·x`
- **Power fixed points**: `|{x : x^d = x}| = gcd(d-1, |F|-1) + 1` via cyclic group theory
- **APN preservation** under 8 different transformations (translation, scaling, Frobenius, inverse, etc.)
- **False conjectures detected and corrected**: e.g., "permutation conjugation preserves APN" (false for non-affine σ), "every element is periodic under any function" (false for non-permutations)

### Design
Each lemma proves one identity using simple, already-available Mathlib patterns — no deep missing infrastructure. The library draws from diverse Mathlib areas: finite fields, characters, polynomials, group theory, linear algebra, combinatorics, topology/dynamics, and coding theory. See `RequestProject/ABAPN/README.md` for full details.