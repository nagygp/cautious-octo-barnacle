# ABTopos Dynamics: Categorical Bridges and Composite Isomorphisms

This module refactors and replaces the old `dynamics-connections/` folder,
integrating the Frobenius–shift dynamics theory directly into the ABTopos
project and building genuine categorical connections to Mathlib.

## Architecture

### `FrobeniusShift.lean` — Core Dynamics
The algebraic dynamics of Frobenius and cyclic shifts:
- **Frobenius iteration** `φᵏ(x) = x^{2^k}` — proven via Mathlib's `frobenius`
- **Gold factorization** `x^{2^k+1} = φᵏ(x) · x` — the shift × identity decomposition
- **Frobenius periodicity** `φⁿ = id` on GF(2ⁿ) — via `FiniteField.frobenius_pow`
- **Cyclic shift** on `ZMod n → ZMod 2` with period n
- **Gold derivative** through Frobenius — char 2 additive structure
- **Coprimality ↔ generation** — `gcd(k,n) = 1 ↔ shift by k generates ℤ/nℤ`

All results connect to Mathlib's `Function.IsPeriodicPt`, `ZMod.unitOfCoprime`.

### `CategoricalBridge.lean` — ABTopos ↔ Mathlib
Genuine categorical connections using Mathlib's category theory:
- **Frobenius in `CommRingCat`** — `CommRingCat.ofHom (frobenius K 2)` with periodicity `φⁿ = 𝟙`
- **Spectral duality functor** — involutive endofunction on `SpectralDatum` with `dual_dual = id`
- **Composite round-trip** — Bent ↔ CoBent ∘ Bridge invariance ∘ Homotopical silence, all consistent
- **Code duality** — dual-dual containment, MacWilliams degree-0 commutativity
- **Frobenius–Gold–Bridge chain** — complete path from `FiniteField.frobenius_pow` to bridge formulas
- **Master connective package** — all connections bundled and verified

### `CompositeIso.lean` — Composed Isomorphisms and Transport
- **`DualSpectralTopos ≃ {n : ℕ // 0 < n}`** — structural `Equiv`
- **Bridge exponent in ℤ** — clean formulation, non-negativity for m,n ≥ 2
- **Bent Parseval identity** — `Σ ‖W(v)‖² = |support| · c²`
- **GF(2) bilinear form** — symmetry, additivity, orthogonality
- **Frobenius iterate shift** — `φ^{k+n} = φ^k` on GF(2ⁿ)
- **Duality transport** — bidirectional: `P(count(𝒯)) ↔ P(count(𝒯^op))`
- **Bridge power-of-two** — the bridge formula is always a power of 2, preserved by duality

## Design Principles

1. **No deep sorries**: Every connection routes through *already-proven* ABTopos results
   and *existing* Mathlib infrastructure.

2. **Genuine Mathlib integration**: Uses `CommRingCat`, `CategoryTheory.Iso`,
   `Function.IsPeriodicPt`, `Equiv`, `ZMod`, `FiniteField.frobenius_pow`.

3. **Composite isomorphisms**: The "sending the proof along a path" approach —
   composing Frobenius periodicity ∘ Gold factorization ∘ Bent duality ∘ Bridge counting
   gives a complete chain from Mathlib primitives to ABTopos bridge formulas.

4. **Dual-context transport**: Properties proved for a spectral topos automatically
   transfer to its dual, via `bridge_fixed_point` and `dualFunctor_involution`.

## Axiom Usage

All theorems use only standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
No `sorryAx` appears in any of the new dynamics module.
