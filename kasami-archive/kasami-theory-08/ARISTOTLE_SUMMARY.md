# Summary of changes for run 8bb14c3b-73d9-47f6-b54d-220fd7af8642
## APN / Almost Bent Function Theory — Lean 4 Formalization

I have created a comprehensive formalization of APN (Almost Perfect Nonlinear) and Almost Bent (AB) function theory in 5 Lean 4 modules under `RequestProject/APN/`:

### Module Structure (666 lines total)

| File | Lines | Description |
|------|-------|-------------|
| `Defs.lean` | 148 | Core definitions: differential uniformity, APN, Walsh transform, AB, nonlinearity, component functions |
| `Basic.lean` | 131 | Basic APN properties: DDT identities, derivative characterizations, invariants |
| `WalshTransform.lean` | 171 | Walsh–Hadamard transform: sign function, character orthogonality, **Parseval's identity** |
| `AlmostBent.lean` | 124 | AB theory: **autocorrelation-Walsh identity**, AB↔component spectrum, delta values for APN |
| `Examples.lean` | 92 | Concrete examples and non-examples |

### Results: 35 of 36 theorems fully proved (no sorry)

**Key proved theorems include:**
- **Parseval's identity** — `∑_a W_f(a)² = 2^{2n}` (both Boolean and vectorial versions)
- **Character orthogonality** — `∑_a (-1)^{⟨a,v⟩} = 0` for `v ≠ 0`
- **Autocorrelation-Walsh identity** — `2^n · C_f(a) = ∑_u W_f(u)² · (-1)^{⟨u,a⟩}`
- **APN ↔ differential uniformity ≤ 2**
- **APN delta values** — For APN functions, `Δ(a,b) ∈ {0, 2}` for `a ≠ 0`
- **APN ↔ two-to-one derivatives** (char 2 characterization)
- **APN invariance** under translation and constant addition
- **AB ↔ component spectrum** characterization
- Various non-APN results (zero function, identity, additive functions)

### One remaining sorry

- **`ab_implies_apn`** (AB ⟹ APN) — This is the deepest theorem in the theory, requiring the fourth-moment identity `∑ W^4 = 2^{2n} · ∑ Δ²`, which involves intricate Fourier-analytic arguments beyond the currently formalized infrastructure.

All 35 proved theorems have been verified to use only standard axioms (propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler) — no `sorryAx`.

A detailed `README.md` with the full theorem listing is provided at `RequestProject/APN/README.md`.