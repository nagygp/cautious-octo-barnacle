# Soundness & Connectedness Analysis — MTupleCount.lean & Full Project

## Executive Summary

**MTupleCount.lean is internally sound**: it compiles with zero `sorry`, uses only
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and every theorem in
it is genuinely proved. The pure number-theoretic content is mathematically correct.

**However, the formalization has two structural gaps that prevent it from being a
fully connected, end-to-end proof grounded in concrete finite-field mathematics:**

1. **The §1 definitions are decorative**: `differentialSet`, `mTupleSet`, and
   `mTupleCount'` are defined over actual finite fields but are **never used** by
   any theorem in the file. All theorems operate on abstract `ℕ` parameters
   (`n, m, δ, κ`) with hypotheses — making them pure arithmetic, not finite-field
   theory.

2. **The bridge to concrete mathematics (WalshGauss.lean) has 16 sorries**: The
   crucial "known results" that MTupleCount.lean's hypotheses represent — the
   spectral identity `2^n · κ = δ^m` and the APN cardinality `δ = 2^{n-1}` — are
   formalized in `WalshGauss.lean` but remain unproved.

---

## Detailed File-by-File Assessment

### 1. `ABTopos/Spectral/MTupleCount.lean` ✅ (Sorry-free, sound)

| Section | Status | Notes |
|---------|--------|-------|
| §1 Definitions | ✅ Compiles | `differentialSet`, `mTupleSet`, `mTupleCount'` defined but **unused** |
| §2 Nat subtraction helpers | ✅ Proved | `sub_bound` |
| §3 Arithmetic lemmas | ✅ Proved | `power_of_power`, `exponent_identity`, `exponent_split`, `power_split` |
| §4 Primal theorem | ✅ Proved | `primal_mTupleCount` + corollaries for m=3,4,5 |
| §5 Dual lemmas | ✅ Proved | `dual_count_product`, `dual_unique_mth_root`, `dual_C_forced` |
| §6 Dual theorem | ✅ Proved | `dual_theorem`, `dual_C_eq_m` |
| §7 Equivalence | ✅ Proved | `primal_dual_equivalence` |
| §8 Kasami triple | ✅ Proved | `kasami_triple_equivalence` |
| §10 Package | ✅ Proved | `mTupleCount_complete_package` |

**Mathematical assessment**: The primal-dual equivalence is correct:

> Given `2^n · κ = δ^m` (spectral identity), then
> `κ = 2^{(m-1)n - m}` if and only if `δ = 2^{n-1}`.

This is **valid arithmetic** — it's essentially the statement that if
`2^n · κ = (2^{n-1})^m = 2^{m(n-1)}`, then `κ = 2^{m(n-1) - n} = 2^{(m-1)n - m}`,
and vice versa. The proofs use `Nat.pow_left_injective` and `Nat.pow_right_injective`
from Mathlib, which are well-established.

**What it does NOT prove**: That the spectral identity `2^n · κ = δ^m` actually holds
for any concrete APN function over a finite field. That is the content of
WalshGauss.lean.

### 2. `ABTopos/Spectral/WalshGauss.lean` ❌ (13 sorries, down from 16)

This file contains the **hard mathematics** connecting abstract arithmetic to
concrete finite-field APN functions. Every sorry here is a real mathematical theorem
from the literature:

| Sorry | Mathematical Content | Difficulty |
|-------|---------------------|------------|
| `AbsTrace` (def) | Absolute trace `Tr: GF(2^n) → GF(2)` | 🔴 Needs Mathlib finite field trace |
| ~~`χ_add`~~ | ~~Additivity of canonical character~~ | ✅ **Proved** |
| ~~`χ_sq`~~ | ~~`χ(x)^2 = 1`~~ | ✅ **Proved** |
| `χ_orthogonality` | Character orthogonality | 🔴 Deep character theory |
| `stickelberger_norm` | `‖𝔤(ψ)‖² = q` | 🔴 Stickelberger theorem |
| ~~`gauss_norm`~~ | ~~`‖𝔤(ψ)‖ = √q`~~ | ✅ **Proved** (from stickelberger) |
| `walsh_gauss_decomposition` | Walsh-Gauss decomposition | 🔴 Deep |
| `kasami_apn` | Kasami exponents are APN | 🔴 Kasami 1971 |
| `walsh_parseval` | Parseval identity | 🟡 Standard but needs character theory |
| `apn_fourth_moment_bound` | Fourth moment bound | 🔴 Requires APN theory |
| `cauchy_schwarz_rigidity` | Spectral flatness from moment bounds | 🔴 Analysis argument |
| `ab_spectral_collapse` | APN+n odd ⟹ AB | 🔴 Chabaud-Vaudenay |
| `ab_delta_hat_spectrum` | deltaHat spectrum collapse | 🔴 |
| `delta_card` | `|Δ| = 2^{n-1}` | 🔴 Key APN result |
| `combined_identity_ab` | `|𝔽|·|Triples| = |Δ|³` | 🔴 Fourier identity |
| `fourier_triple_identity` | Fourier triple-sum identity | 🔴 |

**Mathlib coverage assessment**: Most of these results require finite field trace
functions (`FiniteField.trace`), Gauss sum infrastructure, and character theory
for finite fields. As of Mathlib4 (v4.28.0), the trace map exists
(`FiniteField.trace`) but the full Gauss sum theory and Stickelberger's theorem
are **not formalized**. Building all of this from scratch would be a substantial
multi-week effort.

**Note**: `kasami_triple_count` at the end of WalshGauss.lean does compile — but
it depends on sorry'd lemmas (`combined_identity_ab`, `delta_card`), so it is not
a genuine proof.

### 3. `ABTopos/Conjectures/APN.lean` ✅ (Sorry-free after fix)

The original `apn_image_size` was stated for general `AddCommGroup` with only
`2 ∣ |G|` — but the theorem requires an exponent-2 hypothesis (`∀ g, g + g = 0`)
to guarantee fibre pairing. We:
- Commented out the original statement with an explanation
- Added a corrected version with `(hExp2 : ∀ g : G, g + g = 0)`
- Proved it from scratch, along with the helper `diff_map_pair` and downstream `apn_half_space_decomposition`

All active code in APN.lean is now sorry-free.

### 4. Topos Infrastructure (`PNBoolean.lean`, `Duality.lean`, `ElemTopos.lean`, `TypeTopos.lean`) ⚠️

These files compile with no sorry, but the theorems are **definitionally trivial**:

- `internalMTupleCount` is *defined* as `𝒯.card_Ω ^ ((m-1)*n - m)`, so
  `boolean_topos_recovery : internalMTupleCount booleanSpectralTopos n m = 2^{(m-1)n-m}`
  is literally `rfl`.
- `geometric_morphism_transfers_count` proves `A * B = B * A` by `ring`.
- `bridge_fixed_point` and duality theorems are similarly trivial because the
  "duality functor" is defined to preserve the count by construction.

This is not mathematically wrong — it's a valid axiomatization of an abstract
framework. But the framework is not connected to actual topos theory from Mathlib
(`CategoryTheory.Topos`), Grothendieck toposes, or sheaf theory. It is a
**standalone abstract model** whose axioms are chosen to make the desired theorems
true by definition.

### 5. Other Files (SpectralObject, KasamiCIC, etc.) ✅

These compile with no sorry and contain genuine (if sometimes simple) proofs about
the custom data structures defined in the project.

---

## The Connection Gap

The logical chain that would make the formalization end-to-end is:

```
Concrete APN function f on GF(2^n)
    │
    ▼ (WalshGauss.lean — 16 sorries)
|Δ(f)| = 2^{n-1}  and  spectral identity: 2^n · κ_m = |Δ|^m
    │
    ▼ (MTupleCount.lean — proved ✅)
κ_m = 2^{(m-1)n - m}  ↔  |Δ| = 2^{n-1}
    │
    ▼ (PNBoolean.lean — trivially true by definition)
internalMTupleCount(Boolean, n, m) = 2^{(m-1)n - m}
```

**The middle link (MTupleCount.lean) is fully proved.** But the top link
(WalshGauss.lean) is sorry'd, and the bottom link (PNBoolean.lean) is trivially
true by how `internalMTupleCount` is defined. So the chain is:
- **Top**: Unproved concrete ↔ abstract bridge
- **Middle**: Proved abstract arithmetic
- **Bottom**: True by definition

### What Would Make It Fully Connected

1. **Prove `delta_card`** and **`combined_identity_ab`** in WalshGauss.lean
   (the spectral identity). This requires building finite field trace and
   character theory, which is a major undertaking.

2. **Connect §1 definitions to §4+ theorems** in MTupleCount.lean: prove that
   `mTupleCount' 𝔽 f m coeffs` (the concrete count) equals the abstract `κ`
   satisfying the spectral identity. This requires the Fourier-analytic
   machinery from WalshGauss.lean.

3. **Fix `apn_image_size`** in APN.lean: add a `CharP G 2` or `∀ g, g + g = 0`
   hypothesis, or restrict to `ZMod 2`-vector spaces.

4. **Ground the topos framework**: connect `SpectralTopos` to Mathlib's actual
   category theory, or at minimum acknowledge it as an abstract axiomatization
   rather than a derived construction.

---

## Verdict

| Aspect | Grade | Notes |
|--------|-------|-------|
| MTupleCount.lean internal soundness | ✅ A | Sorry-free, standard axioms, correct arithmetic |
| MTupleCount.lean mathematical significance | ⚠️ B | Valid but essentially pure ℕ arithmetic with hypotheses |
| Connection to concrete APN theory | ❌ D | WalshGauss.lean has 13 sorries blocking the bridge |
| Topos framework grounding | ⚠️ C | Self-consistent but axioms chosen to make theorems trivial |
| Overall formalization completeness | ⚠️ C+ | Sound skeleton with correct structure, but hard math unproved |

The project has a **well-designed proof architecture** — the decomposition into
primal/dual/equivalence is clean, and the file structure is logical. The gap is
that the computationally hard mathematics (character theory, Gauss sums,
Stickelberger, Fourier analysis over finite fields) remains unformalized, and
much of the required Mathlib infrastructure doesn't yet exist.
