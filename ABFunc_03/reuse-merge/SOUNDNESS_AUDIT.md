# Soundness Audit: AB/APN Functions via Topos Theory

## Executive Summary

The project is a **mixed bag**: it contains some genuinely proven, non-trivial mathematical results grounded in real spectral theory and combinatorics, alongside structural/categorical scaffolding that is often **tautological or vacuous**. Several key "theorems" are definitional identities (`rfl` proofs), and the central bridge between topos theory and concrete AB functions has a fundamental gap — the Walsh transform in the Boolean topos is defined as a constant, making ALL functions trivially "AB."

**Overall verdict: The spectral theory core (diversity, moments, cube sums) is solid and non-tautological. The topos-categorical bridge layer is largely tautological. The deep finite-field results (WalshGauss.lean) are honestly marked as `sorry`.**

---

## Detailed Analysis by File

### ✅ Genuinely Proven, Non-Tautological Results

These results involve real mathematical reasoning — the proofs are not trivial:

| File | Result | Assessment |
|------|--------|------------|
| `Spectral/SpectralObject.lean` | `bent_diversity_eq_one` | **Genuine theorem.** Bent spectrum ⟹ spectral diversity = 1. Non-trivial Finset cardinality argument. |
| `Spectral/SpectralObject.lean` | `bent_implies_discrete` | **Genuine theorem.** Derives Postnikov discreteness from bent condition via spectral diversity. The proof chain is: bent → diversity = 1 → πₖ = 1. |
| `Spectral/SpectralObject.lean` | `spectralDiversity_pos` | **Genuine.** Positivity of diversity from nontriviality. |
| `Spectral/KasamiCollapse.lean` | `three_valued_cube_sum` | **Genuine algebraic identity.** Partitions a sum over three-valued spectra into positive/negative components. Non-trivial proof. |
| `Spectral/KasamiCollapse.lean` | `three_valued_is_bent` | **Genuine.** Three-valued {0, ±c} spectrum is bent at level c > 0. |
| `Spectral/KasamiCollapse.lean` | `silence_constraint` | **Genuine.** Two distinct nonzero norms ⟹ diversity > 1. Good contrapositive of rigidity. |
| `Spectral/KasamiCollapse.lean` | `noise_prevents_discreteness` | **Genuine corollary.** Spectral noise ⟹ non-discrete Postnikov tower. |
| `Spectral/KasamiCollapse.lean` | `discreteness_iff_unit_diversity` | **Genuine biconditional.** Clean characterization. |
| `Spectral/KasamiCIC.lean` | All results | **Genuine.** Self-contained reformulation of the above without topos language. All proofs are real. |
| `Spectral/MomentConjectures.lean` | `three_valued_moment_general` | **Genuine.** General m-th moment decomposition for three-valued spectra. Non-trivial sum manipulation. |
| `Spectral/MomentConjectures.lean` | `moment_recurrence` | **Genuine.** M_{m+2} = c² · M_m for three-valued spectra. |
| `Spectral/MomentConjectures.lean` | `support_eq_sPos_add_sNeg` | **Genuine.** Support size = s₊ + s₋ for three-valued spectra. |
| `Spectral/MomentConjectures.lean` | `carrier_partition` | **Genuine.** Domain partitions into three disjoint sets. |
| `Bridge/RosettaStone.lean` | `spectral_power_sum_bent` | **Genuine.** Power sum for bent objects decomposes rigidly. |
| `Bridge/RosettaStone.lean` | `discreteness_forces_euler_rigidity` | **Genuine.** Euler characteristic determined by π₀ when discrete. |
| `Bridge/Duality.lean` | `kBent_iff_kCoBent` | **Genuine.** k-Bent ↔ k-CoBent via conjugation and Heyting algebra swap. |
| `Bridge/Duality.lean` | `pless_moment_zero_eq_card` | **Genuine.** P₀(C) = |C| via weight distribution argument. |
| `Bridge/Duality.lean` | `derived_dual_discreteness` | **Genuine.** Spectral flatness is self-dual. |
| `Foundation/TypeTopos.lean` | Group axiom verifications | **Genuine.** All five group axioms (assoc, units, inverses) formally verified for Type topos group objects. |
| `Foundation/TypeTopos.lean` | `commutatorMTupleCount_comm` | **Genuine.** Abelian commutator count = |G|^{2m}. Non-trivial combinatorial argument. |
| `Foundation/ElemTopos.lean` | `ABFunc.category` | **Genuine.** Category laws (id_comp, comp_id, assoc) for AB functions. Real proof, not `rfl`. |
| `CodingTheory/BinaryCode.lean` | `mTupleCount_eq_card_pow` | **Genuine** (if proven). m-tuple count for linear codes. |
| `Conjectures/APN.lean` | `fibre_sum_eq_card` | **Genuine.** Fibre partition identity. |

### ⚠️ Tautological / Definitionally True Results

These "theorems" are `rfl` or follow immediately from definitions — they encode no real mathematical content:

| File | Result | Issue |
|------|--------|-------|
| `Bridge/PNBoolean.lean` | `boolean_topos_recovery` | **`rfl`.** The internal count was *defined* to be the classical count. |
| `Bridge/PNBoolean.lean` | `pValued_topos_pn_recovery` | **`rfl`.** Same issue. |
| `Bridge/PNBoolean.lean` | `pn_boolean_exponent_match` | **Tautological.** Both counts were defined with the same exponent `(m-1)*n - m`. The "match" is by construction. |
| `Bridge/PNBoolean.lean` | `pn_boolean_relative_existence` | **Tautological.** The Boolean relative is *defined* as the thing satisfying the property, so the theorem is vacuous. |
| `Bridge/PNBoolean.lean` | `bridge_theorem` | **Largely `rfl`.** All three parts follow directly from definitions. No mathematical content beyond the definitions themselves. |
| `Bridge/PNBoolean.lean` | `geometric_morphism_transfers_count` | **`ring`.** Proves `a * b = b * a` (commutativity of natural number multiplication). Not a theorem about geometric morphisms. |
| `Bridge/PNBoolean.lean` | `coulterMatthews_boolean_relative`, `dingHelleseth_boolean_relative` | **`rfl`.** These just instantiate the tautological bridge theorem. |
| `Bridge/Duality.lean` | `bridge_fixed_point` | **`rfl`.** The duality functor is defined as the identity (`card_Ω := 𝒯.card_Ω`), so the "fixed point" is trivially true. |
| `Bridge/Duality.lean` | `dualFunctor_involution` | **`simp`.** Involution of the identity is trivial. |
| `Bridge/Duality.lean` | `bridge_symmetric` | **`rfl`.** Forward and reverse bridges are literally the same definition. |
| `Bridge/Duality.lean` | `bridge_self_dual_invariance` | **`rfl`.** Combines trivially true components. |
| `Bridge/Duality.lean` | `homotopical_silence_self_dual` | **`simp`.** The dual has the same homotopy groups by definition. |
| `Spectral/KasamiCollapse.lean` | `pless_exponent_agreement` | **`rfl`.** `toposExponent` and `plessExponent` are literally the same definition. |
| `Spectral/KasamiCollapse.lean` | `topos_classical_bridge` | **`rfl`.** Same formula, same definitions. |
| `Spectral/KasamiCIC.lean` | `exponent_agreement`, `boolean_recovery`, `pn_recovery` | **`rfl`.** Definitional identities. |
| `Spectral/MomentConjectures.lean` | `κ₃_eq_κ_3` | **`simp`.** κ₃ = κ(3) by definition. |

### 🔴 Fundamental Gap: Vacuous Walsh Transform

**The most critical issue in the entire project:**

In `Foundation/TypeTopos.lean`, the Walsh transform for the Boolean topos is defined as:

```lean
def BoolWalshTr (G : Type) [Group G] :
    WalshTr TypeTopos (FinGrpObj G) (BoolCharObj G) where
  wal := fun _f _u => true  -- ← CONSTANT TRUE for ALL functions
```

This means:
- **Every function is AB** in the Boolean topos, regardless of its actual properties.
- The `boolIsAB` instance proves the spectral dichotomy trivially: every generalized element maps to `true`.
- All 10 AB candidates in `Candidates/ABCandidates.lean` are "AB" only because the Walsh transform is constant.
- The `mkABFunc` constructor accepts ANY function and declares it AB.

**Why this matters:** The AB condition is supposed to be a *selective* property — only certain special functions (Gold, Kasami, Welch, Niho, etc.) should satisfy it. When the Walsh transform is trivially constant, the condition loses all discriminating power. The "10 AB candidates" are not verified to be actually AB in any meaningful sense.

### 🟡 Honestly Marked Sorries (WalshGauss.lean)

`WalshGauss.lean` contains 16 `sorry` statements for deep results from finite field theory:
- `AbsTrace` (absolute trace definition)
- `χ_add`, `χ_sq`, `χ_orthogonality` (character properties)
- `stickelberger_norm`, `gauss_norm` (Gauss sum norms)
- `walsh_gauss_decomposition` (Walsh-Gauss decomposition)
- `kasami_apn` (Kasami APN theorem)
- `walsh_parseval`, `apn_fourth_moment_bound` (moment bounds)
- `cauchy_schwarz_rigidity`, `ab_spectral_collapse` (AB collapse)
- `fourier_triple_identity`, `delta_card`, `combined_identity_ab` (combinatorial identities)

**Assessment:** These are well-known results from the literature (references given). The file is honestly marked as WIP. The final theorem `kasami_triple_count` is genuinely proven *from* these axiomatized results, which is good — it shows the logical structure is correct even if the base results need formalization.

There is also one `sorry` in `Conjectures/APN.lean` for `apn_image_size`, which is an explicit conjecture.

### Axiom Usage

All `#print axioms` outputs show only standard axioms: `propext`, `Classical.choice`, `Quot.sound`, and `Lean.ofReduceBool`. No custom axioms are introduced.

---

## Summary Table

| Category | Count | Examples |
|----------|-------|---------|
| **Genuinely non-tautological proven theorems** | ~25-30 | `bent_diversity_eq_one`, `three_valued_cube_sum`, `spectral_power_sum_bent`, `kBent_iff_kCoBent`, group axiom verifications |
| **Tautological / definitionally true "theorems"** | ~15-20 | `bridge_theorem`, `pn_boolean_exponent_match`, `bridge_fixed_point`, `bridge_symmetric`, `pless_exponent_agreement` |
| **Vacuous due to constant Walsh transform** | ~10+ | All AB candidates, `mkABFunc` instances, `boolIsAB` |
| **Honestly sorry'd deep results** | ~17 | All in `WalshGauss.lean` + 1 in `Conjectures/APN.lean` |
| **Genuine category-theoretic results** | ~5 | `ABFunc.category`, `ABHom.ext`, `ABHom.comp` associativity |

---

## Recommendations for Strengthening

1. **Replace the constant Walsh transform** with a genuine computation (e.g., `BoolWalshTr` should compute character sums, not return constant `true`). This is the single most impactful change.

2. **Distinguish definitions from theorems** — results like `bridge_theorem` that are `rfl` should be documented as "definitional consistency checks," not presented as mathematical theorems.

3. **Prove WalshGauss.lean sorries** — this is where the deep mathematics lives. Even partial progress (e.g., proving Parseval or character orthogonality) would significantly strengthen the formalization.

4. **Add non-trivial verification** of specific AB candidates — e.g., computationally verify that Gold x³ on GF(2⁵) actually has a three-valued Walsh spectrum.

5. **Make the duality functor non-trivial** — currently it's the identity, which makes all duality results vacuous.

6. **Add a computational test**: Use `#eval` to verify that a specific small function (e.g., x³ on GF(2⁵)) actually satisfies the APN/AB conditions.
