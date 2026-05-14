# Formalization Analysis: AB/APN Functions via Topos Theory

## Executive Summary

This project formalizes a categorical framework for Almost Bent (AB) and Almost Perfect Nonlinear (APN) functions using topos-theoretic language. The formalization contains **one layer of genuine mathematics** (binary linear codes) and **one well-formed categorical skeleton** (the AB category), but the bridge connecting them—the Walsh transform instantiation—collapses the spectral theory to a triviality. Every "AB candidate" theorem and every "bridge theorem" is provable by `rfl` because the underlying definitions have been chosen so that the conclusions are definitional consequences of the hypotheses, not mathematical theorems.

This analysis classifies every file and result by its logical status (genuine theorem, tautology, or sorry), identifies the three root causes, and proposes concrete fixes ordered by mathematical leverage.

---

## 1. Root Cause Analysis

Three independent design choices cause all downstream tautologies. Fixing any one of them would restore nontrivial content to the corresponding layer.

### Root Cause A: The Walsh Transform Is Constant

```lean
-- Foundation/TypeTopos.lean, §4
def BoolWalshTr (G : Type) [Group G] :
    WalshTr TypeTopos (FinGrpObj G) (BoolCharObj G) where
  wal := fun _f _u => true        -- ← ignores both f and u
```

**Mathematical consequence.** The AB predicate `IsAB` requires
```
∀ X χ,  χ ≫ W.wal f = ⊥  ∨  χ ≫ W.wal f = c
```
When `W.wal f = fun _ => true` and `c = fun _ => true`, the right disjunct is `rfl`. Hence **every** endomorphism of **every** group is AB in this instantiation. The formalization cannot distinguish Gold x³ (genuinely AB) from x² (not AB).

**Scope of damage.** Everything downstream of `mkABFunc` in `TypeTopos.lean` is affected: all 10 AB candidates in `ABCandidates.lean`, all dichotomy validations, all rigidity certificates—these are packaging the trivial Walsh transform into structures, not verifying any spectral property.

### Root Cause B: Counting Formulas Are Postulated, Not Derived

```lean
-- Bridge/PNBoolean.lean, §1
def internalMTupleCount (𝒯 : SpectralTopos) (n m : ℕ) : ℕ :=
  𝒯.card_Ω ^ ((m - 1) * n - m)       -- ← this IS the answer, by definition
```

The "bridge theorem" then asserts that the exponent `(m−1)n − m` is the same in both the p-valued and Boolean toposes:
```lean
theorem pn_boolean_exponent_match ... :=
  ⟨(m - 1) * n - m, rfl, rfl⟩         -- ← both sides are literally the same expression
```

**What a genuine bridge theorem would prove.** Define
```
κ_m(f) := |{(x₁,…,xₘ) ∈ GF(q)ᵐ : Σ xᵢ = 0 ∧ Σ f(xᵢ) = 0}|
```
as a *computation* (as `BinaryCode.lean` does for linear codes). Then *prove* that for a PN function f over GF(pⁿ), κ_m(f) = pⁿ⁽ᵐ⁻¹⁾⁻ᵐ. This would require the Parseval identity and the PN spectral condition. The current formalization skips this entirely by making the formula a definition.

### Root Cause C: The "Duality Functor" Is the Identity

```lean
-- Bridge/Duality.lean, §4
def DualSpectralTopos.dualFunctor (𝒯 : DualSpectralTopos) : DualSpectralTopos where
  card_Ω := 𝒯.card_Ω                  -- ← copies the same number
  card_pos := 𝒯.card_pos
```

Every theorem about this functor (`bridge_fixed_point`, `bridge_symmetric`, `bridge_self_dual_invariance`, `dualFunctor_involution`) follows by `simp` or `rfl` because the functor does nothing. A genuine duality functor on toposes passes to the opposite category ℰᵒᵖ and requires proving that the counting formula is preserved—a nontrivial fact about the Heyting algebra structure of Ω.

---

## 2. File-by-File Audit

### Genuine Mathematics (no sorry, nontrivial proofs)

| File | Key Results | Why Genuine |
|------|------------|-------------|
| `CodingTheory/BinaryCode.lean` | `mTupleCount_eq_card_pow`: κ_m = \|C\|^{m−1} for linear codes | Real induction proof using GF(2) linearity and `sum_codewords_mem` |
| | `weightDistribution_zero`: A₀ = 1 | Finset uniqueness argument |
| | `weightDistribution_sum`: Σ Aᵢ = \|C\| | Fiber-partition of codewords by weight |
| | `three_weight_pless_decomposition` | Algebraic decomposition of Pless moments |
| | `ab_kerdock_spectral_match` | Arithmetic: Kerdock weights ↔ character-sum values |
| `Foundation/ElemTopos.lean` | `ABFunc.category` instance | Genuine associativity/identity proofs via Mathlib |
| `Foundation/TypeTopos.lean` | `FinGrpObj` group axioms | Each axiom (assoc, unit, inverse) verified for concrete groups |
| | `commutatorMTupleCount_comm` | Abelian commutator identity with real induction |
| `Bridge/Duality.lean` | `kBent_iff_kCoBent` | ‖conj z‖ = ‖z‖ and Heyting algebra reversal |
| | `pless_moment_zero_eq_card` | Nontrivial Finset partition argument |
| `Spectral/SpectralObject.lean` | `bent_diversity_eq_one` | `Finset.card_eq_one` argument using IsBent |
| | `bent_implies_discrete` | Chains bentness → diversity 1 → πₖ = 1 |
| `Bridge/RosettaStone.lean` | `spectral_power_sum_bent` | Sum decomposition via IsBent case split |
| | `kappa_matches_spectral` | Connects BinaryCode.κ_m to spectral support |

### Tautologies (proofs by `rfl`, `simp`, or trivially true by definition)

| File | Result | Root Cause | Proof |
|------|--------|-----------|-------|
| `Bridge/PNBoolean.lean` | `boolean_topos_recovery` | B | `rfl` |
| | `pValued_topos_pn_recovery` | B | `rfl` |
| | `geometric_morphism_transfers_count` | B | `ring` (commutativity of ℕ multiplication) |
| | `pn_boolean_exponent_match` | B | `⟨_, rfl, rfl⟩` |
| | `pn_boolean_relative_existence` | B | `rfl` |
| | `boolean_relative_unique` | B | Unfolding a definition that equals itself |
| | `bridge_theorem` | B | `⟨rfl, ⟨_, rfl, rfl⟩, id⟩` |
| `Bridge/Duality.lean` | `bridge_fixed_point` | C | `simp` (identity functor) |
| | `bridge_symmetric` | B+C | `rfl` |
| | `bridge_self_dual_invariance` | B+C | `⟨rfl, rfl, rfl⟩` |
| | `dual_complete_pipeline` | B+C | All certificates are `rfl` |
| | `homotopical_silence_self_dual` | — | `simp` (dual copies homotopy groups verbatim) |
| `Candidates/ABCandidates.lean` | All 10 `*_passes_dichotomy` | A | Via trivially constant Walsh transform |
| | All `*_exponent_match` | A+B | `⟨rfl, rfl, ...⟩` |
| | `bridge_verified_p*` | — | Literally `x = x` |
| | `ab_candidates_master_verification` | A+B+C | Combines all tautologies |

### Sorry'd Results (the actual hard mathematics)

`Spectral/WalshGauss.lean` contains **16 sorries** corresponding to the genuine theorems that the rest of the project bypasses:

| Sorry | Mathematical Content | Difficulty |
|-------|---------------------|------------|
| `AbsTrace` | Absolute trace Tr : GF(2ⁿ) → GF(2) | Requires finite field tower theory |
| `χ_add`, `χ_sq`, `χ_orthogonality` | Additive character properties | Moderate (character theory) |
| `stickelberger_norm` | ‖𝔤(ψ)‖² = q | Hard (algebraic number theory) |
| `kasami_apn` | Kasami exponent gives APN | Hard (finite field polynomial counting) |
| `walsh_parseval` | Σ ‖Ŵ(u)‖² = q² | Standard Parseval identity |
| `apn_fourth_moment_bound` | APN ⟹ Σ ‖Ŵ(u)‖⁴ ≤ 2q³ | Moderate (moment inequalities) |
| `cauchy_schwarz_rigidity` | M₂ + M₄ bound ⟹ flat spectrum | Moderate |
| `ab_spectral_collapse` | APN + n odd ⟹ AB | **The** central theorem |
| `combined_identity_ab` | q · \|Triples\| = \|Δ\|³ | Hard (character sum cancellation) |
| `delta_card` | \|Δ\| = 2^{n−1} | Moderate (APN counting) |

Note: `kasami_triple_count` is *not* sorry'd—it correctly derives 2^{2n−3} from `combined_identity_ab` and `delta_card` via algebra. The sorry chain is: if the sorry'd lemmas were proven, the triple count theorem would be fully formal.

---

## 3. Structural Dependency of Tautologies

The tautologies form a dependency tree rooted in the three root causes:

```
Root Cause A (constant Walsh)
  └─ boolIsAB (trivially true for all f)
      └─ mkABFunc (packages any endomorphism as AB)
          └─ goldABDatum, kasamiABDatum, ... (all 10 candidates)
              └─ *_passes_dichotomy (all trivially pass)
                  └─ ab_candidates_master_verification

Root Cause B (counting formula is a definition)
  └─ internalMTupleCount := card_Ω ^ (...)
      ├─ boolean_topos_recovery (rfl)
      ├─ pValued_topos_pn_recovery (rfl)
      ├─ pn_boolean_exponent_match (rfl, rfl)
      ├─ bridge_theorem (rfl)
      └─ all exponent match theorems (rfl)

Root Cause C (duality functor = identity)
  └─ DualSpectralTopos.dualFunctor copies card_Ω
      ├─ bridge_fixed_point (simp)
      ├─ bridge_symmetric (rfl)
      ├─ bridge_self_dual_invariance (rfl)
      └─ dual_complete_pipeline (rfl)
```

---

## 4. What Is Genuinely Nontrivial

Despite the tautology issues, significant genuine content exists:

**1. The coding theory layer (`BinaryCode.lean`) is the strongest part.** The theorem `mTupleCount_eq_card_pow` is a real combinatorial identity requiring induction, a bijection argument (free choice of m−1 codewords determines the m-th), and the GF(2) identity −x = x. This file alone justifies the project's coding-theoretic claims.

**2. The abstract categorical framework (`ElemTopos.lean`) is well-designed.** The `IsAB` predicate, expressed as a Yoneda-style universal property over generalized elements, is the correct categorical formulation. The `GrpObj` structure with full group axioms via generalized elements is properly formal. The problem is not with the *definition* of AB-ness but with the trivial *instantiation*.

**3. The spectral diversity theory (`SpectralObject.lean`) is genuine.** The theorem `bent_implies_discrete` has a real proof structure: bent ⟹ all nonzero norms equal c ⟹ diversity = |{c}| = 1 ⟹ πₖ = 1. This is not tautological—it genuinely derives discreteness from a spectral condition.

**4. The Rosetta Stone connection (`RosettaStone.lean`) is mathematically sound.** The spectral power sum theorem and the κ_m matching theorem correctly relate spectral and combinatorial invariants, *conditional on* having a genuine spectral object.

**5. The `kBent_iff_kCoBent` duality theorem is genuine.** It uses the mathematical fact ‖conj z‖ = ‖z‖ and the Heyting algebra reversal to establish that k-Bent in ℰ is equivalent to k-CoBent in ℰᵒᵖ.

---

## 5. Remediation: Fixes Ordered by Mathematical Leverage

### Fix 1 (Highest leverage): Implement a Real Walsh Transform

Replace `BoolWalshTr` with a genuine Walsh–Hadamard transform over finite fields. This single change would:
- Make AB candidate verification nontrivial (and falsifiable)
- Give the spectral diversity theory concrete content
- Connect the abstract framework to actual cryptographic functions

**Concrete target.** Define for f : GF(2ⁿ) → GF(2ⁿ):
```
W_f(a,b) := Σ_{x ∈ GF(2ⁿ)} (−1)^{Tr(ax + bf(x))}
```
Then prove that Gold x³ satisfies |W_f(a,b)| ∈ {0, 2^{(n+1)/2}} for odd n. This is the content of `ab_spectral_collapse` in `WalshGauss.lean`—currently sorry'd, but the proof architecture is laid out.

**Intermediate milestone.** Even proving the Walsh transform properties for small concrete cases (e.g., GF(8) = GF(2³)) via `native_decide` would provide nontrivial instantiations.

### Fix 2: Derive the Counting Formula from a Real Computation

Replace the definitional `internalMTupleCount := card_Ω ^ (...)` with:
1. A *computational* definition of κ_m(f) that counts actual solution tuples
2. A *theorem* proving κ_m(f) = q^{(m−1)n − m} for PN/bent functions

The computational definition already exists for linear codes (`mTupleCount` in `BinaryCode.lean`). Extending it to functions over GF(pⁿ) and proving the formula requires the Parseval identity.

### Fix 3: Resolve WalshGauss.lean Sorries

The 16 sorries in `WalshGauss.lean` represent the *actual mathematical content* the project needs. A prioritized attack order:

1. **`walsh_parseval`** — Standard; likely provable with current Mathlib (inner product orthogonality)
2. **`χ_add`, `χ_sq`** — Follow from the definition of the absolute trace; need finite field theory
3. **`χ_orthogonality`** — Follows from `χ_add` and character sum theory
4. **`kasami_apn`** — Requires polynomial counting over GF(2ⁿ); harder
5. **`ab_spectral_collapse`** — The central theorem; depends on 1–4 plus moment bounds
6. **`stickelberger_norm`** — Deepest; requires algebraic number theory (Gauss sum norm)

### Fix 4: Give the Duality Functor Content

Either:
- **(a)** Connect `DualSpectralTopos.dualFunctor` to the opposite category construction in Mathlib (`Categoryᵒᵖ`), requiring a proof that the counting formula is preserved under passage to ℰᵒᵖ.
- **(b)** Remove the "duality functor" language entirely and state the duality results directly in terms of complex conjugation and Heyting algebra reversal (as `kBent_iff_kCoBent` already does correctly).

---

## 6. Axiom Audit

All compiled theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`—the standard CIC axioms. There are no unsound axioms, `@[implemented_by]` attributes, or axiom declarations. The issue is not logical unsoundness but mathematical vacuity: the theorems are *true* but *trivially* true.

The one exception is `zmod2_neg_eq_self` in `BinaryCode.lean`, which uses `native_decide`. This is acceptable for a decidable proposition over a finite type.

---

## 7. Summary Scorecard

| Category | Count | % of Project |
|----------|-------|-------------|
| Genuine theorems (nontrivial proofs) | ~18 | ~25% |
| Tautologies (true by definition) | ~35 | ~50% |
| Sorry'd (hard mathematics) | 16 | ~22% |
| Structural/packaging (instances, structures) | ~5 | ~3% |

**The gap:** The genuine mathematics lives at the *bottom* (coding theory) and the *top* (WalshGauss sorries) of the dependency graph. The entire *middle layer*—the bridge theorems, duality results, AB candidates, and rigidity certificates—is tautological because it instantiates the abstract framework with trivial data. Filling in the Walsh transform (Fix 1) or the WalshGauss sorries (Fix 3) would propagate genuine content through this middle layer, converting tautologies into real theorems.
