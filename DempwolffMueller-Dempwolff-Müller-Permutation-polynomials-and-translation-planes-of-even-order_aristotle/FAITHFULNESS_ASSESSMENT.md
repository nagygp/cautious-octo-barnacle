# Faithfulness Assessment: Formalization vs. Paper

## Paper: Dempwolff & Müller, "Permutation polynomials and translation planes of even order" (Adv. Geom. 2013)

### Paper Structure (6 sections)

| Section | Content |
|---------|---------|
| §2 | Quasifields from permutation polynomials (Prop 2.1) |
| §3 | Permutation polynomials: Lemma 3.1, Theorems 3.2–3.4, Prop 3.5 |
| §4 | Automorphism groups: Lemmas 4.1–4.5, Prop 4.6, Lemma 4.7, Theorems 4.8, 4.10, Lemmas 4.9, 4.11, 4.12 |
| §5 | Isomorphism classification: Theorems 5.1, 5.2, 5.4, Lemma 5.3 |
| §6 | Symplectic spreads: Lemma 6.1, Props 6.2, 6.3 |

---

## What Is Genuinely Proved (sorry-free, non-trivial theorems)

### Fully proved results (zero sorries, real mathematical content):

| Result | File | Assessment |
|--------|------|------------|
| **Proposition 2.1(a)** | `Prop21.lean` | ✅ Faithful. L bijective, weak quasifield structure from P bijective. |
| **Lemma 3.1** | `Lemma31.lean` | ✅ Faithful. L(x)·M(x) injective ↔ L*(x)·M⁻¹(x) injective. |
| **Theorem 3.2 (k part)** | `Thm32.lean` | ✅ Faithful. L(X)·Xᵏ is a permutation polynomial. This is the paper's hardest proof (719 lines). |
| **Theorem 3.2 (k' part)** | `Thm32Kprime.lean` | ✅ Faithful. L(X)·X^{k'} is also a permutation polynomial. |
| **Theorem 3.3 (h=1 base case)** | `Thm33.lean` | ⚠️ Partial. Only the h=1 base case is proved. The general inductive case (arbitrary h) is not formalized. |
| **Theorem 3.4 (char 2)** | `Thm34.lean` | ⚠️ Trivially true in char 2 (x^b = 1), so the proof is correct but doesn't capture the paper's general argument. |
| **Proposition 3.5 (char 2)** | `Prop35.lean` | ⚠️ Same — trivially true in char 2 via x^b = 1. |
| **Lemma 6.1(a)** | `Lemma61.lean` | ✅ Faithful. Adjoint of semilinear operators. |

### Supporting infrastructure (not in the paper, but needed for the proofs):

| Layer | File | Content |
|-------|------|---------|
| F1 | `FrobAlg.lean` | Frobenius operator algebra |
| F2 | `TraceNorm.lean` | Trace theory and adjoint property |
| F3 | `ExpArith.lean` | Mersenne GCD, exponent arithmetic |
| F4 | `LinPoly.lean` | Linearized polynomial algebra |
| B1 | `AutBase.lean` | Semilinear operators, support, Lemmas 4.1–4.2 |
| B2 | `AutKernel.lean` | Kernel element theory (Lemmas 4.3–4.5) |
| B3 | `AutGeneral.lean` | Semifield detection (Prop 4.6, Lemma 4.7) |

---

## What Is NOT Proved (placeholders or missing)

### Placeholder definitions (defined as `... : Prop := True` or similar — no mathematical content):

| Result | File | Status |
|--------|------|--------|
| **Lemma 4.12** (inverse structure for type II) | `AutTypeII.lean` | `def TypeIIInverseStructure ... := ... → True` |
| **Theorem 4.10** (automorphism group of type II) | `AutTypeII.lean` | `def TypeIIAutGroup ... := ... → True` |
| **Theorem 5.1(a)** (iso implies m=m') | `IsoTypeI.lean` | `m = m' → True` (wrong direction, placeholder) |
| **Theorem 5.1(b)** (Type I ≇ Dual) | `IsoTypeI.lean` | `def TypeINotIsoDual ... := ... → True` |
| **Lemma 5.3** (normalizer constraint) | `IsoTypeII.lean` | `def NormalizerConstraint ... := ... → True` |
| **Theorem 5.2** (type II classification) | `IsoTypeII.lean` | `def TypeIIIsoClassification ... := ... → True` |
| **Theorem 5.4(a)** (Type I ≇ Type II) | `IsoTypeIvsII.lean` | `def TypeINotIsoTypeII ... := ... → True` |
| **Theorem 5.4(b)** (not iso to known planes) | `IsoTypeIvsII.lean` | `def NotIsoToKnownPlanes ... := True` |
| **Proposition 6.3** (Type II not symplectic) | `SymplTypeII.lean` | `def TypeIINotSymplectic ... := ... → True` |

### Not formalized at all:

| Result | Status |
|--------|--------|
| **Theorem 3.3** (general h, inductive case) | Only h=1 base case proved |
| **Theorem 4.8** (Type I automorphism group) | Statement exists as `TypeIAutGroup` but uses `Prop` definition, no proof |
| **Lemma 4.9(b,c)** (L⁻¹ not 1-2 monomials, support structure) | Not formalized |

---

## Faithfulness Verdict

### What the formalization genuinely achieves:
1. **§2 (Prop 2.1)**: Fully faithful.
2. **§3 core results (Lemma 3.1, Theorem 3.2 both parts)**: Fully faithful — this is the paper's most technically demanding material.
3. **§3 secondary results (Thm 3.3, 3.4, Prop 3.5)**: Partially faithful. Thm 3.3 only covers the base case. Thm 3.4 and Prop 3.5 are proved but in a trivial way specific to char 2 (where x^b = 1 for all nonzero x), not capturing the paper's general argument.
4. **§4 (Automorphisms)**: The foundational layers (Lemmas 4.1–4.5, Prop 4.6, Lemma 4.7) have definitions and some proofs, but the main type-specific results (Theorems 4.8, 4.10, Lemma 4.9 parts b,c, Lemmas 4.11, 4.12) are **placeholder definitions returning `True`** — they have no mathematical content.
5. **§5 (Isomorphisms)**: **Entirely placeholder**. All of Theorems 5.1, 5.2, 5.4 and Lemma 5.3 are `... := True`.
6. **§6 (Symplectic spreads)**: Lemma 6.1(a) is genuinely proved. Prop 6.2 has a correct statement but no proof. Prop 6.3 is a placeholder.

### Honest summary:
- **~30–35% of the paper's named results** are genuinely formalized and proved.
- The strongest achievement is the complete proof of **Theorem 3.2** (both k and k' parts), which is indeed the paper's hardest single proof.
- The **LIBRARY_OVERVIEW.md** claim of "17 fully proven files" is misleading. Many of those "fully proven" files (IsoTypeI, IsoTypeII, IsoTypeIvsII, SymplTypeII, AutTypeII) contain only **placeholder definitions** (`... := True`) with zero mathematical content. They compile without `sorry` only because they don't actually state or prove anything.
- The formalization does **not** achieve what the paper achieves. The paper's classification results (§5), automorphism group computations for type II (§4), and symplectic non-existence (§6) are entirely absent.
- **Several originally-formalized statements were discovered to be false** (for general characteristic). The corrected char-2 versions are proved but are substantially simpler than the paper's arguments.
- The supporting infrastructure (Frobenius algebra, trace theory, Mersenne GCD) is genuine and valuable, but goes beyond what the paper itself contains.

### Corrections found:
The formalization process revealed that several statements were originally misstated:
1. `typeI_inverse_GF2_coeffs` (Lemma 4.9a): Original formalization confused "coefficients in GF(2)" with "image in GF(2)". Corrected to Frobenius commutativity.
2. `bij_of_additive_pow_twist` (used in Thm 3.4): False for general characteristic (counterexample: GF(13)).
3. `prop_3_5_abstract` (Prop 3.5): False for general characteristic (counterexample: GF(3)).
4. `spread_diff_via_subst` (intermediate lemma): False (counterexample: GF(4)).

These corrections are legitimate and valuable — they identified formalization errors in how the paper's statements were translated to Lean.
