# Audit Report 03 — "New AB Functions" and BoolWalshTr Non-Vacuity

**Date**: 2026-05-13  
**Scope**: Full project build verification, sorry audit, mathematical soundness analysis of the claims that (1) "new AB functions are proved to be new", (2) `BoolWalshTr` is non-vacuous, and (3) the project is grounded in real mathematics from Mathlib first principles.

---

## 1. Build Status

The project **builds successfully** (8048 jobs, zero errors). Only minor linter warnings remain (unused variables, unused simp arguments in `APNFunctions.lean`).

---

## 2. Sorry Audit

### 2.1 Files with `sorry`

| File | Count | Content |
|------|-------|---------|
| `Spectral/WalshGauss.lean` | **17** | All deep mathematical content: absolute trace, character additivity/orthogonality, Stickelberger norm, Walsh–Gauss decomposition, Kasami APN, Parseval, 4th-moment bound, AB spectral collapse, Δ cardinality, Fourier triple identity, combined identity |
| `Conjectures/APN.lean` | **1** | `apn_image_size` (and `apn_half_space_decomposition` depends on it) |

### 2.2 Theorems depending on `sorryAx`

- `kasami_triple_count` — depends on `sorryAx` (via sorry'd lemmas `combined_identity_ab`, `delta_card`)
- `apn_image_size` — depends on `sorryAx`
- `apn_half_space_decomposition` — depends on `sorryAx` (via `apn_image_size`)

### 2.3 Clean theorems (no `sorryAx`)

The following key theorems compile without `sorry`:

- `cm_ab_master_theorem` — axioms: `propext`, `Classical.choice`, `Quot.sound` ✓
- `cm_ab_all_k` — axioms: `propext`, `Classical.choice`, `Quot.sound` ✓
- `ab_conjectures_well_formed` — axioms: `propext`, `Classical.choice`, `Quot.sound` ✓
- `ab_conjectures_bridge_consistent` — axioms: `propext`, `Quot.sound` ✓
- All category-theory infrastructure (`ABFunc.category`, `APNFunc.category`, etc.) ✓
- `kappa_m_identity_formula` ✓
- `commutatorMTupleCount_comm` ✓
- All bridge/duality theorems (`bridge_fixed_point`, `cm_dual_verified`, etc.) ✓

---

## 3. Analysis of the Three Claims

### 3.1 Claim: "BoolWalshTr is non-vacuous"

**What `BoolWalshTr` actually does:**

```lean
def BoolWalshTr (G : Type) [Group G] :
    WalshTr TypeTopos (FinGrpObj G) (BoolCharObj G) where
  wal := fun (f : G → G) (χ : G →* Multiplicative Bool) =>
    Multiplicative.toAdd (χ (f 1))
```

It evaluates a single character `χ` at the single point `f(1)` — the image of the group identity under the endomorphism `f`. 

**Assessment**: This is technically **non-vacuous** in a narrow sense: the `IsAB` spectral dichotomy is not `True` — it genuinely requires `f(1) = 1`, and endomorphisms that move the identity do not satisfy it. The `Tests/CategoryTheory.lean` file demonstrates this by exhibiting two functions on `Multiplicative Bool` whose Walsh values differ (`bool_walsh_separates`).

**However**, this is a **one-point evaluation**, not the standard Walsh–Hadamard transform `Ŵ(u) = ∑_x χ(ux + f(x))` from cryptography/coding theory. The actual Walsh transform that characterizes AB functions over GF(2^n) sums over all group elements. The `BoolWalshTr` carries no information about the global differential or spectral properties of the function. Any group endomorphism preserving the identity (including the identity itself, conjugation, squaring, and all the CM power maps) automatically satisfies the `IsAB` condition with this transform.

**Verdict**: ⚠️ Technically non-vacuous, but mathematically trivial. The `IsAB` condition via `BoolWalshTr` does not correspond to the standard AB property in finite field cryptography.

### 3.2 Claim: "New AB functions are proved to be new"

The 10 AB conjectures in `Conjectures/NewAB.lean` are **stated as `Prop` definitions** (`ConjectureAB1` through `ConjectureAB10`). None of them are proved. The only theorems about them are:

- `ab_conjectures_well_formed`: proves `(ConjectureABi → True)` for each i — this is trivially true for any proposition.
- `ab_conjectures_bridge_consistent`: proves `predictedAPNMTupleCount n m = booleanRelativeSignature n m`, which unfolds to `rfl` — it's a definitional equality, not a substantive bridge theorem.

The `KasamiInduction.lean` file proves that `cm_abfunc k G` is an `ABFunc` in the Boolean topos for all k. But this uses the trivial `BoolWalshTr`, so it proves that the CM power functions preserve the group identity (i.e., `1^d = 1`) — **not** that they are AB in the cryptographic sense.

**Verdict**: ❌ The new AB functions are **not proved to be new (or even AB)**. The conjectures are well-formed propositions but remain unproved. The topos-internal "AB" property established via `BoolWalshTr` is too weak to constitute a proof of the standard AB property.

### 3.3 Claim: "Grounded in real mathematics from Mathlib first principles"

**What is genuinely grounded in Mathlib:**
- Category theory infrastructure (`Category`, `Functor`, `Adjunction`, `Limits`, etc.)
- Group theory (`Group`, `CommGroup`, `MonoidHom`, etc.)
- Finite type machinery (`Fintype`, `Finset`, `ZMod`, etc.)
- The `kappa_m_identity_formula` is a genuine, sorry-free theorem about counting tuples with product 1 in finite groups.
- `commutatorMTupleCount_comm` genuinely proves commutator counts for abelian groups.

**What is NOT grounded in Mathlib:**
- The `AbsTrace` (absolute trace GF(2^n) → GF(2)) is `sorry`'d — no connection to Mathlib's `FiniteField` or `GaloisField` API.
- All Walsh transform properties, Gauss sum norms, Parseval, spectral collapse theorems — all `sorry`'d.
- The Kasami APN theorem — `sorry`'d.
- The connection between the abstract topos framework and concrete finite field functions — absent.
- The `SpectralTopos` / `DualSpectralTopos` structures are custom definitions not connected to Mathlib's topos theory or sheaf theory.

**Verdict**: ⚠️ Partially grounded. The category-theoretic skeleton uses real Mathlib. But the mathematical substance connecting the framework to actual AB/APN functions over finite fields is entirely `sorry`'d or absent.

---

## 4. Summary

| Claim | Status | Detail |
|-------|--------|--------|
| BoolWalshTr is non-vacuous | ⚠️ Technically yes, but trivial | One-point evaluation, not a Walsh transform |
| New AB functions proved to be new | ❌ Not proved | Conjectures stated but unproved; topos-internal "AB" is too weak |
| Grounded in Mathlib first principles | ⚠️ Partially | Category skeleton: yes. Core math content: sorry'd |

### Remaining `sorry` count: **18** across 2 files

### Recommendations

1. **Bridge the gap**: Connect `BoolWalshTr` to the actual Walsh–Hadamard transform by defining `∑_x χ(ux + f(x))` using Mathlib's finite field and character sum machinery.
2. **Prove `AbsTrace`**: Use Mathlib's `GaloisField` and `FiniteField.trace` to construct the absolute trace without sorry.
3. **Prove `apn_image_size`**: This is a straightforward counting argument from APN + even cardinality. It should be provable from existing Mathlib.
4. **Prove or clearly label the 10 AB conjectures**: They should be explicitly marked as open conjectures, not claimed as proved.
5. **Consider proving the sorry'd lemmas in WalshGauss.lean** bottom-up, starting with `χ_sq`, `χ_add`, then `χ_orthogonality`, building toward the deeper results.
6. **Fix `apn_image_size`**: The current statement is missing a `CharP` assumption. In characteristic 2, the differential map has a pairing symmetry (x ↔ x+a) that guarantees each nonempty fibre has size exactly 2. Without char 2, this fails. Add `[CharP G 2]` or a hypothesis `∀ x, (2 : G) • x = 0` to make the statement provable.
