# CIC Unicode — Category Theory, 2-Category & Topos Results

Results that compile and logically build on established blackboxed infrastructure (Mathlib, `Basic.lean` axioms). Conjectural/sorry'd statements are excluded.

---

## §1 Category Theory (`CategoryTheory.lean`)

### Definitions

```
SpectralObject (F : Type u) [Field F] [Fintype F] :=
  { carrier : Type u,  spectrum : carrier → ℂ }

SpectralMorphism F (X Y : SpectralObject F) :=
  { toFun : X.carrier → Y.carrier,
    map_add : ∀ a b, toFun (a + b) = toFun a + toFun b }

differentialObject (f : F → F) : SpectralObject F :=
  ⟨ F,  walshTransform F f ⟩

SpectralObject.tensorPow (X : SpectralObject F) (m : ℕ) : SpectralObject F :=
  ⟨ Fin m → X.carrier,  λ v ↦ ∏ i, X.spectrum (v i) ⟩

SpectralObject.IsBent (X : SpectralObject F) (c : ℝ) : Prop :=
  ∀ v, X.spectrum v = 0 ∨ ‖X.spectrum v‖ = c

WalshFunctor F :=
  { obj  : SpectralObject F → SpectralObject F,
    monoidal_iso    : ∀ X m, (obj (X.tensorPow m)).carrier ≃ ((obj X).tensorPow m).carrier,
    preserves_bent  : ∀ X c, X.IsBent c → (obj X).IsBent c }
```

### Proven Result

```
linearConstraintMorphism (X : SpectralObject F) (m : ℕ)
    : SpectralMorphism F (X.tensorPow m) X
    := ⟨ λ v ↦ ∑ i, v i,  Finset.sum_add_distrib ⟩
```

The linear-constraint map `v ↦ ∑ᵢ vᵢ` is an additive (spectral) morphism from `X^{⊗m}` to `X`.

---

## §2 Higher (∞,1)-Category Theory (`HigherCategoryFrontier.lean`)

### Definitions

```
HomotopySpectralObject F :=
  { base : SpectralObject F,
    homotopyGroup : ℕ → Type u }         -- πₖ, each Fintype + AddCommGroup

eulerCharacteristic (X : HomotopySpectralObject F) (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N+1), (-1)^k · |πₖ(X)|

isDiscrete (X) : Prop :=  ∀ k ≥ 1, |πₖ(X)| = 1

IsKBent (X) (c : ℝ) (k : ℕ) : Prop :=
  X.base.IsBent c  ∧  ∀ 1 ≤ j ≤ k, |πⱼ(X)| = 1

QuasiIso (X Y) : Prop :=  ∀ k, |πₖ(X)| = |πₖ(Y)|

differentialHomotopyObject (f : F → F) : HomotopySpectralObject F :=
  ⟨ differentialObject f,
    λ k ↦ match k with | 0 => F | _ + 1 => PUnit ⟩
```

### Proven Results

**① k-Bentness is monotone**
```
kBent_monotone : X.IsKBent c (k+1) → X.IsKBent c k
```

**(k+1)-Bent ⟹ k-Bent.  Immediate: requiring more πⱼ = 0 is stronger.*

**② Discrete ⟹ k-Bent for all k**
```
discrete_implies_kBent :
    X.base.IsBent c  →  X.isDiscrete  →  ∀ k, X.IsKBent c k
```

*An object with all πₖ = 0 (k ≥ 1) and a flat base spectrum is k-Bent at every level.*

**③ AB ⟹ spectral rigidity (homotopically discrete)**
```
ab_spectral_rigidity (f : F → F) (hAB : IsAB F f) :
    (differentialHomotopyObject f).isDiscrete
```

*The canonical ∞-lift of an AB differential object has πₖ = PUnit for k ≥ 1 — maximally rigid.*

**④ Derived invariance: quasi-iso preserves Euler characteristic**
```
euler_characteristic_quasiIso_invariant :
    X.QuasiIso Y  →  eulerCharacteristic X N = eulerCharacteristic Y N
```

*If ∀ k, |πₖ(X)| = |πₖ(Y)|, then χ_N(X) = χ_N(Y). The m-tuple count (as Euler characteristic) is a derived invariant.*

---

## §3 2-Category / Bicategory (`TwoCategoryFrontier.lean`)

### Definitions

```
Spectral2Morphism {X Y : SpectralObject F} (φ ψ : SpectralMorphism F X Y) :=
  { spectralGap : ℝ,
    gap_nonneg  : 0 ≤ spectralGap,
    gap_bound   : ∀ v, ‖Y.spectrum (φ v) − Y.spectrum (ψ v)‖ ≤ spectralGap }

mTupleGroupoidObj (X : SpectralObject F) (m : ℕ) :=
  { v : Fin m → X.carrier // ∑ i, v i = 0 }

mTupleGroupoidHom X (v w : mTupleGroupoidObj X m) :=
  { σ : Perm (Fin m) // ∀ i, w.val (σ i) = v.val i }

mTupleGroupoid_isDiscrete X m : Prop :=
  ∀ v σ, (∀ i, v.val (σ i) = v.val i) → σ = Equiv.refl _

IsBent₂ (X : SpectralObject F) (C : ℕ) : Prop :=
  ∀ m ≥ 2,  groupoidCardinality X m = |X.carrier|^{m−1} / |X.carrier|^C
```

*All theorems in this file are conjectural (sorry'd); no completed proofs.*

---

## §4 Topos Theory (`ToposFrontier.lean`)

### Definitions

```
SpectralTopos :=
  { Ω : Type u  [DecidableEq] [Fintype],
    card_Ω : ℕ := |Ω|,
    isBoolean : Prop := card_Ω = 2 }

internalMTupleCount (𝒯 : SpectralTopos) (n m : ℕ) : ℕ :=
  |Ω_𝒯|^{(m−1)·n − m}

classicalMTupleCount (n m : ℕ) : ℕ  :=  2^{(m−1)·n − m}

booleanSpectralTopos : SpectralTopos  :=  ⟨ Bool, 2 ⟩

pValuedSpectralTopos (p : ℕ) [Fact (Nat.Prime p)] : SpectralTopos :=
  ⟨ ZMod p, p ⟩

SheafCohomology F :=
  { cohomGroup : SpectralObject F → ℕ → Type u,
    h0_sections : ∀ X, |H⁰(X)| = |X.carrier| }

isCohomFlat (ℋ) (X) : Prop :=  ∀ k ≥ 1, |Hᵏ(X)| = 1

SpectralGeometricMorphism (𝒯 𝒮 : SpectralTopos) :=
  { Ω_map : Ω_𝒯 → Ω_𝒮 }
```

### Proven Results

**⑤ Internal counting formula (definitional)**
```
internal_mTuple_count :
    internalMTupleCount 𝒯 n m  =  |Ω_𝒯|^{(m−1)·n − m}
```

*True by `rfl` — the definition is the formula.*

**⑥ Boolean topos recovery**
```
boolean_topos_recovery (n m : ℕ) :
    internalMTupleCount booleanSpectralTopos n m  =  classicalMTupleCount n m
```

*In Set (|Ω| = 2), the internal count specialises to the classical 2^{(m−1)n − m}.  Proof: `rfl`.*

**⑦ Geometric morphism transfers counts**
```
geometric_morphism_transfers_count (𝒯 𝒮 : SpectralTopos) (φ : 𝒯 ⟶ 𝒮) (n m : ℕ) :
    κₘ^𝒯 · |Ω_𝒮|^{(m−1)n−m}  =  |Ω_𝒯|^{(m−1)n−m} · κₘ^𝒮
```

*Internal counts commute across geometric morphisms (by commutativity of ℕ-multiplication).*

**⑧ p-valued topos recovery for PN functions**
```
pValued_topos_pn_recovery (p : ℕ) [Fact (Nat.Prime p)] (n m : ℕ) :
    internalMTupleCount (pValuedSpectralTopos p) n m  =  p^{(m−1)·n − m}
```

*In the p-valued topos (|Ω| = p), the count is p^{(m−1)n − m}, matching the PN formula.  Proof: `simp`.*

---

## Summary Table

| # | Result | File | Status |
|---|--------|------|--------|
| — | `linearConstraintMorphism` | CategoryTheory | ✅ proven |
| ① | `kBent_monotone` | HigherCategoryFrontier | ✅ proven |
| ② | `discrete_implies_kBent` | HigherCategoryFrontier | ✅ proven |
| ③ | `ab_spectral_rigidity` | HigherCategoryFrontier | ✅ proven |
| ④ | `euler_characteristic_quasiIso_invariant` | HigherCategoryFrontier | ✅ proven |
| ⑤ | `internal_mTuple_count` | ToposFrontier | ✅ proven (rfl) |
| ⑥ | `boolean_topos_recovery` | ToposFrontier | ✅ proven (rfl) |
| ⑦ | `geometric_morphism_transfers_count` | ToposFrontier | ✅ proven |
| ⑧ | `pValued_topos_pn_recovery` | ToposFrontier | ✅ proven |

All other theorems across the four files remain conjectural (`sorry`).
