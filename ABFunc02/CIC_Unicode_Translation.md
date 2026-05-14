# CIC Unicode Translation of the AB Function Formalisation

A minimal, readable rendering of the entire project in CIC-style pseudocode with Unicode symbols.  
Each component is briefly explained.

---

## Module 1 — `ABCategory`: The Category of AB Functions in a Topos

### §1 Elementary Topos

An elementary topos bundles a category with finite (co)limits, a subobject classifier Ω, and distinguished truth values ⊤, ⊥ : 𝟙 → Ω.

```
𝕋 : ElemTopos  :=
  ℰ     : Type u                        -- underlying category
  Ω     : Obj(ℰ)                        -- subobject classifier
  ⊤_Ω   : 𝟙 ⟶ Ω                        -- "true"
  ⊥_Ω   : 𝟙 ⟶ Ω                        -- "false"
  nondeg : ⊤_Ω ≠ ⊥_Ω                   -- non-degeneracy
```

### §2 Internal Group Object

A group object in ℰ, generalising (𝔽_q, +). Carries full group axioms as commutative diagrams over generalised elements.

```
𝒢 : GrpObj(𝕋)  :=
  carrier : Obj(ℰ)
  μ  : 𝒢 × 𝒢 ⟶ 𝒢                      -- multiplication
  η  : 𝟙 ⟶ 𝒢                           -- unit
  ι  : 𝒢 ⟶ 𝒢                           -- inverse

  -- Axioms (∀ test-object X, ∀ a b c : X ⟶ 𝒢):
  assoc       : μ(μ(a,b), c) = μ(a, μ(b,c))
  left_unit   : μ(η, a) = a
  right_unit  : μ(a, η) = a
  left_inv    : μ(ι(a), a) = η
  right_inv   : μ(a, ι(a)) = η
```

### §3 Character Object (Walsh / Fourier dual)

Bundles a dual object Ĝ with an evaluation pairing into Ω. Stands for the internal hom [𝒢, Ω].

```
Ĝ : CharObj(𝕋, 𝒢)  :=
  dual : Obj(ℰ)                         -- Ĝ
  ev   : Ĝ × 𝒢 ⟶ Ω                    -- evaluation / pairing
```

### §4 Walsh Transform

Axiomatised spectral morphism: sends each endomorphism f : 𝒢 → 𝒢 to a morphism 𝒲(f) : Ĝ → Ω.

```
𝒲 : WalshTr(𝕋, 𝒢, Ĝ)  :=
  wal : (𝒢 ⟶ 𝒢) → (Ĝ ⟶ Ω)
```

### §5 Spectral Flatness — the AB Predicate

An endomorphism f is AB ("Almost Bent") at level c if the Walsh transform exhibits a spectral dichotomy: every generalised element χ of the dual satisfies 𝒲(f)(χ) = ⊥_Ω or 𝒲(f)(χ) = c.

```
IsAB(𝒢, Ĝ, 𝒲, f, c) : Prop  :=
  ∀ X : Obj(ℰ), ∀ χ : X ⟶ Ĝ,
    χ ≫ 𝒲(f) = !_X ≫ ⊥_Ω
  ∨ χ ≫ 𝒲(f) = !_X ≫ c

  -- !_X : X ⟶ 𝟙 is the unique terminal morphism
```

### §6 AB Function Object

A complete datum: group + dual + Walsh + endomorphism + level + AB witness.

```
ABFunc(𝕋) :=
  𝒢  : GrpObj(𝕋)
  Ĝ  : CharObj(𝕋, 𝒢)
  𝒲  : WalshTr(𝕋, 𝒢, Ĝ)
  f  : 𝒢 ⟶ 𝒢
  c  : 𝟙 ⟶ Ω
  ab : IsAB(𝒢, Ĝ, 𝒲, f, c)
```

### §7 AB Morphisms

A morphism between AB data (𝒢₁, f₁) and (𝒢₂, f₂): an intertwining map φ and a contravariant dual map ψ.

```
ABHom(F₁, F₂) :=
  φ    : 𝒢₁ ⟶ 𝒢₂                      -- intertwining map
  comm : φ ≫ f₂ = f₁ ≫ φ              -- intertwining condition
  ψ    : Ĝ₂ ⟶ Ĝ₁                      -- contravariant dual

-- Extensionality: α = β  ⟺  α.φ = β.φ ∧ α.ψ = β.ψ
-- Identity:  id_F = ⟨𝟙, rfl, 𝟙⟩
-- Composition:  α ≫ β = ⟨α.φ ≫ β.φ, ⋯, β.ψ ≫ α.ψ⟩   (ψ reverses)
```

### §8 Category Instance ✅

ABFunc(𝕋) forms a category: identity and composition satisfy the unit and associativity laws.

```
Category(ABFunc(𝕋))  -- ✅ proven (id_comp, comp_id, assoc)
```

### §9 m-Tuple Kernel

The kernel 𝒦_m of the iterated sum Σ_m : 𝒢^m → 𝒢, axiomatised as a mono subobject with a classifying map κ_m : 𝟙 → Ω.

```
KerObj(𝒢, m) :=
  𝒢^m    : Obj(ℰ)
  Σ_m    : 𝒢^m ⟶ 𝒢
  𝒦_m    : Obj(ℰ)
  incl   : 𝒦_m ↪ 𝒢^m                   -- mono
  κ_m    : 𝟙 ⟶ Ω                       -- classifying map
```

### §10 Geometric Morphisms

A geometric morphism between toposes: an adjunction Φ* ⊣ Φ_* where the inverse image Φ* preserves finite limits.

```
GeomMorph(𝕋₁, 𝕋₂) :=
  Φ_* : ℰ₁ ⥤ ℰ₂                       -- direct image
  Φ*  : ℰ₂ ⥤ ℰ₁                       -- inverse image
  adj : Φ* ⊣ Φ_*
  lex : PreservesFiniteLimits(Φ*)       -- left exact
```

---

## Module 2 — `CodingTheoryIsomorphism`: Weight Enumerators & Kerdock

### §1 Basic Definitions

```
hammingWeight(v : 𝔽₂ⁿ) := |{i | vᵢ ≠ 0}|

BinaryCode(n) :=
  C ⊆ 𝔽₂ⁿ,  0⃗ ∈ C,  c₁ + c₂ ∈ C      -- linear code

A_w(C)  := |{c ∈ C | wt(c) = w}|        -- weight distribution
P_m(C)  := Σ_w A_w · (n − 2w)^m         -- Pless moment
κ_m(C)  := |{(c₁,…,c_m) ∈ C^m | Σ cⱼ = 0}|
```

### §2–§4 Proven Claims

| Claim | Statement | Proof |
|-------|-----------|-------|
| **A** ✅ | A₀ = 1 | The only weight-0 codeword is 0⃗ |
| **B** ✅ | Σ_w A_w = \|C\| | Partition of C by weight |
| **C** ✅ | κ_m = \|C\|^{m−1}  (m ≥ 1) | c₁,…,c_{m−1} free; c_m = −Σcⱼ ∈ C (using −x = x in 𝔽₂) |
| **D** ✅ | \|C₁\| = \|C₂\| ⟹ κ_m(C₁) = κ_m(C₂) | Immediate from C |
| **E** ✅ | 3-weight ⟹ 4-term Pless decomposition | Only w₁,w₂,w₃ contribute nonzero A_w |
| **F** ✅ | Kerdock weights ↦ AB spectrum | Weights n/2, n/2±2^{r−1} ↦ eigenvalues {n, 2^r, 0, −2^r} |

### §5–§6 AB ↔ Kerdock Correspondence

Defines predicates and proves both directions:

```
hasABTypeSpectrum(C) :=  ∃ r, ∀ w, A_w ≠ 0 ⟹ (n − 2w) ∈ {n, 2^r, 0, −2^r}

hasKerdockWeightStructure(C) :=  ∃ r ≥ 1, nonzero weights ⊆ {n/2 − 2^{r−1}, n/2, n/2 + 2^{r−1}}

-- Forward  ✅:  Kerdock weights ⟹ AB spectrum
-- Converse ✅:  AB spectrum ⟹ weight constraints (modulo 2 | n)
-- Uniqueness ✅: same |C| ⟹ same κ_m
```

---

## Module 3 — `PNBooleanRelatives`: The Bridge Theorem

### §1 Spectral Topos Framework

A spectral topos is parameterised by |Ω|. The internal m-tuple count is |Ω|^{(m−1)n − m}.

```
SpectralTopos        := ⟨card_Ω : ℕ,  card_Ω > 0⟩
booleanSpectralTopos := ⟨2⟩
pValuedSpectralTopos(p) := ⟨p⟩

κ_m^int(𝒯, n, m)    := |Ω_𝒯|^{(m−1)n − m}
κ_m^classical(n, m)  := 2^{(m−1)n − m}
```

### §2–§4 Recovery Theorems (all ✅ by `rfl`)

```
⑥  κ_m^int(Bool, n, m)    = 2^{(m−1)n − m}        -- Boolean recovery
⑧  κ_m^int(𝔽_p,  n, m)    = p^{(m−1)n − m}        -- PN recovery
⑦  κ_m^𝒯 · κ_m^𝒮          = κ_m^𝒮 · κ_m^𝒯        -- commutativity
```

### §5–§6 PN → Boolean Relatives

A spectral signature has PN-type counting in 𝒯 at dimension n if σ(m) = κ_m^int(𝒯, n, m) for all m ≥ 2. The Boolean relative is the unique such signature at |Ω| = 2.

```
HasPNTypeCounting(𝒯, n, σ) := ∀ m ≥ 2, σ(m) = |Ω_𝒯|^{(m−1)n − m}

booleanRelativeSignature(n)(m) := 2^{(m−1)n − m}
```

**Key results** (all ✅):

```
-- Exponent match: PN and Boolean counts share exponent (m−1)n − m
pn_boolean_exponent_match :
  ∃ e, κ_m^p(n,m) = p^e ∧ κ_m^2(n,m) = 2^e

-- Existence: every PN signature has a Boolean relative
pn_boolean_relative_existence :
  HasPNTypeCounting(𝔽_p, n, σ_p) ⟹ HasPNTypeCounting(Bool, n, σ_bool)

-- Uniqueness: the Boolean relative is determined by n alone
boolean_relative_unique :
  HasPNTypeCounting(Bool, n, σ) ⟹ σ = booleanRelativeSignature(n)
```

### §7–§8 Concrete Instances & Bridge Theorem

Applied to Coulter-Matthews (p = 3) and Ding-Helleseth (general p).

```
Bridge Theorem  ✅ :
  (i)   booleanRelativeSignature has PN-type counting
  (ii)  exponents match for all m ≥ 2
  (iii) the relative is unique
```

---

## Module 4 — `SporadicABFunc`: Instantiation in Type (Boolean Topos)

### §1 The Boolean Topos

Type (= Set) as an elementary topos with Ω = Bool, ⊤ = true, ⊥ = false.

```
TypeTopos : ElemTopos  :=  ⟨Type, Bool, true, false, true ≠ false⟩
```

### §2–§3 Group & Character Objects from Lean Groups

Any `[Group G]` yields a `GrpObj(TypeTopos)` with all five axioms verified via `group`.  
The character object uses `G →* Multiplicative Bool`.

```
FinGrpObj(G) : GrpObj(TypeTopos)         -- from [Group G]
BoolCharObj(G) : CharObj(TypeTopos, FinGrpObj G)
```

### §4–§6 Walsh, AB Witnesses, ABFunc Packaging

The constant-true Walsh transform trivially satisfies the spectral dichotomy.  
`mkABFunc G f` packages any group endomorphism as an ABFunc datum.

```
mkABFunc(G, f) : ABFunc(TypeTopos)
```

### §7 Sporadic Instances

```
ABFunc_ZMod(n)    -- ℤ/nℤ with identity
ABFunc_Perm(α)    -- Sym(α) with identity
ABFunc_S(n)       -- S_n
ABFunc_conj(G, g) -- conjugation x ↦ gxg⁻¹
ABFunc_square(G)  -- squaring x ↦ x²
```

### §8–§9 Kernel Object & Geometric Morphisms

```
finKerObj(G, m) : KerObj(TypeTopos, FinGrpObj G, m)
  -- 𝒦_m = {v : Fin m → G | ∏ v = 1}

GeomMorphOmega(𝕋₁, 𝕋₂) extends GeomMorph with
  ω_comp : Φ*(Ω₂) ⟶ Ω₁                -- Ω-compatibility
```

### §10 Non-Abelian κ_m via Commutator Counting

```
[a,b] := a⁻¹b⁻¹ab

κ_m^comm(G) := |{(x₁,…,x_{2m}) | [x₁,x₂]⋯[x_{2m−1},x_{2m}] = 1}|

-- For abelian G:  κ_m^comm = |G|^{2m}       ✅
-- For trivial G:  κ_m^comm = 1              ✅
```

---

## Module 5 — `HomotopySpectral`: Spectral Rigidity

### §1–§2 Spectral Objects & Diversity

A spectral object carries a ℂ-valued spectrum. Bentness means every spectral value is 0 or has norm c. The **spectral diversity** counts distinct nonzero norm values.

```
SpectralObject(F) :=  ⟨carrier, spectrum : carrier → ℂ⟩

IsBent(X, c) := ∀ v, X(v) = 0 ∨ ‖X(v)‖ = c

spectralDiversity(X) := |{‖X(v)‖ | v ∈ carrier, ‖X(v)‖ ≠ 0}|
```

### §3 Homotopy Spectral Objects

Enriches a spectral object with homotopy group cardinalities πₖ.

```
HomotopySpectralObject(F) :=
  base         : SpectralObject(F)
  πₖ           : ℕ → ℕ                  -- |πₖ|
  πₖ_pos       : ∀ k, πₖ(k) ≥ 1

IsDiscrete(X) := ∀ k ≥ 1, πₖ(k) = 1
IsKBent(X, c, k) := IsBent(base, c) ∧ ∀ 1 ≤ j ≤ k, πⱼ = 1
QuasiIso(X, Y) := ∀ k, πₖ^X(k) = πₖ^Y(k)

χ_N(X) := Σ_{k=0}^{N} (−1)^k · πₖ(k)   -- Euler characteristic
```

### §4 Postnikov Construction

Builds homotopy data from spectral data: π₀ = |carrier|, πₖ = spectralDiversity for k ≥ 1.  
Key property: bent ⟹ diversity = 1 ⟹ discrete.

```
postnikov(X, hNontriv) : HomotopySpectralObject(F)
  π₀ := |X.carrier|
  πₖ := spectralDiversity(X)   for k ≥ 1
```

### §5–§6 Main Theorems (all ✅)

```
-- Bent ⟹ diversity = 1
bent_diversity_eq_one :
  IsBent(X, c) ∧ c > 0 ∧ (∃ v, X(v) ≠ 0) ⟹ spectralDiversity(X) = 1

-- Bent ⟹ discrete (the key rigidity theorem)
bent_implies_discrete :
  IsBent(X, c) ∧ c > 0 ∧ (∃ v, X(v) ≠ 0) ⟹ postnikov(X).IsDiscrete

-- ① k-Bentness is monotone
kBent_monotone :  IsKBent(X, c, k+1) ⟹ IsKBent(X, c, k)

-- ② Discrete + bent ⟹ k-Bent at all levels
discrete_implies_kBent :
  IsBent(base, c) ∧ IsDiscrete(X) ⟹ ∀ k, IsKBent(X, c, k)

-- ③ Quasi-iso preserves Euler characteristic
euler_quasiIso_invariant :
  QuasiIso(X, Y) ⟹ χ_N(X) = χ_N(Y)

-- ④ Bent Postnikov objects are k-Bent at all levels
postnikov_bent_all_kBent :
  IsBent(X, c) ∧ c > 0 ∧ (∃ v, X(v) ≠ 0) ⟹ ∀ k, postnikov(X).IsKBent(c, k)
```

---

## Module 6 — `ABDiscoveryIntegration`: End-to-End Pipeline

Integrates the four stages: **Screening → Bridge → Validation → Rigidity**.

### Pipeline Overview

```
  PN function over 𝔽_{p^n}
        │
        ▼
  ┌─────────────────────┐
  │ 1. SCREENING        │  mkABFunc on groups (S_n, ℤ/nℤ, G×H, …)
  │    ABFunc(TypeTopos) │  κ_m formula: |{v | ∏v = 1}| = |G|^{m−1}  ✅
  └─────────┬───────────┘
            │
            ▼
  ┌─────────────────────┐
  │ 2. BRIDGE           │  bridge_theorem: σ_p ↦ σ_bool
  │    p^e → 2^e        │  Exponent e = (m−1)n − m preserved    ✅
  └─────────┬───────────┘
            │
            ▼
  ┌─────────────────────┐
  │ 3. VALIDATION       │  Kerdock ↔ AB spectrum (both directions) ✅
  │    Coding theory     │  MDS rigidity, Pless 4-term decomposition ✅
  └─────────┬───────────┘
            │
            ▼
  ┌─────────────────────┐
  │ 4. RIGIDITY         │  bent_implies_discrete (derived, not postulated) ✅
  │    Homotopical       │  ∀ k, postnikov(X).IsKBent(c, k)  ✅
  └─────────────────────┘
```

### The Complete Pipeline Theorem ✅

```
complete_pipeline(p, n) :
  (i)   ∀ G [Group G], ∃ ab : ABFunc(TypeTopos)          -- screening
  (ii)  HasPNTypeCounting(Bool, n, σ_bool)                -- bridge
  (iii) ∀ m ≥ 2, ∃ e, κ_m^p = p^e ∧ σ_bool(m) = 2^e    -- exponent match
  (iv)  IsBent(X,c) ∧ c > 0 ⟹ postnikov(X).IsDiscrete  -- rigidity
```

### Concrete Pipelines

```
coulterMatthews_pipeline(n) :                            -- GF(3^n)  ✅
  σ_bool = booleanRelativeSignature(n)
  ∧ HasPNTypeCounting(Bool, n, σ_bool)
  ∧ uniqueness

dingHelleseth_boolean_parent(p, n) :                     -- GF(p^n)  ✅
  σ_bool = booleanRelativeSignature(n)
  ∧ ∀ m ≥ 2, κ_m^p = p^{(m−1)n−m} ∧ σ_bool(m) = 2^{(m−1)n−m}
```

---

## Axiom Audit

All proven theorems depend only on the standard CIC axioms:

| Axiom | Status |
|-------|--------|
| `propext` | ✅ used |
| `Classical.choice` | ✅ used (noncomputable sections) |
| `Quot.sound` | ✅ used |

No `sorry`, no custom axioms, no `@[implemented_by]`.
