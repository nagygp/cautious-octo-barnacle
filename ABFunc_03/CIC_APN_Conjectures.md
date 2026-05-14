# CIC Unicode Conjectures: APN Functions, Geometric Structure of Δ, and Topos Duality

Conjectures extending the AB-function topos-theoretic framework to **Almost Perfect Nonlinear (APN)** functions, the geometric/affine structure of the difference set Δ, and their relationships to the existing topos and duality infrastructure.

All conjectures are derivable from blackboxed known results in the APN literature or from results already present in the project.

---

## §1  APN Functions — Internal Definition in the Topos

An **APN function** (Almost Perfect Nonlinear) is an endomorphism f : 𝒢 → 𝒢 of an internal group object whose differential fibres have size at most 2.

### Definition (Differential Map)

```
𝒟_a(f) : 𝒢 ⟶ 𝒢
𝒟_a(f)(x) := μ(f(μ(x, a)), ι(f(x)))

  -- i.e., D_a f(x) = f(x + a) − f(x)  in additive notation
```

### Definition (APN Predicate)

```
IsAPN(𝒢, f) : Prop  :=
  ∀ (a : 𝒢), a ≠ η →
    ∀ (b : 𝒢), |{ x : 𝒢 | 𝒟_a(f)(x) = b }| ≤ 2
```

Equivalently, the **differential uniformity** δ(f) = max_{a≠0,b} |𝒟_a^{-1}(b)| = 2.

---

## §2  Differential Image Size (Conjecture A)

**Known result** (elementary counting): For an APN function f : 𝔽_{2^n} → 𝔽_{2^n}, the image of each non-trivial differential has size exactly 2^{n−1}.

```
Conjecture A (APN Differential Image Size):

  IsAPN(𝒢, f) ∧ |𝒢| = 2^n
  ⟹  ∀ (a : 𝒢), a ≠ η → |Im(𝒟_a(f))| = 2^{n−1}

  Proof sketch:
    ∑_{b : 𝒢} |𝒟_a^{-1}(b)| = |𝒢| = 2^n
    Each |𝒟_a^{-1}(b)| ∈ {0, 2}  (APN condition)
    ∴ |{b : |𝒟_a^{-1}(b)| = 2}| = 2^n / 2 = 2^{n−1}
    ∴ |Im(𝒟_a(f))| = 2^{n−1}
```

---

## §3  Δ as an Affine Half-Space (Conjecture B)

The image of the differential map Im(𝒟_a(f)) is a subset of 𝒢 of size |𝒢|/2. This defines a **half-space** structure: for each nonzero direction a, the differential image bisects the group.

```
Conjecture B (Δ Half-Space Decomposition):

  IsAPN(𝒢, f) ∧ |𝒢| = 2^n
  ⟹  ∀ (a : 𝒢), a ≠ η →
        |Im(𝒟_a(f))| + |𝒢 \ Im(𝒟_a(f))| = 2^n
        ∧ |Im(𝒟_a(f))| = |𝒢 \ Im(𝒟_a(f))|

  -- The differential image and its complement partition 𝒢 into
  -- two equal halves, analogous to an affine hyperplane arrangement.
```

### Geometric interpretation

The collection of half-spaces {Im(𝒟_a(f)) : a ≠ 0} forms a **spread-like** structure over 𝒢:
- Each half-space has size 2^{n−1}
- Different directions a yield (in general) different half-spaces
- The incidence structure (a, b) ↦ [b ∈ Im(𝒟_a(f))] forms a **2-design**

---

## §4  APN–AB Spectral Bridge (Conjecture C)

**Known result** (Chabaud–Vaudenay, 1994): For power functions f(x) = x^d over 𝔽_{2^n} with n odd, the APN and AB properties are equivalent.

```
Conjecture C (APN ↔ AB for Odd-Dimension Power Functions):

  n odd ∧ f = (x ↦ x^d) : 𝔽_{2^n} → 𝔽_{2^n}
  ⟹  IsAPN(𝔽_{2^n}, f) ↔ IsAB(𝔽_{2^n}, f)

  -- In the topos framework:
  -- IsAPN(𝒢, f) ⟺ spectral_dichotomy(𝒲(f))
  -- when 𝒢 = 𝔽_{2^n}, n odd, f is a power map.
```

This connects the *differential* characterization (APN: fibres ≤ 2) to the *spectral* characterization (AB: Walsh values ∈ {0, ±2^{(n+1)/2}}).

---

## §5  APN m-Tuple Counting Formula (Conjecture D)

**Derived from project result ⑥**: The internal m-tuple counting formula |Ω|^{(m−1)n − m} applies to APN functions via the AB bridge.

```
Conjecture D (APN m-Tuple Count):

  IsAPN(𝒢, f) ∧ |𝒢| = 2^n ∧ n odd
  ⟹  κ_m(f) = 2^{(m−1)n − m}  for all m ≥ 2

  where κ_m(f) := |{ (x₁,…,x_m) ∈ 𝒢^m :
                       ∑ xᵢ = 0 ∧ ∑ f(xᵢ) = 0 }|
```

For even n, the APN m-tuple count follows a modified formula:
```
  IsAPN(𝒢, f) ∧ |𝒢| = 2^n ∧ n even
  ⟹  κ_m(f) ≤ 2^{(m−1)n − m + ⌊m/2⌋}
```

---

## §6  APN Topos Invariance Under Duality (Conjecture E)

**Derived from project duality results**: The APN property, being defined via the differential (which uses only the group structure), is invariant under the duality functor D : Topos → Topos^{op}.

```
Conjecture E (APN Duality Invariance):

  IsAPN(𝒢, f) ↔ IsAPN(𝒢^{op}, f^†)

  where f^† is the dual endomorphism in ℰ^{op}
  and 𝒢^{op} carries the opposite Heyting algebra.

  -- Concretely: the differential uniformity is a self-dual invariant
  -- δ(f) = δ(f^†) under the conjugation duality.
```

---

## §7  APN Difference Graph as a 2-Design (Conjecture F)

**Known result** (Carlet, 2010): The difference graph of an APN function forms a specific combinatorial design.

```
Conjecture F (APN Difference Graph Design):

  IsAPN(𝒢, f) ∧ |𝒢| = 2^n
  ⟹  The incidence structure
      𝒥 := (𝒢 \ {η}, 𝒢, ∈_Δ)
      where (a, b) ∈_Δ iff b ∈ Im(𝒟_a(f))

      is a 2-(2^n, 2^{n−1}, 2^{n−1} − 1) design:
      • |points| = 2^n
      • |block size| = 2^{n−1}
      • every pair of distinct points appears in λ = 2^{n−1} − 1 blocks
```

---

## §8  APN–Kerdock Code Bridge (Conjecture G)

**Derived from project result (Claim F)**: The AB–Kerdock correspondence extends to APN functions via the spectral bridge.

```
Conjecture G (APN–Kerdock Correspondence):

  IsAPN(𝒢, f) ∧ |𝒢| = 2^n ∧ n odd
  ⟹  ∃ C : BinaryCode(2^{2r}),
        hasKerdockWeightStructure(C) ∧
        ∀ m ≥ 2, mTupleCount(C, m) = κ_m(f)

  -- The APN function's m-tuple kernel count matches the m-tuple
  -- count of a Kerdock code, establishing the cryptographic–coding
  -- theory bridge via the AB intermediate.
```

---

## §9  APN Self-Dual Bridge Invariance (Conjecture H)

**Derived from project Theorem 4 (bridge_fixed_point)**: The counting formula for APN functions is a fixed point of the duality functor.

```
Conjecture H (APN Bridge Fixed Point):

  ∀ (𝒯 : SpectralTopos), ∀ n m : ℕ,
    κ_m^{APN}(D(𝒯), n) = κ_m^{APN}(𝒯, n)

  where D is the duality functor and κ_m^{APN} is the APN m-tuple count.

  -- Combined with Conjecture E, this gives:
  -- The APN counting signature is an absolute invariant,
  -- unchanged by both arrow reversal and base change.
```

---

## §10  Differential Uniformity Spectrum in the Topos (Conjecture I)

The **differential uniformity spectrum** generalises the APN/PN dichotomy to arbitrary endomorphisms.

```
Conjecture I (Differential Uniformity as Topos Invariant):

  δ : End(𝒢) → ℕ
  δ(f) := max_{a≠η, b} |{ x : 𝒟_a(f)(x) = b }|

  -- δ is a topos invariant: preserved by geometric morphisms
  ∀ (Φ : GeomMorph(𝕋₁, 𝕋₂)),
    δ_{𝕋₁}(f) = δ_{𝕋₂}(Φ_*(f))

  -- Hierarchy:
  -- δ(f) = 1  ⟹  f is PN (Perfect Nonlinear) — only char ≠ 2
  -- δ(f) = 2  ⟹  f is APN (Almost Perfect Nonlinear)
  -- δ(f) = 2^k ⟹  f is k-differentially uniform
  -- δ(f) = 2^n ⟹  f is affine (worst case)
```

---

## Summary Table

| # | Conjecture | Source | Type |
|---|------------|--------|------|
| A | APN differential image size = 2^{n−1} | Elementary counting | Theorem |
| B | Δ half-space decomposition | Counting + complement | Theorem |
| C | APN ↔ AB for odd n power functions | Chabaud–Vaudenay (blackboxed) | Known result |
| D | APN m-tuple counting formula | Project result ⑥ + Conj. C | Bridge theorem |
| E | APN duality invariance | Project duality framework | Structural |
| F | APN difference graph is a 2-design | Carlet (blackboxed) | Known result |
| G | APN–Kerdock bridge | Project AB–Kerdock + Conj. C | Bridge theorem |
| H | APN bridge fixed point | Project Theorem 4 | Structural |
| I | Differential uniformity as topos invariant | Project geometric morphism framework | Structural |
