# Category-Theoretic Generalizations of the Kasami P₃ Theorem

## 1. The P₃ Theorem and Its Proof Structure

The Kasami P₃ theorem states that for `gcd(k,n) = 1`, `n` odd, `n ≥ 3`, and nonzero `v₁ ≠ v₂` in `F_{2^n}`:

```
|{ (x,y,z) ∈ Δ³ : v₁·x + v₂·y + (v₁+v₂)·z = 0 }| = 2^{2n−3}
```

The proof chain has these logically independent layers:

1. **Fourier Analysis Layer**: The character-sum representation of the triple count (works for any finite abelian group)
2. **Spectral Layer**: The Almost Bent (AB) property constraining the Walsh spectrum to three values
3. **Algebraic Layer**: Proving the Kasami function *is* AB, via quadratic form rank analysis and linearized polynomial kernels

## 2. Levels of Generalization

### Level 1: Finite Abelian Groups (Most General)

The **character-sum representation** of the triple count generalizes immediately to any finite abelian group `G`:

For any subset `Δ ⊆ G` and characters `χ` of `G`:

```
|G| · |{(x,y,z) ∈ Δ³ : v₁·x + v₂·y + v₃·z = 0}| = ∑_χ Ŝ_Δ(χ^{v₁}) · Ŝ_Δ(χ^{v₂}) · Ŝ_Δ(χ^{v₃})
```

where `Ŝ_Δ(χ) = ∑_{x∈Δ} χ(x)`.

In category-theoretic terms, this is the **Pontryagin duality** functor on the category of locally compact abelian groups (restricted to the finite case). The character sum identity is a consequence of the self-duality of the group algebra `ℂ[G]` as a **Frobenius algebra** in the symmetric monoidal category `(Vect_ℂ, ⊗)`.

**What survives**: `tripleCount_charSum_eq` and its proof generalize verbatim to any finite abelian group. No modification needed.

**What breaks**: The specific numerical value `2^{2n-3}` depends entirely on the group being `(ℤ/2ℤ)^n` and the specific function generating `Δ`.

### Level 2: Elementary Abelian p-Groups

The theory extends to `G = (ℤ/pℤ)^n` for any prime `p`, with:

- **Additive characters**: `χ_a(x) = ω^{Tr(a·x)}` where `ω = e^{2πi/p}` and `Tr: 𝔽_{p^n} → 𝔽_p`
- **Walsh-Hadamard transform**: `W_f(a) = ∑_x ω^{Tr(ax + f(x))}`
- **Parseval**: `∑_a |W_f(a)|² = p^{2n}`
- **Almost Bent analogue**: `|W_f(a)|² ∈ {0, p^{n+1}}` (called "almost bent" for `p = 2`, "planar" for odd `p`)

For odd `p`, the "planar" functions (analogues of AB functions) give constant triple-intersection numbers with value `p^{2n-3}`. The theory is richer because:
- The characteristic ≠ 2 means quadratic forms have non-degenerate symmetric bilinear forms (no radical subtleties)
- The Gauss sum evaluation is simpler: `S(Q)² = ε · p^{n-k}` where `ε` is the **Legendre symbol** (not just ±1)

**What survives**: The entire proof skeleton, with `2` replaced by `p` throughout. The quadratic form theory (`QuadFormGF2/`) would need to be generalized to `QuadFormGFp/`, which is mathematically straightforward but requires significant Lean refactoring.

**What breaks**: The Freshman's Dream `(x+y)^p = x^p + y^p` still holds (it's characteristic `p`), but the specific Kasami exponent `d = 4^k - 2^k + 1` is specific to `p = 2`.

### Level 3: Association Schemes and Schur Rings

The deepest category-theoretic generalization uses **association schemes**. An association scheme on a set `X` of size `n` is a partition of `X × X` into `d + 1` relations satisfying regularity conditions. The adjacency algebra of the scheme is a **commutative semisimple algebra** with structure constants `p_{ij}^k`.

The triple-intersection number `T(v₁, v₂)` is a specific structure constant (or sum thereof) of the **Schur ring** associated to the group action.

**Key category-theoretic structure**: The Schur ring `S(G, Δ)` is a **Frobenius algebra** in the monoidal category `(G\text{-Mod}, ⊗_G)` of `G`-modules. The triple count is the trace of a specific multiplication map in this algebra.

For a difference set `Δ` in `G` with parameters `(v, k, λ)`, the triple intersection numbers are determined by the **character table** of the association scheme, which is a matrix satisfying orthogonality relations analogous to the Fourier transform.

**What survives**: The structural decomposition:
```
Triple Count = a=0 term + ∑_{a≠0} spectral terms
```
The a=0 term is always `|Δ|³/|G|`, and the nonzero sum vanishes when `Δ` comes from an AB/planar function.

**What breaks**: The *existence* of an AB/planar generating function is not guaranteed for general association schemes. The Kasami exponent is a very special construction.

### Level 4: Tensor Categories and Quantum Groups

At the highest level of abstraction, the proof uses the following categorical structure:

1. **A symmetric monoidal category** `(𝒞, ⊗, 𝟙)` with a **Frobenius algebra** object `A`
2. **A Fourier transform** natural transformation `ℱ: Fun(G, ℂ) → Fun(Ĝ, ℂ)` (where `Ĝ` is the Pontryagin dual)
3. **A spectral condition** on the image of `ℱ` (the AB property)
4. **A trace computation** in the endomorphism algebra `End(A ⊗ A ⊗ A)`

The P₃ theorem can be stated as: Under the spectral condition on `ℱ(1_Δ)`, the trace of the multiplication morphism `m: A^{⊗3} → A` restricted to the kernel of the linear constraint is a specific rational number times `|G|^3`.

This framework applies to:
- **Finite abelian groups** (classical case)
- **Quantum groups** (deformation quantization of G)
- **Fusion categories** (modular tensor categories from rational CFT)
- **Vertex algebras** (infinite-dimensional analogues)

However, the spectral condition (AB property) becomes increasingly restrictive in each case, and the Kasami-type construction is very specific to the finite field setting.

## 3. Where the Theorem Holds "As Is"

The theorem `T(v₁, v₂) = 2^{2n-3}` holds exactly as stated for:

### (a) Elementary abelian 2-groups with AB functions
- Group: `G = (ℤ/2ℤ)^n`, `n` odd
- Function: Any AB function `f: G → G` (not just the Kasami function)
- Difference set: `Δ = {f(b) + f(b+1) + 1 : b ∈ G}`
- Result: `T(v₁, v₂) = 2^{2n-3}` for all nonzero `v₁ ≠ v₂`

This is the **maximal generalization preserving the exact numerical statement**. The proof goes through identically: the only properties of the Kasami function used are:
1. It is AB (Walsh spectrum in `{0, ±2^{(n+1)/2}}`)
2. It is APN (implied by AB)
3. The delta generator `g(b) = f(b) + f(b+1) + 1` satisfies `g(b) = g(b+1)` (automatic in char 2)

Known AB functions over `𝔽_{2^n}` (n odd) include:
- **Kasami**: `x^{4^k - 2^k + 1}` with `gcd(k,n) = 1`
- **Gold**: `x^{2^k + 1}` with `gcd(k,n) = 1`
- **Welch**: `x^{2^t + 3}` for `n = 2t + 1`
- **Niho**: `x^{2^t + 2^{t/2} - 1}` for specific `t`
- **Inverse**: `x^{2^{2t} - 1}` for `n = 2t + 1`

**All of these satisfy P₃ with the same count `2^{2n-3}`.**

### (b) Elementary abelian p-groups with planar functions (modified count)

For `G = (ℤ/pℤ)^n` with a **planar function** `f` (the odd-characteristic analogue of AB), the triple intersection count is:

```
T(v₁, v₂) = p^{2n-3}
```

This is a direct analogue with `2` replaced by `p`. The proof structure is identical, using `p`-ary characters and the planar spectral condition `|W_f(a)|² ∈ {0, p^{n+1}}`.

### (c) General difference sets with specific parameters

More broadly, for a `(v, k, λ)`-difference set `Δ` in a finite abelian group `G` of order `v`, the triple count depends on the **character sums** of `Δ`. When the character sums take at most 3 values (a "3-valued" difference set), the triple count is constant and equals:

```
T = k³/v + (v-1) · (character sum values)
```

The Kasami difference set is a specific instance of a 3-valued difference set.

## 4. Formalized Abstract Framework

The file `RequestProject/Kasami/AbstractTripleCount.lean` contains a formalization of the abstract framework: the triple count character sum identity for any finite abelian group with any subset, showing exactly which parts of the proof are group-theoretic (fully general) and which are specific to the Kasami setting.

Key abstract results formalized:
- The character-sum representation works for any finite commutative group
- The "splitting at a=0" is group-theoretic
- The vanishing of the nonzero sum requires the specific spectral condition

## 5. Summary: What Generalizes and What Doesn't

| Component | Generalizes to | Category-theoretic structure |
|-----------|---------------|------------------------------|
| Character-sum representation | Any finite abelian group | Pontryagin duality / Fourier on group algebra |
| Parseval identity | Any finite abelian group | Plancherel theorem |
| Split at a=0 | Any finite abelian group | Unit of convolution algebra |
| AB spectral condition | Elementary abelian p-groups | Spectral gap in representation ring |
| 2-to-1 property (APN) | Elementary abelian 2-groups | Differential uniformity in char 2 |
| Kasami exponent | Specific to 𝔽_{2^n} | Arithmetic of 2-power exponents |
| Linearized polynomial kernel | Specific to 𝔽_{2^n} | Frobenius endomorphism algebra |
| Quadratic form rank analysis | Char 2 finite fields | Quadratic module theory over 𝔽₂ |

### The Critical Boundary

The theorem "as is" (with exact count `2^{2n-3}`) generalizes to **any AB function on `𝔽_{2^n}`** — not just the Kasami function. This is because the proof only uses:
1. The AB spectral property (general)
2. The AB ⟹ APN implication (general for n odd)
3. Characteristic-2 arithmetic (specific to p=2)

Replacing "AB" with "planar" and `𝔽_{2^n}` with `𝔽_{p^n}` gives the analogous result for odd primes with count `p^{2n-3}`.

Beyond finite abelian groups, the category-theoretic framework of **Frobenius algebras in symmetric monoidal categories** provides the right language, but the specific numerical results require arithmetic input that doesn't come from the category theory alone.

## 6. References

- **Carlet, C. (2021).** *Boolean Functions for Cryptography and Coding Theory.* Cambridge University Press. — Comprehensive treatment of AB functions and their spectral properties.
- **Pott, A. (2004).** "Nonlinear functions in Abelian groups and relative difference sets." *Discrete Applied Mathematics*, 138(1-2), 177–193. — Generalizations to arbitrary abelian groups.
- **Beth, T., Jungnickel, D., Lenz, H. (1999).** *Design Theory.* Cambridge University Press. — Association schemes and difference sets.
- **Coulter, R.S., Henderson, M. (2004).** "Commutative presemifields and semifields." *Advances in Mathematics*, 217(1), 282–304. — Planar functions over odd characteristic.
