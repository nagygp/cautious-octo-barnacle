# Kasami Triple-Count Conjecture — Proof Structure

## The Conjecture

For the Kasami function `f(x) = x^(4^k − 2^k + 1)` over `GF(2^n)` with
`gcd(k,n) = 1`, `n` odd, `n ≥ 3`, and `Δ = {f(b) + f(b+1) + 1 : b ∈ GF(2^n)}`:

For every pair of distinct nonzero elements `v₁, v₂ ∈ GF(2^n)`:

```
|{(x, y, z) ∈ Δ³ : v₁·x + v₂·y + (v₁ + v₂)·z = 0}| = 2^(2n − 3)
```

**Note:** The original conjecture omits the `n odd` hypothesis, but this is
necessary — the AB (Almost Bent) property, which the proof relies on, only
holds for odd `n`. For even `n`, the Walsh spectrum has a different structure.

## File Structure

### Fully Proved Files (no sorry)

1. **`KasamiDefs.lean`** — Core definitions
   - `kasamiExp k` = `4^k − 2^k + 1`
   - `kasamiFun F k b` = `b ^ kasamiExp k`
   - `kasamiDelta F k` = `{f(b) + f(b+1) + 1 : b ∈ F}`
   - `tripleSet F k v₁ v₂` = the set of triples satisfying the linear constraint

2. **`KasamiCharacters.lean`** — Additive characters (uses Mathlib)
   - `kasamiChar F` — canonical primitive additive character via Mathlib's `AddChar.FiniteField`
   - `sum_char_mul_eq_zero` — orthogonality: `∑_x χ(x·a) = 0` for `a ≠ 0`
   - `kasamiChar_norm` — `‖χ(x)‖ = 1`

3. **`KasamiFourier.lean`** — Fourier identity for triple counting (fully proved)
   - `deltaIndicator`, `deltaFourier` — indicator and Fourier transform of Δ
   - `tripleSpectral` — the spectral triple sum
   - **`fourier_triple_identity`** — `|F| · |tripleSet| = tripleSpectral`
     (the central bridge between combinatorics and spectral analysis)

### Files with Sorry (deep mathematical content)

4. **`KasamiSpectral.lean`** — Spectral properties (3 sorry's)
   - `kasamiDiffCount` — differential count definition
   - **`kasami_is_APN`** ⬚ — Kasami function is APN when `gcd(k,n) = 1`
   - **`APN_power_implies_AB_odd`** ⬚ — APN power functions are AB for odd `n`
   - `kasamiDelta_preimage_two` ✓ — each fiber has exactly 2 preimages (proved from APN)
   - `kasamiDelta_card` ✓ — `|Δ| = 2^(n-1)` (proved from fiber lemma)
   - **`tripleSpectral_nonzero_vanish`** ⬚ — spectral cancellation under AB
   - `tripleSpectral_eq_deltaCube` ✓ — `tripleSpectral = |Δ|³` (proved from vanishing)
   - Arithmetic lemmas ✓

5. **`Kasami_Final_Theorem.lean`** — Final theorem (no new sorry's)
   - **`kasami_triple_count`** — the main theorem
   - **`kasami_triple_count_conjecture`** — the conjecture (= main theorem)

## Proof Pipeline

```
kasami_is_APN (sorry)
    ↓
kasamiDelta_preimage_two (proved)
    ↓
kasamiDelta_card: |Δ| = 2^(n-1) (proved)

APN_power_implies_AB_odd (sorry) ←── kasami_is_APN
    ↓
tripleSpectral_nonzero_vanish (sorry) ←── AB property
    ↓
tripleSpectral_eq_deltaCube (proved)

fourier_triple_identity (proved, no sorry anywhere)

All combined in kasami_triple_count:
  |F| · |tripleSet| = tripleSpectral = |Δ|³ = (2^{n-1})³ = 2^{3n-3} = 2^n · 2^{2n-3}
  ⟹ |tripleSet| = 2^{2n-3}
```

## The Three Open Sorries

### 1. `kasami_is_APN` — Theorem 3 (McGuire et al.)

The Kasami function is APN: for every `u ≠ 0` and `v`, the derivative equation
`f(x+u) + f(x) = v` has at most 2 solutions.

**Proof approach** (from Bracken–Byrne–Markin–McGuire):
- Normalize by `y = x/u` to get a linearized polynomial equation
- Factor the linearized polynomial through Frobenius compositions
- Use `gcd(k,n) = 1` to bound the kernel dimension to ≤ 1 over GF(2)

**Difficulty:** Requires formalizing linearized polynomial theory over finite fields,
kernel dimension arguments, and the specific factorization for the Kasami exponent.

### 2. `APN_power_implies_AB_odd` — Chabaud–Vaudenay / Nyberg

For power functions `x^d` over `GF(2^n)` with `n` odd, APN implies AB.

**Proof approach:**
- Walsh transform of power functions reduces to a single variable
- Fourth moment identity from APN gives `∑ |W|⁴ = 2^{n+1} · ∑ |W|²`
- Parseval gives `∑ |W|² = 2^{2n}`
- Cauchy-Schwarz equality forces all nonzero Walsh values to be `±2^{(n+1)/2}`

**Difficulty:** Requires formalizing the Walsh transform Parseval identity (done in
KasamiCharacters in the reuse directory), fourth moment computation from differential
uniformity, and the forcing argument.

### 3. `tripleSpectral_nonzero_vanish` — Spectral Cancellation

The sum `∑_{a≠0} δ̂(v₁a)·δ̂(v₂a)·δ̂((v₁+v₂)a) = 0` under AB.

**Proof approach:**
- Express `δ̂(c)` in terms of Walsh coefficients
- Under AB, `δ̂(c) = (1/2)·∑_b χ(c·g(b))` where `g(b) = f(b+1)+f(b)+1`
- The triple product cancels due to the 3-design property of AB Walsh supports

**Difficulty:** This is the deepest step. Requires the full AB spectral structure
and careful character sum manipulations.

## Mathlib Components Used

- `AddChar.FiniteField.primitiveChar_to_Complex` — canonical additive character
- `AddChar.sum_mulShift` — character orthogonality
- `AddChar.norm_apply` — character values have norm 1
- `CharP` — characteristic `p` typeclass
- `Finset.sum_*`, `Finset.card_*` — finite set combinatorics
- `Complex.normSq` — complex norm squared

## References

1. Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions", Theorem 3
2. Budaghyan, "Construction and Analysis of Cryptographic Functions", Theorem 2.3
3. Chabaud–Vaudenay (1994), Nyberg (1994) — APN ⟹ AB for odd characteristic
