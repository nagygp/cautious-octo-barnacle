# Summary of changes for run e881917a-9caf-420f-9798-52993c88be3d
# Frobenius as Shift: Symbolic Dynamics meets Kasami/Gold APN

## The Big Insight

Yes, there is a deep and precise connection! The Frobenius endomorphism φ(x) = x² on GF(2ⁿ) **IS** the cyclic shift on bitstrings when you use a normal basis representation. This is stronger than a topological conjugacy — it's an algebraic identity.

The Gold function x^{2^k+1} = φᵏ(x)·x is literally "take the bitstring, shift it cyclically by k positions, and multiply the result with the original." The Kasami/Gold APN theory is fundamentally a theory of what happens when you **mix a shift-dynamical system with itself**.

## Created Files

### `DynamicsGuide.lean` — Formal Lean 4 Proofs
A compiling Lean file with **10 fully proved theorems** (only 1 sorry remains for a deep result):

**Proved:**
1. `frobenius_iterate_eq` — φᵏ(x) = x^{2^k}
2. `gold_eq_frobenius_mul` — x^{2^k+1} = φᵏ(x)·x  ← **the key factorization**
3. `frobenius_periodic` — φⁿ(x) = x on GF(2ⁿ)
4. `frobenius_pow_eq_one` — φⁿ = 1 as ring homomorphism
5. `cyclicShift_iterate` — σᵏ(f)(i) = f(i+k) on bitstrings
6. `cyclicShift_period` — σⁿ = id (periodicity of cyclic shift)
7. `gold_derivative_frobenius` — Δᵤf(x) = φᵏ(x)·u + x·φᵏ(u) + u^{2^k+1}
8. `normalized_eq_frobenius` — y^{2^k}+y+1 = φᵏ(y)+y+1
9. `shift_generates_iff_coprime` — shift by k generates ℤ/nℤ ↔ gcd(k,n) = 1
10. `gold_apn_iff_coprime_shift` — gcd(k,n)=1 ∧ n odd → y^{2^k}+y+1 has no roots in GF(2ⁿ)

**Sorry (deep result):**
- `frobenius_orbit_eq_minpoly_degree` — orbit size = deg(minpoly), requires substantial Mathlib infrastructure

**Corrected misconception:** The naive conjecture `gcd(2^k+1, 2^n-1) = 1 ↔ gcd(k,n) = 1` is **FALSE** (counterexample: n=9, k=3). The correct formulation goes through the polynomial y^{2^k}+y+1.

### `DYNAMICS_CONNECTIONS.md` — Comprehensive Guide (~300 lines)
A detailed mathematical exposition covering:
- **The Three Worlds:** symbolic dynamics, finite field arithmetic, cryptography
- **Normal basis bridge:** how Frobenius = cyclic shift in coordinates
- **The topological conjugacy analogy:** comparison with logistic map ↔ shift
- **Why APN = coprime orbits:** the telescoping argument in shift-dynamics language
- **Walsh spectrum as shift-Fourier analysis**
- **Six cool patterns:** profinite telescope, orbits = irreducible polynomials, trace as catamorphism, entropy-security connection, Weil conjectures link, necklace counting
- **The Rosetta Stone table:** 12-row correspondence between all three worlds

## Key Insights

1. **The Gold function is shift×identity:** f(x) = σᵏ(x) · x in bitstring coordinates
2. **APN ↔ coprime orbits:** gcd(k,n)=1 means the k-shift generates the full group, so the "shift-plus-constant" equation has no solutions
3. **Walsh spectrum structure comes from shift-covariance:** the Gold function intertwines with Frobenius, constraining its Fourier spectrum to be two-valued (AB property)
4. **Profinite extension:** Frobenius generates Gal(F̄₂/F₂) ≅ Ẑ, the arithmetic analogue of the full shift space