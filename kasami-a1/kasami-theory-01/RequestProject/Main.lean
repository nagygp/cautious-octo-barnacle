/-
# Kasami P₃ Framework — Main Entry Point

This project formalizes the proof structure for P₃ for general Kasami exponents
e(k) = 4^k - 2^k + 1 with gcd(k, n) = 1.

## Module Structure

### Foundation modules (fully proved):
* `TraceChar` — Additive characters via trace, character orthogonality
* `WalshHadamard` — Walsh–Hadamard transform, Parseval identity, convolution
* `SpectralIdentity` — The spectral identity ∑ Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c)) = |F|·N(c)
* `APNTheory` — APN/AB definitions, P₃ from AB vanishing
* `LinearizedPoly` — Linearized polynomials, Artin–Schreier theory

### New theory modules (framework with strategic sorries):
* `QuadraticGF2` — Quadratic forms over GF(2), Gauss sum formula
* `KasamiWalshSpectrum` — Walsh spectrum theorem → AB vanishing

### Top-level theorem:
* `GeneralKasami` — The full P₃ statement for general Kasami exponents
-/
import RequestProject.TraceChar
import RequestProject.WalshHadamard
import RequestProject.SpectralIdentity
import RequestProject.APNTheory
import RequestProject.LinearizedPoly
import RequestProject.QuadraticGF2
import RequestProject.KasamiWalshSpectrum
import RequestProject.GeneralKasami
