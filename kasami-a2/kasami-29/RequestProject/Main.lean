/-
# Kasami P₃ Formalization — Root Import File

This project formalizes the Kasami P₃ triple-intersection equidistribution
theorem for the Kasami difference set over F_{2^n}.

## Module Structure

### Core Chain (Kasami/)
- `Basic`             — F_{2^n}, characteristic-2 arithmetic
- `Trace`             — Absolute trace Tr : F_{2^n} → F_2
- `AdditiveCharacter`  — χ(x) = (−1)^{Tr(x)}, orthogonality
- `WalshHadamard`     — WHT, Parseval, inversion
- `KasamiExponent`    — d = 4^k − 2^k + 1, coprimality, bijectivity
- `AlmostBent`        — AB definition, fourth moment, AB ⟹ APN
- `KasamiFunction`    — F(b) = b^d, derivatives, kasami_is_ab
- `DifferenceSet`     — Δ = {F(b)+F(b+1)+1}, character sums
- `TripleCount`       — Character-sum representation, AlmostBentVanishing
- `FourthMoment`      — Autocorrelation, Wiener-Khinchin identity
- `APNFromAB`         — Derivative Parseval identity
- `VanishingProof`    — Delta pairing, cardinality, split assembly
- `KasamiP3`          — Main P₃ theorem assembly
- `DualP3`            — Dual P₃ ↔ P₃ equivalence
- `CCDFactorization`  — CCD algebraic identities
- `CCDHelpers`        — Char-2 helper lemmas

### Linearized Polynomials (LinearizedPoly/)
- `Defs`              — Frobenius, linearized functions, L_k, M_k
- `Kernel`            — Kernel dimension theory
- `ArtinSchreier`     — Artin-Schreier map x² + x
- `KasamiKernel`      — Kasami derivative kernel, 2-to-1, APN

### Quadratic Forms (QuadFormGF2/)
- `Defs`              — QuadFormF2, polar form, radical
- `GaussSum`          — Exponential sums, S(Q)² = |V| · |rad|
- `Kasami`            — Connection to Kasami spectrum (outline)
-/

-- Core chain
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.DifferenceSet
import RequestProject.Kasami.TripleCount
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.APNFromAB
import RequestProject.Kasami.VanishingProof
import RequestProject.Kasami.KasamiP3
import RequestProject.Kasami.DualP3
import RequestProject.Kasami.CCDHelpers
import RequestProject.Kasami.CCDFactorization

-- Linearized polynomials
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel
import RequestProject.LinearizedPoly.ArtinSchreier
import RequestProject.LinearizedPoly.KasamiKernel

-- Quadratic forms over F₂
import RequestProject.QuadFormGF2.Defs
import RequestProject.QuadFormGF2.GaussSum
import RequestProject.QuadFormGF2.Kasami

-- Abstract framework
import RequestProject.Kasami.AbstractTripleCount
