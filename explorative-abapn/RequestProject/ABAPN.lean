/-
# AB/APN Function Theory — Foundations

A bottom-up foundation for Almost Bent (AB) and Almost Perfect Nonlinear (APN)
function theory over finite fields, built on simple Mathlib patterns.

## Module structure

* `Defs` — Core definitions (APN, PN, differential uniformity, deltaCount)
* `CharTwo` — Characteristic 2 arithmetic identities
* `Derivative` — Discrete derivative / difference operator
* `Walsh` — Walsh-Hadamard transform
* `Power` — Power functions, Gold/Kasami exponents
* `Morphism` — EA/CCZ equivalence, Frobenius action
* `Perm` — Permutation properties, fiber structure
* `LinearAlgebra` — F₂-linear maps, kernels, linearized polynomials
* `Coding` — Coding theory connections (graph codes)
* `Topology` — Frobenius dynamics, conjugacy, periodic points
* `Polynomial` — Polynomial representation, DO polynomials

## Design philosophy

Each lemma proves one identity or one implication, using whatever simple
Mathlib building blocks are available: `Finset.filter`, `CharP`, `AddChar`,
`frobenius`, `Function.Injective`, `Equiv.Perm`, `Polynomial.eval`,
`AddMonoidHom`, `LinearMap`, `Fintype.card`, etc.
-/

import RequestProject.ABAPN.Defs
import RequestProject.ABAPN.CharTwo
import RequestProject.ABAPN.Derivative
import RequestProject.ABAPN.Walsh
import RequestProject.ABAPN.Power
import RequestProject.ABAPN.Morphism
import RequestProject.ABAPN.Perm
import RequestProject.ABAPN.LinearAlgebra
import RequestProject.ABAPN.Coding
import RequestProject.ABAPN.Topology
import RequestProject.ABAPN.Polynomial
