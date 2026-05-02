/-
  Kasami Spectrum Proof - Main Entry Point
  =========================================

  This project formalizes the Walsh-Hadamard spectrum of the Kasami power function
  f(x) = x^d over F_{2^n}, where d = 2^(2k) - 2^k + 1 is the Kasami exponent.

  Main result (kasami_spectrum): Under the conditions
  - n is odd
  - k ≥ 1 and gcd(3k, n) = 1
  - F is a finite field of characteristic 2 with |F| = 2^n

  The Walsh-Hadamard transform WHT(a,b) = ∑_x (-1)^{Tr(a·x^d + b·x)} satisfies:
    WHT(a,b)² ∈ {0, 2^(n+1)}

  i.e., WHT(a,b) ∈ {0, ±2^((n+1)/2)}.

  Project structure:
  - Kasami/Defs.lean: Core definitions (exponent, Frobenius, linearized polynomials, trace)
  - Kasami/Radical.lean: Identification rad(Q_a) = ker(L_a)
  - Kasami/WHT.lean: Walsh-Hadamard transform and the spectrum theorem
-/

import RequestProject.Kasami.Defs
import RequestProject.Kasami.Radical
import RequestProject.Kasami.WHT
