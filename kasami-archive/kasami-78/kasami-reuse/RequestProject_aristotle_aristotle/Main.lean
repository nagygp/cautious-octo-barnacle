/-
  Main.lean — Project entry point

  This project formalizes components of the spectral analysis of APN/AB functions
  over finite fields of characteristic 2, related to the Kasami power function.

  ## What is proved (sorry-free):
  - Gold function derivative normalization (`Theorem3/Normalization.lean`)
  - Linearized polynomial factorization and root bounds (`Theorem3/Factorization.lean`)
  - AB ⟹ APN, Walsh support size, pair counting (`Theorem23/Counting.lean`)
  - Bridge theorem combining the above (`Kasami_Final_Theorem.lean`)

  ## What is NOT proved:
  - The Kasami triple-count conjecture (`KasamiConjecture.lean` — sorry)
  - That the Kasami function b^(4^k − 2^k + 1) is AB when gcd(k,n) = 1
  - The connection between the abstract spectral framework and concrete functions

  See ANALYSIS.md for a detailed gap analysis.
-/
import Theorem3.Normalization
import Theorem3.Factorization
import Theorem23.Counting
import Kasami_Final_Theorem
