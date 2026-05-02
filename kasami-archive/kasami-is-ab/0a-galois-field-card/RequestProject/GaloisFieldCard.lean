import Mathlib

/-!
# Galois Field Cardinality

This file formalizes the fact that |GF(2^n)| = 2^n, i.e., the Galois field
with 2^n elements has cardinality exactly 2^n.

## Reference

Item 0a (`galoisField_card`) from the Kasami proof architecture.
-/

/-- The cardinality of GF(2^n) is 2^n, for any positive n. -/
theorem galoisField_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (GaloisField 2 n) = 2 ^ n :=
  GaloisField.card 2 n hn
