/-
  TacticalHelpers.lean — Standalone "Leaf Lemmas" for Kasami P₃

  These lemmas depend only on Mathlib and contain no project-specific imports.
  They provide the atomic arithmetic, algebraic, field-theoretic, and Fourier-analytic
  building blocks needed by the main Kasami P₃ development.
-/
import Mathlib

open scoped BigOperators
open Classical

/-! ## Lemma 1: Arithmetic Leaf — gcd(3k, n) = gcd(3, n) when k and n are coprime -/

/-- If `k` and `n` are coprime, then `gcd(3 * k, n) = gcd(3, n)`.
    The hypothesis `n % 2 = 1` (n is odd) is included for context but is not needed. -/
lemma gcd_3k_n_odd (k n : ℕ) (_hn : n % 2 = 1) (hc : k.Coprime n) :
    (3 * k).gcd n = Nat.gcd 3 n :=
  hc.gcd_mul_right_cancel 3

/-! ## Lemma 2: Algebraic Leaf — Frobenius expansion in characteristic 2

In characteristic 2, the iterated Frobenius `x ↦ x^(2^k)` is a ring homomorphism
(additive + multiplicative). Applying it to `z^(2^(2k)) + z^(2^k) + z` yields
`z^(2^(3k)) + z^(2^(2k)) + z^(2^k)`. -/

/-- In a commutative ring of exponential characteristic 2,
    `(z^(2^(2k)) + z^(2^k) + z)^(2^k) = z^(2^(3k)) + z^(2^(2k)) + z^(2^k)`. -/
lemma frob_arith_expansion {F : Type*} [CommRing F] [ExpChar F 2]
    (z : F) (k : ℕ) :
    (z ^ 2 ^ (2 * k) + z ^ 2 ^ k + z) ^ 2 ^ k =
    z ^ 2 ^ (3 * k) + z ^ 2 ^ (2 * k) + z ^ 2 ^ k := by
  have h_add := (iterateFrobenius F 2 k).map_add
  simp only [iterateFrobenius_def] at h_add
  rw [h_add, h_add]
  congr 1; congr 1
  · rw [← pow_mul, ← pow_add]; congr 1; ring
  · rw [← pow_mul, ← pow_add]; congr 1; ring

/-! ## Lemma 3: Field Theory Leaf — Frobenius fixed-point set cardinality bound

The set `{z ∈ 𝔽_{2^n} | z^(2^m) = z}` is the subfield `𝔽_{2^(gcd m n)}`,
which has `2^(gcd m n)` elements. Any `𝔽₂`-subspace contained in this set
therefore has at most `2^(gcd m n)` elements.

We decompose this into two sub-lemmas:
(a) The set `{z | z^(2^m) = z}` has at most `2^m` elements (degree bound).
(b) In `𝔽_{2^n}`, the roots of `X^(2^m) - X` form a subfield of cardinality `2^(gcd m n)`.
-/

section FrobFixedPoints

variable {F : Type*} [Field F] [Fintype F]

/-- **Sub-lemma 3a**: The set `{z | z^(q) = z}` in a finite field has at most `q` elements.
    These are roots of `X^q - X`, a polynomial of degree `q`. -/
lemma card_frob_fixed_le (q : ℕ) (hq : 1 ≤ q) :
    Finset.card (Finset.filter (fun z : F => z ^ q = z) Finset.univ) ≤ q := by
  sorry

/-- **Sub-lemma 3b** (deep): In `𝔽_{p^n}`, the Frobenius fixed points `{z | z^(p^m) = z}`
    form exactly `𝔽_{p^(gcd m n)}` and thus have cardinality `p^(gcd m n)`.
    This is the core finite field structure theorem. -/
lemma card_frob_fixed_eq_pow_gcd
    (p n : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hcard : Fintype.card F = p ^ n) (m : ℕ) :
    Finset.card (Finset.filter (fun z : F => z ^ (p ^ m) = z) Finset.univ) =
    p ^ (Nat.gcd m n) := by
  sorry

/-- **Lemma 3** (main): If `V` is an `𝔽₂`-subspace of `F` contained in the Frobenius
    fixed-point set `{z | z^(2^m) = z}`, then `|V| ≤ 2^(gcd m n)`.

    Uses sub-lemma 3b: the fixed-point set has exactly `2^(gcd m n)` elements,
    and `V` is a subset of it. -/
lemma card_subspace_le_frob_fixed
    (n m : ℕ) [CharP F 2] [Fact (Nat.Prime 2)] [Algebra (ZMod 2) F]
    (hcard : Fintype.card F = 2 ^ n)
    (V : Submodule (ZMod 2) F)
    [Fintype V]
    (hV : ∀ v : F, v ∈ V → v ^ (2 ^ m) = v) :
    Fintype.card V ≤ 2 ^ (Nat.gcd m n) := by
  sorry

end FrobFixedPoints

/-! ## Lemma 4: Fourier Leaf — Trace adjointness for Frobenius

The identity `Tr(x^(q^k) · y) = Tr(x · y^(q^(n-k)))` (where `n = [F : K]`, `q = |K|`)
follows from Frobenius invariance of the trace: `Tr(a^(q^k)) = Tr(a)`.

We decompose this into:
(a) `Tr(a^(q^k)) = Tr(a)` for the Galois trace.
(b) The main adjointness identity. -/

section TraceIdentity

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F]

/-- **Sub-lemma 4a**: The algebra trace is Frobenius-invariant:
    `Tr_{F/K}(x^(|K|^k)) = Tr_{F/K}(x)` for all `k`.
    This holds because `Tr = Σ_{i=0}^{n-1} Frob^i` and raising to `|K|^k`
    merely cyclically permutes the summands. -/
lemma trace_frobenius_invariant
    (x : F) (k : ℕ) :
    Algebra.trace K F (x ^ (Fintype.card K) ^ k) = Algebra.trace K F x := by
  sorry

/-- **Lemma 4** (main): Trace adjointness for the Frobenius endomorphism.

    `Tr(x^(q^k) · y) = Tr(x · y^(q^(n - k)))`,

    where `q = |K|` and `n = [F : K]`.

    **Proof idea**: Set `a = x · y^(q^(n-k))`. Then
    `a^(q^k) = x^(q^k) · y^(q^n) = x^(q^k) · y` (since `y^(q^n) = y` in `𝔽_{q^n}`).
    By sub-lemma 4a, `Tr(a^(q^k)) = Tr(a)`, giving the result. -/
lemma trace_identity_base
    (x y : F) (k : ℕ) (hk : k ≤ Module.finrank K F) :
    Algebra.trace K F (x ^ (Fintype.card K) ^ k * y) =
    Algebra.trace K F (x * y ^ (Fintype.card K) ^ (Module.finrank K F - k)) := by
  sorry

end TraceIdentity
