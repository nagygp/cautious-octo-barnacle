/-
# Quadratic Form ↔ Walsh-Hadamard Bridge

This file contains the bridge lemmas connecting the quadratic form theory
(Layer 2–4) to the Walsh-Hadamard spectrum (Layer 5), completing the
proof architecture for `kasami_is_ab`.

## Key bridge lemmas (all sorry'd — these are the hard remaining gaps):

- `kasami_Qa`: Construction of Q_a(x) = Tr(a · x^d) as a QuadFormF2
- `kasami_Ba_simplified`: B_a(x,y) = Tr(y · L_a(x)) via Frobenius
- `radical_eq_kernel_La`: rad(B_a) = ker(L_a)
- `kasami_rank_Ba`: rank(B_a) ∈ {n-1, n}
- `kasami_Qa_vanishes_on_radical`: Q_a vanishes on rad(B_a)
- `walsh_eq_expSum`: W_f(a,b) = ±S(Q_{a,b})
- `walsh_sq_values`: W_f(a,b)² ∈ {0, 2^{n+1}}

## Mathematical context

The proof that the Kasami function is Almost Bent proceeds through:

1. For each a ≠ 0, define Q_a(x) = Tr(a · x^d) : GF(2^n) → GF(2).
   This is a quadratic form over the F_2-vector space GF(2^n).

2. The associated bilinear form B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y)
   simplifies (via Frobenius/trace invariance) to B_a(x,y) = Tr(y · L_a(x)),
   where L_a is a linearized polynomial.

3. The radical rad(B_a) = ker(L_a) has dimension 0 or 1
   (from `linPolyL_ker_card_classification` in LinearizedPoly/Kernel.lean).

4. By `expSum_sq_eq_card_mul_radical_card` (QuadFormGF2/GaussSum.lean),
   S(Q_a)² = 2^n · |rad(Q_a)|, yielding S(Q_a)² ∈ {2^n, 2^{n+1}}.

5. Since W_f(a) relates to S(Q_a), we get W_f(a)² ∈ {0, 2^{n+1}}.

## References
- Canteaut, Charpin, Dobbertin (2000), SIAM J. Discrete Math.
- Carlet, *Boolean Functions for Cryptography and Coding Theory*, §6.4
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.CCDFactorization
import RequestProject.Kasami.CCDHelpers
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel
import RequestProject.LinearizedPoly.KasamiKernel
import RequestProject.QuadFormGF2.Defs
import RequestProject.QuadFormGF2.GaussSum

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ## Layer 2b: Q_a is a quadratic form -/

/-- **Lemma 2b** (Qa_is_quadratic):
    Q_a(x) = Tr(a · x^d) defines a quadratic form over GF(2).

    The key property is that B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y) is GF(2)-bilinear.
    Over GF(2), "quadratic" means: the polar form B is biadditive and B(x,x) = 0.

    For the Kasami exponent d = 2^{2k} - 2^k + 1, the mixed terms in (x+y)^d + x^d + y^d
    are all of degree ≤ d-1, and after applying Tr (which is GF(2)-linear), the result
    B_a(x,y) = Tr(a · ((x+y)^d + x^d + y^d)) is bilinear because each mixed term is
    a product of a power of x and a power of y (both being p-th powers via Frobenius). -/
theorem kasami_Qa_is_quadratic (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (a : F2n n) (ha : a ≠ 0) :
    ∃ Q : QuadFormF2 (F2n n),
      (∀ x : F2n n, Q x = tr2 n (a * x ^ kasamiExp k)) := by
  sorry

/-! ## Layer 2e: B_a simplified via Frobenius -/

/-- **Lemma 2e** (Ba_simplified):
    The bilinear form B_a(x,y) = Tr(a · ((x+y)^d + x^d + y^d)) simplifies to
    B_a(x,y) = Tr(y · L_a(x)), where L_a is the linearized polynomial from
    `LinearizedPoly/Defs.lean`.

    The proof uses:
    1. Expand (x+y)^d + x^d + y^d for d = 2^{2k} - 2^k + 1
       (using `char2_sum_powers` from CCDHelpers.lean)
    2. Apply Tr(z^{2^i}) = Tr(z) repeatedly to absorb Frobenius powers
       (using `tr2_pow2` from Trace.lean)
    3. Factor out y to obtain Tr(y · L_a(x)) -/
theorem kasami_Ba_simplified (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (a : F2n n) (ha : a ≠ 0)
    (Q : QuadFormF2 (F2n n))
    (hQ : ∀ x : F2n n, Q x = tr2 n (a * x ^ kasamiExp k)) :
    ∀ x y : F2n n, Q.polar x y = tr2 n (y * linPolyL k (a * x)) := by
  sorry

/-! ## Layer 3c: Radical = kernel of L_a -/

/-- **Lemma 3c** (radical_eq_kernel_La):
    rad(B_a) = ker(L_a).

    Since B_a(x,y) = Tr(y · L_a(x)) and Tr is surjective (from `tr2_surjective`),
    we have: x ∈ rad(B_a) iff ∀ y, Tr(y · L_a(x)) = 0 iff L_a(x) = 0.

    The surjectivity of Tr is crucial: if L_a(x) ≠ 0, then there exists y
    with Tr(y · L_a(x)) ≠ 0, so x ∉ rad(B_a). -/
theorem kasami_radical_eq_kernel (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (a : F2n n) (ha : a ≠ 0)
    (Q : QuadFormF2 (F2n n))
    (hQ : ∀ x : F2n n, Q x = tr2 n (a * x ^ kasamiExp k))
    (hB : ∀ x y : F2n n, Q.polar x y = tr2 n (y * linPolyL k (a * x))) :
    ∀ x : F2n n, x ∈ Q.radical ↔ linPolyL k (a * x) = 0 := by
  sorry

/-! ## Layer 3e: Rank of B_a -/

/-- **Lemma 3e** (rank_Ba):
    The radical of B_a has cardinality 1 or 2 (i.e., dimension 0 or 1 over GF(2)).

    This combines:
    - `kasami_radical_eq_kernel`: rad(B_a) = ker(L_a(a·-))
    - The map x ↦ a·x is a bijection (since a ≠ 0)
    - `linPolyL_ker_card_classification`: |ker(L_k)| ∈ {1, 4} when gcd(k,n) = 1
      (from LinearizedPoly/Kernel.lean)

    Since rank = n - dim(rad), rank ∈ {n-1, n}. -/
theorem kasami_radical_small (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (a : F2n n) (ha : a ≠ 0)
    (Q : QuadFormF2 (F2n n))
    (hQ : ∀ x : F2n n, Q x = tr2 n (a * x ^ kasamiExp k))
    (hrad : ∀ x : F2n n, x ∈ Q.radical ↔ linPolyL k (a * x) = 0) :
    (Finset.univ.filter (fun x : F2n n => x ∈ Q.radical)).card ∈ ({1, 2} : Set ℕ) := by
  sorry

/-! ## Layer 4c: Q_a vanishes on the radical -/

/-- **Lemma 4c** (Qa_vanishes_on_radical):
    Q_a vanishes on rad(B_a), i.e., Q.radicalRestriction = 0.

    If rad = {0}, this is trivial (Q(0) = 0).
    If rad has dimension 1 with generator x₀, need Q_a(x₀) = 0.

    For the Kasami exponent: if x₀ ∈ ker(L_a) \ {0}, then x₀ satisfies
    a specific algebraic relation (from the kernel analysis) which forces
    Tr(a · x₀^d) = 0.

    More specifically: x₀ ∈ rad means L_a(x₀) = 0, which (after the
    substitution t = x₀^{2^k - 1}) implies t^{2^k+1} + t + 1 = 0.
    Then Q_a(x₀) = Tr(a · x₀^d) = Tr(a · x₀ · x₀^{2^{2k} - 2^k})
    = Tr(a · x₀ · (x₀^{2^k})^{2^k - 1}), and using the kernel relation
    this simplifies to a trace of something in Im(Frobenius - id) = ker(Tr). -/
theorem kasami_Qa_vanishes_on_radical (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (a : F2n n) (ha : a ≠ 0)
    (Q : QuadFormF2 (F2n n))
    (hQ : ∀ x : F2n n, Q x = tr2 n (a * x ^ kasamiExp k)) :
    Q.radicalRestriction = 0 := by
  sorry

/-! ## Layer 5a: Walsh = ExpSum -/

/-- **Lemma 5a** (walsh_eq_expSum):
    The Walsh-Hadamard transform W_f(a) equals (up to sign/shift) the
    exponential sum S(Q_a) of the quadratic form Q_a.

    Specifically, for f(x) = x^d:
    W_f(a) = ∑_x χ(a·x + x^d) = ∑_x (-1)^{Tr(a·x + x^d)}

    When b = 0 (simplified AB definition used here):
    W_f(a) = ∑_x (-1)^{Tr(a·x^d)} = S(Q_a)

    For general b: W_f(a,b) involves Q_{a,b}(x) = Tr(a·x^d + b·x),
    and the shift by b·x doesn't affect the quadratic form structure
    (it just translates the variable by a linear term). -/
theorem kasami_walsh_eq_expSum (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (a : F2n n)
    (Q : QuadFormF2 (F2n n))
    (hQ : ∀ x : F2n n, Q x = tr2 n (a * x ^ kasamiExp k)) :
    wht (kasamiF n k) a = Q.expSum := by
  sorry

/-! ## Layer 5b: Walsh² values -/

/-- **Lemma 5b** (walsh_sq_values):
    W_f(a)² ∈ {0, 2^{n+1}} for all a, when gcd(k,n) = 1 and n is odd.

    Proof sketch:
    1. By `kasami_walsh_eq_expSum`: W_f(a) = S(Q_a)
    2. By `kasami_Qa_vanishes_on_radical`: Q_a|_rad = 0
    3. By `expSum_sq_eq_card_mul_radical_card`: S(Q_a)² = 2^n · |rad(Q_a)|
    4. By `kasami_radical_small`: |rad(Q_a)| ∈ {1, 2}
    5. Therefore W_f(a)² ∈ {2^n, 2^{n+1}}
    6. But W_f(a)² = 2^n only happens when rad = {0} and a = 0
       (since the permutation property forces some values to vanish),
       so for the AB definition (which uses wht²), we get {0, 2^{n+1}}. -/
theorem kasami_walsh_sq_values (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (a : F2n n) :
    wht (kasamiF n k) a ^ 2 = 0 ∨ wht (kasamiF n k) a ^ 2 = (2 ^ (n + 1) : ℤ) := by
  sorry

/-! ## Layer 5c: kasami_is_ab from walsh_sq_values -/

/-- **The main theorem** assembled from the bridge lemmas.
    `kasami_is_ab` follows directly from `kasami_walsh_sq_values`. -/
theorem kasami_is_ab_from_bridge (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    IsAlmostBent (kasamiF n k) := by
  intro a
  exact kasami_walsh_sq_values n k hk hn hn_odd hgcd a

end
end Kasami
