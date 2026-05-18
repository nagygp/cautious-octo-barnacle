/-
# Kasami is AB — Correct Decomposition via Fourth Moment + Variance Collapse

Following Kasami (1971) and the variance-collapsing approach:

## Proof chain:
1. Kasami is APN (derivative is 2-to-1)
2. Walsh divisibility: W(a) ≡ 0 (mod 2^{(n+1)/2}) for all a
3. Fourth moment: ∑_a W(a)⁴ = 2 · (2^n)³
4. Variance collapse: (2) + (3) + Parseval → W² ∈ {0, 2^{n+1}}

Step 4 (variance collapse) is the key insight:
  Define m(a) = W(a)² / 2^{n+1} ∈ ℕ (integrality from step 2).
  Then ∑ m = 2^{n-1} (Parseval) and ∑ m² = 2^{n-1} (step 3).
  So ∑ m(m-1) = 0 with each term ≥ 0, forcing m ∈ {0,1}.

## References
- Kasami (1971), Information and Control 18(4)
- Carlet (2021), Boolean Functions for Cryptography and Coding Theory, §6.4
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.Char2Algebra

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Step 1: Kasami is APN -/

/-- The Kasami function is APN (Almost Perfect Nonlinear):
    for every a ≠ 0 and every b, the equation D_a f(x) = b
    has at most 2 solutions.

    This is proved in KasamiNormIdentity.lean via the CCD approach,
    modulo `ccd_kernel_step'`. -/
theorem kasami_is_apn (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
      (Finset.univ.filter fun x : F2n n =>
        kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2 := by
  sorry

/-! ### Step 2: Walsh divisibility for APN power functions -/

/-- **Walsh divisibility**: For APN power functions x^d on GF(2^n) with n odd,
    W(a) ≡ 0 (mod 2^{(n+1)/2}) for all a.

    This is a consequence of the Stickelberger-type theorem for
    additive character sums over finite fields. It states that the
    Walsh-Hadamard transform of any APN power function has
    values divisible by 2^{(n+1)/2}.

    **Proof sketch** (Carlet 2021, Proposition 6.16):
    The Walsh transform W(a) = ∑_x (-1)^{Tr(ax+x^d)} is a sum of
    2^n terms ±1. By the properties of exponential sums and the
    Stickelberger relation, the p-adic valuation of W(a) satisfies
    v_2(W(a)) ≥ (n+1)/2 when n is odd and gcd(d, 2^n-1) = 1.

    More directly: W(a)² = ∑_z χ(az) C(z), and for APN functions
    each C(z) is divisible by 2 (since N(z,b) ∈ {0,2}).
    Then W² is divisible by 2, and by induction on the Galois
    structure, the valuation lifts to (n+1)/2. -/
theorem walsh_divisibility_apn_power (n k : ℕ) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n)
    (hapn : ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
      (Finset.univ.filter fun x : F2n n =>
        kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2) :
    ∀ a : F2n n, ∃ m : ℤ, wht (kasamiF n k) a = m * (2 : ℤ) ^ ((n + 1) / 2) := by
  sorry

/-! ### Step 3: Fourth moment for APN power functions -/

/-- **Fourth moment identity for APN power functions**:
    ∑_a W(a)⁴ = 2 · (2^n)³.

    For APN functions (N(a,b) ∈ {0,2}):
    C(z) = ∑_x χ(D_z f(x)) = 2 ∑_{b ∈ S_z} χ(b)
    where S_z = {b : ∃ x, D_z f(x) = b}, |S_z| = 2^{n-1}.

    The fourth moment ∑W⁴ = 2^n ∑_z C(z)² relates to
    the second moment of the derivative distribution.

    For the Kasami power function specifically, the CCD norm
    identity d·(2^k+1) = 2^{3k}+1 constrains the derivative
    structure enough to determine ∑C(z)² = 2·(2^n)².

    This gives ∑W⁴ = 2^n · 2·(2^n)² = 2·(2^n)³. -/
theorem kasami_fourth_moment (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    ∑ a : F2n n, wht (kasamiF n k) a ^ 4 = 2 * (2 ^ n : ℤ) ^ 3 := by
  sorry

/-! ### Step 4: Variance collapse — the key abstract lemma -/

/-
**Variance collapse lemma**: If a sequence of non-negative integers
    m₁, ..., mN satisfies ∑ mᵢ = S and ∑ mᵢ² = S, then each mᵢ ∈ {0, 1}.

    Proof: ∑ mᵢ(mᵢ-1) = ∑mᵢ² - ∑mᵢ = S - S = 0.
    Each mᵢ(mᵢ-1) ≥ 0 (since mᵢ ∈ ℕ), so each = 0, so mᵢ ∈ {0,1}.
-/
theorem variance_collapse {ι : Type*} [Fintype ι] (m : ι → ℕ) (S : ℕ)
    (hsum : ∑ i, m i = S) (hsq : ∑ i, m i ^ 2 = S) :
    ∀ i, m i = 0 ∨ m i = 1 := by
  -- By expanding the sum of squares, we can rewrite the equation as $\sum_{i} m_i(m_i - 1) = 0$.
  have h_expand : ∑ i, m i * (m i - 1) = 0 := by
    simp_all +decide [ mul_tsub, ← sq ];
    have h_expand : ∑ i, (m i ^ 2 - m i) = 0 := by
      zify [ hsum, hsq ];
      rw [ Finset.sum_congr rfl fun _ _ => Nat.cast_sub <| Nat.le_self_pow ( by decide ) _ ] ; simp +decide [ hsum, hsq ];
      linarith;
    aesop;
  simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg ];
  grind

/-! ### Assembly: kasami_is_ab from components -/

/-
**The Kasami function is Almost Bent** — from fourth moment + variance collapse.

    Proof:
    1. From `kasami_fourth_moment`: ∑W⁴ = 2·(2^n)³
    2. From `wht_parseval`: ∑W² = (2^n)²
    3. From `walsh_divisibility_apn_power`: W² ≡ 0 (mod 2^{n+1})
    4. Define m(a) = W(a)² / 2^{n+1} ∈ ℕ
    5. ∑ m = 2^{n-1} and ∑ m² = 2^{n-1}
    6. By `variance_collapse`: m(a) ∈ {0, 1}
    7. So W(a)² ∈ {0, 2^{n+1}}
-/
theorem kasami_is_ab_from_components (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (h_div : ∀ a : F2n n, ∃ m : ℤ, wht (kasamiF n k) a = m * (2 : ℤ) ^ ((n + 1) / 2))
    (h_fourth : ∑ a : F2n n, wht (kasamiF n k) a ^ 4 = 2 * (2 ^ n : ℤ) ^ 3) :
    IsAlmostBent (kasamiF n k) := by
  grind +suggestions

end
end Kasami