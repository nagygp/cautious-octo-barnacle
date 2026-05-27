import Mathlib
import RequestProject.Thm32
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg

/-!
# Skeleton: Adjoint Swap Chain — DAGs 2-4

Decomposes the chain:
  `adjoint_swap_bijective` → `LxXk'_bijective_v2` → `LxXk'_bijective`

**Prerequisite:** `adjoint_swap_bij_bare` from `BareLemma31Skeleton.lean`.

Once the bare-function Lemma 3.1 (FL-A) is proved, these three sorries
become thin wrappers / short assembly chains.

## DAG Structure

```
  adjoint_swap_bij_bare (FL-A.16, from BareLemma31Skeleton)
    │
    ├──► TT.1 (truncTrace = frobSum 2) [easy]
    │      │
    │      └──► adjoint_swap_bijective [easy]
    │
    ├──► LK.1 (Ladj additive) [easy]
    │
    ├──► LK.2 (trace nondeg) [easy]
    │
    ├──► LK.3 (exp product mod) [meh]
    │
    └──► LK.4 (adj swap apply) + LK.5 (exp match) [meh]
           │
           └──► LxXk'_bijective_v2 [meh]
                  │
                  └──► LxXk'_bijective [easy]
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {n : ℕ} (hn : Fintype.card F = 2 ^ n)

-- ═══════════════════════════════════════════════════
-- TT.1 [easy]: truncTrace = frobSum 2
-- ═══════════════════════════════════════════════════

/-- The truncated trace is just frobSum with p = 2. -/
lemma truncTrace_eq_frobSum_2 (m : ℕ) (x : F) :
    truncTrace m x = frobSum 2 m x := by sorry
-- Proof: Both are ∑_{i<m} x^{2^i}. Unfold definitions and compare.
-- truncTrace m x = ∑ i ∈ range m, x ^ (2 ^ i)
-- frobSum 2 m x = ∑ i ∈ range m, x ^ (2 ^ i)
-- Definitionally equal (or short simp).

-- ═══════════════════════════════════════════════════
-- DAG 2: adjoint_swap_bijective [easy]
-- ═══════════════════════════════════════════════════

/-- `adjoint_swap_bijective` follows directly from `adjoint_swap_bij_bare`
    after rewriting `truncTrace` as `frobSum 2`. -/
lemma adjoint_swap_bijective_skeleton
    (L₁ L₂ : F → F) (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, truncTrace n (L₁ w * z) = truncTrace n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, truncTrace n (x * y) ≠ 0)
    (e l : ℕ) (hel : e * l % (2 ^ n - 1) = 1 % (2 ^ n - 1))
    (hbij : Function.Bijective (fun x : F => L₁ x * x ^ e)) :
    Function.Bijective (fun x : F => L₂ x * x ^ l) := by sorry
-- Proof: Rewrite truncTrace as frobSum 2 in all hypotheses.
-- Then apply adjoint_swap_bij_bare with p = 2.
-- hn : card F = 2^n gives the p^n form.

-- ═══════════════════════════════════════════════════
-- LK.1 [easy]: L* (Frobenius-shifted trace) is additive
-- ═══════════════════════════════════════════════════

/-- The adjoint L*(x) = ∑_{i ∈ Ico(n-m+1, n+1)} x^{2^i} is additive. -/
lemma Ladj_additive_skeleton (m : ℕ) (hm : m ≤ n) (a b : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), (a + b) ^ (2 ^ i)) =
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), a ^ (2 ^ i)) +
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), b ^ (2 ^ i)) := by sorry
-- Proof: Distribute the sum. Each term (a+b)^{2^i} = a^{2^i} + b^{2^i}
-- in char 2 (add_pow_char_pow). Then split the sum.

-- ═══════════════════════════════════════════════════
-- LK.2 [easy]: Trace nondegeneracy wrapper
-- ═══════════════════════════════════════════════════

/-- Nondegeneracy of truncTrace n (= full trace on GF(2^n)). -/
lemma trace_nondeg_wrapper (hn1 : 1 ≤ n) :
    ∀ x : F, x ≠ 0 → ∃ y, truncTrace n (x * y) ≠ 0 := by sorry
-- Proof: truncTrace n = frobSum 2 n. Apply trace_nondegenerate.

-- ═══════════════════════════════════════════════════
-- LK.3 [meh]: Exponent product mod identity
-- ═══════════════════════════════════════════════════

/-- The exponent product: k · (k' · 2^{n-m+1}) ≡ 1 mod (2^n - 1).
    Combines exp_mod_chain with the definition of k. -/
lemma exp_product_mod_skeleton (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (k k' : ℕ)
    (hk_def : k = 2 ^ (n - 1) - 2 ^ (m - 1) - 1)
    (hkk' : k * k' % (2 ^ n - 1) = 2 ^ (m - 1) % (2 ^ n - 1)) :
    k * (k' * 2 ^ (n - m + 1)) % (2 ^ n - 1) = 1 % (2 ^ n - 1) := by sorry
-- Proof: Apply exp_mod_chain with the right parameters.

-- ═══════════════════════════════════════════════════
-- LK.4 [meh]: Apply adjoint swap with Frobenius-shifted trace
-- ═══════════════════════════════════════════════════

/-- Apply adjoint_swap_bijective to get bijectivity of L₂(x)·x^l
    from the Frobenius-shifted bijectivity LadjXe_bijective. -/
lemma adj_swap_apply_skeleton (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (hn1 : 1 ≤ n) (hm : m ≤ n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    (hbij_adj : Function.Bijective (fun x : F =>
      (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) *
      x ^ ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1))))
    (k' : ℕ)
    (hkk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
             2 ^ (m - 1) % (2 ^ n - 1)) :
    ∃ l, Function.Bijective (fun x : F => truncTrace m x * x ^ l) := by sorry
-- Proof:
-- 1. L₁ = Ladj (Frobenius-shifted trace), L₂ = truncTrace m.
-- 2. hAdj: truncTrace_adj_trace_prop (already proved).
-- 3. e = k·2^{n-m+1}, l from exists_pow_inverse'.
-- 4. e·l ≡ 1 from LK.3.
-- 5. Apply adjoint_swap_bijective.

-- ═══════════════════════════════════════════════════
-- LK.5 [meh]: Exponent matching on units
-- ═══════════════════════════════════════════════════

/-- The exponent l from the adjoint swap equals k' on units.
    Uses exp_k'_eq_on_units to show x^l = x^{k'} for all x ≠ 0. -/
lemma exp_match_skeleton (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (hn1 : 1 ≤ n) (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    (k' l : ℕ)
    (hkk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
             2 ^ (m - 1) % (2 ^ n - 1))
    (hkl : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * l % (2 ^ n - 1) =
            1 % (2 ^ n - 1))
    (hbij_l : Function.Bijective (fun x : F => truncTrace m x * x ^ l)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by sorry
-- Proof: Show the two functions agree on all of F:
-- For x = 0: both sides are 0 (truncTrace m 0 = 0).
-- For x ≠ 0: x^l = x^{k'} on units (exp_k'_eq_on_units).
-- Then truncTrace m x * x^l = truncTrace m x * x^{k'}.
-- So the functions are equal, hence both bijective.

-- ═══════════════════════════════════════════════════
-- DAG 3: LxXk'_bijective_v2 [meh]
-- ═══════════════════════════════════════════════════

/-- Assembly: Chain LxXk_bijective → LadjXe → adj_swap → exp_match.
    This is the full proof that L(X)·X^{k'} is a permutation polynomial. -/
theorem LxXk'_bijective_v2_skeleton
    (m : ℕ) (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    (k' : ℕ) (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
                      2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by sorry
-- Proof:
-- 1. LxXk_bijective hn m ... gives bij of truncTrace m x * x^k.
-- 2. LadjXe_bijective hn m ... gives bij of L*(x) * x^{k·2^{n-m+1}}.
-- 3. adj_swap_apply gives ∃ l, bij of truncTrace m x * x^l.
-- 4. exp_match shows l = k' on units, so truncTrace m x * x^{k'} is bij.

-- ═══════════════════════════════════════════════════
-- DAG 4: LxXk'_bijective [easy]
-- ═══════════════════════════════════════════════════

/-- Direct wrapper: same statement as in Thm32.lean. -/
theorem LxXk'_bijective_skeleton (hn : Fintype.card F = 2 ^ n)
    (m : ℕ) (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    (k' : ℕ) (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
                      2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by sorry
-- Proof: Direct invocation of LxXk'_bijective_v2_skeleton hn ...

end DempwolffMueller
