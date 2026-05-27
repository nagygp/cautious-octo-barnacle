import Mathlib
import RequestProject.Thm32
import RequestProject.Thm32Kprime
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg

/-!
# Skeleton: LxXk'_bijective_v2 and adjoint_swap_bijective — Sub-lemma DAG

Decomposes the two remaining sorries in Thm32Kprime.lean:
1. `adjoint_swap_bijective` (line 153)
2. `LxXk'_bijective_v2` (line 210)

And the sorry in Thm32.lean:
3. `LxXk'_bijective` (line 700)

## Strategy

### adjoint_swap_bijective
This is a specialization of adjoint_swap_bij (AdjointBij.lean) to the
truncTrace setting. Since truncTrace n = frobSum 2 n, this is a wrapper.

### LxXk'_bijective_v2
This chains:
1. LxXk_bijective (already proved): L(X)·X^k is bijective.
2. LadjXe_bijective (already proved): L*(X)·X^{k·2^{n-m+1}} is bijective.
3. adjoint_swap_bijective: transfer to L(X)·X^l where l is the modular inverse.
4. exp_k'_eq_on_units (already proved): l ≡ k'·2^{n-m+1} on units.
5. Conclude L(X)·X^{k'} is bijective.

### LxXk'_bijective
Direct wrapper of LxXk'_bijective_v2.

## DAG

```
  TK.1 (truncTrace = frobSum 2)         [easy]
    │
    ├──► TK.2 (nondegeneracy wrapper)    [meh]
    │
    ├──► TK.3 (adjoint identity wrapper) [meh]
    │
    └──► TK.4 (adjoint_swap_bijective)   [meh]  (assuming adjoint_swap_bij proved)
           │
           ├──► TK.5 (exponent chain)     [meh]
           │
           └──► TK.6 (LxXk'_bijective_v2) [hard]
                  │
                  └──► TK.7 (LxXk'_bijective) [easy]
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {n : ℕ} (hn : Fintype.card F = 2 ^ n)

-- ═══════════════════════════════════════════
-- TK.1 [easy]: truncTrace n = frobSum 2 n
-- ═══════════════════════════════════════════

/-- The truncated trace (sum of x^{2^i}) equals frobSum with p = 2. -/
lemma truncTrace_eq_frobSum_2 (m : ℕ) (x : F) :
    truncTrace m x = frobSum 2 m x := by sorry
-- Difficulty: easy
-- Proof: Both are defined as ∑_{i<m} x^{2^i}. Unfold and match.

-- ═══════════════════════════════════════════
-- TK.2 [meh]: Trace nondegeneracy wrapper
-- ═══════════════════════════════════════════

/-- Nondegeneracy of the full trace truncTrace n = Tr on GF(2^n). -/
lemma truncTrace_nondegenerate (hn1 : 1 ≤ n)
    {x : F} (hx : x ≠ 0) :
    ∃ y : F, truncTrace n (x * y) ≠ 0 := by sorry
-- Difficulty: meh
-- Proof: Rewrite truncTrace as frobSum 2 n, then apply trace_nondegenerate.

-- ═══════════════════════════════════════════
-- TK.3 [meh]: Adjoint identity wrapper
-- ═══════════════════════════════════════════

/-- The adjoint property in truncTrace form:
    Tr(L(w)·z) = Tr(w·L*(z)) where L = frobSum m and L* is the Ico sum. -/
lemma truncTrace_adjoint_prop (m : ℕ) (hm : m ≤ n) (w z : F) :
    truncTrace n (truncTrace m w * z) =
    truncTrace n (w * (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (2 ^ i))) := by sorry
-- Difficulty: meh
-- Proof: Rewrite as frobSum, apply frobSum_adjoint_Ico.
-- Note: this is already proved as truncTrace_adj_trace_prop in Thm32Kprime.lean!

-- ═══════════════════════════════════════════
-- TK.4 [meh]: adjoint_swap_bijective from adjoint_swap_bij
-- ═══════════════════════════════════════════

-- Transfer bijectivity from L₁(x)·x^e to L₂(x)·x^l when they are
-- trace-adjoints and e·l ≡ 1 mod (2^n - 1).
-- This wraps adjoint_swap_bij (AdjointBij.lean) in the truncTrace formulation.
--
-- NOTE: This requires adjoint_swap_bij to be proved first.
-- The proof would:
-- 1. Rewrite truncTrace n as frobSum 2 n everywhere.
-- 2. Apply adjoint_swap_bij with p = 2.
-- 3. Match all hypotheses.

-- ═══════════════════════════════════════════
-- TK.5 [meh]: Exponent chain
-- ═══════════════════════════════════════════

/-- The exponent e = k · 2^{n-m+1} satisfies e·l ≡ 1 mod (2^n - 1)
    where l is derived from the modular inverse of k'. -/
lemma exponent_chain_mod
    (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (k' : ℕ)
    (hk' : (2^(n-1) - 2^(m-1) - 1) * k' % (2^n-1) = 2^(m-1) % (2^n-1)) :
    let k := 2 ^ (n - 1) - 2 ^ (m - 1) - 1
    let e := k * 2 ^ (n - m + 1)
    ∃ l, e * l % (2^n - 1) = 1 % (2^n - 1) := by sorry
-- Difficulty: meh
-- Proof: From hk', k·k' ≡ 2^{m-1} mod (2^n-1).
-- So k·(k'·2^{n-m+1}) ≡ 2^{m-1}·2^{n-m+1} = 2^n ≡ 1 mod (2^n-1).
-- Use exp_mod_chain and exists_pow_inverse'.

-- ═══════════════════════════════════════════
-- TK.6a [meh]: L₁ additivity (the Ico sum is additive)
-- ═══════════════════════════════════════════

/-- The adjoint sum ∑_{j ∈ Ico(n-m+1, n+1)} x^{2^j} is additive. -/
lemma Ladj_is_additive (m : ℕ) (hm : m ≤ n) (a b : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), (a + b) ^ (2 ^ i)) =
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), a ^ (2 ^ i)) +
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), b ^ (2 ^ i)) := by sorry
-- Difficulty: meh
-- Proof: Each (a+b)^{2^i} = a^{2^i} + b^{2^i} in char 2 (Frobenius).
-- Then split the sum.

-- ═══════════════════════════════════════════
-- TK.6b [hard]: Assembly of LxXk'_bijective_v2
-- ═══════════════════════════════════════════

-- Full proof of L(X)·X^{k'} bijective.
--
-- Chain:
-- 1. LxXk_bijective: L(X)·X^k is bijective.
-- 2. LadjXe_bijective: L*(X)·X^{k·2^{n-m+1}} is bijective.
-- 3. adjoint_swap_bijective: L₂(X)·X^l is bijective
--    where L₂ = truncTrace m and l is the modular inverse.
-- 4. exp_k'_eq_on_units: l ≡ k'·2^{n-m+1} on units.
-- 5. Since L₂(x)·x^l = truncTrace(m, x)·x^l and l gives the same
--    values as k' on all elements, we get truncTrace(m, x)·x^{k'} bijective.
--
-- NOTE: Step 3 requires adjoint_swap_bijective, and step 5 requires
-- carefully handling the zero case (both sides are 0 at x = 0).

-- ═══════════════════════════════════════════
-- TK.6c [meh]: Function equality from pointwise unit equality
-- ═══════════════════════════════════════════

/-- If f(x) = g(x) for all x (including x = 0), and f is bijective, then g is bijective. -/
lemma bij_of_eq_funcs {f g : F → F}
    (heq : ∀ x, f x = g x) (hf : Function.Bijective f) :
    Function.Bijective g := by sorry
-- Difficulty: easy
-- Proof: funext from heq, then substitute.

-- ═══════════════════════════════════════════
-- TK.6d [meh]: L(x)·x^l = L(x)·x^{k'} pointwise
-- ═══════════════════════════════════════════

/-- If l ≡ k' · 2^{n-m+1} mod (2^n - 1) and k · l ≡ 1 mod (2^n - 1),
    then for all x ∈ F, truncTrace(m, x) · x^l = truncTrace(m, x) · x^{k'}.

    For x = 0: both sides are 0.
    For x ≠ 0: x^l = x^{k'} follows from the exponent congruence mod |F|-1. -/
lemma LxXl_eq_LxXk'
    (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (k' l : ℕ)
    (hl_mod : ∀ {x : F}, x ≠ 0 → x ^ l = x ^ (k' * 2 ^ (n - m + 1)))
    (x : F) :
    truncTrace m x * x ^ l = truncTrace m x * x ^ (k' * 2 ^ (n - m + 1)) := by sorry
-- Difficulty: meh
-- Proof: Case split on x = 0 (both sides 0) and x ≠ 0 (use hl_mod).
-- Hmm, wait — actually we need x^l = x^{k'}, not x^{k'·2^{n-m+1}}.
-- The exponent identification may need to go through a different route.

-- ═══════════════════════════════════════════
-- TK.7 [easy]: LxXk'_bijective wrapper in Thm32.lean
-- ═══════════════════════════════════════════

-- Import LxXk'_bijective_v2 into the Thm32.lean namespace.
-- This requires adding `import RequestProject.Thm32Kprime` to Thm32.lean.
-- Proof: Direct application of LxXk'_bijective_v2 with matching parameters.

end DempwolffMueller
