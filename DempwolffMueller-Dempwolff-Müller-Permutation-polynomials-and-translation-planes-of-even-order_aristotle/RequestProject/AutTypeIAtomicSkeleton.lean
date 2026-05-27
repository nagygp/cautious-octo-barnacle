import Mathlib
import RequestProject.AutGeneral
import RequestProject.Thm32

/-!
# Skeleton: typeI_inverse_GF2_coeffs — Atomic Decomposition (DAG 9)

Decomposes `typeI_inverse_GF2_coeffs` (AutTypeI.lean:77).

## ⚠ FALSE STATEMENT ALERT

The original statement claims `(L⁻¹(x))^2 = L⁻¹(x)` for ALL x.
This says L⁻¹ maps F into GF(2), which is **impossible** when n > 1
since L⁻¹ is bijective on GF(2^n) but GF(2) has only 2 elements.

## Corrected Statement

What the paper likely means: **L⁻¹ commutes with Frobenius**, i.e.,
`L⁻¹(x²) = (L⁻¹(x))²`.

This is true because L (the truncated trace with GF(2) coefficients)
commutes with Frobenius: `L(x²) = L(x)²`. Therefore its inverse
inherits this property.

## DAG Structure (for corrected statement)

```
  TI.1 (L commutes with Frobenius) [easy]
    │
    └──► TI.2 (bijective Frobenius commuter ⟹ inverse commutes) [meh]
           │
           └──► TI.3 (invFun formulation) [easy]
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

-- ═══════════════════════════════════════════════════
-- TI.1 [easy]: Truncated trace commutes with Frobenius
-- ═══════════════════════════════════════════════════

/-- L(x²) = L(x)² for L = truncated trace (sum of Frobenius powers). -/
lemma truncTrace_frob_comm_char2 (m : ℕ) (x : F) :
    truncTrace m (x ^ 2) = (truncTrace m x) ^ 2 := by sorry
-- Proof: truncTrace m x = ∑_{i<m} x^{2^i}.
-- (∑ x^{2^i})² = ∑ (x^{2^i})² = ∑ x^{2^{i+1}} (char 2: sum squares = square sums)
-- truncTrace m (x²) = ∑_{i<m} (x²)^{2^i} = ∑_{i<m} x^{2^{i+1}}
-- These are the same sums (after reindexing i → i+1 and using periodicity/Frobenius cycling).
-- Actually: ∑_{i<m} x^{2^{i+1}} = ∑_{j=1}^{m} x^{2^j} ≠ ∑_{j=0}^{m-1} x^{2^j} in general.
-- So (L(x))² = ∑_{j=1}^{m} x^{2^j} = L(x²) - x^{2^0}·something... hmm.
-- Wait: In char 2, (a+b)² = a² + b².
-- L(x)² = (∑_{i<m} x^{2^i})² = ∑_{i<m} x^{2^{i+1}} (using Frobenius on sum)
-- L(x²) = ∑_{i<m} (x²)^{2^i} = ∑_{i<m} x^{2·2^i} = ∑_{i<m} x^{2^{i+1}}.
-- So L(x)² = L(x²). ✓
-- Already proved as truncTrace_frob_comm in Thm32Kprime.lean!

-- ═══════════════════════════════════════════════════
-- TI.2 [meh]: Bijective Frobenius-commuter ⟹ inverse commutes
-- ═══════════════════════════════════════════════════

/-- If L is bijective and L(x²) = L(x)², then L⁻¹(x²) = (L⁻¹(x))².

    Proof: Let y = L⁻¹(x), so L(y) = x.
    Then L(y²) = L(y)² = x².
    So L⁻¹(x²) = y² = (L⁻¹(x))². -/
lemma inverse_frob_comm (L : F → F)
    (hL_bij : Function.Bijective L)
    (hL_frob : ∀ x, L (x ^ 2) = (L x) ^ 2) :
    ∀ x, Function.invFun L (x ^ 2) = (Function.invFun L x) ^ 2 := by sorry
-- Proof:
-- Let y = invFun L x. By invFun spec (L bij): L y = x.
-- Then L(y²) = L(y)² = x² (by hL_frob).
-- So invFun L (x²) = y² (since L is bijective, invFun L (L(y²)) = y²).
-- i.e., invFun L (x²) = (invFun L x)².
-- Uses Function.Injective.invFun_apply or Function.invFun_eq.

-- ═══════════════════════════════════════════════════
-- TI.3 [easy]: Corrected statement
-- ═══════════════════════════════════════════════════

/-- **Corrected Lemma 4.9(a).** L⁻¹ commutes with Frobenius.

    This is the CORRECT version of `typeI_inverse_GF2_coeffs`.
    The original statement `(L⁻¹(x))² = L⁻¹(x)` is **false**
    (it would force L⁻¹ to map into GF(2), impossible for a bijection on GF(2^n)).

    The correct statement is `L⁻¹(x²) = (L⁻¹(x))²`, which says
    L⁻¹ commutes with the Frobenius automorphism. -/
theorem typeI_inverse_frob_comm
    {n_dim : ℕ} (hn : Fintype.card F = 2 ^ n_dim)
    (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n_dim)
    (hm_odd : Odd m) (hcop : Nat.Coprime m n_dim)
    (hbij : Function.Bijective (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i))) :
    ∀ x : F,
      Function.invFun (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i)) (x ^ 2) =
      (Function.invFun (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i)) x) ^ 2 := by sorry
-- Proof: Apply inverse_frob_comm.
-- L = fun x => ∑ i ∈ range m, x^{2^i}.
-- L(x²) = L(x)²: by truncTrace_frob_comm_char2 (or truncTrace_frob_comm).
-- L is bijective: given as hbij.
-- Conclude by inverse_frob_comm.

-- ═══════════════════════════════════════════════════
-- NOTE on the original sorry
-- ═══════════════════════════════════════════════════

/-
The original sorry in AutTypeI.lean:77 states:
  (Function.invFun L x) ^ 2 = Function.invFun L x
This claims L⁻¹(x) ∈ GF(2) for ALL x, which is FALSE for n_dim > 1.

Options:
1. CORRECT the statement to L⁻¹(x²) = (L⁻¹(x))² (Frobenius commutativity).
2. INTERPRET as "the coefficients of L⁻¹ viewed as a linearized polynomial
   are in GF(2)", which is a different (and true) statement about the
   polynomial representation, not about function values.

Option 2 would be: if L⁻¹(x) = ∑_{i} aᵢ x^{2^i}, then aᵢ² = aᵢ for all i.
This follows from L having GF(2) coefficients (all 1's) and the fact that
inverting a GF(2)-matrix gives a GF(2)-matrix.

The corrected statement (option 1) is what we provide above.
For option 2, see the linearized polynomial coefficient lemma below.
-/

-- ═══════════════════════════════════════════════════
-- BONUS: Option 2 — Inverse polynomial has GF(2) coefficients
-- ═══════════════════════════════════════════════════

-- If L(x) = ∑ aᵢ x^{2^i} with all aᵢ ∈ GF(2) (i.e., aᵢ² = aᵢ),
-- and L is bijective, then L⁻¹(x) = ∑ bⱼ x^{2^j} with all bⱼ ∈ GF(2).
-- This is a statement about coefficients of the linearized polynomial,
-- not about function values. It requires the theory of linearized polynomial
-- composition and Frobenius-matrix inversion.
-- 
-- Decomposition:
-- TI.C1 [meh]: Composition of linearized polys is a linearized poly.
-- TI.C2 [meh]: The GF(2)-linear maps F → F form a ring under composition.
-- TI.C3 [meh]: Inverting a GF(2)-linear bijection gives a GF(2)-linear map.
--              (Since GF(2)-linear maps = additive maps commuting with Frobenius,
--               and the inverse of such a map also commutes with Frobenius.)
-- TI.C4 [easy]: GF(2)-linear ⟹ coefficients in GF(2).
--              (A linearized polynomial L commutes with Frobenius iff all its
--               coefficients are in GF(2), i.e., aᵢ^2 = aᵢ.)

end DempwolffMueller
