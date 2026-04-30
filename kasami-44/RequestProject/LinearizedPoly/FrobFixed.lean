/-
# Frobenius Fixed Points and M_k Kernel

Ported from kasami-38 (CCDCrossterm.lean). These lemmas characterize
the kernel of M_k(x) = x^{2^k} + x as exactly {0, 1} when gcd(k,n) = 1.

## References
- Dobbertin (1999), "Another proof of Kasami's Theorem"
-/
import Mathlib
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- `M_k(x) = 0` iff `x^{2^k} = x`. -/
theorem linPolyM_zero_iff (k : ℕ) (x : F) : linPolyM k x = 0 ↔ x ^ (2 ^ k) = x := by
  simp only [linPolyM]; rw [← CharTwo.sub_eq_add]; exact sub_eq_zero

/-- Frobenius fixed points: `x^{2^k} = x` and `gcd(k,n) = 1` implies `x ∈ {0, 1}`.
    The set `{x : x^{2^k} = x}` is the subfield `GF(2^{gcd(k,n)})`.
    When `gcd(k,n) = 1`, this is `GF(2) = {0, 1}`. -/
theorem frob_fixed_in_GF2 (n k : ℕ) (hn : 0 < n) (hk_pos : 0 < k)
    (hcard : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (x : F) (hx : x ^ (2 ^ k) = x) :
    x = 0 ∨ x = 1 := by
  have hfixed : x ∈ funKer (linPolyM (F := F) k) := by
    simp [funKer, linPolyM, hx, CharTwo.add_self_eq_zero]
  have hker : funKer (linPolyM (F := F) k) = {0, 1} :=
    linPolyM_ker_eq_coprime n hn hcard k hk hk_pos
  rw [hker] at hfixed
  simp at hfixed
  exact hfixed

/-- Kernel of `M_k`: `M_k(x) = 0` implies `x ∈ {0, 1}` when `gcd(k,n) = 1`. -/
theorem mk_ker_eq_F2 (n k : ℕ) (hn : 0 < n) (hk_pos : 0 < k)
    (hcard : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (x : F) (hx : linPolyM k x = 0) :
    x = 0 ∨ x = 1 :=
  frob_fixed_in_GF2 n k hn hk_pos hcard hk x ((linPolyM_zero_iff k x).mp hx)

/-- If `M_k(L_k(z)) = 0` and `gcd(k,n) = 1`, then `L_k(z) ∈ {0, 1}`. -/
theorem mk_lk_zero_implies_lk_01 (n k : ℕ) (hn : 0 < n) (hk_pos : 0 < k)
    (hcard : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (z : F) (h : linPolyM k (linPolyL k z) = 0) :
    linPolyL k z = 0 ∨ linPolyL k z = 1 :=
  mk_ker_eq_F2 n k hn hk_pos hcard hk _ h

/-- `L_k(1) = 1` (not zero!). -/
theorem linPolyL_one (k : ℕ) : linPolyL (F := F) k 1 = 1 := by
  simp [linPolyL, one_pow]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf; simp [h2]

/-- If `L_k(z) = 1`, then `L_k(z + 1) = 0` (by additivity). -/
theorem lk_eq_one_implies_shifted_zero (k : ℕ) (z : F) (h : linPolyL k z = 1) :
    linPolyL k (z + 1) = 0 := by
  rw [linPolyL_add, h, linPolyL_one, CharTwo.add_self_eq_zero]

end
