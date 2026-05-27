import Mathlib
import RequestProject.FrobAlg
import RequestProject.TraceNorm
import RequestProject.AutKernel

/-!
# Foundational Layer: Fixed Field Scalar Theory

Theory of elements fixed by Frobenius powers and kernel element analysis.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

-- ═══════════════════════════════════════════
-- FS.1 : Iterated Frobenius stability
-- ═══════════════════════════════════════════

/-- If `c^q = c`, then `c^{q^k} = c` for all `k`. -/
lemma frob_stable_iterate {q : ℕ} {c : F} (hc : c ^ q = c) (k : ℕ) :
    c ^ (q ^ k) = c := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hc]

/-- If `c^q = c`, then `(c·x)^{q^i} = c · x^{q^i}`. -/
lemma mul_pow_frob_fixed {q : ℕ} {c : F} (hc : c ^ q = c) (x : F) (i : ℕ) :
    (c * x) ^ (q ^ i) = c * x ^ (q ^ i) := by
  rw [mul_pow, frob_stable_iterate hc i]

-- ═══════════════════════════════════════════
-- FS.2 : Scalar distribution over frobSum
-- ═══════════════════════════════════════════

/-- `∑_{i<m} (c·x)^{q^i} = c · ∑_{i<m} x^{q^i}` when `c^q = c`. -/
lemma frobSum_fixed_scalar {q : ℕ} (m : ℕ) {c : F} (hc : c ^ q = c) (x : F) :
    ∑ i ∈ Finset.range m, (c * x) ^ (q ^ i) =
    c * ∑ i ∈ Finset.range m, x ^ (q ^ i) := by
  simp_rw [mul_pow_frob_fixed hc, Finset.mul_sum]

/-- frobSum distributes over fixed-field scalars (frobSum form). -/
lemma frobSum_fixed_scalar' (q : ℕ) (m : ℕ) {c : F} (hc : c ^ q = c) (x : F) :
    frobSum q m (c * x) = c * frobSum q m x := by
  simp only [frobSum]; exact frobSum_fixed_scalar m hc x

-- ═══════════════════════════════════════════
-- FS.3 : Vanishing additive polynomial
-- ═══════════════════════════════════════════

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

/-
**A linearized polynomial vanishing on all of F has all zero coefficients,**
    provided `p^n ≤ |F|` (so the polynomial degree < |F|).
-/
lemma additive_poly_vanishing_coeff_zero (n : ℕ) (coeffs : Fin n → F)
    (hdeg : p ^ n ≤ Fintype.card F)
    (hvan : ∀ x : F, additivePolyEval p n coeffs x = 0)
    (j : Fin n) : coeffs j = 0 := by
      -- Consider the polynomial $g(X) = \sum_{i=0}^{n-1} a_i X^{p^i}$.
      let g : Polynomial F := Finset.sum Finset.univ (fun i => Polynomial.C (coeffs i) * Polynomial.X ^ (p ^ (i : ℕ)));
      -- Since $g$ has degree at most $p^{n-1}$ and $F$ has $p^n$ elements, $g$ must be the zero polynomial.
      have hg_zero : g = 0 := by
        refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
        exact Finset.univ;
        · rw [ Finset.card_univ ];
          rw [ sub_zero, Polynomial.degree_lt_iff_coeff_zero ];
          intro m hm; rw [ Polynomial.finset_sum_coeff ] ; simp +decide [ Polynomial.coeff_C_mul_X_pow ] ;
          exact Finset.sum_eq_zero fun i hi => if_neg ( by linarith [ pow_lt_pow_right₀ hp.1.one_lt ( show ( i : ℕ ) < n from Fin.is_lt i ) ] );
        · simp +zetaDelta at *;
          simpa [ Polynomial.eval_finset_sum, additivePolyEval ] using hvan;
      replace hg_zero := congr_arg ( fun q => Polynomial.coeff q ( p ^ ( j : ℕ ) ) ) hg_zero ; simp_all +decide [ Polynomial.coeff_C, Polynomial.coeff_X_pow ] ;
      simp +zetaDelta at *;
      rw [ Finset.sum_eq_single j ] at hg_zero <;> simp_all +decide [ Fin.val_inj ];
      exact fun i hi h => False.elim <| hi <| Fin.ext <| Nat.pow_right_injective hp.1.one_lt h.symm

-- ═══════════════════════════════════════════
-- FS.4 : Kernel element Frobenius-fixed
-- ═══════════════════════════════════════════

/-- Kernel element ⟹ coefficient-wise Frobenius-fixed,
    provided `p^n ≤ |F|`. -/
lemma kernel_elem_frob_fixed_at (n : ℕ) (coeffs : Fin n → F)
    (hdeg : p ^ n ≤ Fintype.card F)
    {c : F} (hker : isKernelElement p n coeffs c)
    (i : Fin n) (hai : coeffs i ≠ 0) :
    c ^ (p ^ (i : ℕ)) = c := by
  have h_diff_van : ∀ x : F,
      additivePolyEval p n (fun j => coeffs j * (c ^ (p ^ (j : ℕ)) - c)) x = 0 := by
    intro x
    have h_diff : additivePolyEval p n (fun j : Fin n => coeffs j * c ^ (p ^ (j : ℕ))) x = additivePolyEval p n coeffs (c * x) := by
      unfold additivePolyEval; simp +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    have := hker x; simp_all +decide [ mul_sub, Finset.sum_sub_distrib, mul_assoc, mul_comm, mul_left_comm, additivePolyEval ] ;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]
  have h_coeff := additive_poly_vanishing_coeff_zero p n _ hdeg h_diff_van i
  rcases mul_eq_zero.mp h_coeff with h | h
  · exact absurd h hai
  · exact eq_of_sub_eq_zero h

-- ═══════════════════════════════════════════
-- FS.5 : Truncated trace kernel ∈ GF(p)
-- ═══════════════════════════════════════════

/-- Kernel of truncated trace forces GF(p) when `m ≥ 2` and `|F| = p^n` with `m ≤ n`. -/
lemma truncTrace_kernel_in_gfp {n : ℕ} (hn : Fintype.card F = p ^ n)
    (m : ℕ) (hm : 1 < m) (hmn : m ≤ n)
    (hcop : Nat.Coprime m n)
    {c : F} (hker : isKernelElement p m (fun _ : Fin m => (1 : F)) c) :
    c ^ p = c := by
  have hdeg : p ^ m ≤ Fintype.card F := by
    rw [hn]; exact Nat.pow_le_pow_right hp.out.pos hmn
  have h1 := kernel_elem_frob_fixed_at p m (fun _ => (1 : F)) hdeg hker ⟨1, hm⟩ one_ne_zero
  simpa using h1

end DempwolffMueller