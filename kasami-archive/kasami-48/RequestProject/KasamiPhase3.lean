import Mathlib
import RequestProject.KasamiDefs
import RequestProject.KasamiPhase1
import RequestProject.KasamiPhase2

/-!
# Kasami AB — Phase 3: WHT Squared Trichotomy

## Main Results

* `kasami_wht_sq_value` — The Walsh–Hadamard transform squared takes only
  the values {0, 2^n, 2^{n+1}}, which is the Almost Bent property.
-/

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

section Phase3

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-! ### Additive characters and Walsh–Hadamard Transform -/

/-- An additive character of F derived from the trace: χ_b(x) = (-1)^{Tr(bx)}.
    Since Tr(bx) ∈ GF(2) = {0,1}, this gives values in {1, -1}. -/
noncomputable def addChar (b : F) (x : F) : ℂ :=
  if AbsTrace (b * x) = (0 : ZMod 2) then 1 else -1

/-- The Walsh–Hadamard transform of the Kasami function f(x) = x^d at (a, b):
    W_f(a, b) = ∑_{x ∈ F} χ_b(a·x^d + x). -/
noncomputable def wht (k : ℕ) (a b : F) : ℂ :=
  ∑ x : F, addChar b (a * x ^ kasamiExp k + x)

/-- The squared magnitude of the WHT. -/
noncomputable def whtSqMag (k : ℕ) (a b : F) : ℝ :=
  Complex.normSq (wht k a b)

/-! ### WHT and radical connection -/

/-- The dimension of the kernel of L_a (as a GF(2)-vector space). -/
noncomputable def kerDimLA (k : ℕ) (a : F) : ℕ :=
  Set.ncard {y : F | linPolyLA k a y = 0}

/-- **Vanishing case:** If b is nonzero on the radical of Q_a, then W_f(a,b) = 0.

In the sum W_f(a,b) = ∑_x χ_b(a·x^d + x), writing x = x₀ + y where y ranges
over the radical, the inner sum over y cancels unless b vanishes on the radical. -/
lemma wht_vanishing (k : ℕ) (a b : F)
    (hb : ∃ y ∈ radical k a, AbsTrace (b * y) ≠ 0) :
    wht (F := F) k a b = 0 := by
  sorry

/-- **Peak case:** If b vanishes on the radical, then
    |W_f(a,b)|² = |F| · |rad(Q_a)| = 2^n · 2^{dim(ker(L_a))}. -/
lemma wht_peak (k n : ℕ) (a b : F) (hn : n ≠ 0) (hcard : Nat.card F = 2 ^ n)
    (hb : ∀ y ∈ radical k a, AbsTrace (b * y) = 0) :
    whtSqMag (F := F) k a b = (2 : ℝ) ^ n * (kerDimLA k a : ℝ) := by
  sorry

/-- **Phase 3, Main Theorem.** WHT squared trichotomy (Almost Bent property).

For the Kasami function f(x) = x^d with d = 2^{2k} − 2^k + 1:
Under the hypotheses (n odd, gcd(k,n) = 1, gcd(3k,n) = 1):
  |W_f(a,b)|² ∈ {0, 2^n, 2^{n+1}}

This follows from:
1. If b is non-vanishing on the radical: W_f(a,b) = 0.
2. If b vanishes on the radical: |W_f(a,b)|² = 2^n · |ker(L_a)|.
3. Under our hypotheses, |ker(L_a)| ∈ {1, 2}, giving the trichotomy. -/
theorem kasami_wht_sq_value {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (hodd : ¬ 2 ∣ n)
    (a b : F) :
    whtSqMag (F := F) k a b = 0 ∨
    whtSqMag (F := F) k a b = 2 ^ n ∨
    whtSqMag (F := F) k a b = 2 ^ (n + 1) := by
  sorry

end Phase3
