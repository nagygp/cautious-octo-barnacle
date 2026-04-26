/-
# Kasami Derivative Kernel Analysis

## Important Note on `kasamiDiff_eq_implies_linearized`

The original statement of `kasamiDiff_eq_implies_linearized` (without field-size
hypotheses) is **false**. Here is a concrete counterexample:

* **Field**: F₄ = GF(2,2) with 4 elements {0, 1, α, α+1} where α²+α+1 = 0
* **Parameter**: k = 2, giving d = kasamiExp 2 = 13
* **Why it fails**: Over F₄, |F₄*| = 3 and 13 ≡ 1 (mod 3), so x^13 = x for
  all x ∈ F₄. This makes D₁(x^d) = (x+1)+x = 1 (constant!).
  Therefore kasamiDiff 2 1 y₁ = kasamiDiff 2 1 y₂ holds for ALL pairs (y₁,y₂).
  Taking y₁ = α, y₂ = 0: z = α ≠ 0, z ≠ 1, and
  L₂(α) = α^16 + α^4 + α = α + α + α = α ≠ 0.
  All three disjuncts fail.

The root cause: when n | k (here n=2, k=2), the exponent d ≡ 1 (mod 2^n-1),
making x^d the identity. The hypothesis `Nat.Coprime k n` excludes this.

The corrected version adds `Fintype.card F = 2^n` and `Nat.Coprime k n`.

## References

* Kasami (1971), *Information and Control* 18(4)
* Canteaut, Charpin, Dobbertin (2000), *SIAM J. Discrete Math.* 13(1)
-/
import Mathlib
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Kasami Exponent -/

def kasamiExp' (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

theorem kasamiExp'_pos (k : ℕ) : 0 < kasamiExp' k := by unfold kasamiExp'; omega

/-- `d * (2^k + 1) = 2^(3*k) + 1`. -/
theorem kasamiExp'_mul_identity (k : ℕ) :
    kasamiExp' k * (2^k + 1) = 2^(3*k) + 1 := by
  unfold kasamiExp'
  have h4 : (4 : ℕ)^k = (2^k)^2 := by
    rw [show (4 : ℕ) = 2^2 from by norm_num, ← pow_mul]; ring_nf
  have h3k : (2 : ℕ)^(3*k) = (2^k)^3 := by rw [← pow_mul]; ring_nf
  have h2k : 2^k ≤ 4^k := Nat.pow_le_pow_left (by norm_num) k
  rw [h4] at h2k ⊢; rw [h3k]; zify [h2k]; ring

/-! ### Derivative definitions -/

def kasamiDiff' (k : ℕ) (a x : F) : F :=
  (x + a) ^ kasamiExp' k + x ^ kasamiExp' k

def kasamiDelta' (k : ℕ) (b : F) : F :=
  b ^ kasamiExp' k + (b + 1) ^ kasamiExp' k + 1

/-! ### Gold function second derivative -/

/-
Second derivative of Gold function: `D_z D_1(x^(2^m+1)) = z^(2^m) + z`.
-/
theorem gold_second_deriv' (x z : F) (m : ℕ) :
    ((x + z + 1) ^ (2^m + 1) + (x + z) ^ (2^m + 1)) +
    ((x + 1) ^ (2^m + 1) + x ^ (2^m + 1)) =
    z ^ (2^m) + z := by
  ring;
  simp_all +decide [ add_pow_char_pow, mul_add, add_assoc ];
  grind

/-! ### Key identity: z^(2^(3k)) + z = M_k(L_k(z)) -/

/-
z^(2^(3k)) + z = L_k(z)^(2^k) + L_k(z).
-/
theorem frob_cube_eq_mk_lk (z : F) (k : ℕ) :
    z ^ (2 ^ (3 * k)) + z = (linPolyL k z) ^ (2^k) + linPolyL k z := by
  unfold linPolyL; ring;
  rw [ add_pow_char_pow, add_pow_char_pow ] ; ring;
  grind

/-! ### Corrected main theorem -/

/-- **Corrected CCD factorization** — requires coprimality hypothesis.
    The original statement (without `hcard` and `hgcd`) is false; see module doc. -/
theorem kasamiDiff_eq_implies_linearized (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n)
    (y₁ y₂ : F) (heq : kasamiDiff' k 1 y₁ = kasamiDiff' k 1 y₂) :
    y₁ = y₂ ∨ y₁ = y₂ + 1 ∨ linPolyL k (y₁ + y₂) = 0 := by
  sorry

/-! ### The 2-to-1 theorem (downstream) -/

/-
**Kasami 2-to-1**: `gcd(k,n) = 1` and `3 ∤ n` ⟹ `δ(b₁) = δ(b₂)` implies b₁ = b₂ or b₁ = b₂+1.
-/
theorem kasamiDelta_two_to_one' (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (b₁ b₂ : F) (heq : kasamiDelta' k b₁ = kasamiDelta' k b₂) :
    b₂ = b₁ ∨ b₂ = b₁ + 1 := by
  have := @kasamiDiff_eq_implies_linearized F _ _ _ _ n hn k hk hcard hgcd b₁ b₂ ?_;
  · have := @linPolyL_ker_trivial_of_three_ndvd F _ _ _ _ n hn k hk hcard hgcd h3;
    simp_all +decide [ Finset.ext_iff, funKer ];
    grind;
  · grind +locals

end