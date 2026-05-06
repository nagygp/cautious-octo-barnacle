/-
  Kasami/Normalization.lean

  Normalization and root-count bound for the Kasami derivative.

  For the Kasami function f(x) = x^{2^{2k} - 2^k + 1}, the derivative
    Δ_a f(x) = f(x + a) + f(x) = v
  can be transformed (after dividing by a suitable power of a) into a
  polynomial equation of degree 2^{2k} in y = x/a.

  The key result (McGuire et al., Theorem 3) is that the kernel of this
  linearized operator has size at most 4 when gcd(k, n) = 1. Combined
  with the Frobenius structure, this gives at most 2^{2k} roots, which
  bounds the differential uniformity.

  This file provides the root-count bound that feeds into the APN proof.

  Reference: Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN
  Functions", Theorem 3.
-/
import Mathlib
import RequestProject.Kasami.Defs

noncomputable section

open Finset Polynomial Classical

variable (k : ℕ)
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### The linearized operator for the Kasami derivative -/

/-- The linearized operator arising from the Kasami derivative after
    normalization: `L_K(y) = y^{2^{2k}} + y`.
    This is the "double Frobenius minus identity" operator. -/
def LKasami (y : F) : F := y ^ (2 ^ (2 * k)) + y

/-- `LKasami` is additive (𝔽₂-linear). -/
lemma LKasami_add (a b : F) :
    LKasami k F (a + b) = LKasami k F a + LKasami k F b := by
  unfold LKasami
  have : (a + b) ^ (2 ^ (2 * k)) = a ^ (2 ^ (2 * k)) + b ^ (2 ^ (2 * k)) := by
    rw [add_pow_char_pow]
  rw [this]; ring

/-
Root count for the Kasami linearized operator (k ≥ 1):
    The polynomial `X^{2^{2k}} + X` has at most `2^{2k}` roots.
-/
lemma card_roots_LKasami_le (hk : 0 < k) :
    (univ.filter fun y : F => LKasami k F y = 0).card ≤ 2 ^ (2 * k) := by
  -- The polynomial p = X^{2^{2k}} + X is nonzero because its leading coefficient is 1 (for the X^{2^{2k}} term). Use natDegree_add_eq_left_of_natDegree_lt.
  have h_poly_roots : (Finset.filter (fun y => LKasami k F y = 0) (Finset.univ : Finset F)).card ≤ (Polynomial.roots (Polynomial.X ^ (2 ^ (2 * k)) + Polynomial.X : Polynomial F)).toFinset.card := by
    refine' Finset.card_le_card _;
    intro y hy; simp_all +decide [ LKasami ] ;
    exact ne_of_apply_ne Polynomial.natDegree ( by erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num ; linarith [ pow_pos ( zero_lt_two' ℕ ) ( 2 * k ) ] );
  refine' le_trans h_poly_roots ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
  rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num;
  linarith

/-! ### The shifted Kasami operator -/

/-- The shifted Kasami operator:
    `LKnorm(y) = y^{2^{2k}} + y^{2^k} + 1`.
    This is what appears after normalizing the Kasami derivative equation. -/
def LKnorm (y : F) : F := y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + 1

/-
Root count for the shifted Kasami operator (k ≥ 1):
    `|{y ∈ F : y^{2^{2k}} + y^{2^k} + 1 = 0}| ≤ 2^{2k}`.
-/
lemma card_roots_LKnorm_le (hk : 0 < k) :
    (univ.filter fun y : F => LKnorm k F y = 0).card ≤ 2 ^ (2 * k) := by
  -- The degree of the polynomial $p(y) = y^{2^{2k}} + y^{2^k} + 1$ is $2^{2k}$.
  set p : Polynomial F := Polynomial.X ^ (2 ^ (2 * k)) + Polynomial.X ^ (2 ^ k) + 1
  have h_deg : p.natDegree ≤ 2 ^ (2 * k) := by
    rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num [ hk ];
    · gcongr <;> linarith;
    · gcongr <;> linarith;
  refine' le_trans _ h_deg;
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact p.roots.toFinset;
  · intro y hy; simp_all +decide [ LKnorm ] ;
    exact ⟨ ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide [ p ] ), by simpa [ p ] using hy ⟩;
  · exact le_trans ( Multiset.toFinset_card_le _ ) ( Polynomial.card_roots' _ )

/-! ### The factorization step: reducing to a degree-2 kernel

  McGuire et al. show that after combining appropriate Frobenius twists
  of the linearized equation L_b(u) = 0, the solutions are trapped in the
  kernel of an equation of the form A·u + B·u^{2^k} = 0, which has at most
  2^k roots. Further reduction shows at most 4 roots total.

  This is the technical heart of the Kasami APN proof.
-/

/-- The "reduced" linearized operator from McGuire's Equation (3):
    `R(u) = A · u + B · u^{2^k}` where A, B are field elements depending
    on the parameters.
    When A ≠ 0 and B ≠ 0, this has at most 2^k roots, which gives at most
    4 solutions to the original derivative equation (after accounting for
    the reduction steps). -/
def reducedOp (A B : F) (u : F) : F := A * u + B * u ^ (2 ^ k)

/-- The reduced operator has at most `2^k` roots when `A ≠ 0` and `k ≥ 1`. -/
lemma card_roots_reducedOp_le (hk : 0 < k) (A B : F) (hA : A ≠ 0) :
    (univ.filter fun u : F => reducedOp k F A B u = 0).card ≤ 2 ^ k := by
  sorry

/-! ### The kernel bound for the full Kasami derivative

  The main result: when gcd(k, n) = 1, the Kasami derivative Δ_a f(x) = v
  has at most 2 solutions for any nonzero a.

  Proof strategy (McGuire et al.):
  1. Express L_b(u) = 0 as a system involving Frobenius twists.
  2. Combine to get Equations (1) and (2) of degree 3 in Frobenius variables.
  3. Reduce to Equation (3): A·u + B·u^{2^k} = 0.
  4. Show A, B ≠ 0 using the 7th-power argument (since 7 | 2^{3k} - 1 but
     7 ∤ 2^r - 1 when 3 ∤ r, and gcd(s, 3k) = 1).
  5. Conclude |kernel| ≤ 2^k, then further reduce to ≤ 4 via Equation (4).
  6. Since solutions come in char-2 pairs, ≤ 4 roots means ≤ 2 solution pairs.
-/

/-- **Kasami derivative kernel bound.**
    For `gcd(k, n) = 1` and `a ≠ 0`, the equation
    `f(x + a) + f(x) = v` has at most 2 solutions in `F`.

    This is the APN property for the Kasami function.
    Reference: McGuire et al., Theorem 3 (kernel bound step). -/
lemma kasami_derivative_le_two
    (n : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (a : F) (ha : a ≠ 0) (v : F) :
    (univ.filter fun x : F => kasamiDelta F k a x = v).card ≤ 2 := by
  sorry

end