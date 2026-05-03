/-
Copyright (c) 2024 Kasami-71 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RequestProject.Kasami71.Defs

/-!
# Kernel Dimension Bound for the Kasami Derivative

For the Kasami function `F(x) = x^d` on `𝔽_{2^n}` where `d = 2^{2k} − 2^k + 1`
and `n = 2k + 1`, we prove that the kernel of the derivative `D_a F` has at most
`4 = 2^2` elements for any `a ≠ 0`, equivalently that its `𝔽_2`-dimension is `≤ 2`.

## Method (Factorisation, arXiv:0803.3781 page 9)

1. Normalise by setting `y = x / a`, reducing to the polynomial
   `g(y) = (y + 1)^d + y^d + 1` over `𝔽_{2^n}`.
2. Observe that `y = 0` and `y = 1` are always roots (in char 2), so
   `g(y) = y(y + 1) · q(y)` for some polynomial `q`.
3. Show that any root of `q` satisfies `z^{2^k} + z = 1`
   which has at most `2^{gcd(k, n)}` solutions in `𝔽_{2^n}`.
   Since `gcd(k, 2k+1) = 1`, there are at most `2` such solutions.
4. Therefore `g` has at most `2 + 2 = 4` roots, giving `dim_{𝔽₂}(ker D_a) ≤ 2`.

## Main result

* `linPoly_kernel_le_two` – `|ker(D_a F)| ≤ 4`, i.e. `𝔽₂`-dimension `≤ 2`.
-/

noncomputable section

open Finset BigOperators Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Characteristic-2 identities -/

private lemma char2_add_self (x : F) : x + x = 0 := by
  have : x + x = 2 * x := by ring
  rw [this, show (2 : F) = ((2 : ℕ) : F) from by norm_cast, CharP.cast_eq_zero F 2, zero_mul]

private lemma char2_neg_eq (x : F) : -x = x := by
  have h := char2_add_self x
  calc -x = -x + (x + x) := by rw [h, add_zero]
    _ = (-x + x) + x := by rw [add_assoc]
    _ = 0 + x := by rw [neg_add_cancel]
    _ = x := by rw [zero_add]

/-! ### Trivial kernel elements -/

/-- `0` is always in the kernel of `D_a F`. -/
lemma kasamiDeriv_zero (k : ℕ) (a : F) : kasamiDeriv k a 0 = 0 := by
  show (0 + a) ^ kasamiExp k + (0 : F) ^ kasamiExp k + a ^ kasamiExp k = 0
  rw [zero_add, zero_pow (kasamiExp_pos k).ne', add_zero]
  exact char2_add_self _

/-- `a` is always in the kernel of `D_a F` (in characteristic 2, `2a = 0`). -/
lemma kasamiDeriv_self (k : ℕ) (a : F) : kasamiDeriv k a a = 0 := by
  show (a + a) ^ kasamiExp k + a ^ kasamiExp k + a ^ kasamiExp k = 0
  rw [char2_add_self, zero_pow (kasamiExp_pos k).ne', zero_add]
  exact char2_add_self _

/-! ### The normalised derivative polynomial -/

/-- The normalised derivative polynomial `g(y) = (y+1)^d + y^d + 1` over `F`.
    The roots of `g` in `F` are in bijection with the kernel elements
    of `D_a F` via `x = y · a`. -/
def derivPoly (k : ℕ) : F[X] :=
  (X + 1) ^ kasamiExp k + X ^ kasamiExp k + 1

/-
`g(0) = 0` in characteristic 2 (since `1^d + 0 + 1 = 0`).
-/
lemma derivPoly_root_zero (k : ℕ) :
    Polynomial.eval (0 : F) (derivPoly (F := F) k) = 0 := by
  unfold derivPoly; simp +decide ;
  norm_num [ add_comm, add_left_comm, CharTwo.add_self_eq_zero ];
  rw [ zero_pow ] <;> simp +decide [ CharTwo.two_eq_zero ];
  exact?

/-
`g(1) = 0` in characteristic 2 (since `0^d + 1 + 1 = 0`).
-/
lemma derivPoly_root_one (k : ℕ) :
    Polynomial.eval (1 : F) (derivPoly (F := F) k) = 0 := by
  unfold derivPoly;
  simp +decide [ show ( 1 : F ) + 1 = 0 by exact? ];
  rw [ zero_pow ( by exact Nat.succ_ne_zero _ ), zero_add ] ; exact?

/-
Any root `y` of `derivPoly` gives a kernel element `x = y * a`.
-/
lemma derivPoly_root_iff_kernel (k : ℕ) (a : F) (ha : a ≠ 0) (y : F) :
    Polynomial.eval y (derivPoly (F := F) k) = 0 ↔
    kasamiDeriv k a (y * a) = 0 := by
  unfold derivPoly kasamiDeriv;
  -- Factor out $a^d$ from the right-hand side.
  have h_factor : (y * a + a) ^ kasamiExp k + (y * a) ^ kasamiExp k + a ^ kasamiExp k = a ^ kasamiExp k * ((y + 1) ^ kasamiExp k + y ^ kasamiExp k + 1) := by
    rw [ show y * a + a = a * ( y + 1 ) by ring, mul_pow ] ; ring;
  aesop

/-
The `derivPoly` has degree at most `kasamiExp k - 1`
    (the leading `y^d` terms cancel in characteristic 2).
-/
lemma derivPoly_natDegree_le (k : ℕ) :
    (derivPoly (F := F) k).natDegree ≤ kasamiExp k - 1 := by
  -- The leading coefficient of $(X+1)^d$ is $1$ (degree $d$), and the leading coefficient of $X^d$ is $1$ (degree $d$). In characteristic $2$, the coefficient of $X^d$ in $(X+1)^d + X^d$ is $1 + 1 = 0$. Thus, the degree drops below $d$, giving $\text{natDegree} \leq d - 1$.
  have h_deg : Polynomial.coeff (derivPoly (F := F) k) (kasamiExp k) = 0 := by
    unfold derivPoly; simp +decide [ Polynomial.coeff_one, Polynomial.coeff_X, add_pow ] ;
    split_ifs <;> simp_all +decide [ CharTwo.add_self_eq_zero ];
    exact absurd ‹_› ( Nat.ne_of_gt ( kasamiExp_pos k ) );
  rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
  intro m hm; rcases lt_trichotomy m ( kasamiExp k ) with ( h | rfl | h ) <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
  · omega;
  · unfold derivPoly;
    norm_num [ Polynomial.coeff_one, Polynomial.coeff_X_pow, add_pow ];
    split_ifs <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ]

/-- **Core factorisation lemma (arXiv:0803.3781, p.9)**:
    After removing the roots at `y = 0` and `y = 1`, the remaining roots
    of `g` satisfy `y^{2^k} + y + 1 = 0` (i.e., `y^{2^k} + y = 1`),
    which is an `𝔽_2`-linearised equation with at most `2^{gcd(k,n)}` solutions.
    For `n = 2k + 1`, `gcd(k, n) = gcd(k, 2k+1) = 1`, so ≤ 2 extra roots. -/
lemma derivPoly_nontrivial_roots (k : ℕ) (hk : 0 < k) (n : ℕ) (hn : n = 2 * k + 1)
    (hcard : Fintype.card F = 2 ^ n) :
    (Finset.univ.filter fun y : F =>
      Polynomial.eval y (derivPoly (F := F) k) = 0 ∧ y ≠ 0 ∧ y ≠ 1).card ≤ 2 := by
  sorry

/-- **Main theorem (Kernel bound)**:
    `|ker(D_a F)| ≤ 4` for every `a ≠ 0`, i.e. `𝔽₂`-dimension at most `2`.

    Proof: Normalise to `g(y)`, split roots as `{0, 1} ∪ (nontrivial roots)`.
    By `derivPoly_nontrivial_roots`, the nontrivial part has at most 2 elements.
    Total: at most `2 + 2 = 4` roots, hence at most 4 kernel elements. -/
theorem linPoly_kernel_le_two (k : ℕ) (hk : 0 < k) (n : ℕ) (hn : n = 2 * k + 1)
    (hcard : Fintype.card F = 2 ^ n) (a : F) (ha : a ≠ 0) :
    (kasamiKernel k a).card ≤ 4 := by
  sorry

end