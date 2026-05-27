/-
# Polynomial Representation

Every function `F → F` on a finite field is a polynomial of degree < |F|.
Power functions, linearized polynomials, and DO (Dembowski-Ostrom) polynomials.

Built on `Polynomial`, `MvPolynomial`, `Polynomial.eval`.
-/
import Mathlib
import RequestProject.ABAPN.Defs

open Finset Function Polynomial ABAPN

namespace ABAPN.Poly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Polynomial representation of finite field functions -/

/-
Every function `F → F` agrees with some polynomial of degree < |F|.
    (This is a consequence of Lagrange interpolation.)
-/
lemma exists_poly_of_fun (f : F → F) :
    ∃ p : Polynomial F, p.natDegree < Fintype.card F ∧
      ∀ x : F, p.eval x = f x := by
  -- By Lagrange interpolation, there exists a unique polynomial $p$ of degree less than $|F|$ that interpolates the function $f$.
  use Finset.sum Finset.univ fun x => Polynomial.C (f x) * Finset.prod (Finset.erase Finset.univ x) (fun y => Polynomial.C (1 / (x - y)) * (Polynomial.X - Polynomial.C y));
  refine' ⟨ lt_of_le_of_lt ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_lt_iff _ |>.2 _ ), _ ⟩;
  · exact Fintype.card_pos_iff.mpr ⟨ 0 ⟩;
  · intro x _; by_cases hx : f x = 0 <;> simp +decide [ hx, Polynomial.natDegree_prod', Finset.prod_eq_zero_iff, sub_eq_zero ] ;
    · exact Fintype.card_pos;
    · refine' lt_of_le_of_lt ( Polynomial.natDegree_mul_le .. ) _ ; simp +decide [ Polynomial.natDegree_prod', hx ];
      refine' lt_of_le_of_lt ( Polynomial.natDegree_prod_le _ _ ) _;
      refine' lt_of_le_of_lt ( Finset.sum_le_sum fun y hy => Polynomial.natDegree_mul_le .. ) _ ; simp +decide [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
      exact Fintype.card_pos_iff.mpr ⟨ x ⟩;
  · intro x; rw [ Polynomial.eval_finset_sum, Finset.sum_eq_single x ] <;> simp +decide [ Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero ] ;
    · rw [ Finset.prod_eq_one fun y hy => by rw [ inv_mul_cancel₀ ] ; exact sub_ne_zero_of_ne <| by aesop ] ; simp +decide;
    · exact fun y hy => Or.inr ⟨ x, Ne.symm hy, Or.inr rfl ⟩

/-! ### Monomial / power polynomials -/

/-- The monomial polynomial `X^d`. -/
noncomputable def monoPolyFn (d : ℕ) : Polynomial F := Polynomial.X ^ d

/-- Evaluating `X^d` gives the power function. -/
@[simp]
lemma monoPolyFn_eval (d : ℕ) (x : F) :
    (monoPolyFn d).eval x = x ^ d := by
  simp [monoPolyFn]

/-! ### Linearized polynomials -/

/-- A linearized polynomial has the form `∑ᵢ aᵢ · X^(2^i)`.
    We represent it by its coefficient sequence. -/
noncomputable def linearizedPoly [CharP F 2] (coeffs : Fin n → F) : Polynomial F :=
  ∑ i : Fin n, Polynomial.C (coeffs i) * Polynomial.X ^ (2 ^ (i : ℕ))

/-
Evaluating a linearized polynomial.
-/
lemma linearizedPoly_eval [CharP F 2] (coeffs : Fin n → F) (x : F) :
    (linearizedPoly coeffs).eval x = ∑ i : Fin n, coeffs i * x ^ (2 ^ (i : ℕ)) := by
  unfold linearizedPoly; simp +decide [ Polynomial.eval_finset_sum ] ;

/-
A linearized polynomial defines an F₂-linear map.
-/
lemma linearizedPoly_additive [CharP F 2] (coeffs : Fin n → F) (x y : F) :
    (linearizedPoly coeffs).eval (x + y) =
      (linearizedPoly coeffs).eval x + (linearizedPoly coeffs).eval y := by
  rw [ linearizedPoly, Polynomial.eval_finset_sum, Polynomial.eval_finset_sum, Polynomial.eval_finset_sum ];
  simp +decide [ ← Finset.sum_add_distrib, CharTwo.add_sq ];
  exact Finset.sum_congr rfl fun _ _ => by rw [ ← mul_add, add_pow_char_pow ] ;

/-! ### DO (Dembowski-Ostrom) polynomials -/

/-- A DO polynomial has the form `∑_{i,j} a_{i,j} · X^(2^i + 2^j)`.
    These are exactly the polynomials whose difference `f(x+a) - f(x) - f(a) + f(0)`
    is linearized (in `x`) for every `a`. -/
def IsDOPolynomial [CharP F 2] (f : F → F) : Prop :=
  ∀ a : F, ∀ x y : F,
    f (x + y + a) - f (x + a) - f (y + a) + f a =
      (f (x + y) - f x - f y + f 0)

/-
Power functions with Gold exponents are DO polynomials.
-/
lemma gold_is_DO [CharP F 2] (k : ℕ) :
    IsDOPolynomial (fun (x : F) => x ^ (2 ^ k + 1)) := by
  intro a x y;
  norm_num [ pow_succ, pow_mul ];
  simp +decide [ add_pow_char_pow, mul_add, add_mul, sub_eq_add_neg, add_assoc ];
  ring

/-! ### Polynomial degree and APN -/

/-
Note: Over GF(2), every function is trivially APN (since |F| = 2 ≤ 2).
   The following require |F| > 2.

A polynomial of degree 1 (affine function) is never APN when |F| > 2
    (its difference map is constant, giving |F| solutions).
-/
lemma not_isAPN_of_degree_one (a b : F) (ha : a ≠ 0) (hcard : 2 < Fintype.card F) :
    ¬ IsAPN (fun x : F => a * x + b) := by
  intro h;
  have := h 1 one_ne_zero ( a * 1 + b - b ) ; simp_all +decide [ deltaCount ] ;
  simp_all +decide [ mul_add, sub_eq_iff_eq_add ];
  linarith

/-
The zero polynomial is not APN when |F| > 2.
-/
lemma not_isAPN_zero (hcard : 2 < Fintype.card F) :
    ¬ IsAPN (fun (_ : F) => (0 : F)) := by
  intro h;
  have := h 1 one_ne_zero 0; simp_all +decide [ deltaCount ] ;
  linarith

end ABAPN.Poly