/-
  Theorem3/Normalization.lean

  Normalization Lemma for the Budaghyan derivative of a Gold-type APN function.

  Given f(x) = x^(2^k+1) over 𝔽_{2^n}, the derivative
    Δ_u f(x) = f(x + u) + f(x) = x^(2^k) · u + x · u^(2^k) + u^(2^k+1)
  is equivalent (for u ≠ 0) to Lnorm(y) = y^(2^k) + y + 1 = 0 via y = x/u.

  NOTE: This analyzes the **Gold** function (exponent 2^k + 1), not the Kasami
  function (exponent 4^k − 2^k + 1). See ANALYSIS.md for the distinction.
-/
import Mathlib

noncomputable section

open Finset Classical

variable {n : ℕ}
variable (k : ℕ) (hk : 0 < k)
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The Gold exponent: `d = 2^k + 1`. -/
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1

/-- Gold function `f(x) = x ^ (2^k + 1)`. -/
def goldFun (x : F) : F := x ^ goldExp k

/-- Budaghyan derivative `Δ_u f(x) = f(x + u) + f(x)`. -/
def deltaGold (u x : F) : F :=
  goldFun k F (x + u) + goldFun k F x

/-- The linearized part: `L_u(x) = x^(2^k) · u + x · u^(2^k)`. -/
def linPart (u x : F) : F :=
  x ^ (2 ^ k) * u + x * u ^ (2 ^ k)

omit [Fintype F] [DecidableEq F] in
/-- Key identity in characteristic 2:
  `Δ_u f(x) = x^(2^k) · u + x · u^(2^k) + u^(2^k+1)`. -/
lemma delta_eq_lin_plus_const (u x : F) :
    deltaGold k F u x = linPart k F u x + u ^ goldExp k := by
  unfold deltaGold linPart goldExp goldFun
  unfold goldExp
  ring_nf
  erw [add_pow_char_pow]
  grind

/-- Normalized linearized operator: `Lnorm(y) = y^(2^k) + y + 1`. -/
def Lnorm (y : F) : F :=
  y ^ (2 ^ k) + y + 1

omit [Fintype F] [DecidableEq F] in
/-- **Normalization Lemma.** For `u ≠ 0`, `Δ_u f(x) = 0 ↔ Lnorm(x/u) = 0`. -/
lemma kernel_iso_normalized (u : F) (hu : u ≠ 0) (x : F) :
    deltaGold k F u x = 0 ↔ Lnorm k F (x * u⁻¹) = 0 := by
  set y := x * u⁻¹ with hy_def
  have hu_pow : u ^ goldExp k ≠ 0 := pow_ne_zero _ hu
  constructor
  · intro hΔ
    rw [delta_eq_lin_plus_const] at hΔ
    have hx : x = y * u := by
      rw [hy_def, mul_assoc, inv_mul_cancel₀ hu, mul_one]
    rw [hx] at hΔ
    simp_all +decide [mul_comm]
    unfold linPart Lnorm goldExp at *
    exact mul_left_cancel₀ (pow_ne_zero (2 ^ k + 1) hu) (by linear_combination' hΔ)
  · intro hL
    rw [delta_eq_lin_plus_const]
    unfold Lnorm linPart goldExp at *
    convert congr_arg (· * u ^ (2 ^ k + 1)) hL using 1
    · ring_nf; simp +zetaDelta at *; field_simp [hu_pow]; ring_nf; simp +decide [hu_pow]
    · simp

omit [Fintype F] [DecidableEq F] in
/-- The kernel of `Δ_u f` is the image under `· * u` of the roots of `Lnorm`. -/
lemma kernel_deltaGold_eq_image (u : F) (hu : u ≠ 0) :
    {x : F | deltaGold k F u x = 0} =
      (fun y => y * u) '' {y : F | Lnorm k F y = 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨x * u⁻¹, ?_, ?_⟩
    · rwa [← kernel_iso_normalized k F u hu]
    · field_simp
  · rintro ⟨y, hy, rfl⟩
    rwa [kernel_iso_normalized k F u hu, mul_assoc, mul_inv_cancel₀ hu, mul_one]

omit [CharP F 2] in
/-- The number of roots of `Lnorm` in `F` is at most `2^k`. -/
lemma card_roots_Lnorm_le :
    (univ.filter fun y : F => Lnorm k F y = 0).card ≤ 2 ^ k := by
  set p : Polynomial F := Polynomial.X ^ (2 ^ k) + Polynomial.X + 1
  have h_deg : p.roots.toFinset.card ≤ 2 ^ k := by
    refine le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' _) ?_)
    rw [Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero]
    norm_num +zetaDelta at *
    intro m hm
    rw [Polynomial.coeff_X, Polynomial.coeff_one]
    split_ifs <;> simp_all +decide
    · norm_cast at hm; aesop
    · norm_cast at hm
  convert h_deg using 2
  ext y
  simp [p, Lnorm]
  exact fun _ => ne_of_apply_ne (Polynomial.eval 0) (by simp +decide)

end