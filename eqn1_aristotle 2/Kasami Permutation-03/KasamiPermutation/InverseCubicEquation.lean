import Mathlib
import KasamiPermutation.InverseRecurrence

/-!
# Theorem 6 (Dobbertin 1999) — the `𝔽_{2ⁿ}` capstone `q⁻¹(1/y) = R(y)`

This file assembles the field-level statement of **Theorem 6**: over `L = 𝔽_{2ⁿ}`
the compositional inverse of the (trace-free) generalized Kasami permutation `q`
is the explicit polynomial `R`, in the form

  `q(x) = 1/y  ⟹  x = R(y)`,   i.e.   `q⁻¹(1/y) = R(y)`.

It sits on top of the concrete cubic-collapse layer in `InverseRecurrence.lean`
(`Aseq/Bseq/Cseq`, the equation-(10) unfolding `Eqn10_unfold`, and the "lucky"
vanishing `Lam1_eq_zero`, `Lam0_eq_zero`).  The field-specific ingredients added
here are:

* the definitions of `q` (`qPoly`) and `R` (`Rpoly`);
* equation (8): the polynomial form of `q(x) = 1/y`;
* the derivation of equation (9), the linearized equation, from (8)
  (`eqn9`), via the telescoping identity `S + S^{2^k} = x^{2^k} + x^{2^{k+1}}`;
* the Frobenius reduction `x^{2^{kk'}} = x²`, which uses `x^{2ⁿ} = x` and
  `kk' ≡ 1 (mod n)` and is exactly what turns the collapsed equation into a
  genuine cubic;
* the substitution of the now-proved equation (10) back into (8), assembling the
  cubic `x³ + Λ₂x² + Λ₁x + Λ₀ = 0` and, with `Λ₁ = Λ₀ = 0`, inverting `a_{k'}`
  to reach `x²(x + Λ₂) = 0` and `Λ₂ = R(y)`.
-/

namespace KasamiPerm.InverseCubic

open scoped BigOperators
open KasamiPerm.InverseRec

section Field

variable {L : Type*} [Field L] [CharP L 2]

/-- **The (trace-free) generalized Kasami permutation** `q`.  For `ε = k'+1 mod 2`
(here written as the field cast `((kk+1 : ℕ) : L)`),
`q(z) = (∑_{i=1}^{k'} z^{2^{ik}} + ε) / z^{2^k+1}`. -/
noncomputable def qPoly (k kk : ℕ) (z : L) : L :=
  ((∑ i ∈ Finset.Ico 1 (kk + 1), z ^ (2 ^ (i * k))) + ((kk + 1 : ℕ) : L)) * (z ^ (2 ^ k + 1))⁻¹

/-- **The explicit inverse polynomial** `R(z) = ∑_{i=1}^{k'} A_i(z) + B_{k'}(z)`. -/
def Rpoly (k kk : ℕ) (z : L) : L :=
  (∑ i ∈ Finset.Ico 1 (kk + 1), Aseq z k i) + Bseq z k kk

/-! ## Frobenius reduction `x^{2^{kk'}} = x²` -/

/-
Iterating `x^{2ⁿ} = x`: `x^{(2ⁿ)^s} = x` for all `s`.
-/
theorem x_pow_iter (n : ℕ) (x : L) (hxn : x ^ (2 ^ n) = x) :
    ∀ s : ℕ, x ^ ((2 ^ n) ^ s) = x := by
  intro s; induction' s with s ih <;> simp_all +decide [ pow_succ, pow_mul ] ;

/-
The Frobenius reduction driving the collapse to a cubic: if `x ∈ 𝔽_{2ⁿ}`
(`x^{2ⁿ} = x`) and `kk' ≡ 1 (mod n)` (here `kk·k = t·n + 1`), then
`x^{2^{kk'}} = x²`.
-/
theorem x_pow_reduce (n t k kk : ℕ) (x : L) (hxn : x ^ (2 ^ n) = x)
    (hkk : kk * k = t * n + 1) : x ^ (2 ^ (kk * k)) = x ^ 2 := by
  rw [ hkk, pow_add, pow_one, pow_mul ];
  rw [ pow_mul' ];
  exact congr_arg ( · ^ 2 ) ( x_pow_iter n x hxn t )

/-! ## The `A_i = z · a_i` normalization -/

/-
`Aseq` is `aseq` scaled by the seed `z`: `A_i(z) = z · a_i(z)`.
-/
theorem Aseq_eq_mul (z : L) (k i : ℕ) : Aseq z k i = z * aseq z k i := by
  induction' i using KasamiPerm.InverseRec.two_step_ind with i ih;
  · simp +decide [ Aseq, aseq ];
  · simp +decide [ Aseq, aseq ];
  · simp +decide [ Aseq, aseq, twoStep ];
    ring;
  · simp_all +decide [ Aseq_rec, aseq_rec ];
    ring

/-! ## Equation (8): the polynomial form of `q(x) = 1/y` -/

/-
**Equation (8).**  If `q(x) = 1/y` with `x ≠ 0`, then
`x^{2^k+1} + y·∑_{i=1}^{k'} x^{2^{ik}} + (k'+1)·y = 0`.
-/
theorem eqn8 (k kk : ℕ) (x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (hq : qPoly k kk x = y⁻¹) :
    x ^ (2 ^ k + 1) + y * (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k)))
      + ((kk + 1 : ℕ) : L) * y = 0 := by
  unfold qPoly at hq;
  grind

/-! ## Equation (9): the linearized equation -/

/-
The Frobenius power of the Kasami sum telescopes to a shifted sum.
-/
theorem Ssum_frob (k kk : ℕ) (x : L) :
    (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k))) ^ (2 ^ k)
      = ∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ ((i + 1) * k)) := by
  induction' ( Finset.Ico 1 ( kk + 1 ) ) using Finset.induction <;> simp_all +decide [ pow_add, pow_mul ];
  rw [ add_pow_char_pow, ‹ ( ∑ i ∈ _, _ ) ^ 2 ^ k = _› ] ; ring

/-
Char-2 telescoping of consecutive terms over `Ico 1 (m+1)`.
-/
theorem sum_pair_telescope (m : ℕ) (hm : 1 ≤ m) (f : ℕ → L) :
    (∑ i ∈ Finset.Ico 1 (m + 1), f i) + (∑ i ∈ Finset.Ico 1 (m + 1), f (i + 1))
      = f 1 + f (m + 1) := by
  induction' hm with m hm ih <;> simp_all +decide [ Finset.sum_Ico_succ_top ];
  grind

/-
The telescoping identity `S + S^{2^k} = x^{2^k} + x^{2^{k+1}}`, using the
Frobenius reduction `x^{2^{kk'}} = x²` on the top term.
-/
theorem Ssum_add_frob (k kk : ℕ) (x : L) (hk : 1 ≤ kk)
    (hred : x ^ (2 ^ (kk * k)) = x ^ 2) :
    (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k)))
      + (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k))) ^ (2 ^ k)
      = x ^ (2 ^ k) + x ^ (2 ^ (k + 1)) := by
  rw [ Ssum_frob, sum_pair_telescope ];
  · simp_all +decide [ add_mul, pow_add, pow_mul' ];
    rw [ ← pow_mul, mul_comm, pow_mul, hred ];
  · exact hk

/-
**Equation (9)** — the linearized equation, in the `Eqn10`-at-`i = 2` form
(`x^{2^{2k}} + a₂ x^{2^k} + b₂ x + c₂ = 0`).  Derived from equation (8) and the
telescoping identity `Ssum_add_frob`.
-/
theorem eqn9 (k kk : ℕ) (x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (e8 : x ^ (2 ^ k + 1) + y * (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k)))
        + ((kk + 1 : ℕ) : L) * y = 0)
    (htel : (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k)))
        + (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k))) ^ (2 ^ k)
        = x ^ (2 ^ k) + x ^ (2 ^ (k + 1))) :
    Eqn10 y k x 2 = 0 := by
  have h_simp : x ^ (2 ^ k) * (x ^ (2 ^ (2 * k)) + y ^ (2 ^ k) * x ^ (2 ^ k) + y ^ (2 ^ k - 1) * x + y ^ (2 ^ k)) = 0 := by
    have h_e8frob : x ^ (2 ^ k * (2 ^ k + 1)) + y ^ (2 ^ k) * (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k))) ^ (2 ^ k) + (kk + 1) * y ^ (2 ^ k) = 0 := by
      convert congr_arg ( · ^ 2 ^ k ) e8 using 1 <;> ring;
      simp +decide [ add_pow_char_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm, pow_add, pow_mul ] ; ring;
      rcases Nat.even_or_odd' kk with ⟨ c, rfl | rfl ⟩ <;> norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ];
      · norm_cast ; simp +decide [ pow_succ', pow_mul, CharTwo.two_eq_zero ];
      · norm_cast ; simp +decide [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, CharTwo.two_eq_zero ];
    convert congr_arg ( fun z => z + y ^ ( 2 ^ k - 1 ) * ( x ^ ( 2 ^ k + 1 ) + y * ∑ i ∈ Finset.Ico 1 ( kk + 1 ), x ^ 2 ^ ( i * k ) + ( kk + 1 ) * y ) + y ^ ( 2 ^ k ) * ( ∑ i ∈ Finset.Ico 1 ( kk + 1 ), x ^ 2 ^ ( i * k ) + ( ∑ i ∈ Finset.Ico 1 ( kk + 1 ), x ^ 2 ^ ( i * k ) ) ^ 2 ^ k - ( x ^ 2 ^ k + x ^ 2 ^ ( k + 1 ) ) ) ) h_e8frob using 1 ; ring;
    · rw [ show ( 2 ^ k : ℕ ) = ( 2 ^ k - 1 ) + 1 by rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ] ; simp +decide [ pow_add, pow_mul ] ; ring;
      grind;
    · aesop;
  simp_all +decide [ Eqn10, aseq_two, Zc ];
  convert h_simp using 1;
  simp +decide [ Bseq_rec, Cseq_rec, vc, Zc ]

/-! ## Substituting equation (10) back into equation (8) -/

/-
Summing the (now-proved) equation (10) over `i = 1,…,k'−1` and reducing the
top term `x^{2^{kk'}} = x²`, the whole Kasami sum collapses to
`y·S = SA·x^{2^k} + y·SB·x + y·SC + y·x²`.
-/
theorem Ssum_via_eqn10 (k kk : ℕ) (x y : L) (hk : 1 ≤ kk)
    (heq10 : ∀ i, Eqn10 y k x i = 0) (hred : x ^ (2 ^ (kk * k)) = x ^ 2) :
    y * (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k)))
      = SA y k kk * x ^ (2 ^ k) + y * SB y k kk * x + y * SC y k kk + y * x ^ 2 := by
  contrapose! hred;
  contrapose! hred; have := heq10 0; simp_all +decide [ Eqn10 ] ;
  simp_all +decide [ ← two_mul, CharTwo.two_eq_zero ];
  have h_sum : ∑ i ∈ Finset.Ico 1 kk, x ^ (2 ^ (i * k)) = ∑ i ∈ Finset.Ico 1 kk, (aseq y k i * x ^ (2 ^ k) + Bseq y k i * x + Cseq y k i) := by
    grind +suggestions;
  simp_all +decide [ Finset.sum_Ico_succ_top, SA, SB, SC ];
  simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, Aseq_eq_mul ] ; ring;
  simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm, mul_assoc]

/-
Equation (10) at the top index `i = k'`, cleared of denominators and with the
Frobenius reduction applied: `A_{k'}·x^{2^k} = y·x² + y·B_{k'}·x + y·C_{k'}`.
-/
theorem eqn10_top (k kk : ℕ) (x y : L) (heq10kk : Eqn10 y k x kk = 0)
    (hred : x ^ (2 ^ (kk * k)) = x ^ 2) :
    Aseq y k kk * x ^ (2 ^ k) = y * x ^ 2 + y * Bseq y k kk * x + y * Cseq y k kk := by
  simp_all +decide [ Eqn10 ];
  grind +suggestions

/-
`R(y)` in the additive form matching the `x²`-coefficient of the cubic.
-/
omit [CharP L 2] in
theorem Rpoly_eq (k kk : ℕ) (y : L) (hk : 1 ≤ kk) :
    Rpoly k kk y = SA y k kk + Aseq y k kk + Bseq y k kk := by
  unfold SA Rpoly; rw [ Finset.sum_Ico_succ_top ] ; aesop;

/-
**The cubic.**  Substituting equation (10) into equation (8) and inverting
`a_{k'}` assembles the cubic `x³ + Λ₂x² + Λ₁x + Λ₀ = 0` with `Λ₂ = R(y)`.
-/
theorem cubic_eqn (k kk : ℕ) (x y : L) (hk : 1 ≤ kk) (hy : y ≠ 0)
    (e8 : x ^ (2 ^ k + 1) + y * (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k)))
        + ((kk + 1 : ℕ) : L) * y = 0)
    (hS : y * (∑ i ∈ Finset.Ico 1 (kk + 1), x ^ (2 ^ (i * k)))
        = SA y k kk * x ^ (2 ^ k) + y * SB y k kk * x + y * SC y k kk + y * x ^ 2)
    (htop : Aseq y k kk * x ^ (2 ^ k)
        = y * x ^ 2 + y * Bseq y k kk * x + y * Cseq y k kk) :
    x ^ 3 + Rpoly k kk y * x ^ 2 + Lam1 y k kk * x + Lam0 y k kk = 0 := by
  -- Substitute the definitions of Rpoly, Lam1, and Lam0 into the goal.
  rw [Rpoly_eq, Lam1, Lam0];
  · grind +ring;
  · exact hk

/-! ## Theorem 6 -/

/-
**Theorem 6 (Dobbertin 1999).**  Over `L = 𝔽_{2ⁿ}` (encoded by `x^{2ⁿ} = x`),
with `gcd`-inverse exponent `kk' ≡ 1 (mod n)` (encoded by `kk·k = t·n + 1`), if
`x` is the root of `q(x) = 1/y` then `x = R(y)`; that is `q⁻¹(1/y) = R(y)`.
-/
theorem q_inv_eq_Rpoly (n t k kk : ℕ) (x y : L) (hk : 1 ≤ kk)
    (hy : y ≠ 0) (hx : x ≠ 0) (hxn : x ^ (2 ^ n) = x) (hkk : kk * k = t * n + 1)
    (hq : qPoly k kk x = y⁻¹) :
    x = Rpoly k kk y := by
  -- Apply the theorem6_cubic lemma with the given hypotheses.
  apply Eq.symm; exact (by
    have := @cubic_eqn L _ _ k kk x y hk hy (eqn8 k kk x y hx hy hq) (Ssum_via_eqn10 k kk x y hk (Eqn10_unfold y k x (eqn9 k kk x y hx hy (eqn8 k kk x y hx hy hq) (Ssum_add_frob k kk x hk (x_pow_reduce n t k kk x hxn hkk)))) (x_pow_reduce n t k kk x hxn hkk)) (eqn10_top k kk x y (Eqn10_unfold y k x (eqn9 k kk x y hx hy (eqn8 k kk x y hx hy hq) (Ssum_add_frob k kk x hk (x_pow_reduce n t k kk x hxn hkk))) kk) (x_pow_reduce n t k kk x hxn hkk))
    rw [ Lam1_eq_zero, Lam0_eq_zero ] at this;
    grind)

end Field

end KasamiPerm.InverseCubic