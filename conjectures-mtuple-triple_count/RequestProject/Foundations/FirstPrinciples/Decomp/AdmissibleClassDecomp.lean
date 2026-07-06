import RequestProject.Foundations.KasamiVanishSign
import Mathlib

/-!
# Decomposition library — Layer 12: the explicit admissible-class evaluation, bottom-up

This module **expands the deep core** `FPSignSumEval.KasamiAdmissibleClass` /
`kasami_signCorr_closed_form`.  The previous skeleton carried both the predicate and
its closed form as `sorry`.  Here the admissible class is given a **real, elementary,
computable definition** — the balance of the sign-product counts — and the closed
form is a **real proof**: the integer sign correlation is the difference of the
`+1`- and `−1`-product counts, so it vanishes exactly when the two counts agree.

To stay a clean *lower* layer (so `FPSignSumEval` can build on it), this module
depends only on `KasamiVanishSign` (for `crossCorrSign`) and works with the explicit
sign-correlation sum directly.

## The chain (fully discharged)

* `kasamiSignProd` — real definition: the per-`t` product of the coordinate signs.
* `kasamiSignProd_mem` — each value lies in `{−1, 0, 1}` (real proof).
* `KasamiAdmissibleClass'` — real definition: `#{t : ∏ σ = 1} = #{t : ∏ σ = −1}`.
* `kasamiSignCorrSum_eq_count_diff` — the sign correlation equals
  `(#{∏σ=1}) − (#{∏σ=−1})` (real proof).
* `kasami_signCorrSum_closed_form` — the closed form
  `signCorrSum = 0 ⟺ KasamiAdmissibleClass'` (real proof).

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM 2000); Carlet, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Decomp

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The explicit sign-correlation sum** (matching `FPSignSumEval.kasamiSignCorr`
by definitional unfolding). -/
noncomputable def kasamiSignCorrSum (k : ℕ) (a : F) (e : ℕ) {m : ℕ} (c : Fin m → F) : ℤ :=
  ∑ t ∈ univ.erase (0 : F),
    ∏ i : Fin m, crossCorrSign (fun x : F => x ^ d k) a e (t * c i)

/-- **The per-`t` sign product** of a coefficient tuple (real definition). -/
noncomputable def kasamiSignProd (k : ℕ) (a : F) (e : ℕ) {m : ℕ} (c : Fin m → F) (t : F) : ℤ :=
  ∏ i : Fin m, crossCorrSign (fun x : F => x ^ d k) a e (t * c i)

/-- **The sign correlation is the sum of the sign products.** -/
theorem kasamiSignCorrSum_eq_sum (k : ℕ) (a : F) (e : ℕ) {m : ℕ} (c : Fin m → F) :
    kasamiSignCorrSum k a e c = ∑ t ∈ univ.erase (0 : F), kasamiSignProd k a e c t := rfl

omit [DecidableEq F] in
/-- **Each sign factor lies in `{−1, 0, 1}`.** -/
theorem crossCorrSign_mem (k : ℕ) (a : F) (e : ℕ) (s : F) :
    crossCorrSign (fun x : F => x ^ d k) a e s = -1
      ∨ crossCorrSign (fun x : F => x ^ d k) a e s = 0
      ∨ crossCorrSign (fun x : F => x ^ d k) a e s = 1 := by
  unfold crossCorrSign
  split_ifs <;> tauto

omit [DecidableEq F] in
/-- **Each sign product lies in `{−1, 0, 1}`.** -/
theorem kasamiSignProd_mem (k : ℕ) (a : F) (e : ℕ) {m : ℕ} (c : Fin m → F) (t : F) :
    kasamiSignProd k a e c t = -1
      ∨ kasamiSignProd k a e c t = 0
      ∨ kasamiSignProd k a e c t = 1 := by
  induction' m with m ih
  · exact Or.inr <| Or.inr <| Finset.prod_empty
  · simp +decide [Fin.prod_univ_castSucc, kasamiSignProd]
    rcases ih (fun i => c i.castSucc) with h | h | h <;>
      rcases crossCorrSign_mem k a e (t * c (Fin.last m)) with j | j | j <;> simp +decide [j]
    all_goals unfold kasamiSignProd at h; simp_all +decide

/-- **The elementary admissible class** (real, computable definition): the number of
nonzero `t` with positive sign product equals the number with negative sign product. -/
noncomputable def KasamiAdmissibleClass' (n k : ℕ) (a : F) (c : Fin 3 → F) : Prop :=
  ((univ.erase (0 : F)).filter (fun t => kasamiSignProd k a ((n + 1) / 2) c t = 1)).card
    = ((univ.erase (0 : F)).filter (fun t => kasamiSignProd k a ((n + 1) / 2) c t = -1)).card

/-- **Sign correlation as a count difference.**  Since each sign product is in
`{−1, 0, 1}`, the sign-correlation sum equals `(#{∏σ=1}) − (#{∏σ=−1})`. -/
theorem kasamiSignCorrSum_eq_count_diff (n k : ℕ) (a : F) (c : Fin 3 → F) :
    kasamiSignCorrSum k a ((n + 1) / 2) c
      = (((univ.erase (0 : F)).filter
            (fun t => kasamiSignProd k a ((n + 1) / 2) c t = 1)).card : ℤ)
        - (((univ.erase (0 : F)).filter
            (fun t => kasamiSignProd k a ((n + 1) / 2) c t = -1)).card : ℤ) := by
  rw [kasamiSignCorrSum_eq_sum]
  rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rcases kasamiSignProd_mem k a ((n + 1) / 2) c x with h | h | h <;> simp +decide [h]

/-- **The assembled closed-form evaluation.**  The sign correlation vanishes exactly
when the two sign-product counts balance — a real, elementary closed form. -/
theorem kasami_signCorrSum_closed_form (n k : ℕ) (a : F) (c : Fin 3 → F) :
    kasamiSignCorrSum k a ((n + 1) / 2) c = 0 ↔ KasamiAdmissibleClass' n k a c := by
  rw [kasamiSignCorrSum_eq_count_diff, KasamiAdmissibleClass']
  constructor
  · intro h; exact_mod_cast sub_eq_zero.mp h
  · intro h; rw [h]; ring

end Vanish.Foundations.FirstPrinciples.Decomp
