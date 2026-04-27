/-
# Additive Characters of Finite Fields via Trace

This module develops the theory of additive characters for finite fields of
characteristic 2, constructed via the field trace map.

## Main definitions

* `traceInt` : The trace composed with ZMod.val, giving values in ℤ
* `χ` : The canonical additive character χ(a,x) = 1 - 2·Tr(ax) ∈ {±1}

## Main results

* `χ_mul_snd` : χ(a, x+y) = χ(a,x) · χ(a,y)
* `χ_mul_fst` : χ(a+b, x) = χ(a,x) · χ(b,x)
* `χ_sq` : χ(a,x)² = 1
* `χ_sum_ne_zero` : ∑ x, χ(a,x) = 0 for a ≠ 0
* `χ_sum_zero_left` : ∑ x, χ(0,x) = |F|
* `trace_kernel_card` : |{x : Tr(x) = 0}| = |F|/2
* `trace_fiber_balance` : |{x : Tr(x) = 0}| = |{x : Tr(x) = 1}|

## References

* Lidl, Niederreiter, "Finite Fields", Chapter 5
-/

import Mathlib

open Finset BigOperators

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Setup: F as a ZMod 2 - algebra -/

attribute [local instance] ZMod.algebra

instance TraceChar.instFiniteDimensional : FiniteDimensional (ZMod 2) F :=
  Module.Finite.of_finite

instance TraceChar.instIsSeparable : Algebra.IsSeparable (ZMod 2) F :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- The trace is surjective for finite separable extensions. -/
lemma trace_surjective : Function.Surjective (Algebra.trace (ZMod 2) F) :=
  Algebra.trace_surjective (ZMod 2) F

/-! ### Integer-valued trace and character -/

/-- Trace as an integer value: sends x to 0 or 1. -/
def traceInt (x : F) : ℤ :=
  (ZMod.val (Algebra.trace (ZMod 2) F x) : ℤ)

/-- The canonical additive character χ(a,x) = 1 - 2·Tr(ax).
    Takes values in {-1, 1} ⊂ ℤ. This is (-1)^{Tr(ax)}. -/
def χ (a x : F) : ℤ :=
  1 - 2 * traceInt F (a * x)

/-! ### Basic properties of traceInt -/

lemma traceInt_values (x : F) : traceInt F x = 0 ∨ traceInt F x = 1 := by
  unfold traceInt
  have h : ZMod.val (Algebra.trace (ZMod 2) F x) < 2 := ZMod.val_lt _
  omega

lemma traceInt_zero : traceInt F 0 = 0 := by
  simp [traceInt, map_zero]

lemma traceInt_add (x y : F) :
    traceInt F (x + y) = (traceInt F x + traceInt F y) % 2 := by
  unfold traceInt
  rw [map_add, ZMod.val_add]
  simp

lemma traceInt_neg_eq (x : F) : traceInt F (-x) = traceInt F x := by
  rw [CharTwo.neg_eq x]

/-! ### Properties of χ -/

lemma χ_values (a x : F) : χ F a x = 1 ∨ χ F a x = -1 := by
  unfold χ
  rcases traceInt_values F (a * x) with h | h <;> simp [h]

omit [Fintype F] [DecidableEq F] in
lemma χ_zero_left (x : F) : χ F 0 x = 1 := by
  simp [χ, traceInt, mul_comm, map_zero, ZMod.val_zero]

lemma χ_sq (a x : F) : χ F a x ^ 2 = 1 := by
  rcases χ_values F a x with h | h <;> simp [h]

lemma χ_sq' (a x : F) : χ F a x * χ F a x = 1 := by
  have := χ_sq F a x; linarith [sq (χ F a x)]

lemma χ_ne_zero (a x : F) : χ F a x ≠ 0 := by
  rcases χ_values F a x with h | h <;> simp [h]

/-- χ is multiplicative in the second argument (additive character property):
    χ(a, x+y) = χ(a,x) · χ(a,y) -/
lemma χ_mul_snd (a x y : F) : χ F a (x + y) = χ F a x * χ F a y := by
  unfold χ
  have hmul : a * (x + y) = a * x + a * y := mul_add a x y
  rw [hmul]
  have hmod := traceInt_add F (a * x) (a * y)
  rcases traceInt_values F (a * x) with hx | hx <;>
    rcases traceInt_values F (a * y) with hy | hy <;>
    rcases traceInt_values F (a * x + a * y) with hxy | hxy <;>
    simp_all <;> omega

/-- χ is multiplicative in the first argument:
    χ(a+b, x) = χ(a,x) · χ(b,x) -/
lemma χ_mul_fst (a b x : F) : χ F (a + b) x = χ F a x * χ F b x := by
  unfold χ
  have hab : (a + b) * x = a * x + b * x := add_mul a b x
  rw [hab]
  have hmod := traceInt_add F (a * x) (b * x)
  rcases traceInt_values F (a * x) with ha | ha <;>
    rcases traceInt_values F (b * x) with hb | hb <;>
    rcases traceInt_values F (a * x + b * x) with hab | hab <;>
    simp_all <;> omega

/-! ### Character orthogonality -/

/-- Sum of χ(0, x) over all x equals |F|. -/
lemma χ_sum_zero_left : ∑ x : F, χ F 0 x = (Fintype.card F : ℤ) := by
  simp [χ_zero_left]

/-
Core orthogonality: ∑ x, χ(a, x) = 0 for a ≠ 0.
    Proof: multiplication by a is a bijection on F, so
    ∑ x, χ(a,x) = ∑ x, χ(a, x + y) for any y.
    Choose y such that χ(a,y) = -1 (exists since a ≠ 0 and Tr is surjective).
    Then S = S · (-1), hence S = 0.
-/
lemma χ_sum_ne_zero (a : F) (ha : a ≠ 0) : ∑ x : F, χ F a x = 0 := by
  -- Choose y such that χ(a,y) = -1 (exists since a ≠ 0 and Tr is surjective).
  obtain ⟨y, hy⟩ : ∃ y : F, χ F a y = -1 := by
    have := trace_surjective F;
    obtain ⟨ y, hy ⟩ := this 1;
    use y / a;
    unfold χ traceInt;
    rw [ mul_div_cancel₀ _ ha, hy ] ; norm_cast;
  have h_sum : ∑ x : F, χ F a x = ∑ x : F, χ F a (x + y) := by
    rw [ ← Equiv.sum_comp ( Equiv.addRight y ) ] ; aesop;
  rw [ Finset.sum_congr rfl fun x hx => χ_mul_snd F a x y ] at h_sum;
  norm_num [ hy ] at h_sum ; linarith

/-- Character orthogonality (combined). -/
lemma χ_sum (a : F) :
    ∑ x : F, χ F a x = if a = 0 then (Fintype.card F : ℤ) else 0 := by
  split
  · subst_vars; exact χ_sum_zero_left F
  · exact χ_sum_ne_zero F a ‹_›

/-! ### Dual orthogonality -/

/-
Dual orthogonality: ∑ a, χ(a, x) = |F| · δ(x,0).
-/
lemma χ_sum_dual (x : F) :
    ∑ a : F, χ F a x = if x = 0 then (Fintype.card F : ℤ) else 0 := by
      split_ifs with hx;
      · simp +decide [ hx, χ ];
        exact?;
      · convert χ_sum_ne_zero F x hx using 1;
        unfold χ; simp +decide [ mul_comm ] ;

/-! ### Trace fiber properties -/

/-
The cardinality of the field is a power of 2.
-/
lemma card_eq_two_pow : ∃ n : ℕ, n ≥ 1 ∧ Fintype.card F = 2 ^ n := by
  obtain ⟨ n, hn ⟩ := FiniteField.card F 2;
  exact ⟨ n, n.2, hn.2 ⟩

/-
The trace kernel has size |F|/2.
-/
lemma trace_kernel_card :
    (Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0)).card =
    Fintype.card F / 2 := by
      -- Let $q = |F|$. Since $F$ is a finite field of characteristic 2, we have $q = 2^n$ for some $n$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Fintype.card F = 2 ^ n := by
        have := card_eq_two_pow F; aesop;
      rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
      · exact absurd hn ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
      · have := χ_sum_dual F 1; simp_all +decide [ χ ] ;
        rw [ Finset.sum_congr rfl fun x hx => show 2 * traceInt F x = 2 - ( 1 - traceInt F x ) * 2 by linarith [ show traceInt F x = 0 ∨ traceInt F x = 1 from traceInt_values F x |> Or.imp ( fun h => by linarith ) fun h => by linarith ] ] at this ; simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
        simp_all +decide [ Finset.sum_mul _ _ _, sub_mul ];
        rw [ sub_eq_zero, eq_comm ] at this;
        rw [ Finset.sum_congr rfl fun x hx => show traceInt F x * 2 = if traceInt F x = 0 then 0 else 2 by cases traceInt_values F x <;> aesop ] at this ; simp_all +decide [ Finset.sum_ite ];
        rw [ mul_comm ] at this ; norm_cast at this ; simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
        rw [ Nat.sub_eq_iff_eq_add ] at this;
        · convert congr_arg ( fun x : ℕ => x - 2 ^ n ) this.symm using 1 ; simp +decide [ Nat.sub_sub_self ( show 2 ^ n ≤ 2 * 2 ^ n from Nat.le_mul_of_pos_left _ zero_lt_two ) ];
          · unfold traceInt; simp +decide [ ZMod.val ] ;
          · rw [ two_mul, Nat.add_sub_cancel ];
        · exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide [ hn ] )

/-
The trace is balanced: |Tr⁻¹(0)| = |Tr⁻¹(1)| when |F| > 1.
-/
lemma trace_fiber_balance (hcard : Fintype.card F > 1) :
    (Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0)).card =
    (Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 1)).card := by
      obtain ⟨ x, hx ⟩ := trace_surjective F 1;
      refine' Finset.card_bij ( fun y hy => y + x ) _ _ _ <;> simp_all +decide;
      exact fun b hb => ⟨ b - x, by simp +decide [ hx, hb ], by simp +decide ⟩

end