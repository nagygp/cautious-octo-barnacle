/-
# Additive Characters of Finite Fields via Trace
-/
import Mathlib

open Finset BigOperators
noncomputable section
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

attribute [local instance] ZMod.algebra

instance TraceChar.instFiniteDimensional : FiniteDimensional (ZMod 2) F :=
  Module.Finite.of_finite

instance TraceChar.instIsSeparable : Algebra.IsSeparable (ZMod 2) F :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

lemma trace_surjective : Function.Surjective (Algebra.trace (ZMod 2) F) :=
  Algebra.trace_surjective (ZMod 2) F

def traceInt (x : F) : ℤ :=
  (ZMod.val (Algebra.trace (ZMod 2) F x) : ℤ)

def χ (a x : F) : ℤ :=
  1 - 2 * traceInt F (a * x)

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

lemma χ_mul_snd (a x y : F) : χ F a (x + y) = χ F a x * χ F a y := by
  unfold χ
  have hmul : a * (x + y) = a * x + a * y := mul_add a x y
  rw [hmul]
  have hmod := traceInt_add F (a * x) (a * y)
  rcases traceInt_values F (a * x) with hx | hx <;>
    rcases traceInt_values F (a * y) with hy | hy <;>
    rcases traceInt_values F (a * x + a * y) with hxy | hxy <;>
    simp_all <;> omega

lemma χ_mul_fst (a b x : F) : χ F (a + b) x = χ F a x * χ F b x := by
  unfold χ
  have hab : (a + b) * x = a * x + b * x := add_mul a b x
  rw [hab]
  have hmod := traceInt_add F (a * x) (b * x)
  rcases traceInt_values F (a * x) with ha | ha <;>
    rcases traceInt_values F (b * x) with hb | hb <;>
    rcases traceInt_values F (a * x + b * x) with hab | hab <;>
    simp_all <;> omega

lemma χ_sum_zero_left : ∑ x : F, χ F 0 x = (Fintype.card F : ℤ) := by
  simp [χ_zero_left]

lemma χ_sum_ne_zero (a : F) (ha : a ≠ 0) : ∑ x : F, χ F a x = 0 := by
  obtain ⟨y, hy⟩ : ∃ y : F, χ F a y = -1 := by
    have := trace_surjective F
    obtain ⟨ y, hy ⟩ := this 1
    use y / a
    unfold χ traceInt
    rw [mul_div_cancel₀ _ ha, hy]; norm_cast
  have h_sum : ∑ x : F, χ F a x = ∑ x : F, χ F a (x + y) := by
    rw [← Equiv.sum_comp (Equiv.addRight y)]; simp
  rw [Finset.sum_congr rfl fun x _ => χ_mul_snd F a x y] at h_sum
  simp [hy, Finset.sum_mul] at h_sum; linarith

lemma χ_sum (a : F) :
    ∑ x : F, χ F a x = if a = 0 then (Fintype.card F : ℤ) else 0 := by
  split
  · subst_vars; exact χ_sum_zero_left F
  · exact χ_sum_ne_zero F a ‹_›

lemma χ_sum_dual (x : F) :
    ∑ a : F, χ F a x = if x = 0 then (Fintype.card F : ℤ) else 0 := by
  split_ifs with hx
  · simp [hx, χ, traceInt, map_zero, ZMod.val_zero]
  · convert χ_sum_ne_zero F x hx using 1
    unfold χ; simp [mul_comm]

lemma card_eq_two_pow : ∃ n : ℕ, n ≥ 1 ∧ Fintype.card F = 2 ^ n := by
  obtain ⟨ n, hn ⟩ := FiniteField.card F 2
  exact ⟨ n, n.2, hn.2 ⟩

lemma trace_kernel_card :
    (Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0)).card =
    Fintype.card F / 2 := by
  obtain ⟨ n, hn, h ⟩ := card_eq_two_pow F;
  -- Let $a$ be a non-zero element in $F$.
  obtain ⟨a, ha⟩ : ∃ a : F, a ≠ 0 := by
    exact ⟨ 1, one_ne_zero ⟩;
  have h_sum_zero : ∑ x : F, (χ F a x) = 0 := by
    exact?;
  -- Expanding χ(1,x) = 1 - 2·Tr(x), we get ∑_x (1 - 2·Tr(x)) = 0, i.e., |F| - 2·∑ Tr(x) = 0.
  have h_expand : (Fintype.card F : ℤ) - 2 * ∑ x : F, (traceInt F (a * x)) = 0 := by
    convert h_sum_zero using 1;
    simp +decide [ χ, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
  -- Since $\sum_{x \in F} \text{Tr}(x) = \sum_{x \in F} \text{Tr}(ax)$, we have $\sum_{x \in F} \text{Tr}(x) = \frac{|F|}{2}$.
  have h_sum_trace : ∑ x : F, traceInt F x = (Fintype.card F : ℤ) / 2 := by
    exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by decide ) ( by linarith [ show ∑ x : F, traceInt F ( a * x ) = ∑ x : F, traceInt F x from Equiv.sum_comp ( Equiv.mulLeft₀ a ha ) fun x => traceInt F x ] ) );
  -- Since $\text{Tr}(x)$ is either 0 or 1, we have $\sum_{x \in F} \text{Tr}(x) = |\{x \in F \mid \text{Tr}(x) = 1\}|$.
  have h_card_trace : ∑ x : F, traceInt F x = (Finset.univ.filter (fun x => traceInt F x = 1)).card := by
    rw [ Finset.card_filter ];
    push_cast;
    exact Finset.sum_congr rfl fun x hx => by rcases traceInt_values F x with h | h <;> rw [ h ] <;> rfl;
  -- Since $\text{Tr}(x)$ is either 0 or 1, we have $|\{x \in F \mid \text{Tr}(x) = 0\}| = |F| - |\{x \in F \mid \text{Tr}(x) = 1\}|$.
  have h_card_zero : (Finset.univ.filter (fun x => traceInt F x = 0)).card = (Fintype.card F : ℕ) - (Finset.univ.filter (fun x => traceInt F x = 1)).card := by
    rw [ eq_tsub_iff_add_eq_of_le ];
    · rw [ Finset.card_filter, Finset.card_filter ];
      rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x hx => by rcases traceInt_values F x with h | h <;> rw [ h ] ; simp +decide, Finset.sum_const, Finset.card_univ ] ; simp +decide;
    · exact Finset.card_le_univ _;
  convert h_card_zero using 1;
  · unfold traceInt; simp +decide [ ZMod.val ] ;
  · grind

end