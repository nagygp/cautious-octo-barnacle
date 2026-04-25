/-
# Walsh–Hadamard Transform for Finite Fields
-/
import Mathlib
import RequestProject.TraceChar

open Finset BigOperators
noncomputable section
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
attribute [local instance] ZMod.algebra

def walshCoeff (f : F → ℤ) (b : F) : ℤ :=
  ∑ x : F, f x * χ F b x

def indicator (S : Finset F) (x : F) : ℤ :=
  if x ∈ S then 1 else 0

lemma walshCoeff_zero (f : F → ℤ) :
    walshCoeff F f 0 = ∑ x : F, f x := by
  simp [walshCoeff, χ_zero_left]

lemma walshCoeff_indicator_zero (S : Finset F) :
    walshCoeff F (indicator F S) 0 = S.card := by
  unfold walshCoeff indicator
  simp [χ_zero_left]

lemma walshCoeff_indicator (S : Finset F) (b : F) :
    walshCoeff F (indicator F S) b = ∑ x ∈ S, χ F b x := by
  unfold walshCoeff indicator
  simp [Finset.sum_ite]

lemma parseval (f : F → ℤ) :
    ∑ b : F, (walshCoeff F f b) ^ 2 = (Fintype.card F : ℤ) * ∑ x : F, (f x) ^ 2 := by
  -- Expand the square of the Walsh coefficient using the definition.
  have h_expand : ∀ b : F, (walshCoeff F f b) ^ 2 = ∑ x : F, ∑ y : F, f x * f y * χ F b (x + y) := by
    intro b
    unfold walshCoeff
    ring;
    simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [ χ_mul_snd ] ;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ b : F, ∑ x : F, ∑ y : F, f x * f y * χ F b (x + y) = ∑ x : F, ∑ y : F, f x * f y * ∑ b : F, χ F b (x + y) := by
    simp +decide only [Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  -- By the properties of the trace, we know that $\sum_{b \in F} \chi(b, x + y) = |F| \cdot \delta_{x + y, 0}$.
  have h_trace : ∀ x y : F, ∑ b : F, χ F b (x + y) = if x + y = 0 then (Fintype.card F : ℤ) else 0 := by
    exact?;
  simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, sq ];
  rw [ Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_eq_single ( -‹_› ) ] <;> simp +decide [ add_eq_zero_iff_eq_neg ];
  · exact Or.inl ( by rw [ neg_eq_of_add_eq_zero_right ( show _ + _ = 0 from by rw [ ← two_smul F, CharTwo.two_eq_zero, zero_smul ] ) ] );
  · grind +splitImp

def conv (f g : F → ℤ) (x : F) : ℤ :=
  ∑ y : F, f y * g (x - y)

lemma walshCoeff_conv (f g : F → ℤ) (b : F) :
    walshCoeff F (conv F f g) b = walshCoeff F f b * walshCoeff F g b := by
  unfold walshCoeff conv;
  simp +decide only [mul_comm, Finset.sum_mul _ _ _];
  simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ ← Equiv.sum_comp ( Equiv.addRight y ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, χ_mul_snd ] ;

lemma walsh_inversion (f : F → ℤ) (x : F) :
    (Fintype.card F : ℤ) * f x = ∑ b : F, walshCoeff F f b * χ F b x := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ b : F, (∑ y : F, f y * χ F b y) * χ F b x = ∑ y : F, f y * (∑ b : F, χ F b y * χ F b x) := by
    simpa only [ mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ] using Finset.sum_comm;
  -- By Lemma~\ref{lem:χ_sum_dual}, $\sum_b χ(b, y + x) = |F|$ if $y + x = 0$ else $0$.
  have h_char_sum : ∀ y : F, ∑ b : F, χ F b y * χ F b x = if y + x = 0 then (Fintype.card F : ℤ) else 0 := by
    intro y
    have h_char_sum : ∑ b : F, χ F b (y + x) = if y + x = 0 then (Fintype.card F : ℤ) else 0 := by
      convert χ_sum_dual F ( y + x ) using 1;
    convert h_char_sum using 2;
    exact?;
  simp_all +decide [ add_eq_zero_iff_eq_neg ];
  rw [ mul_comm, show -x = x from by rw [ neg_eq_iff_add_eq_zero ] ; exact? ] at h_fubini ; linarith!

end