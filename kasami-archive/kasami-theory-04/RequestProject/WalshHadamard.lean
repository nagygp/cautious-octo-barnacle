/-
# Walsh–Hadamard Transform for Finite Fields

This module defines the Walsh–Hadamard transform (discrete Fourier transform)
for integer-valued functions on finite fields of characteristic 2, and proves
the key identities: Parseval's identity and the convolution theorem.

## Main definitions

* `walshCoeff` : The Walsh coefficient Ŝ(b) = ∑ x, f(x) · χ(b,x)
* `indicator` : The indicator function 1_S for a set S ⊆ F

## Main results

* `parseval` : ∑ b, Ŝ(b)² = |F| · ∑ x, f(x)²  (Parseval's identity)
* `walsh_indicator_zero` : Ŝ(0) = |S| for indicator functions
* `walsh_inversion` : f(x) = (1/|F|) ∑ b, Ŝ(b) · χ(b,x)

## References

* Ceccherini-Silberstein, Scarabotti, Tolli, "Discrete Harmonic Analysis"
* Canteaut, Charpin, Dobbertin, "Weight Divisibility of Cyclic Codes" (2000)
-/

import Mathlib
import RequestProject.TraceChar

open Finset BigOperators

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

attribute [local instance] ZMod.algebra

/-! ### Walsh–Hadamard Transform -/

/-- The Walsh–Hadamard transform of f : F → ℤ at frequency b.
    Ŝ(b) = ∑ x : F, f(x) · χ(b, x) -/
def walshCoeff (f : F → ℤ) (b : F) : ℤ :=
  ∑ x : F, f x * χ F b x

/-- The indicator function of a set S ⊆ F. -/
def indicator (S : Finset F) (x : F) : ℤ :=
  if x ∈ S then 1 else 0

/-! ### Basic properties -/

/-- Walsh coefficient at zero is the sum of the function. -/
lemma walshCoeff_zero (f : F → ℤ) :
    walshCoeff F f 0 = ∑ x : F, f x := by
  simp [walshCoeff, χ_zero_left]

/-
Walsh coefficient of indicator at zero is the cardinality of the set.
-/
lemma walshCoeff_indicator_zero (S : Finset F) :
    walshCoeff F (indicator F S) 0 = S.card := by
      unfold walshCoeff indicator;
      simp +decide [ χ_zero_left ]

/-
Walsh coefficient of indicator function expressed as sum over S.
-/
lemma walshCoeff_indicator (S : Finset F) (b : F) :
    walshCoeff F (indicator F S) b = ∑ x ∈ S, χ F b x := by
      unfold walshCoeff indicator;
      simp +decide [ Finset.sum_ite ]

/-! ### Parseval's Identity -/

/-
Parseval's identity: ∑ b, Ŝ(b)² = |F| · ∑ x, f(x)²
    This is the fundamental energy conservation identity for the Walsh transform.

    Proof sketch: Expand Ŝ(b)² = (∑ x, f(x)χ(b,x))(∑ y, f(y)χ(b,y))
    = ∑ x,y, f(x)f(y)χ(b,x)χ(b,y) = ∑ x,y, f(x)f(y)χ(b,x+y)
    Sum over b: ∑_b χ(b,x+y) = |F|·δ(x,y)
    Result: |F| · ∑ x, f(x)²
-/
lemma parseval (f : F → ℤ) :
    ∑ b : F, (walshCoeff F f b) ^ 2 = (Fintype.card F : ℤ) * ∑ x : F, (f x) ^ 2 := by
  -- Start with the definition of the Walsh-Hadamard transform and expand the square.
  have h_expand : ∀ b, walshCoeff F f b ^ 2 = ∑ x, ∑ y, f x * f y * χ F b (x + y) := by
    intro b
    unfold walshCoeff
    ring;
    simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [ χ_mul_snd ] ;
  -- By the orthogonality of the characters, we have that $\sum_{b \in F} \chi(b, x + y) = |F|$ if $x + y = 0$ and $0$ otherwise.
  have h_orthog : ∀ x y : F, ∑ b : F, χ F b (x + y) = if x + y = 0 then (Fintype.card F : ℤ) else 0 := by
    exact?;
  simp +decide only [h_expand, mul_comm, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx; rw [ Finset.sum_comm ] ; simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_orthog ] ; ring;
  rw [ Finset.sum_eq_single ( -x ) ] <;> simp +decide [ add_eq_zero_iff_eq_neg ] ; ring;
  · rw [ show -x = x from by rw [ neg_eq_iff_add_eq_zero ] ; exact? ] ; ring;
  · grind

/-! ### Convolution -/

/-- Convolution of two functions on F. -/
def conv (f g : F → ℤ) (x : F) : ℤ :=
  ∑ y : F, f y * g (x - y)

/-
The convolution theorem: the Walsh transform of a convolution is the
    pointwise product of Walsh transforms.

    Proof sketch: Expand, substitute z = x - y, use χ multiplicativity.
-/
lemma walshCoeff_conv (f g : F → ℤ) (b : F) :
    walshCoeff F (conv F f g) b = walshCoeff F f b * walshCoeff F g b := by
  unfold walshCoeff conv;
  simp +decide only [mul_comm, sum_mul];
  simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ ← Equiv.sum_comp ( Equiv.addRight y ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, χ_mul_snd ]

/-! ### Walsh Inversion -/

/-
Walsh inversion formula: f can be recovered from its Walsh coefficients.
    |F| · f(x) = ∑ b, Ŝ(b) · χ(b, x)

    Proof sketch: ∑_b Ŝ(b)χ(b,x) = ∑_b (∑_y f(y)χ(b,y))χ(b,x)
    = ∑_y f(y) ∑_b χ(b, x+y) = ∑_y f(y) |F|δ(x,y) = |F|·f(x)
-/
lemma walsh_inversion (f : F → ℤ) (x : F) :
    (Fintype.card F : ℤ) * f x = ∑ b : F, walshCoeff F f b * χ F b x := by
  unfold walshCoeff;
  simp +decide only [mul_comm, mul_sum];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  rotate_right;
  use fun y => f y * ∑ b : F, χ F b ( x + y );
  · rw [ Finset.sum_eq_single x ] <;> simp_all +decide [ χ_sum_dual ];
    · simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
    · grind +suggestions;
  · simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, χ_mul_snd ]

end