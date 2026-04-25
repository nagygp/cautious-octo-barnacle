/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Walsh–Hadamard Transform for Finite Fields

This module defines the Walsh–Hadamard transform (WHT) for integer-valued
functions on finite fields of characteristic 2, and proves the key identities.

## Main definitions

* `wht` : The WHT of `f : F_{2^n} → F_{2^n}` at frequency `a`:
    `W_f(a) = ∑ x, χ(a·x + f(x))`
* `walshCoeff` : The Walsh coefficient of `f : F_{2^n} → ℤ` at frequency `b`:
    `Ŝ(b) = ∑ x, f(x) · χ(b·x)`
* `indicator` : The indicator function `1_S` for a set `S ⊆ F`
* `conv` : Convolution of two functions on `F`

## Main results

* `parseval` : `∑ b, Ŝ(b)² = |F| · ∑ x, f(x)²` (Parseval's identity)
* `walshCoeff_indicator_zero` : `Ŝ(0) = |S|` for indicator functions
* `walsh_inversion` : `|F| · f(x) = ∑ b, Ŝ(b) · χ(b·x)` (Fourier inversion)
* `walshCoeff_conv` : `Ŝ_{f*g}(b) = Ŝ_f(b) · Ŝ_g(b)` (convolution theorem)
* `wht_parseval` : `∑ a, W_f(a)² = (2^n)²`
* `wht_inversion` : `∑ a, W_f(a) · χ(a·x) = 2^n · χ(f(x))`

## References

* Ceccherini-Silberstein, Scarabotti, Tolli, "Discrete Harmonic Analysis"
* Canteaut, Charpin, Dobbertin, "Weight Divisibility of Cyclic Codes" (2000)
* Carlet, "Boolean Functions for Cryptography and Coding Theory" (2021), §4.1
-/

import Mathlib
import RequestProject.WalshHadamard.Basic
import RequestProject.WalshHadamard.Trace
import RequestProject.WalshHadamard.Character

namespace WalshHadamardTheory

open Finset BigOperators Classical

noncomputable section

variable {n : ℕ}

/-! ## Part I: Walsh coefficients for integer-valued functions -/

/-- The Walsh coefficient of `f : F_{2^n} → ℤ` at frequency `b`.
    `Ŝ(b) = ∑ x : F_{2^n}, f(x) · χ(b·x)` -/
def walshCoeff (n : ℕ) (f : F2n n → ℤ) (b : F2n n) : ℤ :=
  ∑ x : F2n n, f x * chi n (b * x)

/-- The indicator function of a set `S ⊆ F_{2^n}`. -/
def indicator (n : ℕ) (S : Finset (F2n n)) (x : F2n n) : ℤ :=
  if x ∈ S then 1 else 0

/-! ### Basic Walsh coefficient properties -/

/-- Walsh coefficient at zero is the sum of the function. -/
theorem walshCoeff_zero (f : F2n n → ℤ) :
    walshCoeff n f 0 = ∑ x : F2n n, f x := by
  simp [walshCoeff, chi_zero]

/-
Walsh coefficient of indicator at zero is the cardinality of the set.
-/
theorem walshCoeff_indicator_zero (S : Finset (F2n n)) :
    walshCoeff n (indicator n S) 0 = S.card := by
  convert walshCoeff_zero _;
  unfold indicator; aesop;

/-
Walsh coefficient of indicator function expressed as sum over `S`.
-/
theorem walshCoeff_indicator (S : Finset (F2n n)) (b : F2n n) :
    walshCoeff n (indicator n S) b = ∑ x ∈ S, chi n (b * x) := by
  unfold walshCoeff indicator; rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ] ; aesop;
  aesop

/-! ### Parseval's Identity -/

/-
**Parseval's identity**: `∑ b, Ŝ(b)² = |F| · ∑ x, f(x)²`.
    This is the fundamental energy conservation identity for the Walsh transform.

    Proof idea: Expand `Ŝ(b)² = (∑ x, f(x)χ(b,x))(∑ y, f(y)χ(b,y))`,
    use `χ(b,x)·χ(b,y) = χ(b,x+y)`, then sum over `b` and apply
    character orthogonality `∑_b χ(b,x+y) = |F|·δ(x,y)`.
-/
theorem parseval (hn : n ≠ 0) (f : F2n n → ℤ) :
    ∑ b : F2n n, (walshCoeff n f b) ^ 2 =
    (Fintype.card (F2n n) : ℤ) * ∑ x : F2n n, (f x) ^ 2 := by
  -- By definition of the Walsh coefficient, we can write
  have h_walsh_def : ∀ b : F2n n, walshCoeff n f b ^ 2 = ∑ x : F2n n, ∑ y : F2n n, f x * f y * chi n (b * (x + y)) := by
    intro b
    rw [sq]
    simp [walshCoeff];
    rw [ Finset.sum_mul ];
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, mul_assoc, mul_add, chi_add];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ b : F2n n, ∑ x : F2n n, ∑ y : F2n n, f x * f y * chi n (b * (x + y)) = ∑ x : F2n n, ∑ y : F2n n, f x * f y * ∑ b : F2n n, chi n (b * (x + y)) := by
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ) );
  -- By the orthogonality relation, we know that $\sum_{b} \chi(b(x+y)) = |F| \delta(x+y)$.
  have h_orthogonality : ∀ x y : F2n n, ∑ b : F2n n, chi n (b * (x + y)) = if x + y = 0 then (Fintype.card (F2n n) : ℤ) else 0 := by
    intro x y;
    convert chi_sum hn ( x + y ) using 1;
    · ac_rfl;
    · rw [ F2n.card n hn ];
      norm_cast;
  simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, sq ];
  simp +decide [ Finset.sum_ite, add_eq_zero_iff_eq_neg ]

/-! ### Convolution -/

/-- Convolution of two functions on `F_{2^n}`. -/
def conv (n : ℕ) (f g : F2n n → ℤ) (x : F2n n) : ℤ :=
  ∑ y : F2n n, f y * g (x - y)

/-
**Convolution theorem**: the Walsh transform of a convolution is the
    pointwise product of Walsh transforms.
-/
theorem walshCoeff_conv (hn : n ≠ 0) (f g : F2n n → ℤ) (b : F2n n) :
    walshCoeff n (conv n f g) b = walshCoeff n f b * walshCoeff n g b := by
  unfold walshCoeff;
  simp +decide only [conv, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx; rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Equiv.sum_comp ( Equiv.addRight x ) ] ; simp +decide [ mul_assoc, mul_left_comm, mul_comm ] ;
  simp +decide [ mul_add, add_mul, mul_comm, mul_left_comm, chi_add ]

/-! ### Walsh Inversion -/

/-
**Walsh inversion formula**: `f` can be recovered from its Walsh coefficients.
    `|F| · f(x) = ∑ b, Ŝ(b) · χ(b·x)`

    Proof idea: `∑_b Ŝ(b)χ(b,x) = ∑_b (∑_y f(y)χ(b,y))χ(b,x)
    = ∑_y f(y) ∑_b χ(b, x+y) = ∑_y f(y) |F|δ(x,y) = |F|·f(x)`
-/
theorem walsh_inversion (hn : n ≠ 0) (f : F2n n → ℤ) (x : F2n n) :
    (Fintype.card (F2n n) : ℤ) * f x = ∑ b : F2n n, walshCoeff n f b * chi n (b * x) := by
  -- Expand the right-hand side using the definition of `walshCoeff`.
  have h_expand : ∑ b : F2n n, walshCoeff n f b * chi n (b * x) = ∑ y : F2n n, f y * ∑ b : F2n n, chi n (b * (y + x)) := by
    simp +decide only [walshCoeff, sum_mul, mul_assoc];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; ring;
    rw [ mul_assoc, ← chi_add ];
  -- Apply the orthogonality relation to the inner sum.
  have h_inner : ∀ y : F2n n, ∑ b : F2n n, chi n (b * (y + x)) = if y + x = 0 then (Fintype.card (F2n n) : ℤ) else 0 := by
    intro y
    by_cases hy : y + x = 0;
    · rw [ if_pos hy, Finset.sum_congr rfl fun _ _ => by rw [ hy, MulZeroClass.mul_zero, chi_zero ] ] ; norm_num;
    · have := chi_orthogonality hn ( y + x ) hy; simp_all +decide [ mul_comm ] ;
  simp_all +decide [ add_eq_zero_iff_eq_neg ];
  ring

/-! ## Part II: Walsh–Hadamard Transform of field-valued functions

The WHT of `f : F_{2^n} → F_{2^n}` is defined as
`W_f(a) = ∑_{x ∈ F_{2^n}} χ(a·x + f(x))`

This is the standard definition used in cryptographic/coding theory applications
(APN functions, Almost Bent functions, etc.). -/

/-- The Walsh–Hadamard transform of `f : F_{2^n} → F_{2^n}` at point `a`.
    `W_f(a) = ∑_{x ∈ F_{2^n}} χ(a·x + f(x))` -/
def wht (f : F2n n → F2n n) (a : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (a * x + f x)

/-- WHT at `a = 0`: `W_f(0) = ∑_x χ(f(x))`. -/
theorem wht_zero (f : F2n n → F2n n) :
    wht f 0 = ∑ x : F2n n, chi n (f x) := by
  simp [wht]

/-- WHT of the zero function. -/
theorem wht_zero_fun (hn : n ≠ 0) (a : F2n n) :
    wht (fun _ : F2n n => (0 : F2n n)) a = if a = 0 then (2 ^ n : ℤ) else 0 := by
  simp only [wht, add_zero]
  exact chi_sum hn a

/-! ### WHT Parseval identity -/

/-
**WHT Parseval identity**: `∑ a, W_f(a)² = (2^n)²`.

    Proof idea: Expand, swap order of summation, apply character orthogonality,
    use `χ(x)² = 1`.
-/
theorem wht_parseval (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  -- Expand W_f(a)^2 using the definition of W_f(a).
  have h_expand : ∑ a : F2n n, (wht f a) ^ 2 = ∑ a : F2n n, ∑ x : F2n n, ∑ y : F2n n, chi n (a * x + f x) * chi n (a * y + f y) := by
    simp +decide only [wht, sq, sum_mul_sum];
  -- By chi_add, this = ∑_x ∑_y χ(a(x+y) + f(x) + f(y)).
  have h_expand' : ∑ a : F2n n, ∑ x : F2n n, ∑ y : F2n n, chi n (a * x + f x) * chi n (a * y + f y) = ∑ x : F2n n, ∑ y : F2n n, ∑ a : F2n n, chi n (a * (x + y) + f x + f y) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro x hx; rw [ Finset.sum_comm ] ; congr; ext y; congr; ext a; rw [ ← chi_add ] ; ring;
  -- Sum over a: ∑_a χ(a(x+y)) = |F|δ_{x,y} by chi_sum.
  have h_sum_a : ∀ x y : F2n n, ∑ a : F2n n, chi n (a * (x + y) + f x + f y) = if x = y then (2 ^ n : ℤ) else 0 := by
    intro x y; split_ifs <;> simp_all +decide [ ← add_assoc, chi_add ] ;
    · rw [ F2n.card n hn, chi_zero ] ; norm_num;
    · have h_sum_a : ∑ a : F2n n, chi n (a * (x + y)) = 0 := by
        convert chi_orthogonality hn ( x + y ) ( add_eq_zero_iff_eq_neg.not.mpr <| by aesop ) using 1;
        ac_rfl;
      simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
  rw [ sq, F2n.card n hn ];
  norm_cast

/-
Sum of `W_f(a)` over all `a` equals `2^n · χ(f(0))`.
-/
theorem wht_sum (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a = (2 ^ n : ℤ) * chi n (f 0) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, wht f a = ∑ x : F2n n, chi n (f x) * ∑ a : F2n n, chi n (a * x) := by
    simp +decide only [wht, Finset.mul_sum _ _ _];
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← chi_add ] ; ring;
  rw [ h_fubini, Finset.sum_eq_single 0 ];
  · simp +decide [ mul_comm, F2n.card n hn ];
    exact Or.inl ( chi_zero n );
  · exact fun x _ hx => mul_eq_zero_of_right _ ( by simpa [ mul_comm ] using chi_sum hn x |> fun h => h.trans ( by simp +decide [ hx ] ) );
  · aesop

/-! ### WHT Inversion formula -/

/-
**WHT Inversion formula**: `∑ a, W_f(a) · χ(a·x) = 2^n · χ(f(x))`.
-/
theorem wht_inversion (hn : n ≠ 0) (f : F2n n → F2n n) (x : F2n n) :
    ∑ a : F2n n, wht f a * chi n (a * x) = (2 ^ n : ℤ) * chi n (f x) := by
  -- Expand `W_f(a)` using its definition and apply `chi_add`.
  have h_expand : ∑ a : F2n n, (∑ y : F2n n, chi n (a * y + f y)) * chi n (a * x) = ∑ y : F2n n, chi n (f y) * ∑ a : F2n n, chi n (a * (y + x)) := by
    simp +decide only [sum_mul, mul_add];
    simp +decide only [chi_add, mul_comm, Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  -- Apply the orthogonality relation `chi_sum` to the inner sum.
  have h_inner : ∀ y : F2n n, ∑ a : F2n n, chi n (a * (y + x)) = if y = x then (2 ^ n : ℤ) else 0 := by
    intro y
    have h_inner_sum : ∑ a : F2n n, chi n (a * (y + x)) = if y + x = 0 then (2 ^ n : ℤ) else 0 := by
      convert chi_sum hn ( y + x ) using 1;
      ac_rfl;
    simp_all +decide [ add_eq_zero_iff_eq_neg ];
  simp_all +decide [ mul_comm ];
  convert h_expand using 1

/-! ### WHT value bounds -/

/-
Trivial bound: `|W_f(a)| ≤ 2^n`.
-/
theorem wht_abs_le (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    |wht f a| ≤ 2 ^ n := by
  refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
  rw [ Finset.sum_congr rfl fun x hx => chi_abs _ ] ; norm_num [ F2n.card n hn ]

/-! ### WHT and function composition -/

/-- WHT of `f + g` (pointwise). -/
theorem wht_add (f g : F2n n → F2n n) (a : F2n n) :
    wht (fun x => f x + g x) a = ∑ x : F2n n, chi n (a * x + f x) * chi n (g x) := by
  simp only [wht]
  congr 1; ext x
  rw [← chi_add]
  congr 1; ring

/-! ### Fourth moment -/

/-- The fourth moment `∑ a, W_f(a)⁴`. -/
def whtFourthMoment (f : F2n n → F2n n) : ℤ :=
  ∑ a : F2n n, wht f a ^ 4

/-
The fourth moment is bounded below by `(2^n)^3` (Cauchy-Schwarz).
-/
theorem whtFourthMoment_ge (hn : n ≠ 0) (f : F2n n → F2n n) :
    whtFourthMoment f ≥ (2 ^ n : ℤ) ^ 3 := by
  -- By Cauchy-Schwarz inequality, we have (∑ a_i^2)^2 ≤ (n) * (∑ a_i^4).
  have h_cauchy_schwarz : (∑ a : F2n n, wht f a ^ 2) ^ 2 ≤ (Fintype.card (F2n n)) * (∑ a : F2n n, wht f a ^ 4) := by
    have h_cauchy_schwarz : ∀ (u v : F2n n → ℤ), (∑ a : F2n n, u a * v a) ^ 2 ≤ (∑ a : F2n n, u a ^ 2) * (∑ a : F2n n, v a ^ 2) := by
      exact fun u v => sum_mul_sq_le_sq_mul_sq Finset.univ u v;
    convert h_cauchy_schwarz 1 ( fun a => wht f a ^ 2 ) using 1 <;> norm_num ; ring;
  unfold whtFourthMoment;
  rw [ F2n.card n hn ] at h_cauchy_schwarz;
  rw [ wht_parseval hn f ] at h_cauchy_schwarz ; norm_num at h_cauchy_schwarz ; nlinarith [ pow_pos ( zero_lt_two' ℤ ) n ]

end
end WalshHadamardTheory