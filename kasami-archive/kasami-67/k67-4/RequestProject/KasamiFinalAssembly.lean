/-
# KasamiFinalAssembly.lean — Final Assembly of the P₃ Triple Count Proof

This file assembles the verified modules into the corrected P₃ triple count
theorem for Almost Bent functions over GF(2^n).

## Result

For an Almost Bent function f : GF(2^n) → GF(2) with n odd, n ≥ 3,
f(0) = 0, and f balanced (W_f(0) = 0):

    T₃ = 2^{2n-3} - 2^{n-2}

## Proof Chain

1. `walsh_sum_from_f0`: ∑_a W(a) = |F| when f(0)=0
2. `ab_walsh_cube_sum`: ∑W(a)³ = 2^{2n+1} for balanced AB functions
3. `triple_correlation_eq_walsh_cubes`: |F|·C₃ = ∑_a W(a)³
4. `triple_count_balanced_expansion`: 8·T₃ = |F|² - C₃
5. `p3_triple_count_corrected`: T₃ = 2^{2n-3} - 2^{n-2}

## Algebraic Foundations (from verified modules)

- `kasami_radical_eq_kernel`: rad(Q_a) = ker(L_a) [KasamiPolarExpansion, 0 sorry]
- `gold_ker_le_two_kasami`: |ker(L_a)| ≤ 2 [GoldKernelBound, 0 sorry]
- `frobenius_gcd_fixed`, `ccd_kernel_bound`: Frobenius GCD [CCDCounting, 0 sorry]
- `character_orthogonality`, `walsh_parseval`: Fourier tools [WalshFourier, 0 sorry]
-/
import Mathlib
import RequestProject.Defs
import RequestProject.WalshFourier

noncomputable section

open scoped BigOperators
open Finset

set_option maxHeartbeats 3200000

/-! ## Step 1: Walsh Sum from f(0) = 0

Using character orthogonality: ∑_a W_f(a) = |F| · (-1)^{f(0)}.
When f(0) = 0, this gives ∑_a W_f(a) = |F|.
-/

theorem walsh_sum_from_f0
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_zero : Tr 0 = 0)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (f : F → ZMod 2) (hf0 : f 0 = 0) :
    ∑ a : F, walshTransform F Tr f a = (Fintype.card F : ℤ) := by
  unfold walshTransform;
  rw [ Finset.sum_comm, Finset.sum_eq_single 0 ];
  · aesop;
  · intro b hb hb_ne_zero
    have h_sum_zero : ∑ x : F, (if (Tr (x * b)).val = 0 then (1 : ℤ) else -1) = 0 := by
      convert character_orthogonality F Tr hTr_add hTr_sep b hb_ne_zero using 1;
    convert congr_arg ( fun x : ℤ => x * ( if ( f b ).val = 0 then 1 else -1 ) ) h_sum_zero using 1;
    · rw [ Finset.sum_mul _ _ _ ] ; congr ; ext x ; rcases f_b : f b with ( _ | _ | f_b ) <;> rcases Tr_x_b : Tr ( x * b ) with ( _ | _ | Tr_x_b ) <;> simp +decide [ f_b, Tr_x_b ] ;
      · linarith;
      · linarith;
      · linarith;
      · linarith;
      · linarith;
    · ring;
  · exact fun h => False.elim <| h <| Finset.mem_univ _

/-! ## Step 2: AB Walsh Cube Sum

For AB functions, W(a)³ = W(a) · s² since W(a) ∈ {0, ±s}.
So ∑W(a)³ = s² · ∑W(a) = 2^{n+1} · 2^n = 2^{2n+1}.
-/

/-- Key algebraic fact: W(a)³ = W(a) · s² when W(a) ∈ {0, ±s}. -/
lemma ab_cube_eq_linear_times_sq (w s : ℤ)
    (h : w = 0 ∨ w = s ∨ w = -s) :
    w ^ 3 = w * s ^ 2 := by
  rcases h with rfl | rfl | rfl <;> ring

theorem ab_walsh_cube_sum
    (n : ℕ) (hn : 3 ≤ n) (hn_odd : Odd n)
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (hcard : Fintype.card F = 2 ^ n)
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_zero : Tr 0 = 0)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (f : F → ZMod 2) (hf0 : f 0 = 0)
    (hAB : IsAlmostBent F Tr f ((n + 1) / 2)) :
    ∑ a : F, (walshTransform F Tr f a) ^ 3 = (2 : ℤ) ^ (2 * n + 1) := by
  -- Apply the lemma ab_cube_eq_linear_times_sq to each term in the sum.
  have h_sum : ∑ a : F, (walshTransform F Tr f a) ^ 3 = (2 ^ ((n + 1) / 2)) ^ 2 * ∑ a : F, (walshTransform F Tr f a) := by
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun x hx => by rcases hAB x with h | h | h <;> rw [ h ] <;> ring;
  have := walsh_sum_from_f0 F Tr hTr_add hTr_zero hTr_sep f hf0; simp_all +decide [ ← pow_mul' ] ;
  rw [ ← pow_add, show 2 * ( ( n + 1 ) / 2 ) + n = 2 * n + 1 by linarith [ Nat.div_mul_cancel ( show 2 ∣ n + 1 from even_iff_two_dvd.mp ( by simpa [ parity_simps ] using hn_odd ) ) ] ]

/-! ## Step 3: Triple Correlation = Walsh Cubes -/

theorem triple_correlation_eq_walsh_cubes
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_zero : Tr 0 = 0)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (f : F → ZMod 2) :
    (Fintype.card F : ℤ) * tripleCorrelation F f =
    ∑ a : F, (walshTransform F Tr f a) ^ 3 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F, (∑ x : F, if (f x + Tr (a * x)).val = 0 then (1 : ℤ) else -1) ^ 3 = ∑ x : F, ∑ y : F, ∑ z : F, (if (f x + f y + f z).val = 0 then (1 : ℤ) else -1) * ∑ a : F, (if (Tr (a * (x + y + z))).val = 0 then (1 : ℤ) else -1) := by
    simp +decide only [pow_three, mul_sum _ _ _, sum_mul];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => _ ) ) );
    refine' Finset.sum_congr rfl fun x _ => _;
    split_ifs <;> norm_num;
    all_goals simp_all +decide [ mul_add, ZMod.val_add ];
    all_goals omega;
  convert h_fubini.symm using 1;
  rw [ Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun z hz => ?_ ];
  rotate_left;
  use fun x y z => if x + y + z = 0 then ( if ( f x + f y + f z ).val = 0 then 1 else -1 ) * ( Fintype.card F : ℤ ) else 0;
  · by_cases h : x + y + z = 0 <;> simp +decide [ h ];
    · aesop;
    · have h_char_ortho : ∑ a : F, (if (Tr (a * (x + y + z))).val = 0 then (1 : ℤ) else -1) = 0 := by
        convert character_orthogonality F Tr hTr_add hTr_sep ( x + y + z ) h using 1;
      simp_all +decide [ ZMod.val_eq_zero ];
  · simp +decide [ mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul, tripleCorrelation ];
    refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
    rw [ Finset.sum_eq_single ( -x - y ) ] <;> simp +decide [ add_eq_zero_iff_eq_neg ];
    · rw [ show -x - y = - ( x + y ) by ring, show f ( - ( x + y ) ) = f ( x + y ) from ?_ ];
      · cases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ f y, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ f ( x + y ), rfl ⟩ <;> simp +decide [ * ];
      · rw [ neg_eq_of_add_eq_zero_right ];
        exact?;
    · grind

/-! ## Step 4: Triple Count from Correlation (for balanced functions) -/

theorem triple_count_balanced_expansion
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (Tr : F → ZMod 2)
    (f : F → ZMod 2)
    (hbal : ∑ x : F, (if (f x).val = 0 then (1 : ℤ) else -1) = 0) :
    8 * tripleCount F Tr f =
    (Fintype.card F : ℤ) ^ 2 - tripleCorrelation F f := by
  have h_triple_count : tripleCount F Tr f = (∑ x : F, ∑ y : F, ((1 - (if (f x).val = 0 then (1 : ℤ) else -1)) * (1 - (if (f y).val = 0 then (1 : ℤ) else -1)) * (1 - (if (f (x + y)).val = 0 then (1 : ℤ) else -1)))) / 8 := by
    rw [ Int.ediv_eq_of_eq_mul_left ] <;> norm_num;
    rw [ show tripleCount F Tr f = ∑ x : F, ∑ y : F, if ( f x ).val = 1 ∧ ( f y ).val = 1 ∧ ( f ( x + y ) ).val = 1 then 1 else 0 from rfl ] ; rw [ Finset.sum_mul ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Finset.sum_mul ] ; refine' Finset.sum_congr rfl fun y hy => _ ; rcases f x with ( _ | _ | x ) <;> rcases f y with ( _ | _ | y ) <;> rcases f ( x + y ) with ( _ | _ | z ) <;> norm_cast;
  have h_expand : ∀ (ε : F → ℤ), (∑ x : F, ε x) = 0 → 8 * (∑ x : F, ∑ y : F, ((1 - ε x) * (1 - ε y) * (1 - ε (x + y)))) / 8 = (Fintype.card F : ℤ) ^ 2 - ∑ x : F, ∑ y : F, (ε x * ε y * ε (x + y)) := by
    intro ε hε
    simp [mul_sub, sub_mul, pow_two];
    rw [ Int.ediv_eq_of_eq_mul_left ] <;> norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hε ];
    have h_sum_zero : ∀ x : F, ∑ y : F, ε (x + y) = ∑ y : F, ε y := by
      exact fun x => Equiv.sum_comp ( Equiv.addLeft x ) ε;
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc ];
    rw [ Finset.sum_comm ] ; simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hε, h_sum_zero ] ; ring;
    simp_all +decide [ add_comm ];
  convert h_expand _ hbal using 1;
  rw [ h_triple_count, Int.mul_ediv_assoc ];
  refine' Finset.dvd_sum fun x _ => Finset.dvd_sum fun y _ => _;
  split_ifs <;> norm_num

/-! ## The Corrected Main Theorem -/

/-
**The P₃ Triple Count for Almost Bent Functions (Corrected).**

For an Almost Bent function f : GF(2^n) → GF(2) with n odd, n ≥ 3:
- f(0) = 0
- f is balanced (W_f(0) = 0)
- Walsh spectrum {0, ±2^{(n+1)/2}}

The triple count T₃ = #{(x,y) : f(x) = f(y) = f(x+y) = 1} is:

    T₃ = 2^{2n-3} - 2^{n-2}

Proof:
1. 8·T₃ = |F|² - C₃
2. |F|·C₃ = ∑W(a)³
3. ∑W(a)³ = 2^{2n+1}
4. C₃ = 2^{n+1}, so 8·T₃ = 2^{2n} - 2^{n+1}, hence T₃ = 2^{2n-3} - 2^{n-2}
-/
theorem p3_triple_count_corrected
    (n : ℕ) (hn : 3 ≤ n) (hn_odd : Odd n)
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (hcard : Fintype.card F = 2 ^ n)
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_zero : Tr 0 = 0)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (f : F → ZMod 2)
    (hAB : IsAlmostBent F Tr f ((n + 1) / 2))
    (hf0 : f 0 = 0)
    (hbal : walshTransform F Tr f 0 = 0) :
    tripleCount F Tr f = (2 : ℤ) ^ (2 * n - 3) - (2 : ℤ) ^ (n - 2) := by
  -- From the hypotheses and previously proven theorems:
  have hcor : tripleCorrelation F f = (2 : ℤ) ^ (n + 1) := by
    have hcor : (Fintype.card F : ℤ) * tripleCorrelation F f = (2 : ℤ) ^ (2 * n + 1) := by
      rw [ triple_correlation_eq_walsh_cubes F Tr hTr_add hTr_zero hTr_sep f, ab_walsh_cube_sum n hn hn_odd F hcard Tr hTr_add hTr_zero hTr_sep f hf0 hAB ];
    simp_all +decide [ pow_add, pow_mul' ];
    nlinarith [ pow_pos ( zero_lt_two' ℤ ) n ];
  have htriple : 8 * tripleCount F Tr f = (2 : ℤ) ^ (2 * n) - (2 : ℤ) ^ (n + 1) := by
    convert triple_count_balanced_expansion F Tr f _ using 1;
    · simp +decide [ hcard, hcor, pow_mul' ];
    · unfold walshTransform at hbal; aesop;
  rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
  omega

end