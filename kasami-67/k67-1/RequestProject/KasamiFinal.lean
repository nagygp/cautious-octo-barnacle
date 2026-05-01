/-
# KasamiFinal.lean — Final Assembly of the P₃ Triple Count Proof

This file links the verified modules (Defs, TraceNondeg, PolarFormBridge,
KasamiPolarExpansion, WalshP3) into a single logical chain, culminating
in the corrected P₃ triple count theorem for Almost Bent functions.

## Correction Note

The original theorem stated T₃ = 2^{2n-3}. This is **mathematically incorrect**.
A direct computation over GF(2³) with the Kasami exponent d=3 shows T₃ = 6,
not 8 = 2^{2·3-3}. The correct formula for balanced AB functions is:

  T₃ = 2^{2n-3} - 2^{n-2}

which gives T₃ = 8 - 2 = 6 for n=3. ✓

The error in the original formulation was the hypothesis `hTriple`:
  |F|² · T₃ = ∑_{v₁,v₂} W(v₁)·W(v₂)·W(v₁+v₂)
This identity is false. The correct relationship goes through the
expansion (1 - (-1)^f(x))/2 and the triple correlation function.

## Verified Proof Chain (from our library)

1. **Gold polar expansion** (`gold_polar_expand`):
   (x+y)^{2^k+1} + x^{2^k+1} + y^{2^k+1} = x·y^{2^k} + x^{2^k}·y

2. **Trace adjoint** (`trace_adjoint`):
   Tr(u · v^{2^j}) = Tr(u^{2^{n-j}} · v)

3. **Kasami polar expansion** (`kasami_polar_expansion`):
   Tr(a · polar(x,y)) = Tr(x · L_a(y))

4. **Radical = Kernel** (`kasami_radical_eq_kernel`):
   rad(Q_a) = ker(L_a)

5. **Trace non-degeneracy** (`trace_nondegenerate_finiteField`)

6. **Character orthogonality** (`character_orthogonality`):
   For x ≠ 0: ∑_a (-1)^{Tr(ax)} = 0

7. **Parseval's identity** (`walsh_parseval`):
   ∑_a W_f(a)² = |F|²

## New results in this file

8. **Walsh sum evaluation** (`walsh_sum_from_f0`):
   If f(0) = 0 then ∑_a W_f(a) = |F|

9. **AB Walsh cube sum** (`ab_walsh_cube_sum`):
   For balanced AB functions with f(0) = 0: ∑_a W(a)³ = 2^{2n+1}

10. **Triple correlation = Walsh cubes** (`triple_correlation_eq_walsh_cubes`):
    |F| · C₃ = ∑_a W(a)³

11. **Triple count expansion** (`triple_count_balanced_expansion`):
    8 · T₃ = |F|² - C₃  (for balanced functions)

12. **Triple count formula** (`p3_triple_count_corrected`):
    T₃ = 2^{2n-3} - 2^{n-2}
-/
import Mathlib
import RequestProject.Defs
import RequestProject.TraceNondeg
import RequestProject.PolarFormBridge
import RequestProject.KasamiPolarExpansion
import RequestProject.WalshP3

noncomputable section

open scoped BigOperators
open Finset

set_option maxHeartbeats 3200000

/-! ## Step 8: Walsh Sum from f(0) = 0

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
  have h_char_ortho : ∀ x : F, ∑ a : F, (-1 : ℤ) ^ ((Tr (a * x)).val) = if x = 0 then (Fintype.card F : ℤ) else 0 := by
    intro x; split_ifs with hx; simp +decide [ hx ] ;
    · simp +decide [ hTr_zero ];
    · convert character_orthogonality F Tr hTr_add hTr_sep x hx using 1;
      exact Finset.sum_congr rfl fun a _ => by rcases Tr ( a * x ) with ( _ | _ | n ) <;> trivial;
  have h_interchange : ∑ a : F, ∑ x : F, (-1 : ℤ) ^ ((f x + Tr (a * x)).val) = ∑ x : F, ∑ a : F, (-1 : ℤ) ^ ((f x + Tr (a * x)).val) := by
    exact Finset.sum_comm;
  have h_inner_sum : ∀ x : F, ∑ a : F, (-1 : ℤ) ^ ((f x + Tr (a * x)).val) = (-1 : ℤ) ^ ((f x).val) * (if x = 0 then (Fintype.card F : ℤ) else 0) := by
    intro x
    have h_inner_sum : ∑ a : F, (-1 : ℤ) ^ ((f x + Tr (a * x)).val) = (-1 : ℤ) ^ ((f x).val) * ∑ a : F, (-1 : ℤ) ^ ((Tr (a * x)).val) := by
      rw [ Finset.mul_sum _ _ _ ] ; congr ; ext a ; rcases f x with ( _ | _ | fx ) <;> rcases Tr ( a * x ) with ( _ | _ | tx ) <;> norm_cast;
    rw [ h_inner_sum, h_char_ortho ];
  convert h_interchange using 1;
  · refine' Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => _;
    cases Fin.exists_fin_two.mp ⟨ f x + Tr ( a * x ), rfl ⟩ <;> simp +decide [ * ];
  · rw [ Finset.sum_congr rfl fun x hx => h_inner_sum x ] ; aesop

/-! ## Step 9: AB Walsh Cube Sum

For a balanced Almost Bent function with f(0) = 0 over GF(2^n):
  ∑_a W(a)³ = 2^{2n+1}

The proof uses:
- AB spectrum: W(a) ∈ {0, ±s} where s = 2^{(n+1)/2}
- Let N₊ = #{a : W(a) = +s}, N₋ = #{a : W(a) = -s}
- Parseval: (N₊ + N₋) · s² = |F|² → N₊ + N₋ = 2^{n-1}
- Walsh sum: (N₊ - N₋) · s + 0 = |F| → N₊ - N₋ = 2^{(n-1)/2}
  (using W_f(0) = 0 from balanced + hTr_zero)
- ∑W(a)³ = s³(N₊ - N₋) = 2^{3(n+1)/2} · 2^{(n-1)/2} = 2^{2n+1}

Note: the balanced property (W_f(0) = 0) is required here and is
a hypothesis of the main theorem. For the Kasami power function,
this follows from gcd(d, 2^n-1) = 1, i.e., x → x^d is a permutation.
-/

/-- Key algebraic fact: for AB functions, W(a)³ = W(a) · s² for all a.
    This is because W(a) ∈ {0, ±s} implies W(a)² = s² when W(a) ≠ 0. -/
lemma ab_cube_eq_linear_times_sq (w s : ℤ)
    (h : w = 0 ∨ w = s ∨ w = -s) :
    w ^ 3 = w * s ^ 2 := by
  rcases h with rfl | rfl | rfl <;> ring

/-
The AB Walsh cube sum identity.
    For AB functions with f(0) = 0:
    ∑_a W(a)³ = s² · ∑_a W(a) = s² · |F| = 2^{n+1} · 2^n = 2^{2n+1}
    The key insight: W(a)³ = W(a) · s² for AB functions.
-/
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
  -- From `walsh_sum_from_f0` (using hf0): ∑_a W(a) = |F| = 2^n (using hcard).
  have hWalshSum : ∑ a : F, walshTransform F Tr f a = (Fintype.card F : ℤ) := by
    exact?;
  -- From `ab_cube_eq_linear_times_sq` applied to each term, converting ∑W(a)³ to ∑(W(a) · s²) = s² · ∑W(a).
  have hWalshCubeSum : ∑ a : F, walshTransform F Tr f a ^ 3 = (2 ^ ((n + 1) / 2) : ℤ) ^ 2 * ∑ a : F, walshTransform F Tr f a := by
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun x _ => by rcases hAB x with h | h | h <;> rw [ h ] <;> ring;
  cases hn_odd ; simp_all +decide [ Nat.mul_succ, pow_succ' ] ; ring;
  norm_num [ Nat.add_div ] ; ring

/-! ## Step 10: Triple Correlation via Walsh Cubes -/

/-- The triple correlation function. -/
def tripleCorrelation (F : Type*) [Fintype F] [Field F]
    (f : F → ZMod 2) : ℤ :=
  ∑ x : F, ∑ y : F,
    (if (f x).val = 0 then (1 : ℤ) else -1) *
    (if (f y).val = 0 then 1 else -1) *
    (if (f (x + y)).val = 0 then 1 else -1)

theorem triple_correlation_eq_walsh_cubes
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_zero : Tr 0 = 0)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (f : F → ZMod 2) :
    (Fintype.card F : ℤ) * tripleCorrelation F f =
    ∑ a : F, (walshTransform F Tr f a) ^ 3 := by
  have h_fubini : ∑ a : F, (∑ x : F, if (f x + Tr (a * x)).val = 0 then (1 : ℤ) else -1) ^ 3 = ∑ x : F, ∑ y : F, ∑ z : F, (if (f x + Tr (0 * x)).val = 0 then (1 : ℤ) else -1) * (if (f y + Tr (0 * y)).val = 0 then (1 : ℤ) else -1) * (if (f z + Tr (0 * z)).val = 0 then (1 : ℤ) else -1) * ∑ a : F, (if (Tr (a * (x + y + z))).val = 0 then (1 : ℤ) else -1) := by
    have h_fubini : ∀ a : F, (∑ x : F, if (f x + Tr (a * x)).val = 0 then (1 : ℤ) else -1) ^ 3 = ∑ x : F, ∑ y : F, ∑ z : F, (if (f x + Tr (a * x)).val = 0 then (1 : ℤ) else -1) * (if (f y + Tr (a * y)).val = 0 then (1 : ℤ) else -1) * (if (f z + Tr (a * z)).val = 0 then (1 : ℤ) else -1) := by
      simp +decide only [pow_three, Finset.mul_sum _ _ _, sum_mul];
      exact fun a => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
    simp +decide only [h_fubini, Finset.mul_sum _ _ _];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun x _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun y _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun z _ => _ ) ) );
    refine' Finset.sum_congr rfl fun a _ => _;
    rw [ show a * ( x + y + z ) = a * x + a * y + a * z by ring ] ; simp +decide [ *, ZMod.val_add ] ; ring;
    cases Fin.exists_fin_two.mp ⟨ f z, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ f y, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ <;> simp +decide [ * ];
    all_goals cases Fin.exists_fin_two.mp ⟨ Tr ( a * z ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ Tr ( a * y ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ Tr ( a * x ), rfl ⟩ <;> simp +decide [ * ] ;
  have h_inner_sum : ∀ x y z : F, ∑ a : F, (if (Tr (a * (x + y + z))).val = 0 then (1 : ℤ) else -1) = if x + y + z = 0 then (Fintype.card F : ℤ) else 0 := by
    intro x y z; split_ifs with h; simp +decide [ h ] ;
    · exact hTr_zero;
    · convert character_orthogonality F Tr hTr_add hTr_sep ( x + y + z ) h using 1;
  have h_equiv : ∀ x y z : F, x + y + z = 0 ↔ z = x + y := by
    grind;
  convert h_fubini.symm using 1;
  simp +decide only [tripleCorrelation, h_inner_sum, h_equiv];
  simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
  refine' Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => _;
  rw [ Finset.sum_eq_single ( x + y ) ] <;> simp +decide [ hTr_zero ];
  grind

/-! ## Step 11: Triple Count from Correlation (for balanced functions) -/

theorem triple_count_balanced_expansion
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (Tr : F → ZMod 2)
    (f : F → ZMod 2)
    (hbal : ∑ x : F, (if (f x).val = 0 then (1 : ℤ) else -1) = 0) :
    8 * tripleCount F Tr f =
    (Fintype.card F : ℤ) ^ 2 - tripleCorrelation F f := by
  have h_sum_zero : ∑ x : F, ∑ y : F, (1 - (if (f x).val = 0 then 1 else -1)) * (1 - (if (f y).val = 0 then 1 else -1)) * (1 - (if (f (x + y)).val = 0 then 1 else -1)) = 8 * tripleCount F Tr f := by
    have h_tripleCount : ∀ x y : F, (1 - (if (f x).val = 0 then 1 else -1)) * (1 - (if (f y).val = 0 then 1 else -1)) * (1 - (if (f (x + y)).val = 0 then 1 else -1)) = 8 * (if (f x).val = 1 ∧ (f y).val = 1 ∧ (f (x + y)).val = 1 then 1 else 0) := by
      grind;
    simp +decide only [h_tripleCount, tripleCount];
    simp +decide only [Finset.mul_sum _ _ _];
  rw [ ← h_sum_zero, eq_sub_iff_add_eq ];
  unfold tripleCorrelation;
  simp +decide only [mul_sub, sub_mul, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul];
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hbal ] ; ring;
  rw [ show ( ∑ x : F, ∑ y : F, if f ( x + y ) = 0 then 1 else -1 : ℤ ) = ∑ x : F, ∑ y : F, if f y = 0 then 1 else -1 from ?_ ];
  · rw [ show ( ∑ x : F, ∑ y : F, if f ( x + y ) = 0 then if f x = 0 then 1 else -1 else -if f x = 0 then 1 else -1 : ℤ ) = ∑ x : F, ∑ y : F, if f y = 0 then if f x = 0 then 1 else -1 else -if f x = 0 then 1 else -1 from ?_ ];
    · rw [ show ( ∑ x : F, ∑ y : F, if f ( x + y ) = 0 then if f y = 0 then 1 else -1 else -if f y = 0 then 1 else -1 : ℤ ) = ∑ x : F, ∑ y : F, if f y = 0 then if f x = 0 then 1 else -1 else -if f x = 0 then 1 else -1 from ?_ ];
      · simp +decide [ Finset.sum_add_distrib, Finset.sum_ite ] at *;
        grind;
      · rw [ Finset.sum_comm ];
        exact Finset.sum_congr rfl fun _ _ => Equiv.sum_comp ( Equiv.addRight _ ) fun x => if f x = 0 then if f _ = 0 then 1 else -1 else -if f _ = 0 then 1 else -1;
    · exact Finset.sum_congr rfl fun x _ => Equiv.sum_comp ( Equiv.addLeft x ) fun y => if f y = 0 then if f x = 0 then 1 else -1 else -if f x = 0 then 1 else -1;
  · exact Finset.sum_congr rfl fun x _ => Equiv.sum_comp ( Equiv.addLeft x ) fun y => if f y = 0 then 1 else -1

/-! ## The Corrected Main Theorem -/

/-
**The P₃ Triple Count for Almost Bent Functions (Corrected).**

For an Almost Bent function f : GF(2^n) → GF(2) with n odd, n ≥ 3:
- f(0) = 0 (true for power functions f(x) = Tr(x^d))
- f is balanced (W_f(0) = 0; for Kasami, follows from gcd(d, 2^n-1) = 1)
- Walsh spectrum {0, ±2^{(n+1)/2}}

The triple count T₃ = #{(x,y) : f(x) = f(y) = f(x+y) = 1} is:

    T₃ = 2^{2n-3} - 2^{n-2}

Proof chain:
1. 8·T₃ = |F|² - C₃  (`triple_count_balanced_expansion`, from balanced property)
2. |F|·C₃ = ∑W(a)³  (`triple_correlation_eq_walsh_cubes`, from Fourier analysis)
3. ∑W(a)³ = 2^{2n+1}  (`ab_walsh_cube_sum`, from AB spectrum + balanced)
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
    -- The balanced property: f has equal number of 0s and 1s.
    -- For the Kasami function, this follows from x → x^d being a permutation
    -- (since gcd(d, 2^n - 1) = 1) combined with Tr being a balanced linear form.
    (hbal : walshTransform F Tr f 0 = 0) :
    tripleCount F Tr f = (2 : ℤ) ^ (2 * n - 3) - (2 : ℤ) ^ (n - 2) := by
  -- Step 1: Convert the balanced condition to the sum-of-signs form
  have hbal_signs : ∑ x : F, (if (f x).val = 0 then (1 : ℤ) else -1) = 0 := by
    have : walshTransform F Tr f 0 = ∑ x : F, (if (f x).val = 0 then (1 : ℤ) else -1) := by
      simp [walshTransform, hTr_zero, mul_zero]
    linarith
  -- Step 2: 8·T₃ = |F|² - C₃
  have hexp := triple_count_balanced_expansion F Tr f hbal_signs
  -- Step 3: |F|·C₃ = ∑_a W(a)³
  have hcorr := triple_correlation_eq_walsh_cubes F Tr hTr_add hTr_zero hTr_sep f
  -- Step 4: ∑_a W(a)³ = 2^{2n+1}
  have hcube := ab_walsh_cube_sum n hn hn_odd F hcard Tr hTr_add hTr_zero hTr_sep f hf0 hAB
  -- Step 5: Algebraic conclusion
  -- From hcorr and hcube: 2^n · C₃ = 2^{2n+1}, so C₃ = 2^{n+1}
  -- From hexp: 8·T₃ = 2^{2n} - 2^{n+1}
  -- So T₃ = (2^{2n} - 2^{n+1})/8 = 2^{2n-3} - 2^{n-2}
  rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
  have := triple_correlation_eq_walsh_cubes F Tr hTr_add hTr_zero hTr_sep f; simp_all +decide [ pow_succ', mul_assoc ] ;
  nlinarith [ pow_pos ( zero_lt_two' ℤ ) n, pow_mul' 2 2 n ]

/-! ## Summary

### Verified results (zero sorries) from the library:
- `Defs.lean`: Core definitions (`walshTransform`, `IsAlmostBent`, `tripleCount`)
- `TraceNondeg.lean`: Trace non-degeneracy for finite field extensions
- `PolarFormBridge.lean`: Bridge theorem `rad(Q_a) = ker(L_a)`
- `KasamiPolarExpansion.lean`: Gold/Kasami polar expansion identity
- `WalshP3.lean`: Character orthogonality, Parseval's identity

### Proved in this file:
- `walsh_sum_from_f0`: ∑_a W(a) = |F| when f(0)=0  ✅
- `triple_correlation_eq_walsh_cubes`: |F|·C₃ = ∑_a W(a)³  ✅
- `triple_count_balanced_expansion`: 8·T₃ = |F|² - C₃  ✅

### Remaining:
- `ab_walsh_partition`: Partition Walsh sum by spectrum values
- `ab_walsh_cube_sum`: ∑W(a)³ = 2^{2n+1} for balanced AB functions
- `p3_triple_count_corrected`: Final assembly (algebraic, depends on above)

### Original incorrect theorem (from WalshP3.lean):
The original `p3_triple_count` claimed T₃ = 2^{2n-3}, which is false.
The correct formula is T₃ = 2^{2n-3} - 2^{n-2}.
-/

end