import Mathlib
import ConjecturesMTupleTripleCount.APN.Defs
import ConjecturesMTupleTripleCount.Walsh.Moments

/-!
# Walsh Transform and Almost Bent (AB) Functions

## Mathematical Background

A function `f : F → F` over `GF(2ⁿ)` is **Almost Bent (AB)** if the Walsh
transform `W_f(a,b) = Σ_x (-1)^{Tr(ax + bf(x))}` satisfies
`|W_f(a,b)|² ∈ {0, 2^{n+1}}` for all `a ≠ 0`.

### Key Theorem (Nyberg 1994)
For power functions `f(x) = x^d` on `GF(2ⁿ)` with n odd: **APN ⟺ AB**.

### Categorical Perspective (Morita / Caramello Bridge)
The APN ⟺ AB equivalence is mediated by the **Pontryagin self-duality** of
`(F, +)` via the trace pairing. This is an instance of **Morita equivalence**:

- The additive group `(F, +)` and its character group `F̂` are isomorphic
  via the trace pairing `⟨x, y⟩ = (-1)^{Tr(xy)}`
- This establishes `Mod-F₂[F] ≃ Mod-F₂[F̂]` (Morita equivalence)
- APN is a property of the **differential** (primal side)
- AB is a property of the **Walsh spectrum** (dual side)
- The **Parseval-Plancherel isomorphism** is the bridge between them

In Mathlib's `CategoryTheory`, this self-duality is the finite abelian group
analog of `CategoryTheory.Abelian.yonedaFunctor` — the Yoneda embedding
restricted to the additive category, combined with the character orthogonality
relations `AddChar.sum_eq_ite` (Schur's lemma) and
`AddChar.sum_apply_eq_ite` (Pontryagin duality).

### Proof Architecture for APN ⟹ AB (Moment Method)

The proof uses a beautiful **integer lattice argument**:

1. **Parseval** (Plancherel): `Σ W² = q²`
2. **Fourth moment** (Caramello bridge): `Σ W⁴ = 2q³`
3. **Divisibility** (Stickelberger/Gauss): `2^{(n+1)/2} ∣ W`

Write `W = 2^{(n+1)/2} · k` with `k ∈ ℤ`. Then:
- From (1): `Σ k² = 2^{n-1}`
- From (2): `Σ k⁴ = 2^{n-1}`
- So `Σ k⁴ = Σ k²`, hence `Σ k²(k²-1) = 0`
- Since `k²(k²-1) ≥ 0` for integers, each `k² ∈ {0, 1}`
- Therefore `W² = 2^{n+1} · k² ∈ {0, 2^{n+1}}` — **AB!**
-/

set_option maxHeartbeats 1600000

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
Frobenius invariance of χ: χ(x²) = χ(x).
This follows from `Tr(x²) = Tr(x)` since the Frobenius
is a Galois automorphism and Tr is Galois-invariant.
-/
theorem χ_sq_eq (x : F) : χ (x ^ 2) = χ x := by
  -- Since Tr is linear, we have Tr(x^2) = Tr(x).
  have h_tr_sq : Tr (x ^ 2) = Tr x := by
    convert Algebra.trace_eq_of_algEquiv _ _;
    swap;
    constructor;
    case convert_9.toEquiv => exact Equiv.ofBijective ( fun x => x ^ 2 ) ⟨ fun x y hxy => by
      grind, fun x => by
      have h_frobenius_surjective : Function.Surjective (fun x : F => x ^ 2) := by
        exact Finite.injective_iff_surjective.mp ( fun x y hxy => by simpa [ sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq ] using hxy );
      exact h_frobenius_surjective x ⟩;
    all_goals norm_num [ mul_pow, add_sq ];
    · exact fun x y => Or.inl <| Or.inl <| CharP.cast_eq_zero F 2;
    · exact fun r => by fin_cases r <;> simp +decide ;
  simp only [χ, h_tr_sq]

/-
Power function scaling: W(a·t, b·t^d) = W(a, b).
The multiplicative group acts on Walsh coefficients via scaling.
-/
theorem walsh_pow_scaling (d : ℕ) (a b t : F) (ht : t ≠ 0) :
    walsh (· ^ d) (a * t) (b * t ^ d) = walsh (· ^ d) a b := by
  -- By changing variables $y = t * x$, we can rewrite the sum.
  have h_change_var : ∑ x : F, χ (a * t * x + b * t ^ d * x ^ d) = ∑ y : F, χ (a * y + b * y ^ d) := by
    have h_bij : Function.Bijective (fun x : F => t * x) := by
      exact ⟨ mul_right_injective₀ ht, mul_left_surjective₀ ht ⟩
    conv_rhs => rw [ ← Equiv.sum_comp ( Equiv.ofBijective _ h_bij ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    exact Finset.sum_congr rfl fun _ _ => by ring;
  exact h_change_var

/-
Frobenius invariance: W(1, c²) = W(1, c).
The Walsh spectrum is constant on Frobenius orbits.
-/
theorem walsh_pow_frob_inv (d : ℕ) (c : F) :
    walsh (· ^ d) 1 (c ^ 2) = walsh (· ^ d) 1 c := by
  -- Since squaring is a bijection in characteristic 2, we can replace $x$ with $y^2$ in the sum.
  have h_bij : ∑ x : F, χ (x + c ^ 2 * x ^ d) = ∑ y : F, χ (y ^ 2 + c ^ 2 * (y ^ 2) ^ d) := by
    have h_bij : Function.Bijective (fun y : F => y ^ 2) := by
      exact ⟨ fun x y hxy => by simpa [ sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq ] using hxy, Finite.injective_iff_surjective.mp ( fun x y hxy => by simpa [ sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq ] using hxy ) ⟩;
    conv_lhs => rw [ ← Equiv.sum_comp ( Equiv.ofBijective _ h_bij ) ] ;
    rfl;
  -- By the properties of the trace, we know that $\chi(y^2 + c^2 \cdot (y^2)^d) = \chi((y + c \cdot y^d)^2)$.
  have h_trace : ∀ y : F, χ (y ^ 2 + c ^ 2 * (y ^ 2) ^ d) = χ ((y + c * y ^ d) ^ 2) := by
    intro y; ring;
    simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ];
  -- By the properties of the trace, we know that $\chi((y + c \cdot y^d)^2) = \chi(y + c \cdot y^d)$.
  have h_trace_sq : ∀ y : F, χ ((y + c * y ^ d) ^ 2) = χ (y + c * y ^ d) := by
    grind +suggestions;
  unfold walsh; aesop;

/-! ## Layer 9: The Integer Lattice Argument for AB

This is the elegant **moment method** proof. The key algebraic fact:

If `Σ k² = Σ k⁴` for non-negative integer terms `k²`, then
`Σ k²(k²-1) = 0`, forcing each `k² ∈ {0, 1}`.

This is a consequence of `k²(k²-1) ≥ 0` for all integers `k`.
-/

/-- For integers: k²(k²-1) ≥ 0. Used in the AB deduction. -/
theorem sq_mul_sq_sub_one_nonneg (k : ℤ) : 0 ≤ k ^ 2 * (k ^ 2 - 1) := by
  nlinarith [sq_nonneg k, sq_nonneg (k ^ 2 - 1)]

/-
If Σ k² = Σ k⁴ (over a finset) and all are integers, then k² ∈ {0,1}.
-/
theorem eq_zero_or_one_of_sum_sq_eq_sum_fourth
    {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (h : ∑ i ∈ s, k i ^ 4 = ∑ i ∈ s, k i ^ 2) :
    ∀ i ∈ s, k i ^ 2 = 0 ∨ k i ^ 2 = 1 := by
  intro i hi;
  contrapose! h;
  refine' ne_of_gt ( Finset.sum_lt_sum _ _ );
  · exact fun i _ => by nlinarith [ sq_nonneg ( k i ^ 2 - 1 ) ] ;
  · exact ⟨ i, hi, by cases lt_or_gt_of_ne h.1 <;> cases lt_or_gt_of_ne h.2 <;> nlinarith [ sq_nonneg ( k i ^ 2 - 1 ) ] ⟩

/-
Walsh coefficients are even (|F| = 2ⁿ is even, and W is a sum of ±1).
-/
theorem walsh_even (f : F → F) (a b : F) : 2 ∣ walsh f a b := by
  have h_even : ∑ x : F, (if Tr (a * x + b * f x) = 0 then 1 else -1) ≡ 0 [ZMOD 2] := by
    simp +decide [ Int.modEq_zero_iff_dvd, Finset.sum_ite ];
    simp +decide [ ← even_iff_two_dvd, parity_simps ];
    simp +decide [ Finset.filter_not, Finset.card_sdiff ];
    rw [ Nat.even_sub ( Finset.card_le_univ _ ) ];
    have h_card : Fintype.card F = 2 ^ (Module.finrank (ZMod 2) F) := by
      have h_card : Fintype.card F = Fintype.card (Fin (Module.finrank (ZMod 2) F) → ZMod 2) := by
        exact Fintype.card_congr ( ( Module.finBasis ( ZMod 2 ) F ).equivFun );
      aesop;
    rcases k : Module.finrank ( ZMod 2 ) F with ( _ | _ | k ) <;> simp_all +decide [ Nat.even_pow ];
    exact absurd h_card ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
  convert Int.dvd_of_emod_eq_zero h_even using 1

/-! ## Layer 10: AB Deduction from Moments + Divisibility

The clean algebraic argument: divisibility forces Walsh values
onto an integer lattice, and the moment constraints pin them down.
-/

/-
**AB from moments**: The integer lattice argument.
Given Parseval, fourth moment, and divisibility, the function is AB.

This is the **Caramello bridge theorem**: the Morita equivalence
between primal (differential) and dual (spectral) theories,
combined with integrality constraints from the Galois action,
forces the spectral values onto a rank-1 lattice.
-/
theorem ab_from_moments {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hodd : Odd n) (hn : n ≥ 1)
    (hparseval : ∀ a, a ≠ 0 →
      ∑ b : F, walsh f a b ^ 2 = (Fintype.card F : ℤ) ^ 2)
    (hfourth : ∀ a, a ≠ 0 →
      ∑ b : F, walsh f a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3)
    (hdiv : ∀ a b, (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh f a b) :
    IsAB hcard f := by
  intro a ha b;
  -- Write W(a,b) = � �2^{(n+1)/2} · k_b for integers k_b (from hdiv).
  obtain ⟨k, hk⟩ : ∃ k : F → ℤ, ∀ b, walsh f a b = 2 ^ ((n + 1) / 2) * k b := by
    exact ⟨ fun b => Classical.choose ( hdiv a b ), fun b => Classical.choose_spec ( hdiv a b ) ⟩;
  -- Then: k_b �²� = 2^{n-1} (from Parseval) and k �_b = 2^{n-1} (from fourth moment).
  have hsum_sq : ∑ b, k b ^ 2 = 2 ^ (n - 1) := by
    have := hparseval a ha; simp_all +decide [ mul_pow, Finset.mul_sum _ _ _ ] ;
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.mul_sum _ _ _ ] at this; simp_all +decide [ ← mul_assoc, ← pow_mul' ] ;
    rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ];
    · exact mul_left_cancel₀ ( pow_ne_zero ( 2 * ( c + 1 ) ) two_ne_zero ) ( by ring_nf at *; linarith );
    · exact absurd hodd ( by simp +decide [ parity_simps ] )
  have hsum_fourth : ∑ b, k b ^ 4 = 2 ^ (n - 1) := by
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.pow_succ', mul_pow ];
    have := hfourth a ha; simp_all +decide [ mul_pow, Finset.mul_sum _ _ _ ] ;
    rw [ ← Finset.mul_sum _ _ _ ] at this; rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ] ; ring_nf at *;
    · exact mul_left_cancel₀ ( pow_ne_zero ( c * 4 ) two_ne_zero ) ( by ring_nf at *; linarith );
    · exact absurd hodd ( by simp +decide [ parity_simps ] );
  -- So k_b⁴ = k_b², hence by eq_zero_or_one_of_sum_sq_eq_sum_four �th�, k_b² ∈ {0,1}.
  have h_k_sq : ∀ b, k b ^ 2 = 0 ∨ k b ^ 2 = 1 := by
    convert eq_zero_or_one_of_sum_sq_eq_sum_fourth Finset.univ k _ using 1;
    · simp +decide;
    · rw [hsum_fourth, hsum_sq];
  cases h_k_sq b <;> simp +decide [ *, mul_pow ];
  rw [ ← pow_mul, Nat.div_mul_cancel ( even_iff_two_dvd.mp ( by simpa [ parity_simps ] using hodd ) ) ]

end WalshAB