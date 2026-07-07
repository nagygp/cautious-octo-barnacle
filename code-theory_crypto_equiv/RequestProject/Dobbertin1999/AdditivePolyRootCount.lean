import Mathlib

/-!
# Additive (𝔽₂-linearized) polynomial root count — Layer A (upstreamable)

This module is **Layer A** of the full-paper roadmap
([`DOBBERTIN1999_FULL_ROADMAP.md`](../../DOBBERTIN1999_FULL_ROADMAP.md)) for
Dobbertin (1999), *"Kasami Power Functions, Permutation Polynomials and Cyclic
Difference Sets"*.

A **linearized** (a.k.a. *additive*) polynomial over a field of characteristic
two is a sum `Σ_i a_i · x^{2^i}`.  Because `x ↦ x^{2^i}` is the `i`-fold Frobenius
(additive in characteristic two), such a map is an additive group homomorphism
`F →+ F`.  Consequently the solution set of a linearized equation `L(x) = c` is
either empty or a coset of `ker L`, so the number of solutions is `0` or
`#(ker L)` — always a power of two over `𝔽_{2ⁿ}`.

This is exactly the counting tool Dobbertin's **Theorem 1** uses to decide, for
the linearized polynomial `ℓ(x) = c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x + 1`
(paper eq. (2)), how many solutions the permutation criterion produces.

Everything here is generic finite-field / additive-group algebra: no Kasami-
specific input, so the module is a clean candidate for upstreaming to Mathlib
(Mathlib provides `AddMonoidHom.fiberEquivKer` but no packaged linearized-
polynomial root count).

## Main definitions

* `linearizedHom a m` — the linearized polynomial `x ↦ Σ_{i<m} a i · x^{2^i}`
  packaged as an `AddMonoidHom F F`.

## Main results

* `linearizedHom_apply` — its underlying function.
* `card_fiber_linearized` — the fibre count of `L(x) = c` is `0` or `#(ker L)`.
* `card_fiber_affine_linearized` — the affine version: the count of
  `Σ_{i<m} a i · x^{2^i} + b = 0` is `0` or `#(ker L)`.
-/

namespace Dobbertin1999.AdditivePolyRootCount

open Finset

variable {F : Type*} [CommRing F] [CharP F 2]

/-- The **linearized (additive) polynomial map** `x ↦ Σ_{i<m} a i · x^{2^i}`,
packaged as an additive group homomorphism `F →+ F`.  It is additive precisely
because `x ↦ x^{2^i}` is the `i`-fold Frobenius endomorphism in characteristic
two. -/
def linearizedHom (a : ℕ → F) (m : ℕ) : F →+ F where
  toFun x := ∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)
  map_zero' := by
    apply Finset.sum_eq_zero
    intro i _
    simp [zero_pow (pow_pos (show (0 : ℕ) < 2 by norm_num) i).ne']
  map_add' x y := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_pow_char_pow (p := 2), mul_add]

@[simp] lemma linearizedHom_apply (a : ℕ → F) (m : ℕ) (x : F) :
    linearizedHom a m x = ∑ i ∈ Finset.range m, a i * x ^ (2 ^ i) := rfl

variable [Fintype F] [DecidableEq F]

/-
**Root count of a linearized equation.**  The number of solutions of
`Σ_{i<m} a i · x^{2^i} = c` is either `0` (no solution) or `#(ker L)`, the number
of solutions of the associated homogeneous equation.  This is the finite-field
"either no or exactly `2^r`" counting principle behind Dobbertin's permutation
criterion (Theorem 1).
-/
theorem card_fiber_linearized (a : ℕ → F) (m : ℕ) (c : F) :
    Nat.card {x : F // (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) = c} = 0 ∨
    Nat.card {x : F // (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) = c} =
      Nat.card {x : F // (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) = 0} := by
  by_contra! h_contra;
  -- By definition of `linearizedHom`, the set of solutions to `∑ i ∈ range m, a i * x^(2^i) = c` is a coset of the kernel of `linearizedHom a m`.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, ∑ i ∈ Finset.range m, a i * x₀ ^ (2 ^ i) = c := by
    exact not_forall_not.mp fun h => h_contra.1 <| by rw [ Nat.card_eq_zero ] ; aesop;
  refine' h_contra.2 _;
  rw [ ← hx₀ ];
  convert Nat.card_congr ( AddMonoidHom.fiberEquivKer ( linearizedHom a m ) x₀ ) using 1

/-
**Root count of an affine-linearized equation.**  The number of solutions of
`Σ_{i<m} a i · x^{2^i} + b = 0` is `0` or `#(ker L)`.  This is the exact shape of
Dobbertin's eq. (2), where the constant term is the paper's `+1`.
-/
theorem card_fiber_affine_linearized (a : ℕ → F) (m : ℕ) (b : F) :
    Nat.card {x : F // (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) + b = 0} = 0 ∨
    Nat.card {x : F // (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) + b = 0} =
      Nat.card {x : F // (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) = 0} := by
  have h_card : Nat.card {x : F | (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) + b = 0} = Nat.card {x : F | (∑ i ∈ Finset.range m, a i * x ^ (2 ^ i)) = -b} := by
    simp +decide only [add_eq_zero_iff_eq_neg];
  have := card_fiber_linearized a m ( -b ) ; aesop;

/-! ## The two-to-one map `t ↦ t^{2^k} + t`

The specialisation Dobbertin uses in the proof of Corollary 2 (and in Theorem 1):
over `𝔽_{2ⁿ}` with `gcd(k, n) = 1`, the additive map `t ↦ t^{2^k} + t` has a
kernel of size exactly two (the fixed field `𝔽₂`), hence is exactly two-to-one.
-/

section TwoToOne

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Kernel size of `t ↦ t^{2^k} + t`.**  Over `𝔽_{2ⁿ}` with `gcd(k, n) = 1`,
the homogeneous equation `t^{2^k} + t = 0` has exactly two
solutions — the fixed field of the `k`-fold Frobenius is `𝔽₂ = {0, 1}`.  Its
cardinality is `gcd(2^k − 1, 2ⁿ − 1) + 1 = (2^{gcd(k,n)} − 1) + 1 = 2`.
-/
theorem card_frobSubSelf_kernel {n k : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime k n) :
    Nat.card {x : F // x ^ (2 ^ k) + x = 0} = 2 := by
  -- The polynomial $x^{2^k} + x$ has at most $2^k$ roots in $F$.
  have h_roots : (Finset.univ.filter (fun x : F => x ^ (2 ^ k) + x = 0)).card ≤ 2 := by
    -- The polynomial $x^{2^k} + x$ has at most $2^k$ roots in $F$, but since $gcd(k, n) = 1$, the only roots are $0$ and $1$.
    have h_roots : ∀ x : F, x ^ (2 ^ k) + x = 0 → x = 0 ∨ x = 1 := by
      intro x hx; by_cases hx0 : x = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      -- Since $x \neq 0$, we have $x^{2^k - 1} = 1$.
      have hx_pow : x ^ (2 ^ k - 1) = 1 := by
        rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ), pow_add, pow_one ] at hx;
        grind;
      -- Since $x^{2^k - 1} = 1$, we have that the order of $x$ divides both $2^k - 1$ and $2^n - 1$.
      have h_order_divides : orderOf x ∣ 2 ^ k - 1 ∧ orderOf x ∣ 2 ^ n - 1 := by
        exact ⟨ orderOf_dvd_iff_pow_eq_one.mpr hx_pow, orderOf_dvd_iff_pow_eq_one.mpr ( by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx0 ] ) ⟩;
      have := Nat.dvd_gcd h_order_divides.1 h_order_divides.2; simp_all +decide [ Nat.Coprime ] ;
    exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun x : F => x ^ 2 ^ k + x = 0 ) Finset.univ ⊆ { 0, 1 } by intros x hx; aesop ) ) ( Finset.card_insert_le _ _ );
  convert Nat.le_antisymm h_roots _;
  · rw [ Nat.card_eq_fintype_card, Fintype.card_subtype ];
  · refine' Finset.one_lt_card.2 ⟨ 0, _, 1, _, _ ⟩ <;> simp +decide [ CharTwo.add_self_eq_zero ]

/-
**`t ↦ t^{2^k} + t` is two-to-one.**  Over `𝔽_{2ⁿ}` with `gcd(k, n) = 1`,
every fibre of `t ↦ t^{2^k} + t` has cardinality `0` or `2`.  This is the
two-to-one collapse in Dobbertin's proof of Corollary 2.
-/
theorem frobSubSelf_two_to_one {n k : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime k n) (c : F) :
    Nat.card {x : F // x ^ (2 ^ k) + x = c} = 0 ∨
    Nat.card {x : F // x ^ (2 ^ k) + x = c} = 2 := by
  by_cases h : ∃ x₀ : F, x₀ ^ 2 ^ k + x₀ = c;
  · obtain ⟨x₀, hx₀⟩ := h
    have h_fiber : {x : F | x ^ (2 ^ k) + x = c} = (fun x => x₀ + x) '' {x : F | x ^ (2 ^ k) + x = 0} := by
      ext x; simp +decide [ ← hx₀, add_pow_char_pow ] ;
      grind +suggestions;
    convert Or.inr ( card_frobSubSelf_kernel hn hcop ) using 1;
    rw [ show { x : F // x ^ 2 ^ k + x = c } = ( { x : F | x ^ 2 ^ k + x = c } : Set F ) from rfl, show { x : F // x ^ 2 ^ k + x = 0 } = ( { x : F | x ^ 2 ^ k + x = 0 } : Set F ) from rfl, h_fiber, Nat.card_image_of_injective ] ; simp +decide [ Function.Injective ];
  · simp_all +decide

end TwoToOne

end Dobbertin1999.AdditivePolyRootCount