import Mathlib

/-!
# Layer T1: Trace Form Nondegeneracy

This module establishes that the absolute trace `Tr : GF(2^n) → GF(2)` induces a
nondegenerate GF(2)-bilinear form `(x, y) ↦ Tr(x · y)` on GF(2^n).

## Mathematical content

- **Trace definition**: `Tr(x) = x + x^2 + x^4 + ⋯ + x^{2^{n-1}}` (Frobenius sum over GF(2))
- **GF(2)-linearity**: `Tr(x + y) = Tr(x) + Tr(y)`
- **Surjectivity**: `Tr` is surjective (not identically zero)
- **Nondegeneracy**: `(∀ y, Tr(x · y) = 0) → x = 0`
- **Kernel dimension**: `ker(Tr) = 2^{n-1}`

## DAG Dependencies

- Mathlib (finite field theory, Frobenius endomorphism)

## Downstream consumers

- `AdjointMap` (adjoint existence requires nondegeneracy)
- `AdjointTransfer` (transfer theorem uses trace duality)
- `MCMBridge` (final application)
-/

namespace AdjointTransfer

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The absolute trace map `Tr_n : F → F`, defined as the Frobenius sum
    `Tr_n(x) = ∑_{i=0}^{n-1} x^{2^i}`.
    In char 2, this takes values in GF(2) = {0, 1} ⊆ F. -/
def Tr_n (n : ℕ) (x : F) : F := ∑ i ∈ Finset.range n, x ^ (2 ^ i)

/-- Trace is GF(2)-linear (additive in char 2). -/
lemma Tr_n_add (n : ℕ) (x y : F) : Tr_n (F := F) n (x + y) = Tr_n n x + Tr_n n y := by
  simp only [Tr_n, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_expChar_pow x y 2 i

/-- Trace of zero is zero. -/
lemma Tr_n_zero (n : ℕ) : Tr_n n (0 : F) = 0 := by
  simp [Tr_n, zero_pow (pow_ne_zero _ two_ne_zero)]

/-
Trace is Frobenius-fixed: `Tr_n(x)^2 = Tr_n(x)`, so `Tr_n(x) ∈ GF(2)`.

    **Proof sketch**: `(∑ x^{2^i})^2 = ∑ x^{2^{i+1}}` by char 2 linearity.
    This is a cyclic shift of the sum; the extra term `x^{2^n} = x` replaces
    the missing `x^1` term, so the sum is unchanged.
-/
lemma Tr_n_sq {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    Tr_n n x ^ 2 = Tr_n n x := by
  -- By Fermat's Little Theorem, we know that $x^{2^n} = x$ for any $x \in F$.
  have h_fermat : x ^ (2 ^ n) = x := by
    rw [ ← hn, FiniteField.pow_card ];
  -- By the properties of finite fields, we know that $(\sum_{i=0}^{n-1} x^{2^i})^2 = \sum_{i=0}^{n-1} x^{2^{i+1}}$.
  have h_sum_sq : (∑ i ∈ Finset.range n, x ^ (2 ^ i)) ^ 2 = ∑ i ∈ Finset.range n, x ^ (2 ^ (i + 1)) := by
    induction' ( Finset.range n ) using Finset.induction <;> simp_all +decide [ pow_succ, pow_mul, Finset.sum_range_succ ];
    grind +ring;
  rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ, pow_mul ];
  · exact absurd hn ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
  · convert h_sum_sq using 1;
    convert Finset.sum_range_succ' ( fun i => x ^ 2 ^ i ) n using 1 ; simp +decide [ *, pow_succ, pow_mul ];
    simp +decide [ Finset.sum_range_succ, h_fermat ]

/-
Trace takes values in {0, 1}.
-/
lemma Tr_n_mem_GF2 {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    Tr_n n x = 0 ∨ Tr_n n x = 1 := by
  have h := Tr_n_sq hn x;
  exact or_iff_not_imp_left.mpr fun hx => mul_left_cancel₀ hx <| by linear_combination' h;

/-
Trace is surjective onto GF(2) (i.e., there exists x with Tr_n(x) = 1).

    **Proof sketch**: The polynomial `∑ X^{2^i}` has degree `2^{n-1} < 2^n = |F|`,
    so it cannot vanish on all of F. Since it takes values in {0,1},
    it must hit 1 somewhere.
-/
lemma Tr_n_surjective {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n) :
    ∃ x : F, Tr_n n x = 1 := by
  by_contra! h_contra;
  -- Consider the polynomial $P(X) = \sum_{i=0}^{n-1} X^{2^i}$.
  set P : Polynomial F := Finset.sum (Finset.range n) (fun i => Polynomial.X ^ (2 ^ i)) with hP_def

  -- Since $P(x) = 0$ for all $x \in F$, $P$ has at most $2^{n-1}$ roots.
  have hP_roots : (Finset.image (fun x : F => x) (Finset.univ : Finset F)).card ≤ P.natDegree := by
    have hP_roots : (Finset.image (fun x : F => x) (Finset.univ : Finset F)) ⊆ Multiset.toFinset (Polynomial.roots P) := by
      intro x hx
      simp [hP_def] at hx
      have h_eval : P.eval x = 0 := by
        simp +zetaDelta at *;
        simp +decide [ Polynomial.eval_finset_sum ];
        exact Or.resolve_right ( Tr_n_mem_GF2 hn x ) ( h_contra x )
      exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots ( show P ≠ 0 from by
                                                                refine' ne_of_apply_ne ( fun p => p.coeff ( 2 ^ ( n - 1 ) ) ) _ ; simp +decide [ Polynomial.coeff_X_pow, Finset.sum_range_succ ] ; aesop; ) |>.2 h_eval );
    exact le_trans ( Finset.card_le_card hP_roots ) ( le_trans ( Multiset.toFinset_card_le _ ) ( Polynomial.card_roots' _ ) );
  rw [ Polynomial.natDegree_sum_eq_of_disjoint ] at hP_roots <;> simp_all +decide [ Polynomial.natDegree_X_pow ];
  · exact hP_roots.elim fun b hb => not_lt_of_ge hb.2 ( pow_lt_pow_right₀ ( by decide ) hb.1 );
  · intro i hi j hj hij; simp_all +decide [ Polynomial.natDegree_X_pow ] ;

/-
The trace bilinear form `B(x, y) = Tr_n(x · y)` is nondegenerate:
    if `Tr_n(x · y) = 0` for all `y`, then `x = 0`.

    **Proof sketch**: The map `y ↦ Tr_n(x · y)` is GF(2)-linear.
    If it vanishes identically, then `x · F ⊆ ker(Tr_n)`.
    But `|ker(Tr_n)| = 2^{n-1}` and `|x · F| = |F| = 2^n` for `x ≠ 0`,
    so `x · F ⊄ ker(Tr_n)`, contradiction.
-/
theorem trace_bilinear_nondegenerate {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hn_pos : 0 < n)
    {x : F} (h : ∀ y : F, Tr_n n (x * y) = 0) : x = 0 := by
  contrapose! h;
  -- By Tr_n_surjective �,� there exists z with Tr_n(z) = 1.
  obtain ⟨z, hz⟩ : ∃ z : F, Tr_n n z = 1 := by
    -- By Tr_n_surjective, there exists z with Tr_n(z) = 1.
    apply Tr_n_surjective hn hn_pos;
  exact ⟨ z / x, by rw [ mul_div_cancel₀ _ h ] ; aesop ⟩

/-- The trace bilinear form is symmetric: `Tr_n(x · y) = Tr_n(y · x)`. -/
lemma Tr_n_mul_comm (n : ℕ) (x y : F) :
    Tr_n n (x * y) = Tr_n n (y * x) := by
  rw [mul_comm]

/-
The kernel of Tr_n has cardinality `2^{n-1}`.

    **Proof sketch**: `Tr_n` is a GF(2)-linear map `F → GF(2)`.
    It is surjective (by `Tr_n_surjective`), so
    `|ker(Tr_n)| = |F|/|GF(2)| = 2^n/2 = 2^{n-1}`.
-/
lemma Tr_n_kernel_card {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n) :
    Fintype.card { x : F // Tr_n n x = 0 } = 2 ^ (n - 1) := by
  -- By Tr_n_surjective, � there� exists x such that Tr_n(x) = 1. Then (ker(Tr_n) + x) is the preimage of 1, so |ker(Tr_n)| = |F|/2 = 2^{n-1}.
  obtain ⟨x, hx⟩ : ∃ x : F, Tr_n n x = 1 := by
    exact?;
  -- Since the map $y \mapsto Tr_n(y \cdot z)$ is GF(2)-linear, the preimage of 0 under this map is the kernel of the map.
  have h_preimage : Finset.filter (fun y => Tr_n n y = 0) Finset.univ = Finset.image (fun y => y - x) (Finset.filter (fun y => Tr_n n y = 1) Finset.univ) := by
    ext y; simp [hx];
    have := Tr_n_add n y x; aesop;
  -- Since the map $y \mapsto Tr_n(y \cdot z)$ is GF(2)-linear, the preimage of 1 under this map is the coset of the kernel.
  have h_preimage_one : Finset.filter (fun y => Tr_n n y = 1) Finset.univ = Finset.image (fun y => y + x) (Finset.filter (fun y => Tr_n n y = 0) Finset.univ) := by
    simp_all +decide [ Finset.ext_iff ];
    grind;
  -- Since the map $y \mapsto Tr_n(y \cdot z)$ is GF(2)-linear, the preimage of 0 under this map is the kernel of the map, and the preimage of 1 under this map is the coset of the kernel.
  have h_card : Fintype.card { y : F | Tr_n n y = 0 } + Fintype.card { y : F | Tr_n n y = 1 } = Fintype.card F := by
    rw [ Fintype.card_subtype, Fintype.card_subtype ];
    rw [ Fintype.card_eq_sum_ones, Finset.card_filter, Finset.card_filter ];
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ] ; simp +decide [ Tr_n_mem_GF2 hn ];
    intro y; rcases Tr_n_mem_GF2 hn y with h | h <;> simp +decide [ h ] ;
  -- Since the map $y \mapsto Tr_n(y \cdot z)$ is GF(2)-linear, the preimage of 0 under this map is the kernel of the map, and the preimage of 1 under this map is the coset of the kernel. Therefore, the cardinalities of these sets are equal.
  have h_card_eq : Fintype.card { y : F | Tr_n n y = 0 } = Fintype.card { y : F | Tr_n n y = 1 } := by
    rw [ Fintype.card_subtype, Fintype.card_subtype ] at *;
    grind +splitIndPred;
  cases n <;> simp +decide [ pow_succ' ] at * ; linarith!

/-
Trace is invariant under all Frobenius powers: `Tr_n(x^{2^j}) = Tr_n(x)`.

    **Proof sketch**: The Frobenius `x ↦ x^{2^j}` permutes the terms of the sum
    `∑ x^{2^i}` cyclically (using `x^{2^n} = x`), hence the sum is unchanged.
-/
lemma Tr_n_frob_pow {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) (j : ℕ) :
    Tr_n n (x ^ (2 ^ j)) = Tr_n n x := by
  by_contra! h_contra;
  -- By definition of exponentiation in a finite field, we know that $x^{2^n} = x$.
  have h_exp : x ^ (2 ^ n) = x := by
    rw [ ← hn, FiniteField.pow_card ];
  refine' h_contra ( Finset.sum_bij ( fun i _ => ( j + i ) % n ) _ _ _ _ );
  · exact fun i hi => Finset.mem_range.mpr ( Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
  · intro a₁ ha₁ a₂ ha₂ h; have := Nat.modEq_iff_dvd.1 h.symm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    obtain ⟨ k, hk ⟩ := this; nlinarith [ show k = 0 by nlinarith [ Finset.mem_range.mp ha₁, Finset.mem_range.mp ha₂ ] ] ;
  · intro b hb
    use (b + n - j % n) % n;
    simp +decide [ Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop_cat : n ≠ 0 ) ) ];
    simp +decide [ add_tsub_assoc_of_le ( show j % n ≤ b + n from le_trans ( Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop_cat ) ) |> Nat.le_of_lt ) ( Nat.le_add_left _ _ ) ), Nat.add_mod, Nat.mod_eq_of_lt ( Finset.mem_range.mp hb ) ];
    simp +decide [ add_tsub_cancel_of_le ( show j % n ≤ b + n from le_trans ( Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop_cat ) ) |> Nat.le_of_lt ) ( Nat.le_add_left _ _ ) ), Nat.mod_eq_of_lt ( Finset.mem_range.mp hb ) ];
  · intro i hi; rw [ ← pow_mul, ← pow_add ] ;
    rw [ ← Nat.mod_add_div ( j + i ) n ] ; simp_all +decide [ pow_add, pow_mul ] ;
    induction' ( j + i ) / n with k hk <;> simp_all +decide [ pow_succ, pow_mul ];
    rw [ pow_right_comm, h_exp ]

/-- Trace commutes with Frobenius: `Tr_n(x^2) = Tr_n(x)`. -/
lemma Tr_n_frob {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    Tr_n n (x ^ 2) = Tr_n n x :=
  Tr_n_frob_pow hn x 1

end AdjointTransfer