import Mathlib
import CodeTheoryCryptoEquiv.CodingTheory.Dual
import CodeTheoryCryptoEquiv.CodingTheory.WeightEnumerator

/-!
# The MacWilliams identity

This module is the headline step of the coding-theory development transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977.

It proves the **MacWilliams identity** (Ch. 5, Thm 1), the transformation law that
relates the weight enumerator of a linear code `C` to that of its dual `Cᗮ`:

`W_{Cᗮ}(X, Y) = (1 / |C|) · W_C(X + (q-1) Y, X - Y)`,

where `q = #F` is the alphabet size.  Following the standard proof via additive
characters / discrete Poisson summation, the identity is established here as an
identity of complex numbers, valid for **all** `X, Y : ℂ`:

`∑_{v ∈ Cᗮ} X^{n - wt v} Y^{wt v}
   = (1/|C|) · ∑_{u ∈ C} (X + (q-1) Y)^{n - wt u} (X - Y)^{wt u}`.

(Since this holds for every complex substitution, it is exactly the bivariate
polynomial identity of the book.)

## Proof outline

Let `ψ : AddChar F ℂ` be a primitive additive character of the finite field `F`
(`AddChar.FiniteField.primitiveChar_to_Complex`).  For `f : (ι → F) → ℂ` define the
Fourier transform `f̂(u) = ∑_v ψ(⟨u, v⟩) f(v)` with `⟨u, v⟩ = ∑_i u_i v_i`.

* **Poisson summation over a subspace.**  `∑_{u ∈ C} ψ(⟨u, v⟩) = |C|` if
  `v ∈ Cᗮ` and `0` otherwise, hence `∑_{u ∈ C} f̂(u) = |C| ∑_{v ∈ Cᗮ} f(v)`.
* **Factorization.**  For `f(v) = ∏_i g(v_i)` with `g(0) = X`, `g(a) = Y` (`a ≠ 0`),
  the transform factors: `f̂(u) = ∏_i ĝ(u_i)`, with `ĝ(0) = X + (q-1) Y` and
  `ĝ(c) = X - Y` for `c ≠ 0`.

Combining the two gives the identity.

## Main results

* `CodingTheory.MacWilliams.macwilliams` — the MacWilliams identity over `ℂ`.
-/

namespace CodingTheory

open scoped Classical
open Finset

namespace MacWilliams

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- A primitive additive character of the finite field `F` with values in `ℂ`. -/
noncomputable def chF (F : Type*) [Field F] [Fintype F] : AddChar F ℂ :=
  AddChar.FiniteField.primitiveChar_to_Complex F

theorem chF_primitive : (chF F).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F

omit [Fintype F] in
/--
A two-valued product over all coordinates collapses to a product of powers
governed by the Hamming weight: the coordinates where `v i = 0` contribute `a`,
the others contribute `b`.
-/
theorem prod_ite_pow (v : ι → F) (a b : ℂ) :
    ∏ i, (if v i = 0 then a else b) =
      a ^ (Fintype.card ι - hammingNorm v) * b ^ hammingNorm v := by
  simp +decide [ Finset.prod_ite, hammingNorm ];
  simp +decide [ Finset.filter_not, Finset.card_sdiff ];
  exact Or.inl ( by rw [ Nat.sub_sub_self ( Finset.card_le_univ _ ) ] )

/-- The "single-coordinate weight" function whose product is `X^{n-wt} Y^{wt}`. -/
noncomputable def fWeight (X Y : ℂ) (v : ι → F) : ℂ :=
  X ^ (Fintype.card ι - hammingNorm v) * Y ^ hammingNorm v

omit [Fintype F] in
theorem fWeight_eq_prod (X Y : ℂ) (v : ι → F) :
    fWeight X Y v = ∏ i, (if v i = 0 then X else Y) := by
  rw [fWeight, prod_ite_pow]

/--
The character of a dot product factors as a product of characters.
-/
theorem chF_dotProduct (u v : ι → F) :
    chF F (∑ i, u i * v i) = ∏ i, chF F (u i * v i) := by
  induction' ( Finset.univ : Finset ι ) using Finset.induction <;> simp_all +decide [ Finset.prod_insert, Finset.sum_insert ];
  rw [ ← ‹ ( chF F ) ( ∑ i ∈ _, u i * v i ) = ∏ i ∈ _, ( chF F ) ( u i * v i ) ›, AddChar.map_add_eq_mul ]

/-- The one-dimensional Fourier transform of the two-valued weight function. -/
noncomputable def ghat (X Y : ℂ) (c : F) : ℂ :=
  ∑ a : F, chF F (a * c) * (if a = 0 then X else Y)

theorem ghat_zero (X Y : ℂ) :
    ghat (F := F) X Y 0 = X + ((Fintype.card F : ℂ) - 1) * Y := by
  unfold ghat; simp +decide [ Finset.sum_ite, Finset.filter_ne' ] ; ring;
  rw [ Nat.cast_sub ] <;> norm_num ; ring;
  · rw [ Finset.card_filter ] ; norm_num;
  · exact Fintype.card_pos_iff.mpr ⟨ 0 ⟩

theorem ghat_ne (X Y : ℂ) {c : F} (hc : c ≠ 0) :
    ghat (F := F) X Y c = X - Y := by
  convert congr_arg ( fun x : ℂ => X + Y * ( x - 1 ) ) ( AddChar.sum_mulShift c ( chF_primitive ( F := F ) ) ) using 1;
  · unfold ghat;
    simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', mul_comm Y ];
    simp +decide [ Finset.sum_filter, sub_mul, Finset.sum_mul _ _ _ ];
  · simp +decide [ hc ] ; ring

/-- The Fourier transform of the weight function over the whole word space. -/
noncomputable def fhat (X Y : ℂ) (u : ι → F) : ℂ :=
  ∑ v : ι → F, chF F (∑ i, u i * v i) * fWeight X Y v

/--
**Factorization of the Fourier transform.**  The transform factors as a
product of one-dimensional transforms.
-/
theorem fhat_eq_prod_ghat (X Y : ℂ) (u : ι → F) :
    fhat X Y u = ∏ i, ghat X Y (u i) := by
  unfold fhat ghat;
  rw [ Finset.prod_sum ];
  refine' Finset.sum_bij ( fun v _ => fun i _ => v i ) _ _ _ _ <;> simp +decide;
  · simp +decide [ funext_iff ];
  · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
  · intro a; simp +decide [ fWeight_eq_prod, mul_comm ] ;
    rw [ chF_dotProduct, ← Finset.prod_mul_distrib ] ; congr ; ext ; aesop

/-- **The transformed weight enumerator term.**  The Fourier transform of the
weight function evaluates to the MacWilliams-substituted weight monomial. -/
theorem fhat_eq (X Y : ℂ) (u : ι → F) :
    fhat X Y u =
      (X + ((Fintype.card F : ℂ) - 1) * Y) ^ (Fintype.card ι - hammingNorm u) *
        (X - Y) ^ hammingNorm u := by
  rw [fhat_eq_prod_ghat]
  rw [show (∏ i, ghat X Y (u i)) =
      ∏ i, (if u i = 0 then (X + ((Fintype.card F : ℂ) - 1) * Y) else (X - Y)) from
    Finset.prod_congr rfl fun i _ => by
      by_cases h : u i = 0
      · rw [h, if_pos rfl, ghat_zero]
      · rw [if_neg h, ghat_ne X Y h]]
  rw [prod_ite_pow]

/--
There is a codeword witnessing a nontrivial character value whenever `v` is
not in the dual code.
-/
theorem exists_mem_char_ne_one {C : Submodule F (ι → F)} {v : ι → F}
    (hv : v ∉ dualCode C) :
    ∃ u ∈ C, chF F (∑ i, u i * v i) ≠ 1 := by
  obtain ⟨a, ha⟩ : ∃ a ∈ C, ∑ i, a i * v i ≠ 0 := by
    contrapose! hv; simp_all +decide [ mem_dualCode_iff ] ;
  contrapose! ha;
  intro haC
  have h_char : ∀ k : F, chF F (k * (∑ i, a i * v i)) = 1 := by
    intro k
    specialize ha (k • a) (C.smul_mem k haC);
    simpa [ Finset.mul_sum _ _ _, mul_assoc, Pi.smul_apply ] using ha;
  have := chF_primitive ( F := F );
  exact Classical.not_not.1 fun h => this h <| by ext x; simpa [ mul_comm x ] using h_char x;

/--
**Poisson summation over a subspace (character form).**  Summing the dot-product
character over the code yields `|C|` on the dual code and `0` elsewhere.
-/
theorem subgroup_char_sum (C : Submodule F (ι → F)) (v : ι → F) :
    ∑ u : C, chF F (∑ i, (u : ι → F) i * v i) =
      if v ∈ dualCode C then (Fintype.card C : ℂ) else 0 := by
  split_ifs with hv;
  · rw [ Finset.sum_congr rfl fun u hu => by rw [ mem_dualCode_iff.mp hv u u.2 ] ] ; simp +decide;
  · -- By `exists_mem_char_ne_one`, there exists `u0 ∈ C` such that `chF F (∑ i, u0 i * v i) ≠ 1`.
    obtain ⟨u0, hu0⟩ : ∃ u0 : C, chF F (∑ i, (u0 : ι → F) i * v i) ≠ 1 := by
      obtain ⟨ u, hu, hu' ⟩ := exists_mem_char_ne_one hv; exact ⟨ ⟨ u, hu ⟩, hu' ⟩ ;
    -- Reindexing the sum by `u ↦ u + u0` gives `S = chF F (∑ i, (u0:ι→F) i * v i) * S`.
    have h_reindex : ∑ u : C, chF F (∑ i, (u : ι → F) i * v i) = chF F (∑ i, (u0 : ι → F) i * v i) * ∑ u : C, chF F (∑ i, (u : ι → F) i * v i) := by
      rw [ Finset.mul_sum _ _ _ ];
      rw [ ← Equiv.sum_comp ( Equiv.addLeft u0 ) ] ; simp +decide;
      simp +decide only [add_mul, sum_add_distrib, AddChar.map_add_eq_mul];
    exact mul_left_cancel₀ ( sub_ne_zero_of_ne hu0 ) ( by linear_combination' h_reindex.symm )

/--
**Poisson summation.**  The sum of the Fourier transform over the code equals
`|C|` times the sum of the weight function over the dual code.
-/
theorem poisson (C : Submodule F (ι → F)) (X Y : ℂ) :
    ∑ u : C, fhat X Y (u : ι → F) =
      (Fintype.card C : ℂ) * ∑ v : dualCode C, fWeight X Y (v : ι → F) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ u : C, ∑ v : ι → F, chF F (∑ i, (u : ι → F) i * v i) * fWeight X Y v = ∑ v : ι → F, ∑ u : C, chF F (∑ i, (u : ι → F) i * v i) * fWeight X Y v := by
    exact Finset.sum_comm;
  convert h_fubini using 1;
  simp +decide [ ← Finset.sum_mul, subgroup_char_sum ];
  rw [ ← Finset.sum_filter ];
  rw [ ← Finset.mul_sum _ _ _ ];
  refine' congr_arg _ ( Finset.sum_bij ( fun x _ => x ) _ _ _ _ ) <;> simp +decide

/-- **The MacWilliams identity** (MacWilliams–Sloane, Ch. 5, Thm 1), as an
identity of complex numbers valid for every substitution `X, Y : ℂ`:
`∑_{v ∈ Cᗮ} X^{n - wt v} Y^{wt v}
  = (1/|C|) ∑_{u ∈ C} (X + (q-1) Y)^{n - wt u} (X - Y)^{wt u}`. -/
theorem macwilliams (C : Submodule F (ι → F)) (X Y : ℂ) :
    ∑ v : dualCode C,
        X ^ (Fintype.card ι - hammingNorm (v : ι → F)) *
          Y ^ hammingNorm (v : ι → F) =
      (Fintype.card C : ℂ)⁻¹ *
        ∑ u : C,
          (X + ((Fintype.card F : ℂ) - 1) * Y) ^
              (Fintype.card ι - hammingNorm (u : ι → F)) *
            (X - Y) ^ hammingNorm (u : ι → F) := by
  have hcard : (Fintype.card C : ℂ) ≠ 0 := by
    have : 0 < Fintype.card C := Fintype.card_pos
    exact_mod_cast this.ne'
  have hp := poisson C X Y
  have hr : ∑ u : C, fhat X Y (u : ι → F) =
      ∑ u : C, (X + ((Fintype.card F : ℂ) - 1) * Y) ^
          (Fintype.card ι - hammingNorm (u : ι → F)) *
        (X - Y) ^ hammingNorm (u : ι → F) :=
    Finset.sum_congr rfl fun u _ => fhat_eq X Y (u : ι → F)
  simp only [fWeight] at hp
  rw [hr] at hp
  rw [hp, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end MacWilliams

end CodingTheory