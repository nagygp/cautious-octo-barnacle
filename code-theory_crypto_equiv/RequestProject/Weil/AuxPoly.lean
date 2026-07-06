import RequestProject.Weil.ArtinSchreier
import RequestProject.Weil.Hasse
import RequestProject.Weil.Frobenius

/-!
# The Stepanov auxiliary-polynomial construction

This module decomposes the genuinely hard core of the Stepanov route — `exists_aux_poly` in
`Weil.Stepanov` — into its constituent provable pieces.  The construction has three independent
ingredients:

1. **A linear-algebra existence engine** (`exists_nonzero_of_linear_system`,
   `exists_nonzero_of_card_lt`): an underdetermined homogeneous linear system over `𝔽_q` (more
   unknowns than equations) has a nonzero solution.  This is what produces the auxiliary polynomial
   without ever writing it down explicitly.

2. **An explicit ansatz** (`auxAnsatz`): the auxiliary polynomial is taken in the special form
   `g = ∑_{i,j} c_{i,j} · x^i · (x^q - x is killed)…` — concretely an `𝔽_q`-linear combination of
   `p`-th powers `(∑_i a_i x^i)^p` multiplied by low-degree polynomials.  Using `x^q = x` on `𝔽_q`
   and the Frobenius interaction `hasseDeriv_pow_char`, the high-order vanishing at curve points
   becomes a *linear* condition on the coefficient vector `c`.

3. **The counting inequality** (`stepanov_count_lt`): for suitably tuned parameters `(m, ℓ)`, the
   number of linear vanishing conditions is strictly smaller than the number of free coefficients,
   so engine (1) applies, while the degree of `g` stays controlled.

Assembling (1)–(3) gives `exists_aux_poly`; optimising `(m, ℓ)` then yields the sharp constant
`(d-1)(p-1)` in the point-count bounds.  All three ingredients are stated here as `sorry`-skeletons.

## Main statements (skeletons)
* `Weil.AuxPoly.exists_nonzero_of_linear_system` — homogeneous underdetermined systems have nonzero
  solutions (matrix form).
* `Weil.AuxPoly.exists_nonzero_of_card_lt` — the same as a linear-map / dimension statement.
* `Weil.AuxPoly.auxAnsatz` — the explicit coefficient-indexed ansatz for the auxiliary polynomial.
* `Weil.AuxPoly.auxAnsatz_natDegree_le` — its controlled degree.
* `Weil.AuxPoly.auxAnsatz_ne_zero_of_coeff` — nonzero coefficients give a nonzero polynomial.
* `Weil.AuxPoly.hasseDeriv_auxAnsatz_curvePoint` — high-order vanishing reduces to linear conditions.
* `Weil.AuxPoly.stepanov_count_lt` — the decisive counting inequality `#conditions < #coeffs`.
-/

open scoped BigOperators
open Polynomial
open Classical

namespace Weil
namespace AuxPoly

variable {F : Type*} [Field F] [Fintype F]

/-
**Linear-algebra engine (map form).**  An `𝔽_q`-linear map from a space of dimension `n` to one
of dimension `s < n` has nontrivial kernel.
-/
omit [Fintype F] in
lemma exists_nonzero_of_card_lt {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ T v = 0 := by
  contrapose! h with h_contra;
  exact LinearMap.finrank_le_finrank_of_injective ( show Function.Injective T from fun v w h => Classical.not_not.1 fun h' => h_contra ( v - w ) ( sub_ne_zero_of_ne h' ) ( by simpa [ sub_eq_zero ] using h ) )

/-- **Linear-algebra engine (matrix form).**  A homogeneous linear system `A·v = 0` with strictly
more unknowns than equations has a nonzero solution. -/
lemma exists_nonzero_of_linear_system {n s : ℕ} (A : Matrix (Fin s) (Fin n) F) (h : s < n) :
    ∃ v : Fin n → F, v ≠ 0 ∧ A.mulVec v = 0 := by
  obtain ⟨v, hv, hT⟩ := exists_nonzero_of_card_lt A.mulVecLin
    (by simpa [Module.finrank_fintype_fun_eq_card] using h)
  exact ⟨v, hv, by simpa using hT⟩

/-- **The Stepanov ansatz.**  Given parameters `(m, ℓ)` and a coefficient vector `c`, this is the
explicit candidate auxiliary polynomial — an `𝔽_q`-linear combination of products of low-degree
monomials with `p`-th powers, reduced using `x^q = x`.  (The precise index set is part of the
construction; here it is presented schematically as a coefficient-indexed family so that the
structural lemmas below can be stated.) -/
noncomputable def auxAnsatz (f : F[X]) (m ℓ : ℕ) (c : ℕ × ℕ → F) : F[X] :=
  ∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (m * f.natDegree + 1),
    Polynomial.C (c (i, j)) * Polynomial.X ^ i * (f ^ j)

/-
The ansatz has degree controlled by `ℓ + m·d²` (with `d = deg f`).

NOTE (correction).  The degree bound originally recorded in this skeleton,
`ℓ * Fintype.card F + m * f.natDegree * ℓ`, is **false** for the naive ansatz defined above: e.g.
with `ℓ = m = 1` and `c` supported on `(0, m·d)`, the term `c₀,ₘₙ · f^{m·d}` already has degree
`m·d·deg f = m·d²`, which exceeds the claimed bound whenever `d > ℓ` and the field is small.  The
true (and provable) degree bound for this ansatz is `ℓ + m·d²`, stated here.
-/
lemma auxAnsatz_natDegree_le (f : F[X]) (m ℓ : ℕ) (c : ℕ × ℕ → F) :
    (auxAnsatz f m ℓ c).natDegree ≤ ℓ + m * f.natDegree * f.natDegree := by
  refine' le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le _ );
  intro i hi; refine' le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le _ ) ; intro j hj; by_cases h : c ( i, j ) = 0 <;> simp_all +decide [ Polynomial.natDegree_mul' ] ;
  refine' le_trans ( Polynomial.natDegree_mul_le .. ) _;
  refine' le_trans ( add_le_add ( Polynomial.natDegree_C_mul_X_pow_le _ _ ) ( Polynomial.natDegree_pow_le ) ) _ ; nlinarith

/-
**Nonvanishing (corrected: commented out — false for the naive ansatz).**

The original skeleton claimed that *any* nonzero coefficient vector `c` yields a nonzero ansatz
("the building blocks are `𝔽_q`-linearly independent in the relevant degree range").  This is **false**
for the naive ansatz `∑_{i<ℓ} ∑_{j≤m·d} c_{i,j} X^i f^j`: the monomials `X^i f^j` are *not* linearly
independent in general.  For instance if `f = X` then `X^i f^j = X^{i+j}`, so any two index pairs
`(i, j)` with the same `i + j` collide and a nonzero `c` in their kernel gives `auxAnsatz = 0`.

A faithful Stepanov construction must therefore use the genuine auxiliary polynomial (an `𝔽_q`-linear
combination of `p`-th powers, with the `x^q = x` reduction), for which an independent family *can* be
arranged.  This is part of the genuine deep content of `exists_aux_poly` and is not captured by the
naive `auxAnsatz` above, so the false lemma is removed rather than left as a misleading `sorry`.

lemma auxAnsatz_ne_zero_of_coeff (f : F[X]) (m ℓ : ℕ) (c : ℕ × ℕ → F) (hc : c ≠ 0) :
    auxAnsatz f m ℓ c ≠ 0 := by
  sorry
-/

/-
**High-order vanishing as linear conditions.**  For each curve point `x` and each order `k < m`,
the value `(hasseDeriv k (auxAnsatz f m ℓ c)).eval x` is an `𝔽_q`-*linear* functional of the
coefficient vector `c` (via `hasseDeriv_pow_char` and `x^q = x`).  This is the statement that the
vanishing conditions assemble into a linear system.
-/
lemma hasseDeriv_auxAnsatz_linear (f : F[X]) (m ℓ : ℕ) (x : F) (k : ℕ) :
    ∃ φ : (ℕ × ℕ → F) →ₗ[F] F,
      ∀ c : ℕ × ℕ → F, (Polynomial.hasseDeriv k (auxAnsatz f m ℓ c)).eval x = φ c := by
  refine' ⟨ _, _ ⟩;
  refine' { .. };
  use fun c => ∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range ( m * f.natDegree + 1 ), c ( i, j ) * ( Polynomial.hasseDeriv k ( Polynomial.X ^ i * f ^ j ) ).eval x;
  all_goals simp +decide [ Finset.sum_add_distrib, add_mul, mul_add, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, auxAnsatz ];
  · exact fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
  · have h_linear : ∀ (c : F) (p : F[X]), Polynomial.hasseDeriv k (Polynomial.C c * p) = Polynomial.C c * Polynomial.hasseDeriv k p := by
      simp +decide [ Polynomial.hasseDeriv ];
      simp +decide [ Polynomial.sum_def, mul_assoc, Finset.mul_sum _ _ _ ];
      intro c p; by_cases hc : c = 0 <;> simp +decide [ hc, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      refine' Finset.sum_subset _ _ <;> intro x hx <;> simp_all +decide [ Polynomial.coeff_C_mul ];
    simp +decide [ h_linear, mul_assoc ]

/-- **The decisive counting inequality.**  For the Stepanov-optimal parameters the number of linear
vanishing conditions (`m` orders at each of the at most `q + (d-1)(p-1)√q` curve points) is strictly
smaller than the number of free coefficients (`ℓ·(m·d+1)`).  Choosing `ℓ ≈ √q` makes this hold and
yields the sharp constant.  Stated abstractly as the existence of admissible parameters. -/
lemma stepanov_count_lt (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) (N : ℕ) :
    ∃ m ℓ : ℕ, 1 ≤ m ∧ 1 ≤ ℓ ∧ m * N < ℓ * (m * f.natDegree + 1) := by
  refine ⟨1, N + 1, le_refl _, Nat.le_add_left 1 N, ?_⟩
  nlinarith [Nat.zero_le f.natDegree, Nat.zero_le N]

end AuxPoly
end Weil