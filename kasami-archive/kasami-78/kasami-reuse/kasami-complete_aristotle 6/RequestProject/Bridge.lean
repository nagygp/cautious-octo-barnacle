/-
  Bridge.lean

  Integration bridge connecting the concrete Gold function analysis
  (Normalization.lean, Factorization.lean) with the abstract spectral
  framework (Counting.lean).

  ## Main results

  * `gold_kernel_card_le` — The kernel of the Gold derivative has at most
    2^k elements, combining the kernel isomorphism with the root bound.

  * `gold_diffCount_le` — For the Gold function f(x) = x^{2^k+1} over a
    finite field of characteristic 2, the differential count δ_f(u,v) ≤ 2^k
    for every nonzero u.

  * `gold_IsAPN_of_k_eq_one` — When k = 1, the Gold function x ↦ x³ is APN.
    This is the concrete instantiation of the abstract `IsAPN` from Counting.lean.

  ## References

  * Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions"
  * Budaghyan, "Construction and Analysis of Cryptographic Functions"
-/

import RequestProject.Theorem3.Normalization
import RequestProject.Theorem3.Factorization
import RequestProject.Theorem23.Counting

open Finset BigOperators FourierSpectralBridge

noncomputable section

set_option maxHeartbeats 400000

/-! ### Step 1: From kernel bijection to differential count bound

  The kernel of Δ_u f is in bijection with roots of Lnorm (Normalization.lean),
  and Lnorm has at most 2^k roots (card_roots_Lnorm_le). We combine these to
  bound the total number of x with Δ_u f(x) = 0.
-/

/-
The set of x such that Δ_u f(x) = 0 has cardinality at most 2^k.
    This combines `kernel_deltaGold_eq_image` with `card_roots_Lnorm_le`.
-/
lemma gold_kernel_card_le
    (k : ℕ) (hk : 0 < k)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (u : F) (hu : u ≠ 0) :
    (univ.filter fun x => deltaGold k F u x = 0).card ≤ 2 ^ k := by
  have := @kernel_deltaGold_eq_image;
  specialize this k F u hu;
  rw [ Set.ext_iff ] at this;
  rw [ show ( Finset.filter ( fun x => deltaGold k F u x = 0 ) Finset.univ ) = Finset.image ( fun y => y * u ) ( Finset.filter ( fun y => Lnorm k F y = 0 ) Finset.univ ) by ext; aesop ];
  exact Finset.card_image_le.trans ( by exact_mod_cast card_roots_Lnorm_le k F )

/-! ### Step 2: From kernel bound to differential count

  The differential count δ_f(u, v) counts solutions to f(x+u) + f(x) = v.
  For v = 0, this is exactly the kernel. For general v, we use a translation
  argument: the solution set for v is a coset of the kernel of the linearized
  part, so it has the same cardinality.
-/

/-
The differential count of the Gold function is bounded by 2^k for u ≠ 0.
    This means the Gold function has differential uniformity at most 2^k.
-/
lemma gold_diffCount_le
    (k : ℕ) (hk : 0 < k)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (u : F) (hu : u ≠ 0) (v : F) :
    diffCount (goldFun k F) u v ≤ 2 ^ k := by
  -- The equation `linPart k F u x = c` has at most 2^k solutions for any c.
  have h_linPart_roots (c : F) : (Finset.univ.filter (fun x => linPart k F u x = c)).card ≤ 2 ^ k := by
    -- The polynomial $x^{2^k} * u + x * u^{2^k} - c$ has degree $2^k$, thus it has at most $2^k$ roots.
    have h_poly_roots : (Finset.univ.filter (fun x => linPart k F u x = c)).card ≤ (Polynomial.roots (Polynomial.X ^ (2 ^ k) * Polynomial.C u + Polynomial.X * Polynomial.C (u ^ (2 ^ k)) - Polynomial.C c)).toFinset.card := by
      refine' Finset.card_le_card _;
      intro x hx; simp_all +decide [ sub_eq_iff_eq_add, linPart ] ;
      refine' ⟨ ne_of_apply_ne Polynomial.natDegree _, by linear_combination' hx ⟩;
      rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> simp +decide [ hu, hk.ne' ];
    refine' le_trans h_poly_roots ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
    rw [ Polynomial.natDegree_sub_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num [ hu ];
    linarith;
  -- By definition of `diffCount`, we need to show that the number of solutions to `deltaGold k F u x = v` is at most 2^k.
  have h_diffCount : (Finset.univ.filter (fun x => deltaGold k F u x = v)).card ≤ 2 ^ k := by
    convert h_linPart_roots ( v + u ^ goldExp k ) using 2 ; ext x ; simp +decide [ delta_eq_lin_plus_const ] ; ring;
    grind;
  convert h_diffCount using 1

/-! ### Step 3: Concrete APN for k = 1

  When k = 1, 2^k = 2, so the Gold function x ↦ x³ is APN.
  This connects the Normalization/Factorization pipeline to the
  abstract `IsAPN` definition from Counting.lean.
-/

/-- The Gold function with k = 1 (i.e., f(x) = x³) is APN.
    This is the concrete bridge to the abstract `IsAPN` from Counting.lean. -/
theorem gold_IsAPN_of_k_eq_one
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] :
    IsAPN (goldFun 1 F) := by
  intro u hu v
  exact gold_diffCount_le 1 one_pos F u hu v

end