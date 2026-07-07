import Mathlib
import RequestProject.CodingTheory.MacWilliams
import RequestProject.CodingTheory.Krawtchouk

/-!
# The MacWilliams identity in weight-distribution (Krawtchouk) form

This module is the next layer of the MacWilliams development transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977 (Ch. 5).

The polynomial **MacWilliams identity** (`CodingTheory.MacWilliams.macwilliams`)
relates the weight enumerator of a code `C` to that of its dual `Cᗮ`.  Reading off
its coefficients, with the **Krawtchouk polynomials**
(`CodingTheory.krawtchouk`) as the transition matrix, gives the identity in the
form used by the Delsarte linear-programming bound (MacWilliams–Sloane, Ch. 5,
eq. (38) / Thm 12): the dual weight distribution `B_k` is the Krawtchouk
transform of the primal weight distribution `A_i`,

`B_k = (1 / |C|) · Σ_{i=0}^{n} A_i K_k(i)`,

where `A_i = weightDistribution C i`, `B_k = weightDistribution Cᗮ k`,
`n = #ι` is the length and `q = #F` is the alphabet size.

## Proof outline

Specialising the complex MacWilliams identity at `X = 1` turns both sides into
polynomial functions of `Y`:

* the left side `Σ_v Y^{wt v}` regroups (by weight) into `Σ_k B_k Y^k`;
* the right side `(1/|C|) Σ_u (1 + (q-1)Y)^{n - wt u} (1 - Y)^{wt u}` regroups
  into `(1/|C|) Σ_i A_i (1 + (q-1)Y)^{n-i}(1-Y)^i`, and the Krawtchouk generating
  function `(1+(q-1)Y)^{n-i}(1-Y)^i = Σ_k K_k(i) Y^k` turns it into
  `Σ_k [(1/|C|) Σ_i A_i K_k(i)] Y^k`.

Two polynomial functions on the infinite field `ℂ` that agree everywhere have
equal coefficients, which yields the claimed identity coefficient by coefficient.

## Main results

* `macwilliams_distribution` — `B_k = (1/|C|) Σ_i A_i K_k(i)` over `ℂ`.

## Auxiliary results

* `codeSum_eq_sum_weightDistribution` — regrouping a weight-power sum over a code
  by its weight distribution.
* `krawtchouk_genfun_eval` — the Krawtchouk generating function evaluated in `ℂ`.
* `coeff_eq_of_eval_eq` — coefficient uniqueness for polynomial functions on `ℂ`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/--
Regrouping by weight: a sum of `X^{n - wt c} Y^{wt c}` over the codewords of a
code `D` equals `Σ_{i=0}^{n} A_i(D) · X^{n-i} Y^i`, the weight-distribution form,
now over `ℂ`.
-/
theorem codeSum_eq_sum_weightDistribution (D : Submodule F (ι → F)) (X Y : ℂ) :
    ∑ c : D, X ^ (Fintype.card ι - hammingNorm (c : ι → F)) *
        Y ^ hammingNorm (c : ι → F)
      = ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (weightDistribution D i : ℂ) * (X ^ (Fintype.card ι - i) * Y ^ i) := by
  rw [ Finset.sum_congr rfl fun x hx => ?_ ];
  rotate_left;
  use fun x => ∑ i ∈ Finset.range ( Fintype.card ι + 1 ), ( if hammingNorm x.val = i then X ^ ( Fintype.card ι - i ) * Y ^ i else 0 );
  · simp +decide [ hammingNorm ];
    exact fun h => False.elim <| h.not_ge <| le_trans ( Finset.card_le_univ _ ) <| by simp +decide ;
  · rw [ Finset.sum_comm ];
    simp +decide [ Finset.sum_ite, weightDistribution ];
    simp +decide only [card_filter, Fintype.card_subtype]

omit [Field F] in
/--
The Krawtchouk generating function evaluated at a complex point `Y`:
`(1 + (q-1)Y)^{n-i} (1 - Y)^i = Σ_{k=0}^{n} K_k(i) Y^k`, for `i ≤ n`.
-/
theorem krawtchouk_genfun_eval (i : ℕ) (hi : i ≤ Fintype.card ι) (Y : ℂ) :
    (1 + ((Fintype.card F : ℂ) - 1) * Y) ^ (Fintype.card ι - i) * (1 - Y) ^ i
      = ∑ k ∈ Finset.range (Fintype.card ι + 1),
          (krawtchouk (Fintype.card F) (Fintype.card ι) k i : ℂ) * Y ^ k := by
  convert ( congr_arg ( Polynomial.eval₂ ( Int.castRingHom ℂ ) Y ) ( krawtchouk_generating_function ( Fintype.card F ) ( Fintype.card ι ) i hi ) ) using 1;
  · convert ( congr_arg ( Polynomial.eval₂ ( Int.castRingHom ℂ ) Y ) ( krawtchouk_generating_function ( Fintype.card F ) ( Fintype.card ι ) i hi ) ) |> Eq.symm using 1
    simp +decide [ Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_one ];
  · convert ( congr_arg ( Polynomial.eval₂ ( Int.castRingHom ℂ ) Y ) ( krawtchouk_generating_function ( Fintype.card F ) ( Fintype.card ι ) i hi ) ) using 1;
    simp +decide [ Polynomial.eval₂_finset_sum ];
    exact Finset.sum_congr rfl fun _ _ => by erw [ Polynomial.eval₂_C ] ; norm_num;

/--
Coefficient uniqueness over `ℂ`: if two polynomial functions of degree `< N`
agree at every complex argument, their coefficients agree.
-/
theorem coeff_eq_of_eval_eq (a b : ℕ → ℂ) (N : ℕ)
    (h : ∀ Y : ℂ, ∑ k ∈ Finset.range N, a k * Y ^ k
          = ∑ k ∈ Finset.range N, b k * Y ^ k)
    (k : ℕ) (hk : k < N) : a k = b k := by
  -- Consider the polynomial `p := ∑ k ∈ Finset.range N, Polynomial.C (a k - b k) * Polynomial.X ^ k`.
  set p : Polynomial ℂ := ∑ k ∈ Finset.range N, Polynomial.C (a k - b k) * Polynomial.X ^ k;
  -- Since `p.eval Y = ∑ k ∈ Finset.range N, (a k - b k) * Y^k = (∑ a k Y^k) - (∑ b k Y^k) = 0` by the hypothesis `h`, `p` is the zero polynomial.
  have hp_zero : p = 0 := by
    refine' Polynomial.funext fun x => _;
    simp +zetaDelta at *;
    simp +decide [ Polynomial.eval_finset_sum, sub_mul, h ];
  simp +zetaDelta at *;
  replace hp_zero := congr_arg ( fun q => Polynomial.coeff q k ) hp_zero ; simp_all +decide [ sub_mul ];
  exact eq_of_sub_eq_zero hp_zero

/--
The polynomial form of the (`X = 1`-specialised) MacWilliams identity: for every
complex `Y`,
`Σ_k B_k Y^k = Σ_k [(1/|C|) Σ_i A_i K_k(i)] Y^k`.
-/
theorem macwilliams_poly_eval (C : Submodule F (ι → F)) (Y : ℂ) :
    ∑ k ∈ Finset.range (Fintype.card ι + 1),
        (weightDistribution (dualCode C) k : ℂ) * Y ^ k
      = ∑ k ∈ Finset.range (Fintype.card ι + 1),
          ((Fintype.card C : ℂ)⁻¹ *
            ∑ i ∈ Finset.range (Fintype.card ι + 1),
              (weightDistribution C i : ℂ) *
                (krawtchouk (Fintype.card F) (Fintype.card ι) k i : ℂ)) * Y ^ k := by
  have hMacWilliams := MacWilliams.macwilliams C 1 Y;
  rw [ codeSum_eq_sum_weightDistribution ] at hMacWilliams;
  convert hMacWilliams using 1;
  · simp +decide;
  · rw [ codeSum_eq_sum_weightDistribution ];
    simp +decide only [Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ ← Finset.mul_sum _ _ _, ← Finset.mul_sum _ _ _, krawtchouk_genfun_eval i ( Finset.mem_range_succ_iff.mp hi ) Y ]

/--
**The MacWilliams identity, weight-distribution (Krawtchouk) form**
(MacWilliams–Sloane, Ch. 5, Thm 12).  The dual weight distribution is the
Krawtchouk transform of the primal one:
`B_k = (1/|C|) Σ_{i=0}^{n} A_i K_k(i)` for `k ≤ n`,
where `A_i = weightDistribution C i`, `B_k = weightDistribution Cᗮ k`,
`n = #ι`, `q = #F`.
-/
theorem macwilliams_distribution (C : Submodule F (ι → F)) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    (weightDistribution (dualCode C) k : ℂ)
      = (Fintype.card C : ℂ)⁻¹ *
          ∑ i ∈ Finset.range (Fintype.card ι + 1),
            (weightDistribution C i : ℂ) *
              (krawtchouk (Fintype.card F) (Fintype.card ι) k i : ℂ) := by
  convert coeff_eq_of_eval_eq ( fun k => ( weightDistribution ( dualCode C ) k : ℂ ) ) ( fun k => ( Fintype.card C : ℂ ) ⁻¹ * ∑ i ∈ Finset.range ( Fintype.card ι + 1 ), ( weightDistribution C i : ℂ ) * ( krawtchouk ( Fintype.card F ) ( Fintype.card ι ) k i : ℂ ) ) ( Fintype.card ι + 1 ) _ k ( Nat.lt_succ_of_le hk ) using 1;
  convert macwilliams_poly_eval C using 1

end CodingTheory