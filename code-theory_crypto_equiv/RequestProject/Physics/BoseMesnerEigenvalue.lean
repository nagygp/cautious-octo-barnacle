import RequestProject.CodingTheory.MacWilliams
import RequestProject.CodingTheory.Krawtchouk
import RequestProject.Physics.BoseMesner

/-!
# The Bose–Mesner eigenvalue identity: distance-sphere character sums are Krawtchouk values

This module proves the **central eigenvalue identity** of the Bose–Mesner algebra
of the Hamming scheme `H(n, q)` over `Fⁿ = (ι → F)`, the identity that re-homes
the Delsarte/MacWilliams linear-programming theory inside the association scheme:

> for a fixed mask `a : ι → F` and `0 ≤ i ≤ n`,
> `∑_{z : wt z = i} χ_a(z) = K_i(wt a)`,
> where `χ_a(z) = ψ(⟨a, z⟩) = ∏_j ψ(a_j z_j)` is the additive character indexed
> by `a` and `K_i` is the `i`-th Krawtchouk polynomial.

Equivalently, summing over the `i`-th relation `R_i = {(x, y) : d(x,y) = i}`,
`∑_{y : d(x,y) = i} χ_a(y - x) = K_i(wt a)`: the character `χ_a` is a common
eigenvector of every adjacency matrix `A_i`, with eigenvalue the Krawtchouk value
`K_i(wt a)` (the `(i, wt a)` entry of the eigenvalue matrix `P` of the scheme).

The proof reuses the additive-character / Fourier machinery already developed for
the MacWilliams identity (`RequestProject/CodingTheory/MacWilliams.lean`): the
generating function `∑_z χ_a(z) T^{wt z} = (1 + (q-1)T)^{n - wt a}(1 - T)^{wt a}`
is exactly `MacWilliams.fhat 1 T a` (`fhat_eq`), and the right-hand side is the
Krawtchouk generating function (`krawtchouk_eq_coeff`).  Matching the coefficient
of `T^i` yields the identity.

## Main results

* `charSum_weightSphere_genfun` — the generating-function identity
  `∑_z χ_a(z) T^{wt z} = (1 + (q-1)T)^{n-wt a}(1-T)^{wt a}` for every `T : ℂ`.
* `charSum_weightSphere_eq_krawtchouk` — the **Bose–Mesner eigenvalue identity**:
  `∑_{z : wt z = i} χ_a(z) = K_i(wt a)`.
* `charSum_distanceSphere_eq_krawtchouk` — the translated form
  `∑_{y : d(x,y) = i} χ_a(y - x) = K_i(wt a)`.
-/

namespace CodingTheory

open scoped Classical
open Finset Polynomial

namespace BoseMesner

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The additive character `χ_a(z) = ψ(⟨a, z⟩)` indexed by the mask `a`. -/
noncomputable def charMask (a z : ι → F) : ℂ :=
  MacWilliams.chF F (∑ j, a j * z j)

/--
**The generating function for the masked character sum.** Summing `χ_a(z) T^{wt z}`
over all words gives the MacWilliams-factorised form
`(1 + (q-1)T)^{n - wt a}(1 - T)^{wt a}`.  This is `MacWilliams.fhat 1 T a`
evaluated through `MacWilliams.fhat_eq`.
-/
theorem charSum_weightSphere_genfun (a : ι → F) (T : ℂ) :
    ∑ z : ι → F, charMask a z * T ^ hammingNorm z
      = (1 + ((Fintype.card F : ℂ) - 1) * T) ^ (Fintype.card ι - hammingNorm a)
        * (1 - T) ^ hammingNorm a := by
  have h := MacWilliams.fhat_eq (1 : ℂ) T a
  unfold MacWilliams.fhat MacWilliams.fWeight charMask at *
  simp only [one_pow, one_mul] at h
  rw [← h]

/-
**The Bose–Mesner eigenvalue identity.**  For a fixed mask `a` and `0 ≤ i ≤ n`,
the sum of the character `χ_a` over the weight-`i` sphere is the Krawtchouk value
`K_i(wt a)`:
`∑_{z : wt z = i} χ_a(z) = K_i(wt a)`.
-/
theorem charSum_weightSphere_eq_krawtchouk (a : ι → F) (i : ℕ) :
    ∑ z ∈ Finset.univ.filter (fun z : ι → F => hammingNorm z = i), charMask a z
      = (krawtchouk (Fintype.card F) (Fintype.card ι) i (hammingNorm a) : ℂ) := by
  convert congr_arg ( fun p : Polynomial ℂ => p.coeff i ) ( show ( ∑ z : ι → F, Polynomial.C ( MacWilliams.chF F ( ∑ j, a j * z j ) ) * Polynomial.X ^ ( hammingNorm z ) ) = ( 1 + ( ( Fintype.card F : ℂ ) - 1 ) • Polynomial.X ) ^ ( Fintype.card ι - hammingNorm a ) * ( 1 - Polynomial.X ) ^ ( hammingNorm a ) from ?_ ) using 1;
  · simp +decide [ Polynomial.coeff_sum, charMask ];
    rw [ ← Finset.sum_filter ] ; congr ; ext ; aesop;
  · have := @krawtchouk_eq_coeff ( Fintype.card F ) ( Fintype.card ι ) i ( hammingNorm a );
    convert congr_arg ( fun x : ℤ => ( x : ℂ ) ) this using 1;
    convert Polynomial.coeff_map ( algebraMap ℤ ℂ ) _ using 1;
    norm_num [ Polynomial.smul_eq_C_mul ];
  · refine' Polynomial.funext fun x => _;
    convert charSum_weightSphere_genfun a x using 1;
    · simp +decide [ Polynomial.eval_finset_sum, charMask ];
    · simp +decide [ Polynomial.smul_eq_C_mul ]

/-
**The distance form of the eigenvalue identity.**  For a fixed base point `x` and
mask `a`, summing `χ_a(y - x)` over the distance-`i` sphere about `x` gives
`K_i(wt a)`: the character `χ_a` is an eigenvector of the `i`-th adjacency matrix
with eigenvalue `K_i(wt a)`.
-/
theorem charSum_distanceSphere_eq_krawtchouk (a x : ι → F) (i : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : ι → F => hammingDist x y = i),
        MacWilliams.chF F (∑ j, a j * (y j - x j))
      = (krawtchouk (Fintype.card F) (Fintype.card ι) i (hammingNorm a) : ℂ) := by
  convert charSum_weightSphere_eq_krawtchouk a i using 1;
  refine' Finset.sum_bij ( fun y hy => y - x ) _ _ _ _ <;> simp_all +decide [ hammingDist_eq_hammingNorm, hammingNorm ];
  · simp +decide [ sub_eq_zero, eq_comm ];
  · exact fun b hb => ⟨ b + x, by simpa [ sub_eq_iff_eq_add ] using hb, by simp +decide ⟩;
  · unfold charMask; aesop;

/-
**The Delsarte linear-programming inequality for an arbitrary code, re-homed in
the Hamming scheme.**  For *any* code `Y ⊆ Fⁿ` (no linearity assumption) and any
`k`, the Krawtchouk transform of its inner distribution is nonnegative:
`0 ≤ ∑_{x, y ∈ Y} K_k(d(x, y))`.

This is the scheme/eigenvalue derivation of the Delsarte LP positivity (cf. the
linear-code version `CodingTheory.delsarte_inequality`): writing `f̂(z) =
∑_{x∈Y} χ_z(x)`, the eigenvalue identity `charSum_weightSphere_eq_krawtchouk`
gives `∑_{wt z = k} ‖f̂(z)‖² = ∑_{x,y∈Y} K_k(d(x,y))`, and the left side is a sum
of squared norms, hence `≥ 0`.
-/
theorem delsarte_innerSum_nonneg (Y : Finset (ι → F)) (k : ℕ) :
    0 ≤ ∑ x ∈ Y, ∑ y ∈ Y,
        krawtchouk (Fintype.card F) (Fintype.card ι) k (hammingDist x y) := by
  have h_sum_nonneg : ∑ z ∈ Finset.univ.filter (fun z => hammingNorm z = k), ‖∑ x ∈ Y, MacWilliams.chF F (∑ j, z j * x j)‖ ^ 2 = ∑ x ∈ Y, ∑ y ∈ Y, (krawtchouk (Fintype.card F) (Fintype.card ι) k (hammingDist x y) : ℝ) := by
    have h_sum_nonneg : ∀ z : ι → F, ‖∑ x ∈ Y, MacWilliams.chF F (∑ j, z j * x j)‖ ^ 2 = ∑ x ∈ Y, ∑ y ∈ Y, MacWilliams.chF F (∑ j, z j * (x j - y j)) := by
      intro z
      have h_charmask : ∀ x y : ι → F, MacWilliams.chF F (∑ j, z j * (x j - y j)) = MacWilliams.chF F (∑ j, z j * x j) * starRingEnd ℂ (MacWilliams.chF F (∑ j, z j * y j)) := by
        intro x y; simp +decide [ mul_sub, Finset.sum_sub_distrib, AddChar.map_add_eq_mul ] ;
        simp +decide [ sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj ];
      simp +decide only [h_charmask];
      simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, Complex.ext_iff, sq ];
      simp +decide [ Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im, mul_comm ];
      rw [ Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ ) ) ];
    have h_sum_nonneg : ∀ x y : ι → F, ∑ z ∈ Finset.univ.filter (fun z => hammingNorm z = k), MacWilliams.chF F (∑ j, z j * (x j - y j)) = (krawtchouk (Fintype.card F) (Fintype.card ι) k (hammingNorm (x - y)) : ℝ) := by
      intro x y
      convert charSum_weightSphere_eq_krawtchouk (x - y) k using 1;
      simp +decide [ charMask, mul_sub ];
      simp +decide only [sub_mul, sum_sub_distrib];
      simp +decide only [mul_comm];
    have h_sum_nonneg : ∑ z ∈ Finset.univ.filter (fun z => hammingNorm z = k), ‖∑ x ∈ Y, MacWilliams.chF F (∑ j, z j * x j)‖ ^ 2 = ∑ x ∈ Y, ∑ y ∈ Y, ∑ z ∈ Finset.univ.filter (fun z => hammingNorm z = k), MacWilliams.chF F (∑ j, z j * (x j - y j)) := by
      simp +zetaDelta at *;
      rw [ Finset.sum_congr rfl fun z hz => by solve_by_elim, Finset.sum_comm, Finset.sum_congr rfl fun x hx => Finset.sum_comm ];
    convert congr_arg Complex.re h_sum_nonneg using 1;
    simp +decide [ *, hammingDist_eq_hammingNorm ];
  exact_mod_cast h_sum_nonneg ▸ Finset.sum_nonneg fun _ _ => sq_nonneg _

end BoseMesner

end CodingTheory