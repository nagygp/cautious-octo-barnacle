import CodeTheoryCryptoEquiv.Walsh.Transform

/-!
# Difference sets and the Fourier / Walsh bridge (Dillon–Dobbertin, Stage 0)

This module is **Stage 0** of the staged program to formalize

> J. F. Dillon and H. Dobbertin, *New cyclic difference sets with Singer
> parameters*, Finite Fields Appl. **10** (2004) 342–389,

as described in `ASSESSMENT_DILLON_DOBBERTIN.md` and
`DILLON_DOBBERTIN_ROADMAP.md`.  It introduces difference sets in the additive
group of a finite field of characteristic two and proves the load-bearing
**Proposition 2** of the paper at the level of the Walsh transform: a subset `D`
has *flat Fourier spectrum* off the origin **iff** it is a difference set
(constant autocorrelation off the origin).

The organizing identity is the discrete **Wiener–Khinchin** relation
`fourier_sq_eq_sum_diffCount`: the squared Fourier coefficient of the indicator
of `D` is the Fourier transform of its autocorrelation, expressed purely with the
sign character `WalshAB.χ` and the orthogonality relations
`WalshAB.χ_sum_eq` / `WalshAB.χ_sum_dual` already in the repository.

## Main definitions

* `ind D x` — the integer indicator `1` if `x ∈ D`, else `0`.
* `fourier D a = ∑ x ∈ D, χ (a · x)` — the additive-character Fourier
  transform of the indicator of `D` (the paper's `F_D`).
* `diffCount D s = #{x ∈ D : x + s ∈ D}` — the autocorrelation, i.e. the number
  of representations of `s` as a difference of two elements of `D`.
* `IsDifferenceSet D lam` — every nonzero `s` has exactly `lam` such
  representations (constant autocorrelation off `0`).
* `HasFlatSpectrum D mu` — every nonzero frequency `a` has `fourier D a ^ 2 = mu`.

## Main results

* `fourier_sq_eq_sum_diffCount` — Wiener–Khinchin:
  `fourier D b ^ 2 = ∑ s, diffCount D s * χ (b · s)`.
* `wiener_khinchin` — the dual form
  `card F * diffCount D s = ∑ a, fourier D a ^ 2 * χ (a · s)`.
* `diffCount_zero` — `diffCount D 0 = #D`.
* `IsDifferenceSet.hasFlatSpectrum` — **Proposition 2, forward**: a difference
  set has flat spectrum with `mu = #D - lam`.
* `HasFlatSpectrum.diffCount_const` — **Proposition 2, reverse**: flat spectrum
  forces constant autocorrelation, `card F * diffCount D s = (#D)^2 - mu` for
  every nonzero `s`.
-/

set_option maxHeartbeats 1600000

namespace DillonDobbertin

open Finset Fintype BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Integer indicator of a finite subset `D ⊆ F`. -/
noncomputable def ind (D : Finset F) (x : F) : ℤ := if x ∈ D then 1 else 0

/-- The additive-character Fourier transform of the indicator of `D`
(the paper's `F_D`): `fourier D a = ∑_{x ∈ D} χ(a·x)`. -/
noncomputable def fourier (D : Finset F) (a : F) : ℤ := ∑ x : F, ind D x * χ (a * x)

/-- The autocorrelation of `D` at shift `s`: the number of `x ∈ D` with
`x + s ∈ D`.  In characteristic two this is the number of ordered pairs of
elements of `D` whose difference (= sum) is `s`. -/
noncomputable def diffCount (D : Finset F) (s : F) : ℤ := ∑ x : F, ind D x * ind D (x + s)

/-- `D` is a difference set with parameter `lam` if every nonzero shift has
exactly `lam` autocorrelation, i.e. constant off the origin. -/
def IsDifferenceSet (D : Finset F) (lam : ℤ) : Prop := ∀ s : F, s ≠ 0 → diffCount D s = lam

/-- `D` has a flat Fourier spectrum with value `mu` if every nonzero frequency
has squared Fourier coefficient `mu`. -/
def HasFlatSpectrum (D : Finset F) (mu : ℤ) : Prop := ∀ a : F, a ≠ 0 → fourier D a ^ 2 = mu

/-
`fourier D a` is the sum of `χ (a·x)` over `x ∈ D`.
-/
theorem fourier_eq_sum_mem (D : Finset F) (a : F) :
    fourier D a = ∑ x ∈ D, χ (a * x) := by
  unfold fourier; simp +decide [ Finset.sum_ite, ind ] ;

/-
The autocorrelation at the origin counts the elements of `D`.
-/
theorem diffCount_zero (D : Finset F) : diffCount D 0 = (D.card : ℤ) := by
  unfold diffCount; simp +decide [ ind ] ;

/-
**Wiener–Khinchin (Fourier inversion form).**  The squared Fourier
coefficient of the indicator of `D` is the Fourier transform of the
autocorrelation:
`fourier D b ^ 2 = ∑ s, diffCount D s * χ (b · s)`.
-/
theorem fourier_sq_eq_sum_diffCount (D : Finset F) (b : F) :
    fourier D b ^ 2 = ∑ s : F, diffCount D s * χ (b * s) := by
  unfold fourier diffCount;
  simp +decide only [ind, sq, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ ← Equiv.sum_comp ( Equiv.addLeft y ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  simp +decide [ mul_add, add_mul, mul_comm, mul_left_comm, χ_mul ];
  grind +suggestions

/-
**Wiener–Khinchin (dual form).**  `card F` times the autocorrelation is the
inverse transform of the squared spectrum.
-/
theorem wiener_khinchin (D : Finset F) (s : F) :
    (Fintype.card F : ℤ) * diffCount D s = ∑ a : F, fourier D a ^ 2 * χ (a * s) := by
  have h_rhs : ∑ a : F, fourier D a ^ 2 * χ (a * s) = ∑ t : F, diffCount D t * ∑ a : F, χ (a * t) * χ (a * s) := by
    simp +decide only [fourier_sq_eq_sum_diffCount, sum_mul _ _ _];
    simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using Finset.sum_comm;
  -- By the orthogonality relations, we know that $\sum_{a \in F} \chi(a(t+s)) = \begin{cases} |F| & \text{if } t+s=0 \\ 0 & \text{otherwise} \end{cases}$.
  have h_orthog : ∀ t : F, ∑ a : F, χ (a * t) * χ (a * s) = if t + s = 0 then (Fintype.card F : ℤ) else 0 := by
    have h_orthog : ∀ t : F, ∑ a : F, χ (a * t) * χ (a * s) = ∑ a : F, χ (a * (t + s)) := by
      intro t; congr; ext a; rw [ ← WalshAB.χ_mul ] ; ring;
    intro t; rw [ h_orthog t ] ; rw [ χ_sum_dual ] ;
  simp_all +decide [ Finset.sum_ite, add_eq_zero_iff_eq_neg ];
  rw [ mul_comm ];
  simp +decide [ diffCount, CharTwo.neg_eq ]

/-
**Proposition 2, forward direction.**  A difference set has a flat Fourier
spectrum: every nonzero frequency `a` has `fourier D a ^ 2 = #D - lam`.
-/
theorem IsDifferenceSet.hasFlatSpectrum {D : Finset F} {lam : ℤ}
    (h : IsDifferenceSet D lam) : HasFlatSpectrum D ((D.card : ℤ) - lam) := by
  intro a ha;
  rw [ fourier_sq_eq_sum_diffCount, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ h x ( by aesop ) ] ];
  have := χ_sum_eq a; simp_all +decide [ ← Finset.mul_sum _ _ _ ] ;
  rw [ diffCount_zero, χ_zero ] ; ring

/-
**Proposition 2, reverse direction.**  A flat Fourier spectrum forces
constant autocorrelation off the origin:
`card F * diffCount D s = (#D)^2 - mu` for every nonzero `s`.
-/
theorem HasFlatSpectrum.diffCount_const {D : Finset F} {mu : ℤ}
    (h : HasFlatSpectrum D mu) (s : F) (hs : s ≠ 0) :
    (Fintype.card F : ℤ) * diffCount D s = (D.card : ℤ) ^ 2 - mu := by
  rw [ wiener_khinchin, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ h x ( by aesop ) ] ];
  have h_fourier_zero : fourier D 0 = (D.card : ℤ) := by
    convert fourier_eq_sum_mem D 0 using 1;
    simp +decide [ χ ];
  simp +decide [ ← Finset.mul_sum _ _ _, h_fourier_zero, hs, χ_zero, χ_sum_dual ];
  ring

end DillonDobbertin