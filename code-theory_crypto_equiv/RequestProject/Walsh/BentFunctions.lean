import Mathlib
import RequestProject.Walsh.Transform
import RequestProject.DifferenceSets.Basic

/-!
# Bent Boolean functions and their Parseval-based basic theory

This module is **Layer 1** of the Dillon–Dobbertin roadmap
(`DILLON_DOBBERTIN_ROADMAP.md`): the bent-function predicate together with its
Parseval-based basic theory, and the bridge that joins it to the difference-set
machinery of Stage 0 (`RequestProject/DifferenceSets/Basic.lean`).

A **Boolean function** here is a map `g : F → ZMod 2`, where `F` is a finite
field of characteristic two with `q = #F` elements.  Its *sign function* is
`signFn g x = (-1)^{g x} ∈ {1, -1}`, and its **Walsh transform** is
`bwalsh g a = ∑_x (-1)^{g x} χ(a·x)`, where `χ` is the trace sign character
(`WalshAB.χ`).

`g` is **bent** when its Walsh spectrum is *flat*: `(bwalsh g a)² = q` for every
frequency `a`.  Bent functions exist only for even `n` (`q` a perfect square),
but the predicate and its basic theory are stated unconditionally.

## Main results

* `parseval` — the **Parseval / Plancherel identity** `∑_a (bwalsh g a)² = q²`,
  the cornerstone of the basic theory.
* `signFn_eq_one_sub_two_ind` / `bwalsh_eq_neg_two_fourier` — the bridge to the
  indicator Fourier transform `DillonDobbertin.fourier`: away from the origin,
  `bwalsh g a = -2 · fourier (support g) a`.
* `IsBent.four_mul_fourier_sq` — for a bent `g`, `4 · fourier (support g) a² = q`
  at every nonzero frequency.
* `IsBent.exists_hasFlatSpectrum` — a bent function's support has a flat Fourier
  spectrum in the sense of `DillonDobbertin.HasFlatSpectrum`, hence (Proposition
  2) is a difference set: `IsBent.diffCount_const`.  This is the crypto→geometry
  bridge from bent functions to combinatorial designs.
-/

set_option maxHeartbeats 1600000

namespace BentFunctions

open Finset Fintype BigOperators WalshAB DillonDobbertin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The sign function `(-1)^{g x}` of a Boolean function `g : F → ZMod 2`. -/
noncomputable def signFn (g : F → ZMod 2) (x : F) : ℤ := if g x = 0 then 1 else -1

/-- The **Walsh transform** of a Boolean function `g`:
`bwalsh g a = ∑_x (-1)^{g x} χ(a·x)`. -/
noncomputable def bwalsh (g : F → ZMod 2) (a : F) : ℤ := ∑ x : F, signFn g x * χ (a * x)

/-- The **support** of `g`, i.e. `{x | g x = 1}`. -/
noncomputable def support (g : F → ZMod 2) : Finset F := Finset.univ.filter (fun x => g x = 1)

/-- A Boolean function `g` is **bent** when its Walsh spectrum is flat:
`(bwalsh g a)² = q` for every frequency `a`. -/
def IsBent {n : ℕ} (_ : Fintype.card F = 2 ^ n) (g : F → ZMod 2) : Prop :=
  ∀ a : F, (bwalsh g a) ^ 2 = (Fintype.card F : ℤ)

/-
The sign function squares to `1`.
-/
theorem signFn_sq (g : F → ZMod 2) (x : F) : signFn g x ^ 2 = 1 := by
  unfold signFn; split_ifs <;> simp_all +decide ;

/-
The sign function in terms of the integer indicator of the support:
`(-1)^{g x} = 1 - 2·ind (support g) x`.
-/
theorem signFn_eq_one_sub_two_ind (g : F → ZMod 2) (x : F) :
    signFn g x = 1 - 2 * ind (support g) x := by
  cases' Fin.exists_fin_two.mp ⟨ g x, rfl ⟩ with h h <;> simp +decide [ h, signFn, ind, support ]

/-
**Parseval / Plancherel identity.** `∑_a (bwalsh g a)² = q²`.
-/
theorem parseval (g : F → ZMod 2) :
    ∑ a : F, (bwalsh g a) ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  -- Expand `(bwalsh g a)^2` using the definition of `bwalsh`.
  have h_expand : ∀ a : F, (bwalsh g a) ^ 2 = ∑ x : F, ∑ y : F, signFn g x * signFn g y * χ (a * (x + y)) := by
    intro a;
    rw [ sq, bwalsh ];
    simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc, mul_add, χ_mul];
  -- Swap the order of summation over `a`.
  have h_swap : ∑ a : F, ∑ x : F, ∑ y : F, signFn g x * signFn g y * χ (a * (x + y)) = ∑ x : F, ∑ y : F, signFn g x * signFn g y * ∑ a : F, χ (a * (x + y)) := by
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ) );
  -- By `WalshAB.χ_sum_dual`, `∑ a, χ(a*(x+y)) = if x+y = 0 then (card F) else 0`.
  have h_dual : ∀ x y : F, ∑ a : F, χ (a * (x + y)) = if x + y = 0 then (Fintype.card F : ℤ) else 0 := by
    intro x y; specialize h_swap; have := χ_sum_dual ( x + y ) ; aesop;
  simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
  simp +decide [ ← eq_sub_iff_add_eq', Finset.sum_filter ];
  simp +decide [ signFn, CharTwo.neg_eq ];
  rw [ Finset.sum_congr rfl fun x hx => by aesop ] ; simp +decide [ sq ]

/-
**Bridge to the indicator Fourier transform.** Away from the origin, the
Walsh transform of `g` is `-2` times the Fourier transform of the indicator of
its support.
-/
theorem bwalsh_eq_neg_two_fourier (g : F → ZMod 2) (a : F) (ha : a ≠ 0) :
    bwalsh g a = -2 * fourier (support g) a := by
  -- Unfold `bwalsh` and rewrite `signFn g x = 1 - 2 * ind (support g) x` (lemma `signFn_eq_one_sub_two_ind`).
  have hbwalsh : bwalsh g a = ∑ x : F, (1 - 2 * ind (support g) x) * χ (a * x) := by
    exact Finset.sum_congr rfl fun x _ => by rw [ ← signFn_eq_one_sub_two_ind g x ] ;
  simp_all +decide [ sub_mul, mul_assoc, Finset.mul_sum _ _ _, DillonDobbertin.fourier ];
  convert WalshAB.χ_sum_eq a using 1 ; aesop

/-
For a bent function, the indicator Fourier transform of the support has
constant squared modulus off the origin: `4 · fourier (support g) a² = q`.
-/
theorem IsBent.four_mul_fourier_sq {n : ℕ} {hcard : Fintype.card F = 2 ^ n}
    {g : F → ZMod 2} (h : IsBent hcard g) (a : F) (ha : a ≠ 0) :
    4 * fourier (support g) a ^ 2 = (Fintype.card F : ℤ) := by
  -- By h_bwalsh_eq, we have bwalsh g a = -2 * DillonDobbertin.fourier (support g) a.
  have h_bwalsh_eq : bwalsh g a = -2 * DillonDobbertin.fourier (support g) a := by
    grind +suggestions;
  convert h a using 1 ; rw [ h_bwalsh_eq ] ; ring

/-
A bent function's support has a **flat Fourier spectrum** in the sense of
`DillonDobbertin.HasFlatSpectrum`.
-/
theorem IsBent.exists_hasFlatSpectrum {n : ℕ} {hcard : Fintype.card F = 2 ^ n}
    {g : F → ZMod 2} (h : IsBent hcard g) :
    ∃ mu, HasFlatSpectrum (support g) mu := by
  obtain ⟨a0, ha0⟩ : ∃ a0 : F, a0 ≠ 0 := by
    exact exists_ne 0;
  refine' ⟨ fourier ( support g ) a0 ^ 2, fun a ha => _ ⟩;
  linarith [ IsBent.four_mul_fourier_sq h a ha, IsBent.four_mul_fourier_sq h a0 ha0 ]

/-
**Crypto → geometry bridge.** The support of a bent function is a difference
set: its autocorrelation is constant off the origin
(`card F · diffCount = (#D)² − mu`), via Proposition 2.
-/
theorem IsBent.diffCount_const {n : ℕ} {hcard : Fintype.card F = 2 ^ n}
    {g : F → ZMod 2} (h : IsBent hcard g) :
    ∃ mu, ∀ s : F, s ≠ 0 →
      (Fintype.card F : ℤ) * diffCount (support g) s = ((support g).card : ℤ) ^ 2 - mu := by
  obtain ⟨ mu, hmu ⟩ := IsBent.exists_hasFlatSpectrum h;
  exact ⟨ mu, fun s hs => DillonDobbertin.HasFlatSpectrum.diffCount_const hmu s hs ⟩

end BentFunctions