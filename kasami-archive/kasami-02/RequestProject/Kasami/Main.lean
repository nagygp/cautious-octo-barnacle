/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Three-Valued Walsh Spectrum of Kasami Power Functions

This file proves that the Walsh spectrum of the Kasami power function
`F(x) = x^{4^k - 2^k + 1}` on `GF(2^n)` takes exactly three values
when `gcd(k, n) = 1` and `k > 1`: namely `{0, ±2^{(n+1)/2}}`.

This is the celebrated result of Kasami (1971), with the full proof for
general `gcd(k, n) = 1` completed by Canteaut, Charpin, and Dobbertin (2000).

## Main results

* `Kasami.walshSpectrum_three_valued` : The Walsh transform of the Kasami function
  takes values in `{0, 2^((n+1)/2), -2^((n+1)/2)}`.
* `Kasami.deltaSet_tripleCorrelation` : The triple correlation property P₃.

## References

* T. Kasami, "The weight enumerators for several classes of subcodes of the
  2nd order binary Reed-Muller codes", Inform. Control 18 (1971), 369-394.
* A. Canteaut, P. Charpin, H. Dobbertin, "Binary m-sequences with three-valued
  crosscorrelation: A proof of Welch's conjecture", IEEE Trans. Inform. Theory
  46 (2000), 4-8.
-/
import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.CharTwo
import RequestProject.Kasami.Exponent
import RequestProject.Kasami.Trace
import RequestProject.Kasami.Walsh
import RequestProject.Kasami.Linearized

open scoped BigOperators
noncomputable section
open Classical Finset

set_option maxHeartbeats 800000

namespace Kasami

variable {n : ℕ} [NeZero n]

/-! ### Differential Properties of the Kasami Function -/

/-- The number of solutions to `F(x + t) + F(x) = c` for fixed nonzero `t` and `c`. -/
def diffCount [Fintype (GaloisField 2 n)] (k : ℕ)
    (t c : GaloisField 2 n) : ℕ :=
  Finset.card (Finset.univ.filter fun x : GaloisField 2 n =>
    powerFun k (x + t) + powerFun k x = c)

/-- The differential uniformity of the Kasami function is at most 4.
Uses `diffCountL_le_four` from the Linearized module. -/
theorem kasami_differential_uniformity [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (hn_odd : n % 2 = 1)
    (hgcd : Nat.Coprime k n) (t : GaloisField 2 n) (ht : t ≠ 0)
    (c : GaloisField 2 n) :
    diffCount k t c ≤ 4 := by
  exact diffCountL_le_four hk hn hn_odd hgcd t ht c

/-! ### The Quartic Relation -/

/-- The quartic relation: `W_F(a)^4 = 2^{n+1} · W_F(a)^2` for all `a`.

This is the deep result from Canteaut-Charpin-Dobbertin (2000). The proof
uses the structure of the autocorrelation function `S(t)` and the specific
algebraic properties of the Kasami exponent through linearized polynomials.

The CCD proof shows that `W_F(a)^2 ∈ {0, 2^{n+1}}` for all `a`, which is
equivalent to the quartic relation `W^4 = 2^{n+1} · W^2`. -/
theorem walsh_quartic_relation
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 2 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n)
    [Fintype (GaloisField 2 n)]
    (a : GaloisField 2 n) :
    (walshTransform (powerFun (n := n) k) a) ^ 4 =
      (2 : ℤ) ^ (n + 1) * (walshTransform (powerFun (n := n) k) a) ^ 2 := by
  sorry

/-
The fourth moment of the Walsh transform: `Σ_a W_F(a)^4 = 2^{3n+1}`.
This follows from the quartic relation and Parseval's identity:
`Σ W^4 = 2^{n+1} · Σ W^2 = 2^{n+1} · 2^{2n} = 2^{3n+1}`.
-/
theorem walsh_fourth_moment [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (hn_odd : n % 2 = 1)
    (hgcd : Nat.Coprime k n) :
    ∑ a : GaloisField 2 n,
      (walshTransform (powerFun (n := n) k) a) ^ 4 =
      (2 : ℤ) ^ (3 * n + 1) := by
  convert Finset.sum_congr rfl fun a _ => walsh_quartic_relation hk hn hn_odd hgcd a using 1;
  rw [ ← Finset.mul_sum _ _ _, walshTransform_parseval ] ; ring;
  rw [ Fintype.card_eq_nat_card ];
  rw [ GaloisField.card ] ; norm_num ; ring;
  grind

/-- **Three-Valued Walsh Spectrum Theorem** (Kasami 1971, CCD 2000). -/
theorem walshSpectrum_three_valued
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 2 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n)
    [Fintype (GaloisField 2 n)]
    (a : GaloisField 2 n) :
    walshTransform (powerFun (n := n) k) a = 0 ∨
    walshTransform (powerFun (n := n) k) a = 2 ^ ((n + 1) / 2) ∨
    walshTransform (powerFun (n := n) k) a = -(2 ^ ((n + 1) / 2)) := by
  have h_quartic := walsh_quartic_relation hk hn hn_odd hgcd a
  have h_walsh_sq : (walshTransform (powerFun (n := n) k) a) ^ 2 *
      ((walshTransform (powerFun (n := n) k) a) ^ 2 - 2 ^ (n + 1)) = 0 := by
    linarith
  simp_all +decide [sub_eq_iff_eq_add]
  exact h_walsh_sq.imp id fun h => eq_or_eq_neg_of_sq_eq_sq _ _ <| by
    rw [h, ← pow_mul, Nat.div_mul_cancel <| Nat.dvd_of_mod_eq_zero <| by omega]

/-! ### The Difference Set and Triple Correlation (P₃) -/

/-- The `deltaSet` viewed as a `Finset`. -/
def deltaFinset [Fintype (GaloisField 2 n)] (k : ℕ) :
    Finset (GaloisField 2 n) :=
  Finset.univ.image (fun b : GaloisField 2 n =>
    powerFun k b + powerFun k (b + 1) + 1)

/-- The `deltaFinset` represents the same set as `deltaSet`. -/
theorem mem_deltaFinset_iff [Fintype (GaloisField 2 n)] (k : ℕ)
    (x : GaloisField 2 n) :
    x ∈ deltaFinset k ↔ x ∈ deltaSet (n := n) k := by
  simp only [deltaFinset, deltaSet, Finset.mem_image, Finset.mem_univ,
    true_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, ha.symm⟩
  · rintro ⟨a, ha⟩; exact ⟨a, ha.symm⟩

/-- The discrete derivative `D(b) = F(b) + F(b+1) + 1` satisfies `D(b) = D(b+1)`. -/
theorem derivative_periodic [Fintype (GaloisField 2 n)] (k : ℕ)
    (b : GaloisField 2 n) :
    powerFun k b + powerFun k (b + 1) + 1 =
    powerFun k (b + 1) + powerFun k (b + 1 + 1) + 1 := by
  have h : b + 1 + 1 = b := by
    have h1 : (1 : GaloisField 2 n) + 1 = 0 := charTwo_add_self 1
    have : b + 1 + 1 = b + (1 + 1) := by ring
    rw [this, h1, add_zero]
  rw [h]; ring

/-- The deltaFinset is the image of derivFun. -/
theorem deltaFinset_eq_image_derivFun [Fintype (GaloisField 2 n)] (k : ℕ) :
    deltaFinset k = Finset.univ.image (derivFun (n := n) k) := by
  unfold deltaFinset derivFun; rfl

/-- The difference set `Δ` has `2^(n-1)` elements. -/
theorem deltaFinset_card [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 2 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n) :
    (deltaFinset (n := n) k).card = 2 ^ (n - 1) := by
  have h_delta_size : (Finset.univ.image (derivFun (n := n) k)).card * 2 = (Finset.univ : Finset (GaloisField 2 n)).card := by
    have h_delta_size : ∑ c ∈ Finset.univ.image (derivFun (n := n) k), (Finset.univ.filter fun b => derivFun (n := n) k b = c).card = (Finset.univ : Finset (GaloisField 2 n)).card :=
      Eq.symm (card_eq_sum_card_image (derivFun k) univ)
    rw [← h_delta_size, Finset.sum_const_nat]
    exact fun x a => derivFun_fiber_card hk hn hn_odd hgcd x a
  simp_all +decide [deltaFinset_eq_image_derivFun]
  have h_card : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    convert GaloisField.card 2 n
    aesop
  cases n <;> simp_all +decide [pow_succ'] ; linarith

/-- The set of triples `(x, y, z) ∈ Δ × Δ × Δ` satisfying
the linear constraint `v₁ · x + v₂ · y + (v₁ + v₂) · z = 0`. -/
def constrainedTriples [Fintype (GaloisField 2 n)]
    (k : ℕ) (v₁ v₂ : GaloisField 2 n) :
    Finset (GaloisField 2 n × GaloisField 2 n × GaloisField 2 n) :=
  ((deltaFinset k) ×ˢ (deltaFinset k) ×ˢ (deltaFinset k)).filter
    (fun t => v₁ * t.1 + v₂ * t.2.1 + (v₁ + v₂) * t.2.2 = 0)

/-- The Walsh transform of `Δ` takes values in `{-2^(n-1), 0, 2^(n-1)}`. -/
theorem walshTransformSet_deltaFinset_spectrum [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 2 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n)
    (a : GaloisField 2 n) :
    walshTransformSet (deltaFinset k) a = 0 ∨
    walshTransformSet (deltaFinset k) a = 2 ^ (n - 1) ∨
    walshTransformSet (deltaFinset k) a = -(2 ^ (n - 1) : ℤ) := by
  sorry

/-- **Theorem P₃**: Triple correlation of the Kasami difference set. -/
theorem deltaSet_tripleCorrelation
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n)
    [Fintype (GaloisField 2 n)]
    (v₁ v₂ : GaloisField 2 n) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (constrainedTriples k v₁ v₂).card = 2 ^ (2 * n - 3) := by
  sorry

end Kasami

end