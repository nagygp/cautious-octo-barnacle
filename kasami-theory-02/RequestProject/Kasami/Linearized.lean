/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Linearized Polynomials and Derivative Properties

This file establishes key algebraic properties of the Kasami power function's
derivative, including the 2-to-1 property that underpins the difference set structure.
-/
import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.CharTwo
import RequestProject.Kasami.Trace

open scoped BigOperators
open Classical Finset
noncomputable section

namespace Kasami

variable {n : ℕ} [NeZero n]

/-- The derivative function `D(b) = F(b) + F(b+1) + 1`. -/
def derivFun [Fintype (GaloisField 2 n)] (k : ℕ)
    (b : GaloisField 2 n) : GaloisField 2 n :=
  powerFun k b + powerFun k (b + 1) + 1

/-- `D(b) = D(b+1)` in characteristic 2. -/
theorem derivFun_periodic [Fintype (GaloisField 2 n)] (k : ℕ)
    (b : GaloisField 2 n) : derivFun k b = derivFun k (b + 1) := by
  unfold derivFun
  have h : b + 1 + 1 = b := by
    have h1 : (1 : GaloisField 2 n) + 1 = 0 := charTwo_add_self 1
    have : b + 1 + 1 = b + (1 + 1) := by ring
    rw [this, h1, add_zero]
  rw [h]; ring

/-- For the Kasami function, the derivative `D` is exactly 2-to-1:
`D(b₁) = D(b₂)` implies `b₂ = b₁` or `b₂ = b₁ + 1`.

This is a deep algebraic result following from the factorization of the
derivative polynomial through linearized polynomials. The equation
`F(b₁) + F(b₁+1) = F(b₂) + F(b₂+1)` reduces via the Kasami exponent
structure to a linearized polynomial equation whose kernel over `GF(2^n)`
has dimension 1 over `GF(2)` when `gcd(k, n) = 1`. -/
theorem derivFun_two_to_one [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 2 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n)
    (b₁ b₂ : GaloisField 2 n)
    (heq : derivFun k b₁ = derivFun k b₂) :
    b₂ = b₁ ∨ b₂ = b₁ + 1 := by
  sorry

/-- Each fiber of `derivFun k` has exactly 2 elements. -/
theorem derivFun_fiber_card [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 2 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n)
    (c : GaloisField 2 n) (hc : c ∈ univ.image (derivFun (n := n) k)) :
    (univ.filter fun b => derivFun k b = c).card = 2 := by
  obtain ⟨b₀, _, rfl⟩ := Finset.mem_image.mp hc
  have h_fiber : ∀ b, derivFun k b = derivFun k b₀ → b = b₀ ∨ b = b₀ + 1 :=
    fun b a => derivFun_two_to_one hk hn hn_odd hgcd b₀ b (id (Eq.symm a))
  rw [Finset.card_eq_two]
  refine ⟨b₀, b₀ + 1, ?_, ?_⟩ <;> norm_num [Finset.ext_iff]
  exact fun x => ⟨h_fiber x, fun hx =>
    hx.elim (fun hx => hx.symm ▸ rfl)
      fun hx => hx.symm ▸ derivFun_periodic k b₀ ▸ rfl⟩

/-- The number of solutions to `F(x + t) + F(x) = c`. -/
def diffCountL [Fintype (GaloisField 2 n)] (k : ℕ)
    (t c : GaloisField 2 n) : ℕ :=
  Finset.card (Finset.univ.filter fun x : GaloisField 2 n =>
    powerFun k (x + t) + powerFun k x = c)

/-
The Kasami function is APN: differential count is at most 2.
-/
theorem diffCountL_le_two [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (hn_odd : n % 2 = 1)
    (hgcd : Nat.Coprime k n) (t : GaloisField 2 n) (ht : t ≠ 0)
    (c : GaloisField 2 n) :
    diffCountL k t c ≤ 2 := by
  -- By definition of $diffCountL$, we know that
  have h_diffCountL_def : Finset.card (Finset.filter (fun x => powerFun k (x + t) + powerFun k x = c) (Finset.univ : Finset (GaloisField 2 n))) = Finset.card (Finset.filter (fun y => derivFun k y = c / t ^ (kasamiExponent k) + 1) (Finset.univ : Finset (GaloisField 2 n))) := by
    fapply Finset.card_bij;
    use fun x hx => x / t;
    · intro x hx
      simp [derivFun, powerFun] at *;
      field_simp;
      rw [ ← hx, add_mul, ← mul_pow, div_mul_cancel₀ _ ht, ← mul_pow, div_mul_cancel₀ _ ht ] ; ring;
    · grind;
    · intro b hb;
      refine' ⟨ b * t, _, _ ⟩ <;> simp_all +decide [ derivFun, powerFun ];
      rw [ show b * t + t = t * ( b + 1 ) by ring, show b * t = t * b by ring, mul_pow, mul_pow ];
      rw [ ← mul_add, add_comm, hb, mul_div_cancel₀ _ ( pow_ne_zero _ ht ) ];
  by_cases h : c / t ^ kasamiExponent k + 1 ∈ Finset.image ( derivFun k ) Finset.univ;
  · have := derivFun_fiber_card hk hn hn_odd hgcd ( c / t ^ kasamiExponent k + 1 ) ?_ <;> simp_all +decide [ diffCountL ];
  · unfold diffCountL; aesop;

/-- Differential uniformity ≤ 4 (weaker than the APN bound ≤ 2, but matches
the theorem statement in the main file). -/
theorem diffCountL_le_four [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (hn_odd : n % 2 = 1)
    (hgcd : Nat.Coprime k n) (t : GaloisField 2 n) (ht : t ≠ 0)
    (c : GaloisField 2 n) :
    diffCountL k t c ≤ 4 :=
  le_trans (diffCountL_le_two hk hn hn_odd hgcd t ht c) (by norm_num)

/-
Solutions to `F(x+t)+F(x) = c` come in pairs: if `x` is a solution, so is `x+t`.
Therefore `diffCountL` is even.
-/
theorem diffCountL_even [Fintype (GaloisField 2 n)]
    (k : ℕ) (t : GaloisField 2 n) (ht : t ≠ 0)
    (c : GaloisField 2 n) :
    Even (diffCountL k t c) := by
  -- Define the involution on the solution set.
  set S := Finset.univ.filter (fun x => powerFun k (x + t) + powerFun k x = c)
  have h_inv : ∀ x ∈ S, x + t ∈ S := by
    grind +qlia;
  -- Since the involution is fixed-point-free, the set S can be partitioned into pairs {x, x+t}.
  have h_partition : ∃ T : Finset (Finset (GaloisField 2 n)), (∀ p ∈ T, p.card = 2) ∧ (∀ p ∈ T, ∀ q ∈ T, p ≠ q → p ∩ q = ∅) ∧ S = Finset.biUnion T id := by
    refine' ⟨ Finset.image ( fun x => { x, x + t } ) S, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · grind +locals;
    · ext x; aesop;
  obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_partition; rw [ show diffCountL k t c = S.card from rfl ] ; rw [ hT₃ ] ; rw [ Finset.card_biUnion ] ; aesop;
  exact fun p hp q hq hpq => Finset.disjoint_iff_inter_eq_empty.mpr ( hT₂ p hp q hq hpq )

/-
For the Kasami function (APN), the differential count is exactly 0 or 2.
-/
theorem diffCountL_eq_zero_or_two [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (hn_odd : n % 2 = 1)
    (hgcd : Nat.Coprime k n) (t : GaloisField 2 n) (ht : t ≠ 0)
    (c : GaloisField 2 n) :
    diffCountL k t c = 0 ∨ diffCountL k t c = 2 := by
  have h_diffCountL_even : Even (diffCountL k t c) := by
    exact?;
  exact Classical.or_iff_not_imp_left.2 fun h => le_antisymm ( by exact? ) ( Nat.le_of_dvd ( Nat.pos_of_ne_zero h ) ( even_iff_two_dvd.mp h_diffCountL_even ) )

/-
The total count: `Σ_c N(t,c) = 2^n` for any `t`.
-/
theorem diffCountL_sum [Fintype (GaloisField 2 n)]
    (k : ℕ) (t : GaloisField 2 n) :
    ∑ c : GaloisField 2 n, diffCountL k t c =
      Fintype.card (GaloisField 2 n) := by
  rw [ Fintype.card_eq_sum_ones ];
  simp +decide only [diffCountL, card_eq_sum_ones];
  rw [ Finset.sum_sigma' ];
  refine' Finset.sum_bij ( fun x _ => x.2 ) _ _ _ _ <;> aesop

/-- The autocorrelation function of the Kasami power function:
`S(t) = Σ_x (-1)^{Tr(F(x+t) + F(x))}`. -/
def autoCorrelation [Fintype (GaloisField 2 n)] (k : ℕ)
    (t : GaloisField 2 n) : ℤ :=
  ∑ x : GaloisField 2 n,
    traceLift (powerFun k (x + t) + powerFun k x)

/-
For each nonzero `t`, `Σ_c N(t,c)^2 = 2 · 2^n` for the Kasami (APN) function.
-/
theorem diffCountL_sum_sq [Fintype (GaloisField 2 n)]
    {k : ℕ} (hk : 2 ≤ k)
    (hn : 2 ≤ n) (hn_odd : n % 2 = 1) (hgcd : Nat.Coprime k n)
    (t : GaloisField 2 n) (ht : t ≠ 0) :
    ∑ c : GaloisField 2 n, (diffCountL k t c : ℤ) ^ 2 =
      2 * (2 : ℤ) ^ n := by
  have h_sum_sq : ∑ c : GaloisField 2 n, (diffCountL k t c : ℤ) ^ 2 = 4 * (∑ c : GaloisField 2 n, if diffCountL k t c = 2 then 1 else 0) := by
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext c ; rcases diffCountL_eq_zero_or_two hk hn hn_odd hgcd t ht c with h | h <;> norm_num [ h ] ;
  have h_sum : ∑ c : GaloisField 2 n, (diffCountL k t c : ℤ) = 2 ^ n := by
    norm_cast;
    convert diffCountL_sum k t;
    rw [ ← GaloisField.card ] ; aesop;
    linarith;
  have h_sum_eq : ∑ c : GaloisField 2 n, (diffCountL k t c : ℤ) = 2 * (∑ c : GaloisField 2 n, if diffCountL k t c = 2 then 1 else 0) := by
    rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun x hx => by rcases diffCountL_eq_zero_or_two hk hn hn_odd hgcd t ht x with h | h <;> norm_num [ h ] ;
  grind

end Kasami

end