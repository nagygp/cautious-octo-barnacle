import RequestProject.CrossFormAnalysis
import RequestProject.KasamiMCM

/-!
# Cross-Pair Analysis: Kasami APN Proof

Proves: no cross-pairs exist for the Kasami sVal map, hence
the Kasami function is APN (each differential equation has ≤ 2 solutions).

## Proof strategy

1. From the collision equation: `Cross(s₀, P) = L_{3k}(c)`
2. From cross-zero triviality + power map injectivity: `Cross(s₀, P) ≠ 0`
3. The Gold-level equation then yields a contradiction via MCM injectivity.

## Key results
- `cross_pair_analysis`: no cross-pairs exist
- `sval_fiber_le_two`: each sVal fiber has ≤ 2 elements
- `kasami_apn`: the Kasami power function is APN
-/

set_option maxHeartbeats 800000

namespace CollisionAnalysis

open Finset Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Injectivity constraints on P -/

/-- `t₁^d + t₂^d ≠ 0` when `t₁ ≠ t₂` (from power map injectivity). -/
theorem P_ne_zero {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) (t₁ t₂ : F) (hne : t₂ ≠ t₁) :
    t₁ ^ d k + t₂ ^ d k ≠ 0 := by
  by_contra h_contra
  have h_eq : t₁ ^ d k = t₂ ^ d k := by grind +ring
  by_cases ht₁ : t₁ = 0 <;> by_cases ht₂ : t₂ = 0 <;> simp_all +decide
  · exact absurd h_eq.symm (by
      rw [zero_pow (by exact Nat.ne_of_gt (d_pos k hk))]
      exact pow_ne_zero _ ht₂)
  · simp_all +decide [ne_of_gt (d_pos k hk)]
  · have := pow_d_injective hcard k hk hcop hnodd hn t₁ t₂ ht₁ ht₂ h_eq; aesop

/-- `t₁^d + t₂^d ≠ sVal(t₁)` when `t₂ ≠ t₁ + 1` (from power map injectivity). -/
theorem P_ne_sVal {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) (t₁ t₂ : F) (hne1 : t₂ ≠ t₁ + 1) :
    t₁ ^ d k + t₂ ^ d k ≠ sVal k t₁ := by
  intro h_eq
  have h_power : t₂ ^ d k = (t₁ + 1) ^ d k := by
    unfold sVal at h_eq; linear_combination h_eq
  by_cases h : t₂ = 0 <;> by_cases h' : t₁ + 1 = 0 <;> simp_all +decide
  · exact absurd h_power (by
      rw [zero_pow (d_pos k hk |> ne_of_gt)]
      exact Ne.symm (pow_ne_zero _ h'))
  · simp_all +decide [show d k ≠ 0 from by exact ne_of_gt (d_pos k hk)]
  · exact hne1 (pow_d_injective hcard k hk hcop hnodd hn t₂ (t₁ + 1) h h' h_power)

/-- `Cross(s₀, P) ≠ 0` when `t₂ ∉ {t₁, t₁+1}`. -/
theorem Cross_ne_zero {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) (t₁ t₂ : F) (hne : t₂ ≠ t₁) (hne1 : t₂ ≠ t₁ + 1)
    (hs0 : sVal k t₁ ≠ 0) :
    Cross k (sVal k t₁) (t₁ ^ d k + t₂ ^ d k) ≠ 0 := by
  intro habs
  rw [cross_zero_iff_trivial hcard k hcop _ _ hs0] at habs
  rcases habs with h | h
  · exact P_ne_zero hcard k hk hcop hnodd hn t₁ t₂ hne h
  · exact P_ne_sVal hcard k hk hcop hnodd hn t₁ t₂ hne1 h

/-! ## Gold-level equation -/

omit [Fintype F] [DecidableEq F] in
/-- Raises `(t+1)^d + t^d = s₀` to the `(2^k+1)`-th power. -/
theorem gold_level_equation (k : ℕ) (hk : k ≥ 1) (t s₀ : F)
    (hs : sVal k t = s₀) :
    Cross k s₀ (t ^ d k) = L (3 * k) t + 1 + N k s₀ := by
  have h_freshman :
      ((t + 1) ^ d k + t ^ d k) ^ (2 ^ k + 1) =
      (t + 1) ^ (d k * (2 ^ k + 1)) + t ^ (d k * (2 ^ k + 1)) +
      (t + 1) ^ d k * t ^ (d k * 2 ^ k) +
      (t + 1) ^ (d k * 2 ^ k) * t ^ d k := by
    ring
    simp +decide [pow_mul, add_pow_char_pow]; ring
  simp_all +decide [sVal, Cross, L, N, d_mul_gold _ hk]
  rw [← hs]; ring
  simp +decide [add_pow_char_pow, mul_add, add_assoc, add_left_comm, add_comm]; ring
  rw [show (2 : F) = 0 by exact CharP.cast_eq_zero F 2]; ring

/-! ## Main theorem -/

/-- No cross-pairs exist: if `sVal(t₁) = sVal(t₂)` then `t₂ ∈ {t₁, t₁+1}`. -/
theorem cross_pair_analysis {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) (t₁ t₂ : F)
    (hs : sVal k t₁ = sVal k t₂)
    (hne : t₂ ≠ t₁) (hne1 : t₂ ≠ t₁ + 1)
    (hs0 : sVal k t₁ ≠ 0) :
    False := by
  have hG1 := gold_level_equation k hk t₁ (sVal k t₁) rfl
  have hG2 := gold_level_equation k hk t₂ (sVal k t₁) (hs ▸ rfl)
  have hSum : Cross k (sVal k t₁) (t₁ ^ d k + t₂ ^ d k) =
      L (3 * k) (t₁ + t₂) :=
    collision_equation k hk t₁ t₂ hs
  have hCross_ne := Cross_ne_zero hcard k hk hcop hnodd hn t₁ t₂ hne hne1 hs0
  exact cross_pair_analysis_mcm hcard k hk hcop hnodd hn t₁ t₂ hs hne hne1 hs0

/-! ## Applications -/

/-- Each sVal fiber has at most 2 elements. -/
theorem sval_fiber_le_two {k n : ℕ} (hk : k ≥ 1) (hn : 0 < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) (s : F) :
    Fintype.card {t : F // sVal k t = s} ≤ 2 := by
  by_contra h_contra
  obtain ⟨t₁, t₂, t₃, ht₁, ht₂, ht₃, h_distinct⟩ :
      ∃ t₁ t₂ t₃ : F, sVal k t₁ = s ∧ sVal k t₂ = s ∧ sVal k t₃ = s ∧
        t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ := by
    obtain ⟨t₁, t₂, t₃, h⟩ := Fintype.two_lt_card_iff.mp (lt_of_not_ge h_contra)
    use t₁, t₂, t₃; aesop
  have h_contradiction : ∀ t₁ t₂ : F,
      sVal k t₁ = sVal k t₂ → t₂ ≠ t₁ → t₂ ≠ t₁ + 1 → False :=
    fun t₁ t₂ h_eq h_ne h_ne1 =>
      cross_pair_analysis hcard k hk hcop hnodd hn t₁ t₂ h_eq h_ne h_ne1
        (sVal_ne_zero hk hn hcop hnodd hcard t₁)
  grind +ring

/-- **Kasami APN**: the Kasami power function `x^d` is APN. -/
theorem kasami_apn {k n : ℕ} (hk : k ≥ 1) (hn : n ≥ 1)
    (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤ 2 := by
  intro a ha b
  have h_card :
      Fintype.card {x : F | (x + a) ^ d k + x ^ d k = b} =
      Fintype.card {t : F | (t + 1) ^ d k + t ^ d k = b / a ^ d k} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    refine Finset.card_bij (fun x _ => x / a) ?_ ?_ ?_ <;>
      simp_all +decide [mul_pow, div_eq_iff]
    · field_simp
      intro x hx; rw [← hx]; simp +decide [add_mul, div_pow, ha]
    · intro x hx
      rw [show x * a + a = a * (x + 1) by ring, mul_pow]
      rw [eq_div_iff (pow_ne_zero _ ha)] at hx; linear_combination hx
  convert sval_fiber_le_two hk hn hcop hnodd hcard (b / a ^ d k) using 1

end CollisionAnalysis
