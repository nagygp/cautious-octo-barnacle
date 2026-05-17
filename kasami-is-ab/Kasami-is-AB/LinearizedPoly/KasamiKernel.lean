/-
# Kasami Derivative Kernel Analysis

This module establishes the connection between the Kasami power function
derivative and linearized polynomials, then uses the kernel dimension
theory to prove key properties of the Kasami derivative.

## Main results

* `kasamiExp` : The Kasami exponent `d = 4^k - 2^k + 1`
* `kasamiDelta_periodic` : δ(b) = δ(b+1) (char 2 symmetry)
* `kasamiDiff_normalize` : Normalization of the differential
* `kasamiDelta_two_to_one` : 2-to-1 property when gcd(k,n) = 1 and 3 ∤ n
* `kasamiDiff_count_even` : Differential count is always even

## References

* Kasami (1971), *Information and Control* 18(4)
* Canteaut, Charpin, Dobbertin (2000), *SIAM J. Discrete Math.* 13(1)
-/
import Mathlib
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Kasami Exponent -/

/-- The Kasami exponent: `d(k) = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- For k ≥ 1, `2^k ≤ 4^k`. -/
theorem two_pow_le_four_pow (k : ℕ) : 2 ^ k ≤ 4 ^ k := by
  calc 2 ^ k ≤ (2 ^ 2) ^ k := Nat.pow_le_pow_left (by norm_num) k
    _ = 4 ^ k := by ring_nf

/-- `d(1) = 3` (the Gold exponent). -/
@[simp] theorem kasamiExp_one : kasamiExp 1 = 3 := by simp [kasamiExp]

/-- `d(2) = 13`. -/
@[simp] theorem kasamiExp_two : kasamiExp 2 = 13 := by simp [kasamiExp]

/-! ### The Kasami power function and its derivative -/

/-- The Kasami power function `G(x) = x^{d(k)}`. -/
def kasamiPow (k : ℕ) (x : F) : F := x ^ kasamiExp k

/-- The Kasami delta function: `δ(b) = G(b) + G(b+1) + 1`. -/
def kasamiDelta (k : ℕ) (b : F) : F :=
  kasamiPow k b + kasamiPow k (b + 1) + 1

/-- The symmetry `δ(b) = δ(b + 1)` in characteristic 2. -/
theorem kasamiDelta_periodic (k : ℕ) (b : F) :
    kasamiDelta k b = kasamiDelta k (b + 1) := by
  unfold kasamiDelta kasamiPow
  have h1 : b + 1 + 1 = b := by
    have : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    calc b + 1 + 1 = b + (1 + 1) := by ring
      _ = b + 0 := by rw [this]
      _ = b := by ring
  rw [h1]; ring

/-! ### Derivative and linearized polynomial connection -/

/-- The differential operator: `D_a G(x) = G(x + a) + G(x)`. -/
def kasamiDiff (k : ℕ) (a x : F) : F :=
  kasamiPow k (x + a) + kasamiPow k x

/-
For the power function `x^d`, the differential satisfies
    `D_a G(x) = a^d · D_1(x/a)` for `a ≠ 0`.
-/
theorem kasamiDiff_normalize (k : ℕ) (a x : F) (ha : a ≠ 0) :
    kasamiDiff k a x = a ^ kasamiExp k * kasamiDiff k 1 (x * a⁻¹) := by
  unfold kasamiDiff;
  unfold kasamiPow;
  field_simp;
  rw [ mul_add, ← mul_pow, ← mul_pow, mul_div_cancel₀ _ ha, mul_div_cancel₀ _ ha ]

/-- The equation `D_1 G(y₁) = D_1 G(y₂)` implies either `y₁ = y₂`, `y₁ = y₂ + 1`,
    or `z = y₁ + y₂` is a nonzero root of a linearized polynomial equation. -/
theorem kasamiDiff_eq_implies_linearized (k : ℕ) (hk : 0 < k)
    (y₁ y₂ : F) (heq : kasamiDiff k 1 y₁ = kasamiDiff k 1 y₂) :
    y₁ = y₂ ∨ y₁ = y₂ + 1 ∨ linPolyL k (y₁ + y₂) = 0 := by
  sorry

/-! ### The 2-to-1 theorem -/

/-
**Kasami derivative is 2-to-1** when `gcd(k,n) = 1` and `3 ∤ n`:
    `δ(b₁) = δ(b₂)` implies `b₂ = b₁` or `b₂ = b₁ + 1`.
-/
theorem kasamiDelta_two_to_one (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (b₁ b₂ : F) (heq : kasamiDelta k b₁ = kasamiDelta k b₂) :
    b₂ = b₁ ∨ b₂ = b₁ + 1 := by
  -- By kasamiDiff_eq_implies_linearized, we have either `b₁ = b₂`, `b₁ = b₂ + 1`, or `linPolyL k (b₁ + b₂) = 0`.
  have h_cases : b₁ = b₂ ∨ b₁ = b₂ + 1 ∨ linPolyL k (b₁ + b₂) = 0 := by
    unfold kasamiDelta at heq
    have h_diff : kasamiDiff k 1 b₁ = kasamiDiff k 1 b₂ := by
      unfold kasamiDiff; ring;
      grind +ring;
    exact?;
  -- By linPolyL_ker_trivial_of_three_ndvd, if `linPolyL k (b₁ + b₂) = 0`, then `b₁ + b₂ = 0`, i.e., `b₁ = b₂`.
  have h_trivial : funKer (linPolyL (F := F) k) = {0} := by
    exact?;
  simp_all +decide [ Finset.ext_iff, funKer ];
  grind +splitImp

/-
**Kasami delta set cardinality**: When the derivative is 2-to-1,
    the delta set has `|F|/2` elements.
-/
theorem kasamiDelta_image_card (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n) :
    (Finset.univ.image (kasamiDelta (F := F) k)).card = 2 ^ (n - 1) := by
  have h_delta_card : ∀ b : F, (Finset.filter (fun x => kasamiDelta k x = kasamiDelta k b) Finset.univ).card = 2 := by
    intro b
    have h_fiber : ∀ x : F, kasamiDelta k x = kasamiDelta k b ↔ x = b ∨ x = b + 1 := by
      grind +suggestions;
    rw [ show ( Finset.filter ( fun x => kasamiDelta k x = kasamiDelta k b ) Finset.univ ) = { b, b + 1 } by ext; aesop, Finset.card_pair ] ; simp +decide [ CharTwo.add_self_eq_zero ];
  have h_partition : ∑ c ∈ Finset.image (fun b => kasamiDelta k b) (Finset.univ : Finset F), (Finset.filter (fun x => kasamiDelta k x = c) (Finset.univ : Finset F)).card = Fintype.card F := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; simp +decide;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
  rw [ Finset.sum_congr rfl fun x hx => show Finset.card ( Finset.filter ( fun y => kasamiDelta k y = x ) Finset.univ ) = 2 from by rcases Finset.mem_image.mp hx with ⟨ y, _, rfl ⟩ ; exact h_delta_card y ] at h_partition ; norm_num at h_partition ; linarith

/-! ### Differential uniformity -/

/-
The differential count is always even (solutions come in pairs `{x, x+a}`).
-/
theorem kasamiDiff_count_even (k : ℕ) (a c : F) (ha : a ≠ 0) :
    Even (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card := by
  -- The solutions to $D_a G(x) = c$ come in pairs $(x, x+a)$.
  have h_pairs : ∀ x : F, (kasamiDiff k a x = c) → (kasamiDiff k a (x + a) = c) := by
    unfold kasamiDiff;
    grind +splitImp;
  -- Since the solutions come in pairs, the set of solutions can be partitioned into pairs.
  have h_partition : ∃ S : Finset (Finset F), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ x ∈ s, kasamiDiff k a x = c) ∧ (∀ x, kasamiDiff k a x = c → ∃ s ∈ S, x ∈ s) ∧ (∀ s₁ s₂, s₁ ∈ S → s₂ ∈ S → s₁ ≠ s₂ → Disjoint s₁ s₂) := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) ( Finset.filter ( fun x => kasamiDiff k a x = c ) Finset.univ ), _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · exact fun x hx => ⟨ x, hx, Or.inl rfl ⟩;
    · grind +splitIndPred;
  obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := h_partition;
  have h_card : Finset.card (Finset.filter (fun x => kasamiDiff k a x = c) Finset.univ) = Finset.sum S (fun s => Finset.card s) := by
    rw [ ← Finset.card_biUnion ];
    · congr with x ; aesop;
    · exact fun s₁ hs₁ s₂ hs₂ h => hS₄ s₁ s₂ hs₁ hs₂ h;
  exact h_card.symm ▸ even_iff_two_dvd.mpr ( Finset.dvd_sum fun s hs => hS₁ s hs ▸ dvd_rfl )

/-
The Kasami function is APN when `gcd(k,n) = 1` and `3 ∤ n`:
    the differential count is 0 or 2 for nonzero `a`.
-/
theorem kasami_apn (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (a c : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card = 0 ∨
    (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card = 2 := by
  -- By kasamiDiff_normalize, D_a G(x) = a^d * D_1(x/a), so D_a G(x) = c iff D_1(x/a) = c/a^d =: c'.
  have h_normalize : Finset.filter (fun x => kasamiDiff k a x = c) (Finset.univ : Finset F) = Finset.image (fun x => x / a⁻¹) (Finset.filter (fun x => kasamiDiff k 1 x = c / a ^ (kasamiExp k)) (Finset.univ : Finset F)) := by
    ext x;
    simp +decide [ kasamiDiff, ha, mul_div_cancel_left₀ ];
    constructor;
    · intro hx
      use x / a;
      simp_all +decide [ kasamiPow, pow_add, pow_mul, mul_pow, div_pow, div_mul_cancel₀, ha ];
      rw [ ← hx, div_add_one, div_pow, add_div ] ; aesop;
    · rintro ⟨ y, hy, rfl ⟩;
      convert congr_arg ( · * a ^ kasamiExp k ) hy using 1 <;> ring;
      · unfold kasamiPow;
        rw [ show y * a + a = a * ( y + 1 ) by ring, mul_pow ] ; ring;
      · simp +decide [ ha ];
  have h_solutions : ∀ y₁ y₂ : F, kasamiDiff k 1 y₁ = c / a ^ (kasamiExp k) → kasamiDiff k 1 y₂ = c / a ^ (kasamiExp k) → y₁ = y₂ ∨ y₁ = y₂ + 1 := by
    intro y₁ y₂ hy₁ hy₂
    have h_eq : kasamiDiff k 1 y₁ = kasamiDiff k 1 y₂ := by
      rw [hy₁, hy₂];
    have := kasamiDiff_eq_implies_linearized k hk y₁ y₂ h_eq;
    have := linPolyL_ker_trivial_of_three_ndvd n hn k hk hcard hgcd h3;
    simp_all +decide [ Finset.ext_iff, funKer ];
    grind;
  by_cases h : ∃ y : F, kasamiDiff k 1 y = c / a ^ (kasamiExp k) <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
  obtain ⟨ y, hy ⟩ := h;
  refine' Or.inr ( le_antisymm _ _ );
  · exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun x => kasamiDiff k 1 x = c / a ^ kasamiExp k ) Finset.univ ⊆ { y, y + 1 } from fun x hx => by simpa using h_solutions x y ( Finset.mem_filter.mp hx |>.2 ) hy ) ) ( Finset.card_insert_le _ _ );
  · refine' Finset.one_lt_card.mpr ⟨ y, _, y + 1, _, _ ⟩ <;> simp_all +decide [ kasamiDiff ];
    grind

end