/-
  KasamiHelpers.lean

  Helper lemmas for the Kasami triple-count conjecture.

  This file provides:
  1. Characteristic 2 helper lemmas
  2. The APN property definition
  3. The Delta set cardinality (|Δ| = 2^(n-1)) — depends on kasami_is_apn (sorry)
  4. The triple set reduction to pairs (tripleSet_card_eq_pair_filter) — proved!
  5. The pair filter count — depends on spectral_uniformity (sorry)
  6. The combined Kasami triple count theorem

  Sorry chain:
  - kasami_is_apn (KasamiAPN.lean) — deep finite field result
  - spectral_uniformity (KasamiAPN.lean) — requires AB property
  Everything else is proved modulo these two.
-/
import Mathlib
import KasamiConjecture
import KasamiAPN

noncomputable section

open Finset BigOperators

set_option maxHeartbeats 800000

namespace KasamiHelpers

variable {n k : ℕ}
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Section 1: Characteristic 2 Helpers -/

/-- In characteristic 2, `x + x = 0` for all x. -/
lemma char2_add_self (x : F) : x + x = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  calc x + x = 2 * x := by ring
    _ = 0 * x := by rw [h2]
    _ = 0 := by ring

/-- In characteristic 2, negation is the identity. -/
lemma char2_neg_eq (x : F) : -x = x :=
  neg_eq_of_add_eq_zero_left (char2_add_self F x)

/-- In characteristic 2, subtraction equals addition. -/
lemma char2_sub_eq_add (x y : F) : x - y = x + y := by
  rw [sub_eq_add_neg, char2_neg_eq]

/-- In characteristic 2, if `v₁ ≠ v₂` then `v₁ + v₂ ≠ 0`. -/
lemma char2_add_ne_zero {v₁ v₂ : F} (hne : v₁ ≠ v₂) : v₁ + v₂ ≠ 0 := by
  intro h
  apply hne
  have : v₁ = v₁ + v₂ + v₂ := by rw [add_assoc, char2_add_self F v₂, add_zero]
  rw [this, h, zero_add]

/-! ## Section 2: APN Property -/

/-- A function f : F → F is APN if for every nonzero a,
    the derivative D_a f(x) = f(x+a) + f(x) takes each value at most 2 times. -/
def IsAPN (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ v : F,
    (Finset.univ.filter fun x => f (x + a) + f x = v).card ≤ 2

/-! ## Section 3: Kasami APN and Delta Size -/

/-- **The Kasami function is APN when gcd(k,n) = 1.**
    Wraps `KasamiAPN.kasami_is_apn`. -/
theorem kasami_is_apn
    (hn : 3 ≤ n) (hcard : Fintype.card F = 2 ^ n) (hcoprime : Nat.Coprime k n) :
    IsAPN F (kasamiFun F k) :=
  KasamiAPN.kasami_is_apn F n k hn hcard hcoprime

/-- **Size of the Kasami Delta set.**
    When gcd(k,n) = 1 and |F| = 2^n, |Δ| = 2^(n-1).

    Proof: The APN property implies the derivative D_1(f) is exactly 2-to-1,
    so |im(D_1 f)| = |F|/2 = 2^(n-1). -/
theorem kasamiDelta_card
    (hn : 3 ≤ n) (hcard : Fintype.card F = 2 ^ n) (hcoprime : Nat.Coprime k n) :
    (kasamiDelta F k).card = 2 ^ (n - 1) := by
  set f : F → F := fun x => kasamiFun F k x + kasamiFun F k (x + 1) + 1
  have h_image_size : (Finset.image f Finset.univ).card * 2 = Fintype.card F := by
    have h_two_to_one : ∀ y ∈ Finset.image f Finset.univ,
        (Finset.filter (fun x => f x = y) Finset.univ).card = 2 := by
      intro y hy
      have h_preimage : ∀ x : F, f x = y → f (x + 1) = y := by grind
      have h_preimage_card : ∀ x : F, f x = y →
          (Finset.filter (fun z => f z = y) Finset.univ).card ≤ 2 := by
        intro x hx
        have h_preimage_card : ∀ z : F, f z = y → z = x ∨ z = x + 1 := by
          intro z hz
          have h_diff : kasamiFun F k z + kasamiFun F k (z + 1) =
              kasamiFun F k x + kasamiFun F k (x + 1) := by grind
          have := kasami_is_apn F hn hcard hcoprime 1 (by simp +decide)
            (kasamiFun F k z + kasamiFun F k (z + 1))
          simp_all +decide [Finset.card_le_one]
          contrapose! this
          refine' lt_of_lt_of_le _ (Finset.card_mono <|
            show {z, x, x + 1} ⊆ Finset.filter
              (fun x_1 => kasamiFun F k (x_1 + 1) + kasamiFun F k x_1 =
                kasamiFun F k x + kasamiFun F k (x + 1)) Finset.univ from _)
          · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] <;>
              simp +decide [this]
          · grind
        exact le_trans (Finset.card_le_card
          (show Finset.filter (fun z => f z = y) Finset.univ ⊆ {x, x + 1} by
            intros z hz; aesop))
          (Finset.card_insert_le _ _)
      obtain ⟨x, hx⟩ := Finset.mem_image.mp hy
      refine' le_antisymm (h_preimage_card x hx.2) _
      refine' Finset.one_lt_card.mpr ⟨x, _, x + 1, _, _⟩ <;> simp_all +decide
    have h_image_size :
        ∑ y ∈ Finset.image f Finset.univ,
          (Finset.filter (fun x => f x = y) Finset.univ).card = Fintype.card F := by
      rw [← Finset.card_eq_sum_card_fiberwise]
      · rfl
      · exact fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)
    rw [← h_image_size, Finset.sum_congr rfl h_two_to_one, Finset.sum_const,
        smul_eq_mul, mul_comm]
  cases n <;> simp_all +decide [pow_succ'] <;> linarith!

/-! ## Section 4: Triple Set Reduction -/

/-- The triple set bijects to pairs (x,y) ∈ Δ² with z determined.
    In char 2 with v₁ ≠ v₂, v₁+v₂ ≠ 0 so z = (v₁x + v₂y)/(v₁+v₂). -/
theorem tripleSet_card_eq_pair_filter
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (tripleSet F k v₁ v₂).card =
      ((kasamiDelta F k ×ˢ kasamiDelta F k).filter fun p =>
        (v₁ * p.1 + v₂ * p.2) * (v₁ + v₂)⁻¹ ∈ kasamiDelta F k).card := by
  refine' Eq.symm (Finset.card_bij _ _ _ _)
  use fun p _ => (p.1, p.2, (v₁ * p.1 + v₂ * p.2) * (v₁ + v₂)⁻¹)
  · simp +contextual [tripleSet]; grind
  · grind
  · unfold tripleSet; simp +decide [hne]; grind

/-! ## Section 5: Pair Filter Count via Spectral Uniformity -/

/-- The pair filter count equals 2^(2n-3).

    Proof pathway: This follows from `KasamiAPN.kasami_triple_from_spectral`,
    which uses `spectral_uniformity` (the AB property ensures uniform
    distribution of triples) and `delta_cube_div_field` (arithmetic). -/
theorem pair_filter_count
    (hn : 3 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    ((kasamiDelta F k ×ˢ kasamiDelta F k).filter fun p =>
      (v₁ * p.1 + v₂ * p.2) * (v₁ + v₂)⁻¹ ∈ kasamiDelta F k).card = 2 ^ (2 * n - 3) := by
  -- Reduce to triple set count via the bijection (reversed)
  rw [← tripleSet_card_eq_pair_filter F v₁ v₂ hv₁ hv₂ hne]
  -- Use the spectral approach
  exact KasamiAPN.kasami_triple_from_spectral F n k hn hcard hcoprime v₁ v₂ hv₁ hv₂ hne
    (kasamiDelta_card F hn hcard hcoprime)

/-! ## Section 6: Combined Result -/

/-- **Kasami triple count from helpers.**
    Combines `tripleSet_card_eq_pair_filter` and `pair_filter_count`. -/
theorem kasami_triple_count_from_helpers
    (hn : 3 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (tripleSet F k v₁ v₂).card = 2 ^ (2 * n - 3) := by
  rw [tripleSet_card_eq_pair_filter F v₁ v₂ hv₁ hv₂ hne]
  exact pair_filter_count F hn hcard hcoprime v₁ v₂ hv₁ hv₂ hne

end KasamiHelpers

end
