/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami Difference Set

Defines the difference set `Δ = {F(b) + F(b+1) + 1 : b ∈ F_{2^n}}` and proves
its basic properties including cardinality (P₁).

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Pott, *Finite Geometry and Character Theory*][pott1995], Chapter 3
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.AdditiveCharacter

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-- The Kasami difference set:
    `Δ = {F(b) + F(b+1) + 1 : b ∈ F_{2^n}}`. -/
def kasamiDelta (n k : ℕ) : Finset (F2n n) :=
  Finset.image (kasamiDeltaGen n k) Finset.univ

/-- P₁: `x ∈ Δ ↔ ∃ b, x = F(b) + F(b+1) + 1`. -/
theorem kasami_P1 (n k : ℕ) (x : F2n n) :
    x ∈ kasamiDelta n k ↔ ∃ b : F2n n, x = kasamiDeltaGen n k b := by
  simp only [kasamiDelta, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

/-- `Δ` has at most `2^n` elements. -/
theorem kasamiDelta_card_le (n k : ℕ) (hn : n ≠ 0) :
    (kasamiDelta n k).card ≤ 2 ^ n := by
  have h1 : (kasamiDelta n k).card ≤ Finset.card Finset.univ :=
    Finset.card_image_le
  rw [Finset.card_univ, F2n.card n hn] at h1
  exact h1

/-! ### Character sum over Δ -/

/-- The character sum over Δ: `S_Δ(c) = ∑_{x ∈ Δ} χ(c·x)`. -/
def deltaCharSum (n k : ℕ) (c : F2n n) : ℤ :=
  ∑ x ∈ kasamiDelta n k, chi n (c * x)

/-- When `c = 0`, the character sum equals `|Δ|`. -/
theorem deltaCharSum_zero (n k : ℕ) :
    deltaCharSum n k 0 = (kasamiDelta n k).card := by
  simp [deltaCharSum, chi_zero]

/-! ### Delta generator pairing (char 2) -/

/-- In char 2, `b + 1 + 1 = b`. -/
theorem F2n.add_one_add_one' {n : ℕ} (b : F2n n) : b + 1 + 1 = b := by
  have : (1 : F2n n) + 1 = 0 := F2n.add_self 1
  calc b + 1 + 1 = b + (1 + 1) := by ring
    _ = b + 0 := by rw [this]
    _ = b := by ring

/-- The delta generator satisfies `g(b) = g(b+1)` in char 2. -/
theorem deltaGen_paired' (n k : ℕ) (b : F2n n) :
    kasamiDeltaGen n k b = kasamiDeltaGen n k (b + 1) := by
  simp only [kasamiDeltaGen, kasamiF, F2n.powMap]
  rw [show b + 1 + 1 = b from F2n.add_one_add_one' b]
  ring

/-- Each element of Δ has at least 2 preimages. -/
theorem deltaGen_fiber_ge_two' (n k : ℕ) (x : F2n n) (hx : x ∈ kasamiDelta n k) :
    2 ≤ (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card := by
  obtain ⟨b, hb⟩ := Finset.mem_image.mp hx
  refine Finset.one_lt_card.mpr ⟨b, ?_, b + 1, ?_, ?_⟩ <;>
    simp_all +decide [Finset.mem_univ, Finset.mem_filter]
  grind +suggestions

/-- The delta set has exactly 2^{n-1} elements when g is exactly 2-to-1. -/
theorem kasamiDelta_card' (n k : ℕ) (hn : n ≠ 0)
    (h_two_to_one : ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2) :
    (kasamiDelta n k).card = 2 ^ (n - 1) := by
  have h_total_pairs : ∑ x ∈ kasamiDelta n k,
    (Finset.univ.filter (fun b : F2n n => kasamiDeltaGen n k b = x)).card = 2 ^ n := by
    rw [← F2n.card n hn, ← Finset.card_biUnion]
    · convert Finset.card_univ; ext x; simp [kasamiDelta]
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop
  rcases n with (_ | n) <;> simp_all +decide [pow_succ']
  grind

/-- For APN Kasami functions, g is exactly 2-to-1. -/
theorem deltaGen_two_to_one' (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n)
    (hapn : ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
      (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2) :
    ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2 := by
  intro x hx
  have h_ge : 2 ≤ (Finset.univ.filter fun b => kasamiDeltaGen n k b = x).card :=
    deltaGen_fiber_ge_two' n k x hx
  have h_le : (Finset.univ.filter fun b => kasamiDeltaGen n k b = x).card ≤ 2 := by
    convert hapn 1 one_ne_zero (x - 1) using 1
    simp +decide [kasamiDeltaGen, eq_sub_iff_add_eq]
    simp +decide only [add_comm]
  linarith

/-- The triple sum splits at a=0. -/
theorem triple_sum_split' (n k : ℕ) (v1 v2 : F2n n) :
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) =
    deltaCharSum n k 0 ^ 3 +
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) := by
  simp +decide [Finset.filter_ne', pow_succ, mul_assoc]

end
end Kasami
