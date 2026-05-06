/-
  TripleCount.lean

  # Triple Count for Hyperplane Sets in Finite Fields of Characteristic 2

  ## Main Result

  For a finite field F = GF(2^n), a hyperplane Δ ⊆ F (additive subgroup of
  index 2), and distinct nonzero v₁, v₂ ∈ F:

    |{(x, y, z) ∈ Δ³ : v₁·x + v₂·y + (v₁ + v₂)·z = 0}| = 2^{2n-3}

  ## Proof Strategy (Crystallographic / Coset Geometry)

  The proof uses a "crystallographic" perspective — viewing the hyperplane as a
  lattice of index 2 in the additive group of the field, and analyzing how
  scalar multiplication permutes the two cosets:

  1. **Reduction to pairs:** x is determined by (y,z) since v₁ ≠ 0.
  2. **Coset analysis:** H partitions F into H and F\H. For c ∉ {0,1},
     multiplication by c maps exactly half of H into H.
  3. **Key insight:** c·H ≠ H for c ∉ {0,1} (any hyperplane is NOT closed
     under non-trivial scalar multiplication in char 2).
  4. **Count:** 2·(|H|/2)² = |H|²/2 = 2^{2n-3}.

  ## Connection to the Kasami Function

  The Kasami function F(b) = b^{4^k - 2^k + 1} is "crooked" (when AB), so
  Δ = {F(b)+F(b+1)+1 : b} is a hyperplane or its complement. The formula
  applies in both cases.
-/

import Mathlib

open Finset BigOperators Classical

set_option maxHeartbeats 800000

noncomputable section

namespace TripleCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- In characteristic 2, -1 = 1. -/
lemma char2_neg_one : (-1 : F) = 1 :=
  neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero 1)

/-- In characteristic 2, -x = x. -/
lemma char2_neg_eq (x : F) : -x = x :=
  neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero x)

/-- In characteristic 2, c ≠ 1 implies c + 1 ≠ 0. -/
lemma char2_add_one_ne_zero {c : F} (hc1 : c ≠ 1) : c + 1 ≠ 0 := by
  intro h; exact hc1 (by rw [eq_neg_of_add_eq_zero_left h, char2_neg_one])

/-! ## Part 1: Index-2 Subgroup Combinatorics -/

/-- The finset of elements in an additive subgroup. -/
def subgroupFinset (H : AddSubgroup F) : Finset F :=
  Finset.univ.filter (· ∈ H)

/-- In an index-2 subgroup, two elements outside the subgroup sum to an element inside. -/
lemma index_two_complement_add (H : AddSubgroup F) (hH : H.index = 2)
    (x y : F) (hx : x ∉ H) (hy : y ∉ H) : x + y ∈ H := by
  sorry

/-- Multiplication by a nonzero scalar maps a subgroup to a subgroup of the same size.
    (Since the multiplication map is injective.) -/
lemma card_smul_eq (H : AddSubgroup F) (c : F) (hc : c ≠ 0) :
    ((subgroupFinset H).image (c * ·)).card = (subgroupFinset H).card := by
  exact Finset.card_image_of_injective _ (mul_right_injective₀ hc)

/-- If c·H ⊆ H (as sets) and c ≠ 0, then c maps elements outside H to outside H. -/
lemma smul_complement (H : AddSubgroup F) (c : F) (hc : c ≠ 0)
    (hinv : ∀ h : F, h ∈ H → c * h ∈ H)
    (a : F) (ha : a ∉ H) : c * a ∉ H := by
  sorry

/-- A subgroup of index 2 is NOT closed under multiplication by c ∉ {0,1}.
    Proof: If c·H ⊆ H, then (c+1)·H ⊆ H (by closure). For a ∉ H,
    both c·a and a are outside H, so (c+1)·a = c·a + a ∈ H (index-2 property).
    But (c+1)·H ⊆ H implies (c+1) maps complement to complement, contradiction. -/
lemma not_smul_subset (H : AddSubgroup F) (hH : H.index = 2)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ¬ (∀ h : F, h ∈ H → c * h ∈ H) := by
  sorry

/-- The set {h ∈ H : c·h ∈ H} is an additive subgroup of H.
    Its index in H is 2 (when c·H ≠ H), so it has |H|/2 elements. -/
lemma card_smul_inter (H : AddSubgroup F) (hH : H.index = 2)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (Finset.univ.filter (fun x => x ∈ H ∧ c * x ∈ H)).card =
    (subgroupFinset H).card / 2 := by
  sorry

/-- A subgroup of index 2 has |F|/2 elements. -/
lemma card_index_two (H : AddSubgroup F) (hH : H.index = 2) :
    (subgroupFinset H).card = Fintype.card F / 2 := by
  sorry

/-! ## Part 2: The Triple Count Theorem -/

/-- The set of triples (x, y, z) ∈ Δ³ satisfying v₁x + v₂y + (v₁+v₂)z = 0. -/
def tripleSet (Δ : Finset F) (v₁ v₂ : F) : Finset (F × F × F) :=
  (Δ ×ˢ (Δ ×ˢ Δ)).filter fun ⟨x, y, z⟩ =>
    v₁ * x + v₂ * y + (v₁ + v₂) * z = 0

/-- The triple count. -/
def tripleCountN (Δ : Finset F) (v₁ v₂ : F) : ℕ :=
  (tripleSet Δ v₁ v₂).card

/-- **Main Theorem (Hyperplane case):**
    |{(x,y,z) ∈ H³ : v₁x + v₂y + (v₁+v₂)z = 0}| = |H|² / 2 -/
theorem tripleCount_hyperplane
    (H : AddSubgroup F) (hH : H.index = 2)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    tripleCountN (subgroupFinset H) v₁ v₂ = (subgroupFinset H).card ^ 2 / 2 := by
  sorry

/-! ## Part 3: Connecting to 2^{2n-3} -/

/-- For |F| = 2^n, a subgroup of index 2 has 2^{n-1} elements. -/
lemma hyperplane_card (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (H : AddSubgroup F) (hH : H.index = 2) :
    (subgroupFinset H).card = 2 ^ (n - 1) := by
  sorry

/-- Arithmetic: (2^{n-1})² / 2 = 2^{2n-3} for n ≥ 2. -/
lemma half_sq_pow (n : ℕ) (hn : 2 ≤ n) :
    (2 ^ (n - 1)) ^ 2 / 2 = 2 ^ (2 * n - 3) := by
  rcases n with (_ | _ | n) <;> simp_all +arith +decide [Nat.mul_succ, pow_succ']
  norm_num [mul_assoc, pow_mul']; ring

/-- **The Triple Count = 2^{2n-3}** -/
theorem tripleCount_eq_pow (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (H : AddSubgroup F) (hH : H.index = 2)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    tripleCountN (subgroupFinset H) v₁ v₂ = 2 ^ (2 * n - 3) := by
  rw [tripleCount_hyperplane H hH v₁ v₂ hv₁ hv₂ hne,
      hyperplane_card n hn hcard H hH, half_sq_pow n hn]

/-! ## Part 4: The Kasami Function -/

/-- The Kasami exponent: d = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Kasami function F(b) = b^d. -/
def kasamiFun (k : ℕ) (b : F) : F := b ^ kasamiExp k

/-- The differential set Δ = {F(b) + F(b+1) + 1 : b ∈ F}. -/
def kasamiDelta (k : ℕ) : Finset F :=
  Finset.univ.image fun b => kasamiFun k b + kasamiFun k (b + 1) + 1

/-- **Kasami Triple Count Theorem** -/
theorem kasami_triple_count (n k : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (H : AddSubgroup F) (hH : H.index = 2)
    (hΔ : kasamiDelta (F := F) k = subgroupFinset H)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    tripleCountN (kasamiDelta k) v₁ v₂ = 2 ^ (2 * n - 3) := by
  rw [hΔ]; exact tripleCount_eq_pow n hn hcard H hH v₁ v₂ hv₁ hv₂ hne

end TripleCount