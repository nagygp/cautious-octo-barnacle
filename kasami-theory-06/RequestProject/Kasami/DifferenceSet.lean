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

end
end Kasami
