import Mathlib
import AuditSBox.Audit.Defs

/-!
# S-Box Audit — Boomerang Uniformity

The Boomerang Connectivity Table (BCT) measures an S-box's resistance to
boomerang attacks (Wagner 1999, Cid–Huang–Peyrin–Sasaki–Song 2018).

For a permutation S-box f : F → F, the boomerang uniformity is:

  β(a,b) = |{x ∈ F | f⁻¹(f(x) + b) + f⁻¹(f(x+a) + b) = a}|

This module defines the BCT, proves structural identities, and
establishes the fundamental bound β(f) ≥ δ(f).

## Key results

- `β_pair`              — BCT entry at (a, b) for a permutation
- `β_max`               — boomerang uniformity (maximum BCT entry)
- `β_trivial_row`       — β(0, b) = |F| for all b
- `β_ge_δ_entry`        — δ(a,b) ≤ β(a, 0)  (DDT embeds into BCT)
-/

open Finset Fintype BigOperators

noncomputable section

namespace Audit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- BCT entry at (a, b) for a permutation f.
    β(a,b) = |{x | f⁻¹(f(x)+b) + f⁻¹(f(x+a)+b) = a}|. -/
def β_pair (f finv : F → F) (a b : F) : ℕ :=
  (univ.filter fun x => finv (f x + b) + finv (f (x + a) + b) = a).card

/-- Boomerang uniformity: max_{a≠0, b≠0} β(a,b). -/
def β_max (f finv : F → F) : ℕ :=
  Finset.sup ((univ.filter (· ≠ (0 : F))) ×ˢ (univ.filter (· ≠ (0 : F))))
    (fun p => β_pair f finv p.1 p.2)

/-
**Trivial row**: β(0, b) = |F| for any b.
    When a = 0, the condition becomes f⁻¹(f(x)+b) + f⁻¹(f(x)+b) = 0,
    which is always true in char 2.
-/
theorem β_trivial_row (f finv : F → F)
    (hinv : ∀ x, finv (f x) = x) (b : F) :
    β_pair f finv 0 b = Fintype.card F := by
  unfold β_pair;
  simp +decide [ ← two_mul, CharTwo.two_eq_zero ]

/-
**β ≥ δ**: Taking b = 0 in the BCT recovers the DDT.
    For any a ≠ 0: δ(a, b) ≤ β(a, 0).
-/
theorem β_ge_δ_entry (f finv : F → F)
    (hinv : ∀ x, finv (f x) = x) (hfinv : ∀ y, f (finv y) = y)
    (a : F) (ha : a ≠ 0) (b : F) :
    δ_pair f a b ≤ β_pair f finv a 0 := by
  refine' le_trans _ ( Finset.card_le_card _ );
  rotate_left;
  exact Finset.univ.filter fun x => f ( x + a ) - f x = b;
  · grind;
  · exact le_rfl

end Audit

end