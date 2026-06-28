import Mathlib
import AuditSBox.Audit.Defs

/-!
# S-Box Audit — Differential Profile

Structural theorems about the differential profile of an endomorphism
over a finite field of characteristic 2.

## Key results

- `fiber_sum`          — ∑_b δ(a,b) = |F|  (partition of domain)
- `img_card_mul_omega` — ω-uniform ⟹ |img(a)| · ω = |F|
- `bounded_iff_uniform` — when ω divides every fiber size, bounded ↔ uniform
- `δ_max_le_of_bounded` — Bounded ω f ⟹ δ_max f ≤ ω
- `uniform_imp_bounded` — Uniform ω ⟹ Bounded ω
-/

open Finset Fintype BigOperators

noncomputable section

namespace Audit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Partition identity**: `∑_b δ(a,b) = |F|`. -/
theorem fiber_sum (f : F → F) (a : F) :
    ∑ b : F, δ_pair f a b = Fintype.card F := by
  simp only [δ_pair, fiber, D, card_filter]
  rw [Finset.sum_comm]; simp

/-- ω-uniform ⟹ Bounded ω. -/
theorem uniform_imp_bounded (ω : ℕ) (f : F → F) (h : Uniform ω f) :
    Bounded ω f := by
  intro a ha b
  cases h a ha b with
  | inl h0 => simp [h0]
  | inr hw => exact le_of_eq hw

/-- When ω | δ(a,b) for all a≠0, b, then Bounded ω ↔ Uniform ω. -/
theorem bounded_iff_uniform (ω : ℕ) (f : F → F)
    (hdvd : ∀ a : F, a ≠ 0 → ∀ b : F, ω ∣ δ_pair f a b) :
    Bounded ω f ↔ Uniform ω f := by
  constructor
  · intro hb a ha b
    have hd := hdvd a ha b
    have hle := hb a ha b
    rcases Nat.eq_zero_or_pos (δ_pair f a b) with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (Nat.le_antisymm hle (Nat.le_of_dvd hpos hd))
  · exact uniform_imp_bounded ω f

/-
**Image cardinality from uniformity**: If f is ω-uniform with ω > 0 and a ≠ 0,
    then |img f a| · ω = |F|.
-/
theorem img_card_mul_omega (f : F → F) (ω : ℕ) (hω : 0 < ω) (a : F) (ha : a ≠ 0)
    (hu : Uniform ω f) :
    (img f a).card * ω = Fintype.card F := by
  rw [ ← fiber_sum f a, Finset.sum_congr rfl fun b hb => show δ_pair f a b = if b ∈ img f a then ω else 0 from ?_ ];
  · simp +decide [ Finset.sum_ite ];
  · split_ifs with h;
    · exact Or.resolve_left ( hu a ha b ) ( by contrapose! h; unfold img δ_pair fiber at *; aesop );
    · exact Finset.card_eq_zero.mpr ( Finset.filter_eq_empty_iff.mpr fun x _ => fun hx => h <| Finset.mem_image.mpr ⟨ x, Finset.mem_univ _, hx ⟩ )

/-
**Bounded ω ⟹ δ_max ≤ ω** (the sup over all pairs is at most ω).
-/
theorem δ_max_le_of_bounded (ω : ℕ) (f : F → F) (hb : Bounded ω f) :
    δ_max f ≤ ω := by
  exact Finset.sup_le fun p hp => hb _ ( by aesop ) _

end Audit

end