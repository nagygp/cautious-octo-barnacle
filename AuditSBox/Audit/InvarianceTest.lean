import Mathlib
import AuditSBox.Audit.Defs

/-!
# S-Box Audit — Affine Invariance Testing

Two S-boxes that are affine-equivalent have identical differential profiles.
This module formalizes the affine invariance of the differential uniformity,
which is essential for auditing: it means the DDT analysis is independent of
the particular affine representation of the S-box.

## Key results

- `δ_pair_precomp_linear` — δ(a,b) is invariant under pre-composition by linear bijection
- `bounded_precomp_linear` — Bounded ω is preserved by linear pre-composition
- `δ_pair_postcomp_linear` — δ(a,b) transforms predictably under post-composition
-/

open Finset Fintype BigOperators

noncomputable section

namespace Audit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
**Differential uniformity is affine-invariant** (pre-composition).
    Pre-composition by a linear bijection L transforms the fiber:
    δ_{f∘L}(a, b) = δ_f(L(a), b).
-/
theorem δ_pair_precomp_linear (f : F → F) (L : F ≃ₗ[F] F) (a b : F) :
    δ_pair (f ∘ L) a b = δ_pair f (L a) b := by
  refine' Finset.card_bij ( fun x hx => L x ) _ _ _ <;> simp +decide [ fiber ];
  · unfold D; aesop;
  · intro x hx; use L.symm x; simp_all +decide [ D ] ;

/-- **Bounded ω is preserved by linear pre-composition.** -/
theorem bounded_precomp_linear (ω : ℕ) (f : F → F) (L : F ≃ₗ[F] F)
    (hb : Bounded ω f) :
    Bounded ω (f ∘ L) := by
  intro a ha b
  rw [δ_pair_precomp_linear]
  apply hb
  intro hLa
  apply ha
  exact L.map_eq_zero_iff.mp hLa

/-
**Post-composition by a linear bijection preserves fiber cardinality.**
    δ_{L∘f}(a, b) = δ_f(a, L⁻¹(b)).
-/
theorem δ_pair_postcomp_linear (f : F → F) (L : F ≃ₗ[F] F) (a b : F) :
    δ_pair (L ∘ f) a b = δ_pair f a (L.symm b) := by
  refine' Finset.card_bij ( fun x _ => x ) _ _ _ <;> simp +decide [ δ_pair, fiber ];
  · intro x hx; rw [ ← hx ] ; simp +decide [ D ] ;
  · intro y hy; have := L.apply_symm_apply b; simp_all +decide [ D ] ;
    rw [ ← map_sub, hy, L.apply_symm_apply ]

end Audit

end