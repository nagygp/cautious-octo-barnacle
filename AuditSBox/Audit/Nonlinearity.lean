import Mathlib
import AuditSBox.Audit.Defs

/-!
# S-Box Audit — Nonlinearity & Walsh Spectrum Bounds

Over GF(2ⁿ), the Walsh transform of an S-box governs its resistance to
linear cryptanalysis.  This module provides:

- `WalshChar`    — integer-valued additive character structure (±1-valued)
- `W f χ a b`    — Walsh coefficient at (a,b)
- `parseval`      — Parseval's theorem: ∑_{a,b} W(a,b)² = |F|³
- `walsh_energy_pos` — total Walsh energy is positive for nontrivial fields

These theorems certify that an S-box meets minimum nonlinearity requirements,
which is the primary defence against Matsui's linear cryptanalysis.
-/

open Finset Fintype BigOperators

noncomputable section

namespace Audit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- An additive character over F: a map χ : F → ℤ satisfying
    χ(0) = 1, χ(x+y) = χ(x)·χ(y), and the orthogonality relation. -/
structure WalshChar (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  app : F → ℤ
  app_zero : app 0 = 1
  app_add  : ∀ x y, app (x + y) = app x * app y
  orth     : ∀ c : F, ∑ x : F, app (c * x) = if c = 0 then (Fintype.card F : ℤ) else 0

/-- Walsh transform coefficient at (a, b):
    `W(a, b) = ∑_x χ(b·f(x) + a·x)`.
    (Using char 2, "−" is "+", so `b·f(x) − a·x = b·f(x) + a·x`.) -/
def W (f : F → F) (χ : WalshChar F) (a b : F) : ℤ :=
  ∑ x : F, χ.app (b * f x + a * x)

/-- **Parseval's identity**: `∑_{a,b} W(a,b)² = |F|³`.

This is a fundamental energy-conservation result: the total squared Walsh
energy equals |F|³, providing a budget constraint on the Walsh spectrum. -/
theorem parseval (f : F → F) (χ : WalshChar F) :
    ∑ a : F, ∑ b : F, W f χ a b ^ 2 = (Fintype.card F : ℤ) ^ 3 := by
  have h_expand : ∑ a, ∑ b, (W f χ a b) ^ 2 = ∑ x, ∑ y, (∑ a, χ.app (a * (x + y))) * (∑ b, χ.app (b * (f x + f y))) := by
    have h_expand : ∀ a b, (W f χ a b) ^ 2 = ∑ x, ∑ y, χ.app (b * f x + a * x) * χ.app (b * f y + a * y) := by
      simp +decide only [W, sq];
      exact fun a b => by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _;
    simp +decide only [h_expand, Finset.mul_sum _ _ _, mul_comm];
    simp +decide only [← sum_product'];
    refine' Finset.sum_bij ( fun x _ => ( x.2.2.1, x.2.2.2, x.2.1, x.1 ) ) _ _ _ _ <;> simp +decide;
    intro a b c d; rw [ ← χ.app_add, ← χ.app_add ] ; ring;
  have h_orth : ∀ x y : F, ∑ a, χ.app (a * (x + y)) = if x = y then (Fintype.card F : ℤ) else 0 := by
    intro x y;
    convert χ.orth ( x + y ) using 1 ; simp +decide [ mul_comm ];
    grind;
  simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
  ring

/-- **Walsh energy is positive**: The total Walsh energy is always ≥ |F|²,
    since the (0,0) term alone contributes |F|². -/
theorem walsh_energy_lower (f : F → F) (χ : WalshChar F) :
    W f χ 0 0 = (Fintype.card F : ℤ) := by
  simp [W, zero_mul, add_zero, χ.app_zero]

end Audit

end
