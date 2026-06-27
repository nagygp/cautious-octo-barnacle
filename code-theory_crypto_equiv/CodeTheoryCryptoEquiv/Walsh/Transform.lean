import Mathlib
import CodeTheoryCryptoEquiv.APN.Defs

/-!
# Walsh Transform — Trace, Sign Character, and Orthogonality

## Definitions
- `Tr`: Absolute trace `F → GF(2)`
- `χ`: Sign character `F → ℤ`
- `walsh f a b`: Walsh coefficient `∑_x χ(a·x + b·f(x))`

## Key results
- `χ_mul`: χ is multiplicative (χ(x+y) = χ(x)·χ(y))
- `χ_sum_eq`: Character orthogonality (Schur's lemma)
- `walsh_b_zero`: W(f, a, 0) = 0 for a ≠ 0
-/

set_option maxHeartbeats 1600000

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

instance instFact2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Layer 0: Absolute Trace -/

noncomputable instance instAlgZMod2 : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The absolute trace Tr : F → GF(2). -/
noncomputable abbrev Tr : F → ZMod 2 := Algebra.trace (ZMod 2) F

theorem Tr_add (x y : F) : Tr (x + y) = Tr x + Tr y := map_add _ x y
theorem Tr_zero : Tr (0 : F) = 0 := map_zero _

/-! ## Layer 1: Sign Character -/

/-- Sign character: χ(x) = 1 if Tr(x) = 0, χ(x) = -1 if Tr(x) ≠ 0. -/
noncomputable def χ (x : F) : ℤ := if Tr x = 0 then 1 else -1

theorem χ_zero : χ (0 : F) = 1 := by simp [χ, Tr_zero]

theorem χ_values (x : F) : χ x = 1 ∨ χ x = -1 := by
  unfold χ; split <;> simp

theorem χ_sq (x : F) : χ x ^ 2 = 1 := by
  rcases χ_values x with h | h <;> simp [h]

theorem χ_mul (x y : F) : χ (x + y) = χ x * χ y := by
  simp only [χ, Tr_add]
  have : Fact (1 < 2) := ⟨by omega⟩
  by_cases hx : Tr x = 0 <;> by_cases hy : Tr y = 0 <;> simp_all
  · have hx1 : Tr x = 1 := by
      have h := (Tr x).val_lt
      have hne : (Tr x).val ≠ 0 := fun h => hx ((ZMod.val_eq_zero (Tr x)).mp h)
      exact (ZMod.val_injective 2) (by rw [show (Tr x).val = 1 by omega, ZMod.val_one])
    have hy1 : Tr y = 1 := by
      have h := (Tr y).val_lt
      have hne : (Tr y).val ≠ 0 := fun h => hy ((ZMod.val_eq_zero (Tr y)).mp h)
      exact (ZMod.val_injective 2) (by rw [show (Tr y).val = 1 by omega, ZMod.val_one])
    simp [hx1, hy1]; decide

/-! ## Layer 2: Walsh Transform -/

/-- Walsh coefficient of f at (a, b). -/
noncomputable def walsh (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, χ (a * x + b * f x)

theorem walsh_zero_zero (f : F → F) : walsh f 0 0 = Fintype.card F := by
  simp [walsh, χ_zero]

/-- W(f, a, 0) = 0 for a ≠ 0. -/
theorem walsh_b_zero (f : F → F) (a : F) (ha : a ≠ 0) :
    walsh f a 0 = 0 := by
  have h_subst : ∑ x : F, χ (a * x) = ∑ y : F, χ y := by
    exact Equiv.sum_comp ( Equiv.mulLeft₀ a ha ) fun x => χ x;
  convert h_subst;
  · exact Finset.sum_congr rfl fun _ _ => by simp +decide [ walsh ] ;
  · obtain ⟨y0, hy0⟩ : ∃ y0 : F, Tr y0 = 1 := by
      exact ( Algebra.trace_surjective ( ZMod 2 ) F ) 1;
    have h_sum_shift : ∀ y : F, ∑ x : F, χ (x + y) = ∑ x : F, χ x := by
      exact fun y => Equiv.sum_comp ( Equiv.addRight y ) fun x => χ x;
    specialize h_sum_shift y0;
    have h_sum_neg : ∑ x : F, χ (x + y0) = ∑ x : F, -χ x := by
      apply Finset.sum_congr rfl
      intro x _
      simp [χ, Tr_add, hy0];
      cases Fin.exists_fin_two.mp ⟨ Tr x, rfl ⟩ <;> simp +decide [ * ];
    rw [ Finset.sum_neg_distrib ] at h_sum_neg ; linarith

/-- W(f, 0, b) = 0 for b ≠ 0 when f is bijective. -/
theorem walsh_a_zero_perm (f : F → F) (hf : Function.Bijective f)
    (b : F) (hb : b ≠ 0) : walsh f 0 b = 0 := by
  unfold walsh; simp +decide [ hf.injective.eq_iff, hb ] ;
  convert walsh_b_zero ( fun x => x ) b hb using 1;
  exact ( Equiv.sum_comp ( Equiv.ofBijective f hf ) fun x => χ ( b * x ) ) ▸ by simp +decide [ walsh ] ;

/-! ## Layer 3: Character Orthogonality (Schur's Lemma) -/

/-- Orthogonality: Σ_x χ(c·x) = |F| if c = 0, else 0. -/
theorem χ_sum_eq (c : F) :
    ∑ x : F, χ (c * x) = if c = 0 then (Fintype.card F : ℤ) else 0 := by
  convert walsh_b_zero ( fun x => x ) c using 1;
  split_ifs <;> simp_all +decide [ walsh ];
  exact χ_zero

/-- Dual orthogonality (Pontryagin duality). -/
theorem χ_sum_dual (x : F) :
    ∑ c : F, χ (c * x) = if x = 0 then (Fintype.card F : ℤ) else 0 := by
  convert χ_sum_eq x using 1 ; simp +decide [ mul_comm ]

end WalshAB
