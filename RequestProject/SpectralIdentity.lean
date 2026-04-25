/-
# Spectral Identity: Bridge Between Spatial and Spectral Sides
-/
import Mathlib
import RequestProject.TraceChar
import RequestProject.WalshHadamard

open Finset BigOperators
noncomputable section
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
attribute [local instance] ZMod.algebra

def tripleCount (S : Finset F) (c : F) : ℤ :=
  ((S ×ˢ S ×ˢ S).filter (fun xyz : F × F × F =>
    xyz.1 + c * xyz.2.1 + (1 + c) * xyz.2.2 = 0)).card

theorem spectral_identity (S : Finset F) (c : F) :
    ∑ b : F, walshCoeff F (indicator F S) b *
             walshCoeff F (indicator F S) (b * c) *
             walshCoeff F (indicator F S) (b * (1 + c)) =
    (Fintype.card F : ℤ) * tripleCount F S c := by
  -- Expand the Walsh coefficients using walshCoeff_indicator.
  have h_expand : ∑ b : F, (∑ x ∈ S, χ F b x) * (∑ y ∈ S, χ F (b * c) y) * (∑ z ∈ S, χ F (b * (1 + c)) z) = ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, (∑ b : F, χ F b x * χ F (b * c) y * χ F (b * (1 + c)) z) := by
    simp +decide only [Finset.sum_mul _ _ _, mul_sum];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm ) );
  -- Using χ(bc,y) = χ(b,cy) and χ(b(1+c),z) = χ(b,(1+c)z), combine with χ_mul_snd to get χ(b, x+cy+(1+c)z).
  have h_combine : ∀ x y z : F, ∑ b : F, χ F b x * χ F (b * c) y * χ F (b * (1 + c)) z = ∑ b : F, χ F b (x + c * y + (1 + c) * z) := by
    intro x y z;
    refine' Finset.sum_congr rfl fun b _ => _;
    rw [ χ_mul_snd, χ_mul_snd ];
    unfold χ; ring;
  -- Sum over b using χ_sum_dual: this is |F| if x+cy+(1+c)z = 0, else 0.
  have h_sum_dual : ∀ x y z : F, ∑ b : F, χ F b (x + c * y + (1 + c) * z) = if x + c * y + (1 + c) * z = 0 then (Fintype.card F : ℤ) else 0 := by
    exact?;
  simp_all +decide [ Finset.sum_ite ];
  convert h_expand using 1;
  · exact Finset.sum_congr rfl fun _ _ => by rw [ walshCoeff_indicator, walshCoeff_indicator, walshCoeff_indicator ] ;
  · simp +decide [ mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul, tripleCount ];
    simp +decide only [card_filter, mul_comm, sum_product, Finset.mul_sum _ _ _];
    simp +decide only [Nat.cast_sum, Finset.mul_sum _ _ _]

theorem ratio_reduction (S : Finset F) (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) :
    ((S ×ˢ S ×ˢ S).filter (fun xyz : F × F × F =>
      v₁ * xyz.1 + v₂ * xyz.2.1 + (v₁ + v₂) * xyz.2.2 = 0)).card =
    ((S ×ˢ S ×ˢ S).filter (fun xyz : F × F × F =>
      xyz.1 + (v₂ / v₁) * xyz.2.1 + (1 + v₂ / v₁) * xyz.2.2 = 0)).card := by
  field_simp;
  rw [ MulZeroClass.mul_zero ]

end