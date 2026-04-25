/-
# Spectral Identity: Bridge Between Spatial and Spectral Sides

This module proves the spectral identity that connects the triple intersection
count N(c) with the triple product of Walsh coefficients. This is the key
bridge between the primal (spatial) and dual (spectral) sides of P₃.

## Main definitions

* `tripleCount` : N(c) = |{(x,y,z) ∈ S³ : x + c·y + (1+c)·z = 0}|

## Main results

* `spectral_identity` : ∑ b, Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c)) = |F|·N(c)

This is an instance of the Parseval/Plancherel-type convolution theorem for
the group algebra ℤ[(F,+)].

## References

* The spectral identity is a special case of the general fact that for
  f, g, h : G → ℂ on a finite abelian group G:
    ∑_{x+y+z=0} f(x)g(y)h(z) = (1/|G|) ∑_χ f̂(χ)ĝ(χ)ĥ(χ)
-/

import Mathlib
import RequestProject.TraceChar
import RequestProject.WalshHadamard

open Finset BigOperators

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

attribute [local instance] ZMod.algebra

/-! ### Triple Intersection Count -/

/-- N(S, c) = |{(x,y,z) ∈ S³ : x + c·y + (1+c)·z = 0}|.
    This is the count of collinear triples in the set S with slope parameter c. -/
def tripleCount (S : Finset F) (c : F) : ℤ :=
  ((S ×ˢ S ×ˢ S).filter (fun xyz : F × F × F =>
    xyz.1 + c * xyz.2.1 + (1 + c) * xyz.2.2 = 0)).card

/-! ### The Spectral Identity -/

/-
**Spectral Identity**: The triple product of Walsh coefficients equals |F| times
    the triple intersection count.

    ∑ b : F, Ŝ(b) · Ŝ(b·c) · Ŝ(b·(1+c)) = |F| · N(S, c)

    Proof sketch: Expand the Walsh coefficients, use character orthogonality to
    collapse the sum over b, obtaining a delta function that enforces the
    linear constraint x + c·y + (1+c)·z = 0.

    This is the fundamental bridge between the spatial counting problem (N(c))
    and the spectral vanishing problem (AlmostBentVanishing).
-/
theorem spectral_identity (S : Finset F) (c : F) :
    ∑ b : F, walshCoeff F (indicator F S) b *
             walshCoeff F (indicator F S) (b * c) *
             walshCoeff F (indicator F S) (b * (1 + c)) =
    (Fintype.card F : ℤ) * tripleCount F S c := by
  -- We expand the left-hand side using the definition of `walshCoeff`.
  suffices h : ∑ b : F, (∑ x ∈ S, χ F b x) * (∑ y ∈ S, χ F (b * c) y) * (∑ z ∈ S, χ F (b * (1 + c)) z) = (Fintype.card F : ℤ) * tripleCount F S c by
    convert h using 2;
    rw [ ← walshCoeff_indicator, ← walshCoeff_indicator, ← walshCoeff_indicator ];
  -- We can rewrite the left-hand side using the properties of the characters.
  have h_lhs : ∑ b : F, (∑ x ∈ S, χ F b x) * (∑ y ∈ S, χ F (b * c) y) * (∑ z ∈ S, χ F (b * (1 + c)) z) = ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ∑ b : F, χ F b (x + c * y + (1 + c) * z) := by
    have h_lhs : ∑ b : F, (∑ x ∈ S, χ F b x) * (∑ y ∈ S, χ F (b * c) y) * (∑ z ∈ S, χ F (b * (1 + c)) z) = ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ∑ b : F, χ F b x * χ F (b * c) y * χ F (b * (1 + c)) z := by
      simp +decide only [sum_mul _ _ _, mul_sum];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm ) );
    -- Using the multiplicativity of the characters, we can combine the terms inside the sum.
    have h_mul : ∀ b x y z : F, χ F b x * χ F (b * c) y * χ F (b * (1 + c)) z = χ F b (x + c * y + (1 + c) * z) := by
      intro b x y z
      have h_mul : χ F b x * χ F (b * c) y * χ F (b * (1 + c)) z = χ F b x * χ F b (c * y) * χ F b ((1 + c) * z) := by
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, χ ];
      rw [ h_mul, χ_mul_snd, χ_mul_snd ];
    simpa only [ h_mul ] using h_lhs;
  -- By character orthogonality, the inner sum $\sum_{b \in F} \chi(b, w)$ is $|F|$ if $w = 0$ and $0$ otherwise.
  have h_ortho : ∀ w : F, ∑ b : F, χ F b w = if w = 0 then (Fintype.card F : ℤ) else 0 := by
    exact?;
  simp_all +decide [ Finset.sum_ite ];
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_comm, tripleCount ];
  simp +decide only [card_filter, sum_product];
  simp +decide only [Nat.cast_sum, mul_comm]

/-! ### Ratio reduction -/

/-
The triple count with general v₁, v₂ reduces to the normalized form.
    If v₁ ≠ 0, then the count with parameters (v₁, v₂) equals
    the count with parameters (1, v₂/v₁), i.e., N(v₂/v₁).
-/
theorem ratio_reduction (S : Finset F) (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) :
    ((S ×ˢ S ×ˢ S).filter (fun xyz : F × F × F =>
      v₁ * xyz.1 + v₂ * xyz.2.1 + (v₁ + v₂) * xyz.2.2 = 0)).card =
    ((S ×ˢ S ×ˢ S).filter (fun xyz : F × F × F =>
      xyz.1 + (v₂ / v₁) * xyz.2.1 + (1 + v₂ / v₁) * xyz.2.2 = 0)).card := by
  congr! 2;
  grind +qlia

end