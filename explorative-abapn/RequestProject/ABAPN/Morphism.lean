/-
# AB/APN Morphisms and Equivalences

Categorical and algebraic structure: equivalence of APN/AB functions
under affine transformations, composition with linear maps, and
the action of the Frobenius automorphism.

Built on `Equiv.Perm`, `RingHom`, `AddMonoidHom`, `Function.Injective`.
-/
import Mathlib
import RequestProject.ABAPN.Defs

open Finset Function ABAPN

namespace ABAPN.Morphism

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### CCZ-equivalence and EA-equivalence

Two functions `f, g : F → F` are:
- **EA-equivalent** if `g = A₁ ∘ f ∘ A₂ + A₃` for affine permutations `A₁, A₂`
  and affine map `A₃`.
- **CCZ-equivalent** if the graphs `{(x, f(x))}` and `{(x, g(x))}` are related
  by an affine permutation of `F × F`.

Both preserve the APN property.
-/

/-- An affine map `A(x) = L(x) + c` where `L` is `F`-linear. -/
structure AffineMap (F : Type*) [Field F] where
  linear : F →+* F
  constant : F

/-- Apply an affine map. -/
def AffineMap.apply (A : AffineMap F) (x : F) : F :=
  A.linear x + A.constant

/-! ### EA-equivalence -/

/-- Two functions are EA-equivalent if one can be obtained from the other
    by pre/post-composing with affine permutations (plus an additive affine). -/
def IsEAEquiv (f g : F → F) : Prop :=
  ∃ (A₁ A₂ : AffineMap F) (A₃ : F → F),
    Function.Bijective A₁.apply ∧
    Function.Bijective A₂.apply ∧
    (∀ x, A₃ (x + 0) = A₃ x) ∧  -- A₃ is affine
    ∀ x, g x = A₁.apply (f (A₂.apply x)) + A₃ x

/-! ### CCZ-equivalence -/

/-- The graph of `f : F → F` as a subset of `F × F`. -/
def graphSet (f : F → F) : Finset (F × F) :=
  Finset.univ.image (fun x => (x, f x))

/-- Two functions are CCZ-equivalent if there's an affine permutation of `F × F`
    mapping the graph of one to the graph of the other. -/
def IsCCZEquiv (f g : F → F) : Prop :=
  ∃ (L : F × F →+ F × F),
    Function.Bijective L ∧
    ∀ x, (x, f x) ∈ (graphSet g).val ↔ ∃ y, L (y, g y) = (x, f x)

/-! ### Preservation of APN under transformations -/

/-
Adding a constant preserves APN.
-/
lemma isAPN_add_const (f : F → F) (c : F) (hf : IsAPN f) :
    IsAPN (fun x => f x + c) := by
  -- By definition of APN, we need to show that for any nonzero a and any b, the number of solutions to (f(x+a) + c) - (f(x) + c) = b is at most 2.
  intro a ha b
  have h_eq : ∀ x, (f (x + a) + c) - (f x + c) = b ↔ f (x + a) - f x = b := by
    simp +decide;
  convert hf a ha b using 1;
  exact congr_arg Finset.card ( Finset.filter_congr fun x hx => by aesop )

/-
Pre-composing with a translation preserves APN.
-/
lemma isAPN_translate (f : F → F) (c : F) (hf : IsAPN f) :
    IsAPN (fun x => f (x + c)) := by
  intro a ha b;
  convert hf a ha b using 1;
  refine' Finset.card_bij ( fun x hx => x + c ) _ _ _ <;> simp +decide [ deltaSet ];
  · exact fun x hx => by rw [ add_right_comm ] ; exact hx;
  · exact fun x hx => ⟨ x - c, by simpa [ add_assoc ] using hx, by ring ⟩

/-
Post-composing with a field automorphism preserves APN.
-/
lemma isAPN_comp_ringHom (f : F → F) (σ : F →+* F)
    (hσ : Function.Bijective σ) (hf : IsAPN f) :
    IsAPN (σ ∘ f) := by
  intro a ha b;
  -- Let $b' = \sigma^{-1}(b)$.
  obtain ⟨b', hb'⟩ : ∃ b', σ b' = b := hσ.2 b;
  convert hf a ha b' using 1;
  refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp_all +decide [ deltaCount, deltaSet ];
  · intro x hx; have := σ.injective; aesop;
  · exact fun x hx => by rw [ ← hb', ← map_sub, hx ] ;

/-
Pre-composing with a nonzero scalar preserves APN.
-/
lemma isAPN_smul_pre (f : F → F) (c : F) (hc : c ≠ 0) (hf : IsAPN f) :
    IsAPN (fun x => f (c * x)) := by
  intro a ha b;
  convert hf ( c * a ) ( mul_ne_zero hc ha ) b using 1;
  refine' Finset.card_bij ( fun x hx => c * x ) _ _ _ <;> simp +decide [ *, mul_add, mul_assoc, mul_left_comm ];
  exact fun x hx => ⟨ c⁻¹ * x, by simpa [ mul_add, mul_assoc, mul_left_comm c, hc ] using hx, by simp +decide [ mul_assoc, mul_left_comm c, hc ] ⟩

/-
Post-composing with a nonzero scalar preserves APN.
-/
lemma isAPN_smul_post (f : F → F) (c : F) (hc : c ≠ 0) (hf : IsAPN f) :
    IsAPN (fun x => c * f x) := by
  intro a ha b
  have h_eq : deltaCount (fun x => c * f x) a b = deltaCount f a (b / c) := by
    refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp_all +decide [ deltaCount ];
    · exact fun x hx => by rw [ ← hx, ← mul_sub, mul_div_cancel_left₀ _ hc ] ;
    · exact fun x hx => by rw [ ← mul_sub, hx, mul_div_cancel₀ _ hc ] ;
  exact h_eq.symm ▸ hf a ha ( b / c )

/-
Adding a linear function preserves APN.
-/
lemma isAPN_add_linear (f : F → F) (L : F →+ F) (hf : IsAPN f) :
    IsAPN (fun x => f x + L x) := by
  intro a ha b
  simp [IsAPN] at *;
  convert hf a ha ( b - L a ) using 2 ; ring;
  grind +ring

/-! ### Frobenius action -/

variable [CharP F 2]

/-
The Frobenius automorphism preserves APN: if `f` is APN, so is `frobenius ∘ f`.
-/
lemma isAPN_frobenius_comp (f : F → F) (hf : IsAPN f) :
    IsAPN (fun x => frobenius F 2 (f x)) := by
  convert isAPN_comp_ringHom f ( frobenius F 2 ) _ hf using 1;
  exact Finite.injective_iff_bijective.mp ( frobenius_inj F 2 )

/-
Frobenius applied to input preserves APN: if `f` is APN, so is `f ∘ frobenius`.
-/
lemma isAPN_comp_frobenius (f : F → F) (hf : IsAPN f) :
    IsAPN (fun x => f (frobenius F 2 x)) := by
  intro a ha b
  have h_frobenius_eq : ∀ x, f (frobenius F 2 x + frobenius F 2 a) - f (frobenius F 2 x) = f (frobenius F 2 (x + a)) - f (frobenius F 2 x) := by
    grind +extAll;
  -- Since frobenius is injective, the set of solutions to $f(frobenius(x+a)) - f(frobenius(x)) = b$ is in bijection with the set of solutions to $f(frobenius(x)+frobenius(a)) - f(frobenius(x)) = b$.
  have h_bij : Finset.card (Finset.filter (fun x => f (frobenius F 2 x + frobenius F 2 a) - f (frobenius F 2 x) = b) Finset.univ) ≤ 2 := by
    have h_bij : Finset.card (Finset.image (fun x => frobenius F 2 x) (Finset.filter (fun x => f (frobenius F 2 x + frobenius F 2 a) - f (frobenius F 2 x) = b) Finset.univ)) ≤ 2 := by
      have h_bij : Finset.card (Finset.filter (fun x => f (x + frobenius F 2 a) - f x = b) Finset.univ) ≤ 2 := by
        convert hf ( frobenius F 2 a ) _ b using 1;
        simp +decide [ ha, frobenius ];
      refine' le_trans ( Finset.card_le_card _ ) h_bij;
      simp +contextual [ Finset.subset_iff ];
    rwa [ Finset.card_image_of_injective _ ( frobenius_inj F 2 ) ] at h_bij;
  unfold deltaCount; aesop;

/-
Power equivalence: `x^d` is APN iff `x^(2·d)` is APN (Frobenius twist).
-/
lemma isAPN_power_double_iff (d : ℕ) :
    IsAPN (fun (x : F) => x ^ d) ↔ IsAPN (fun (x : F) => x ^ (2 * d)) := by
  -- By definition of exponentiation in characteristic 2, we have $x^{2d} = (x^d)^2$.
  have h_exp : ∀ x : F, x ^ (2 * d) = (x ^ d) ^ 2 := by
    exact fun x => pow_mul' x 2 d ▸ rfl;
  constructor <;> intro h <;> simp_all +decide [ IsAPN ];
  · -- Since we're in characteristic 2, squaring is a bijection. Therefore, the number of solutions to ((x + a)^d)^2 - (x^d)^2 = b is the same as the number of solutions to (x + a)^d - x^d = sqrt(b).
    have h_bij : ∀ b : F, ∃ c : F, b = c^2 := by
      intro b
      have h_bij : Function.Bijective (fun x : F => x^2) := by
        have h_bij : Function.Injective (fun x : F => x^2) := by
          intro x y hxy;
          grind;
        exact ⟨ h_bij, Finite.injective_iff_surjective.mp h_bij ⟩
      exact h_bij.surjective b |> fun ⟨c, hc⟩ => ⟨c, hc.symm⟩;
    intro a ha b
    obtain ⟨c, hc⟩ := h_bij b
    have h_eq : ∀ x : F, ((x + a) ^ d) ^ 2 - (x ^ d) ^ 2 = b ↔ (x + a) ^ d - x ^ d = c := by
      grind;
    simpa only [ h_eq ] using h a ha c;
  · intro a ha b; specialize h a ha ( b ^ 2 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    convert h using 2 ; ext x ; simp +decide [ ← sq_eq_sq_iff_eq_or_eq_neg ] ; ring;
    grind

/-! ### Inverse and permutation -/

/-
If `f` is a bijection and APN, then `f⁻¹` is also APN.
-/
lemma isAPN_of_bijective_inverse (f : F → F) (hbij : Function.Bijective f) (hf : IsAPN f) :
    IsAPN (Function.invFun f) := by
  intro a ha b
  have h_eq : ∀ x, f (invFun f x) = x := by
    exact fun x => invFun_eq ( hbij.2 x );
  by_cases hb : b = 0 <;> simp_all +decide [ deltaCount ];
  · simp +decide [ sub_eq_zero ];
    exact le_trans ( Finset.card_le_one.mpr fun x hx y hy => by have := h_eq ( x + a ) ; have := h_eq x; have := h_eq ( y + a ) ; have := h_eq y; aesop ) ( by decide );
  · have h_eq : Finset.card (Finset.filter (fun x => f (invFun f (x + a)) - f (invFun f x) = a) (Finset.univ.filter (fun x => invFun f (x + a) - invFun f x = b))) ≤ 2 := by
      have h_eq : Finset.card (Finset.filter (fun x => f (invFun f (x + a)) - f (invFun f x) = a) (Finset.univ.filter (fun x => invFun f (x + a) - invFun f x = b))) ≤ Finset.card (Finset.filter (fun x => f (x + b) - f x = a) (Finset.univ)) := by
        have h_eq : Finset.image (fun x => invFun f x) (Finset.filter (fun x => f (invFun f (x + a)) - f (invFun f x) = a) (Finset.univ.filter (fun x => invFun f (x + a) - invFun f x = b))) ⊆ Finset.filter (fun x => f (x + b) - f x = a) (Finset.univ) := by
          grind;
        have := Finset.card_le_card h_eq;
        rwa [ Finset.card_image_of_injective _ ( show Function.Injective ( invFun f ) from fun x y hxy => by have := ‹∀ x, f ( invFun f x ) = x› x; have := ‹∀ x, f ( invFun f x ) = x› y; aesop ) ] at this;
      exact h_eq.trans ( hf b hb a );
    convert h_eq using 2 ; aesop

/-! ### Permutation group action -/

/-- The symmetric group `Equiv.Perm F` acts on functions `F → F` by conjugation. -/
def permConj (σ : Equiv.Perm F) (f : F → F) : F → F := σ ∘ f ∘ σ.symm

/- Note: Conjugation by a *general* permutation does NOT preserve APN.
   The permutation must be affine (composition of linear map + translation)
   for APN to be preserved. See `isAPN_comp_ringHom` and `isAPN_translate`
   for the correct preservation results. -/

end ABAPN.Morphism