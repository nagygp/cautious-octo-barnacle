/-
# Linear Algebra Perspective

APN/AB functions through the lens of vector spaces over GF(2).
The key observation: GF(2^n) is an n-dimensional vector space over GF(2),
and linearized polynomials are F₂-linear maps.

Built on `Module`, `LinearMap`, `Submodule`, `frobenius`.
-/
import Mathlib
import RequestProject.ABAPN.Defs
import RequestProject.ABAPN.CharTwo

open Finset Function ABAPN

namespace ABAPN.LinAlg

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Linearized polynomials

A linearized polynomial over GF(2^n) has the form
  L(x) = ∑ᵢ aᵢ · x^(2^i)
These are exactly the F₂-linear maps F → F.
-/

/-- A function is F₂-linear (additive) if `f(x + y) = f(x) + f(y)`. -/
def IsF2Linear (f : F → F) : Prop :=
  ∀ x y, f (x + y) = f x + f y

/-
The Frobenius `x ↦ x^2` is F₂-linear.
-/
lemma frobenius_isF2Linear : IsF2Linear (fun (x : F) => x ^ 2) := by
  grind +locals

/-
Iterated Frobenius `x ↦ x^(2^k)` is F₂-linear.
-/
lemma iterFrob_isF2Linear (k : ℕ) : IsF2Linear (fun (x : F) => x ^ (2 ^ k)) := by
  intro x y; induction k <;> simp_all +decide [ pow_succ, pow_mul, mul_assoc ] ;
  grind +ring

/-
Composition of F₂-linear functions is F₂-linear.
-/
lemma isF2Linear_comp {f g : F → F} (hf : IsF2Linear f) (hg : IsF2Linear g) :
    IsF2Linear (f ∘ g) := by
  exact fun x y => by rw [ Function.comp_apply, hg, Function.comp_apply, Function.comp_apply, hf ] ;

/-
Sum of F₂-linear functions is F₂-linear.
-/
lemma isF2Linear_add {f g : F → F} (hf : IsF2Linear f) (hg : IsF2Linear g) :
    IsF2Linear (fun x => f x + g x) := by
  exact fun x y => by simp +decide [ hf x y, hg x y, add_assoc, add_comm, add_left_comm ] ;

/-
Scalar multiple of F₂-linear function is F₂-linear.
-/
lemma isF2Linear_smul (c : F) {f : F → F} (hf : IsF2Linear f) :
    IsF2Linear (fun x => c * f x) := by
  exact fun x y => by simp +decide [ hf x y, mul_add ] ;

/-- The zero function is F₂-linear. -/
lemma isF2Linear_zero : IsF2Linear (fun (_ : F) => (0 : F)) := by
  intro x y; simp

/-- The identity is F₂-linear. -/
lemma isF2Linear_id : IsF2Linear (fun (x : F) => x) := by
  intro x y; rfl

/-! ### Kernel of F₂-linear maps -/

/-- The kernel of an F₂-linear map as a Finset. -/
def f2Kernel (f : F → F) : Finset F :=
  Finset.univ.filter (fun x => f x = 0)

/-
The kernel size of an F₂-linear map is a power of 2.
-/
lemma f2Kernel_card_pow_two (f : F → F) (hf : IsF2Linear f) :
    ∃ k : ℕ, (f2Kernel f).card = 2 ^ k := by
  have h_kernel : ∃ k : ℕ, (Nat.card (Finset.filter (fun x => f x = 0) Finset.univ : Finset F)) = 2 ^ k := by
    have h_vector_space : ∀ x y : F, f (x + y) = f x + f y := by
      exact hf
    have h_zero : f 0 = 0 := by
      simpa using h_vector_space 0 0
    have h_add_group : ∃ (G : AddSubgroup (Fin 1 → F)), Nat.card G = Nat.card {x | f x = 0} := by
      refine' ⟨ _, _ ⟩;
      refine' { carrier := Set.range ( fun x : { x : F | f x = 0 } => fun _ => x.val ), zero_mem' := _, add_mem' := _, neg_mem' := _ };
      all_goals simp_all +decide [ funext_iff, Fin.forall_fin_one ];
      · intro x hx; have := h_vector_space ( -x 0 ) ( x 0 ) ; aesop;
      · exact Fintype.card_congr ( Equiv.ofBijective ( fun x => ⟨ x.val 0, x.property ⟩ ) ⟨ fun x => by
          simp +decide [ funext_iff, Fin.forall_fin_one ];
          exact fun a ha hx => Subtype.ext <| funext fun i => by fin_cases i; exact hx;, fun x => by
          exact ⟨ ⟨ fun _ => x.val, x.property ⟩, rfl ⟩ ⟩ );
    obtain ⟨ G, hG ⟩ := h_add_group;
    have h_card_G : ∃ k : ℕ, Nat.card G = 2 ^ k := by
      have h_vector_space : Module (ZMod 2) (Fin 1 → F) := by
        have h_vector_space : Algebra (ZMod 2) F := by
          exact ZMod.algebra _ _;
        exact inferInstance
      have h_card_G : ∃ k : ℕ, Nat.card G = Nat.card (Fin k → ZMod 2) := by
        have h_card_G : ∃ k : ℕ, Nonempty (G ≃ₗ[ZMod 2] Fin k → ZMod 2) := by
          exact ⟨ Module.finrank ( ZMod 2 ) G, ⟨ ( Module.finBasis ( ZMod 2 ) G ).equivFun ⟩ ⟩;
        exact ⟨ h_card_G.choose, Nat.card_congr h_card_G.choose_spec.some ⟩;
      aesop;
    aesop;
  simpa [ Fintype.card_subtype ] using h_kernel

/-
An F₂-linear map is injective iff its kernel is trivial.
-/
lemma f2Linear_injective_iff_kernel_trivial (f : F → F) (hf : IsF2Linear f)
    (hf0 : f 0 = 0) :
    Function.Injective f ↔ f2Kernel f = {0} := by
  constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, f2Kernel ];
  · lia;
  · intro x y hxy; have := hf x ( y - x ) ; simp_all +decide ;
    exact Eq.symm ( sub_eq_zero.mp this )

/-! ### APN for Gold exponents via kernel dimension

For Gold `d = 2^k + 1`, the difference `(x+a)^d + x^d = a^d + L_a(x)`
where `L_a(x) = a · x^(2^k) + a^(2^k) · x` is F₂-linear.
APN ⟺ ker(L_a) = {0, a} for all a ≠ 0
⟺ ker(L_a) has dimension ≤ 1 over F₂.
-/

/-- The linearized part of the Gold difference: `L_a(x) = a · x^(2^k) + a^(2^k) · x`. -/
def goldLinearPart (k : ℕ) (a : F) (x : F) : F :=
  a * x ^ (2 ^ k) + a ^ (2 ^ k) * x

/-
The Gold linear part is F₂-linear in `x`.
-/
lemma goldLinearPart_isF2Linear (k : ℕ) (a : F) :
    IsF2Linear (goldLinearPart k a) := by
  convert isF2Linear_add ( isF2Linear_smul a ( iterFrob_isF2Linear k ) ) ( isF2Linear_smul ( a ^ ( 2 ^ k ) ) ( isF2Linear_id ) ) using 1

/-
The Gold linear part at `x = a` vanishes: `L_a(a) = 0` in char 2.
-/
lemma goldLinearPart_self (k : ℕ) (a : F) :
    goldLinearPart k a a = 0 := by
  convert ABAPN.CharTwo.add_self_eq_zero ( a ^ ( 2 ^ k ) * a ) using 1 ; ring;
  unfold goldLinearPart; ring;

/-- The Gold linear part at `x = 0` vanishes. -/
@[simp]
lemma goldLinearPart_zero (k : ℕ) (a : F) :
    goldLinearPart k a 0 = 0 := by
  simp [goldLinearPart]

/-! ### Image of F₂-linear maps -/

/-
The image of an F₂-linear map has size `|F| / |ker|`.
-/
lemma f2Linear_image_card (f : F → F) (hf : IsF2Linear f) (hf0 : f 0 = 0) :
    (Finset.univ.image f).card * (f2Kernel f).card = Fintype.card F := by
  have h_card_image : ∀ y ∈ Finset.image f Finset.univ, Finset.card (Finset.filter (fun x => f x = y) Finset.univ) = Finset.card (f2Kernel f) := by
    intro y hy
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ = y := by
      aesop;
    have h_bij : Finset.image (fun x => x₀ + x) (f2Kernel f) = Finset.filter (fun x => f x = y) Finset.univ := by
      ext x; simp [f2Kernel];
      have := hf ( -x₀ + x ) x₀; simp_all +decide [ add_comm, add_left_comm ] ;
    rw [ ← h_bij, Finset.card_image_of_injective _ ( add_right_injective x₀ ) ];
  have h_card_image : ∑ y ∈ Finset.image f Finset.univ, Finset.card (Finset.filter (fun x => f x = y) Finset.univ) = Fintype.card F := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; aesop;
  rw [ ← h_card_image, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ]

end ABAPN.LinAlg