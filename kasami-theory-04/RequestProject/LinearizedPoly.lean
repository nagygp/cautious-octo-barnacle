/-
# Linearized Polynomials over Finite Fields

This module develops the theory of q-linearized polynomials, which are
polynomials of the form L(x) = ∑ aᵢ x^{qⁱ} where q is a prime power.
These polynomials are 𝔽_q-linear maps, meaning L(x+y) = L(x) + L(y)
and L(αx) = αL(x) for α ∈ 𝔽_q.

## Main definitions

* `IsLinearized` : Predicate for q-linearized polynomials
* `frobenius_endo` : The Frobenius endomorphism x ↦ x^q
* `artinSchreier` : The Artin–Schreier map x ↦ x^q + x (= x^q - x in char p)

## Main results

* `artinSchreier_additive` : x ↦ x² + x is additive over F_{2^n}
* `artinSchreier_image_eq_trace_kernel` : Im(x ↦ x² + x) = ker(Tr)
* `artinSchreier_kernel_card` : |ker(x ↦ x² + x)| = 2

## References

* Lidl, Niederreiter, "Finite Fields", Chapter 3.4
* Goss, "Basic Structures of Function Field Arithmetic"
-/

import Mathlib
import RequestProject.TraceChar

open Finset BigOperators

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

attribute [local instance] ZMod.algebra

/-! ### Frobenius and Artin–Schreier -/

/-- The Frobenius endomorphism x ↦ x² in characteristic 2.
    This is a field automorphism of any finite field of characteristic 2. -/
def frobeniusEndo (x : F) : F := x ^ 2

/-- The Artin–Schreier map x ↦ x² + x.
    In characteristic 2, this equals x ↦ x² - x = x^q - x for q = 2.
    Its image is ker(Tr) and its kernel is 𝔽₂ = {0, 1}. -/
def artinSchreier (x : F) : F := x ^ 2 + x

/-
The Artin–Schreier map is 𝔽₂-linear (additive in char 2).
    Proof: (x+y)² + (x+y) = x² + y² + x + y = (x² + x) + (y² + y)
    using the Frobenius property (x+y)² = x² + y² in char 2.
-/
lemma artinSchreier_add (x y : F) :
    artinSchreier F (x + y) = artinSchreier F x + artinSchreier F y := by
  unfold artinSchreier; ring;
  grind +qlia

/-
The kernel of the Artin–Schreier map is {0, 1} = 𝔽₂.
-/
lemma artinSchreier_kernel :
    (Finset.univ.filter (fun x : F => artinSchreier F x = 0)) =
    ({0, 1} : Finset F) := by
  ext x
  simp [artinSchreier];
  grind

/-
The kernel has exactly 2 elements.
-/
lemma artinSchreier_kernel_card :
    (Finset.univ.filter (fun x : F => artinSchreier F x = 0)).card = 2 := by
  rw [ ← Finset.card_pair ( show ( 0 : F ) ≠ 1 by simp +decide ) ];
  convert congr_arg Finset.card ( artinSchreier_kernel F ) using 1

/-
The image of the Artin–Schreier map has size |F|/2.
    Since the kernel has size 2 and AS is a group homomorphism,
    |Im| = |F|/|Ker| = |F|/2.
-/
lemma artinSchreier_image_card :
    (Finset.univ.image (artinSchreier F)).card = Fintype.card F / 2 := by
  rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
  have h_image : Finset.card (Finset.image (artinSchreier F) Finset.univ) * 2 = Finset.card (Finset.univ : Finset F) := by
    have h_image : ∀ y ∈ Finset.image (artinSchreier F) Finset.univ, Finset.card (Finset.filter (fun x => artinSchreier F x = y) Finset.univ) = 2 := by
      intro y hy
      obtain ⟨x, hx⟩ : ∃ x, artinSchreier F x = y := by
        grind;
      have h_card : Finset.filter (fun x => artinSchreier F x = y) (Finset.univ : Finset F) = Finset.image (fun z => z + x) (Finset.filter (fun x => artinSchreier F x = 0) (Finset.univ : Finset F)) := by
        ext z; simp [hx, artinSchreier_add];
        grind;
      rw [ h_card, Finset.card_image_of_injective _ ( add_left_injective x ), artinSchreier_kernel_card ];
    have h_image : ∑ y ∈ Finset.image (artinSchreier F) Finset.univ, Finset.card (Finset.filter (fun x => artinSchreier F x = y) Finset.univ) = Finset.card (Finset.univ : Finset F) := by
      exact?;
    rw [ ← h_image, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ];
  exact h_image.symm

/-
The image of the Artin–Schreier map equals the trace kernel.
    Proof: For any x, Tr(x² + x) = Tr(x²) + Tr(x) = Tr(x) + Tr(x) = 0
    (using Tr ∘ Frob = Tr). So Im(AS) ⊆ ker(Tr).
    Both have size |F|/2, so they are equal.
-/
lemma artinSchreier_image_eq_trace_kernel :
    Finset.univ.image (artinSchreier F) =
    Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0) := by
  refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
  · unfold artinSchreier;
    simp +decide [ sq, add_eq_zero_iff_eq_neg ];
    -- Since $F$ is a finite field of characteristic 2, we have $x^2 = x$ for all $x \in F$.
    have h_frobenius : ∀ x : F, x^Fintype.card F = x := by
      exact FiniteField.pow_card;
    obtain ⟨ n, hn ⟩ := card_eq_two_pow F;
    intro x; rw [ ← sq ] ; induction' n with n ih <;> simp_all +decide [ pow_succ', pow_mul ] ;
    convert ( Algebra.trace_eq_of_algEquiv ( show F ≃ₐ[ZMod 2] F from { Equiv.ofBijective ( fun x => x * x ) ⟨ fun a b h => ?_, fun a => ?_ ⟩ with .. } ) ) x using 1;
    all_goals simp_all +decide [ mul_pow, add_pow_char ];
    · grind;
    · exact ⟨ a ^ ( 2 ^ n ), by linear_combination' h_frobenius a ⟩;
    · exact fun x y => by ring;
    · grind +ring;
    · intro r; fin_cases r <;> simp +decide ;
  · rw [ artinSchreier_image_card, trace_kernel_card ]

/-! ### Linearized Polynomials (general theory) -/

/-- A polynomial P(x) over F is q-linearized if P(x) = ∑ aᵢ x^{qⁱ}.
    We define this as the property that P is additive: P(x+y) = P(x) + P(y). -/
def IsLinearized (P : F → F) : Prop :=
  ∀ x y : F, P (x + y) = P x + P y

/-- The operator L_k(x) = x^{2^k} + x, used in Kasami derivative analysis. -/
def L_op (k : ℕ) (x : F) : F := x ^ (2 ^ k) + x

/-
L_k is linearized (additive) in characteristic 2.
    Proof: (x+y)^{2^k} = x^{2^k} + y^{2^k} by the Frobenius,
    so L_k(x+y) = (x+y)^{2^k} + (x+y) = x^{2^k} + y^{2^k} + x + y
                = L_k(x) + L_k(y).
-/
lemma L_op_linearized (k : ℕ) : IsLinearized F (L_op F k) := by
  intro x y; simp +decide [ L_op ] ;
  induction' k with k ih <;> simp_all +decide [ pow_succ, pow_mul ];
  · ring;
  · grind +extAll

/-- The kernel of a linearized polynomial is an 𝔽₂-subspace. -/
lemma linearized_kernel_subspace (P : F → F) (hP : IsLinearized F P) :
    ∀ x y : F, P x = 0 → P y = 0 → P (x + y) = 0 := by
  intro x y hx hy
  rw [hP x y, hx, hy, add_zero]

/-! ### Gold case: connection to Δ -/

/-
For the Gold exponent e = 3, the Kasami delta set equals the image of
    the Artin–Schreier map (which is ker(Tr)).

    Proof: b³ + (b+1)³ + 1
    = b³ + b³ + 3b² + 3b + 1 + 1  (expand)
    = 2b³ + 3b² + 3b + 2          (collect)
    = b² + b                        (reduce mod 2, since char = 2)
    = artinSchreier(b)
-/
lemma gold_delta_eq_artinSchreier :
    (Finset.univ.image (fun b : F => b ^ 3 + (b + 1) ^ 3 + 1)) =
    (Finset.univ.image (artinSchreier F)) := by
  -- By expanding $(b+1)^3$ and simplifying, we can show that $b^3 + (b+1)^3 + 1 = b^2 + b$.
  have h_expand : ∀ b : F, b^3 + (b + 1)^3 + 1 = b^2 + b := by
    grind +ring;
  aesop

/-
Combining: the Gold delta set equals the trace kernel.
-/
lemma gold_delta_eq_trace_kernel :
    (Finset.univ.image (fun b : F => b ^ 3 + (b + 1) ^ 3 + 1)) =
    Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0) := by
  -- Apply lemma gold_delta_eq_artinSchreier to interchange the image of either L_op or AS mapping.
  rw [gold_delta_eq_artinSchreier F];
  exact?

end