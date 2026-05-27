/-
# Walsh Transform

The Walsh (Hadamard) transform of a function `f : F → F` using an additive character.
Built on `AddChar`, `Finset.sum`, `Complex.abs`.

The Walsh transform is:
  W_f(a, b) = ∑_{x ∈ F} χ(b · f(x) + a · x)

where χ is an additive character from F to ℂ*.
-/
import Mathlib
import RequestProject.ABAPN.Defs

open Finset Function

namespace ABAPN.Walsh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Walsh transform -/

/-- The Walsh transform of `f` with respect to additive character `χ`,
    evaluated at `(a, b)`. -/
noncomputable def walshTransform (χ : AddChar F ℂ) (f : F → F) (a b : F) : ℂ :=
  ∑ x : F, χ (b * f x + a * x)

/-- Autocorrelation of `f` at direction `a`, which counts via character sums. -/
noncomputable def autoCorr (χ : AddChar F ℂ) (f : F → F) (a : F) : ℂ :=
  ∑ x : F, χ (f (x + a) - f x)

/-! ### Basic Walsh identities -/

/-
Walsh transform at `(0, 0)` equals `|F|`.
-/
lemma walshTransform_zero_zero (χ : AddChar F ℂ) (f : F → F) :
    walshTransform χ f 0 0 = Fintype.card F := by
  simp [walshTransform];

/-
Walsh transform at `b = 0` is a character sum of `χ(a · x)`.
-/
lemma walshTransform_zero_right (χ : AddChar F ℂ) (f : F → F) (a : F) :
    walshTransform χ f a 0 = ∑ x : F, χ (a * x) := by
  exact Finset.sum_congr rfl fun _ _ => by simp +decide [ mul_comm ] ;

/-
Walsh transform at `a = 0` is a character sum of `χ(b · f(x))`.
-/
lemma walshTransform_zero_left (χ : AddChar F ℂ) (f : F → F) (b : F) :
    walshTransform χ f 0 b = ∑ x : F, χ (b * f x) := by
  exact Finset.sum_congr rfl fun _ _ => by simp +decide ;

/-! ### Parseval's theorem (energy conservation) -/

/-
Parseval's identity: `∑_{a,b} |W_f(a,b)|^2 = |F|^2 · |F|`.
    This is a fundamental identity connecting Walsh spectrum to field size.
-/
lemma parseval (χ : AddChar F ℂ) (hχ : χ.IsPrimitive) (f : F → F) :
    ∑ a : F, ∑ b : F, ‖walshTransform χ f a b‖ ^ 2 =
      (Fintype.card F : ℝ) ^ 2 * Fintype.card F := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F, ∑ b : F, ‖∑ x : F, χ (b * f x + a * x)‖ ^ 2 = ∑ a : F, ∑ b : F, ∑ x : F, ∑ y : F, χ (b * (f x - f y) + a * (x - y)) := by
    have h_fubini : ∀ a b : F, ‖∑ x : F, χ (b * f x + a * x)‖ ^ 2 = ∑ x : F, ∑ y : F, χ (b * (f x - f y) + a * (x - y)) := by
      intro a b
      have h_expand : ‖∑ x : F, χ (b * f x + a * x)‖ ^ 2 = (∑ x : F, χ (b * f x + a * x)) * (∑ y : F, χ (-b * f y - a * y)) := by
        have h_expand : ∀ (z : ℂ), ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
          simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        convert h_expand _ using 2;
        rw [ map_sum ];
        refine' Finset.sum_congr rfl fun x _ => _;
        rw [ ← AddChar.map_neg_eq_conj ] ; ring;
      rw [ h_expand, Finset.sum_mul ];
      simp +decide only [Finset.mul_sum _ _ _];
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [ ← AddChar.map_add_eq_mul ] ; ring;
    simp +decide only [Complex.ofReal_sum, Complex.ofReal_pow, h_fubini];
  -- By Fubini's theorem, we can interchange the order of summation in the double sum.
  have h_fubini : ∑ a : F, ∑ b : F, ∑ x : F, ∑ y : F, χ (b * (f x - f y) + a * (x - y)) = ∑ x : F, ∑ y : F, ∑ a : F, ∑ b : F, χ (b * (f x - f y) + a * (x - y)) := by
    simp +decide only [← sum_product'];
    refine' Finset.sum_bij ( fun x _ => ( x.2.2.1, x.2.2.2, x.1, x.2.1 ) ) _ _ _ _ <;> simp +decide;
  -- By the properties of the character sum, we know that $\sum_{b \in F} \chi(b \cdot c) = 0$ if $c \neq 0$ and $|F|$ if $c = 0$.
  have h_char_sum : ∀ c : F, ∑ b : F, χ (b * c) = if c = 0 then (Fintype.card F : ℂ) else 0 := by
    intro c
    by_cases hc : c = 0;
    · simp +decide [ hc ];
    · have h_char_sum : ∑ b : F, χ (b * c) = 0 := by
        have h_nontrivial : χ ≠ 1 := by
          rintro rfl; simp_all +decide [ AddChar.IsPrimitive ] ;
          exact hχ one_ne_zero ( by ext; simp +decide [ AddChar.mulShift ] )
        have h_char_sum : ∑ b : F, χ (b * c) = ∑ b : F, χ b := by
          have h_char_sum : Function.Bijective (fun b : F => b * c) := by
            exact ⟨ mul_left_injective₀ hc, mul_right_surjective₀ hc ⟩;
          exact Equiv.sum_comp ( Equiv.ofBijective _ h_char_sum ) _;
        exact h_char_sum.trans ( AddChar.sum_eq_zero_of_ne_one h_nontrivial );
      rw [ if_neg hc, h_char_sum ];
  -- By the properties of the character sum, we know that $\sum_{a \in F} \chi(a \cdot d) = 0$ if $d \neq 0$ and $|F|$ if $d = 0$.
  have h_char_sum_a : ∀ d : F, ∑ a : F, χ (a * d) = if d = 0 then (Fintype.card F : ℂ) else 0 := by
    exact h_char_sum;
  -- Apply the character sum properties to simplify the expression.
  have h_simplify : ∑ x : F, ∑ y : F, ∑ a : F, ∑ b : F, χ (b * (f x - f y) + a * (x - y)) = ∑ x : F, ∑ y : F, (if f x - f y = 0 then (Fintype.card F : ℂ) else 0) * (if x - y = 0 then (Fintype.card F : ℂ) else 0) := by
    refine' Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => _;
    convert congr_arg₂ ( · * · ) ( h_char_sum ( f x - f y ) ) ( h_char_sum_a ( x - y ) ) using 1;
    simp +decide only [sum_mul _ _ _];
    simp +decide only [AddChar.map_add_eq_mul, Finset.mul_sum _ _ _];
    exact Finset.sum_comm;
  convert congr_arg Complex.re ‹↑ ( ∑ a : F, ∑ b : F, ‖∑ x : F, χ ( b * f x + a * x )‖ ^ 2 ) = ∑ a : F, ∑ b : F, ∑ x : F, ∑ y : F, χ ( b * ( f x - f y ) + a * ( x - y ) ) › using 1;
  rw [ h_fubini, h_simplify ];
  simp +decide [ sub_eq_zero, Finset.sum_ite ];
  ring

/-! ### Walsh spectrum and APN connection -/

/- The sum of fourth powers of Walsh values relates to differential uniformity.
   The correct identity is:
     ∑_{a,b} |W_f(a,b)|^4 = |F|^2 · ∑_{a,b} (deltaCount f a b)^2
   For APN functions in char 2, this evaluates to |F|^2 · (3|F|^2 - 2|F|).
   This requires substantial Fourier analysis infrastructure to formalize;
   the identity connecting Walsh spectrum to deltaCount squared sums
   is left as future work. -/

/-! ### Autocorrelation and deltaCount -/

/-
The autocorrelation decomposes via deltaCount and the character.
-/
lemma autoCorr_eq_sum_deltaCount (χ : AddChar F ℂ) (f : F → F) (a : F) :
    autoCorr χ f a = ∑ b : F, (deltaCount f a b : ℂ) * χ b := by
  -- By definition of deltaCount, we can rewrite the right-hand side of the equation.
  have h_deltaCount : ∀ b, (deltaCount f a b : ℂ) = ∑ x : F, if f (x + a) - f x = b then 1 else 0 := by
    simp +decide [ deltaCount, deltaSet ];
  simp +decide only [autoCorr, h_deltaCount, sum_mul _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop

/-! ### Walsh transform of linear functions -/

/-
If `f` is additive (`f(x+y) = f(x) + f(y)`), then the Walsh transform
    concentrates: `W_f(a,b) = 0` or `|F|`.
-/
lemma walshTransform_of_additive (χ : AddChar F ℂ) (_hχ : χ.IsPrimitive)
    (f : F → F) (hf : ∀ x y, f (x + y) = f x + f y) (a b : F) :
    walshTransform χ f a b = 0 ∨
    ‖walshTransform χ f a b‖ = Fintype.card F := by
  -- Since ψ is additive, we can write it as ψ = χ ∘ g for some additive map g : F → F.
  obtain ⟨g, hg⟩ : ∃ g : AddMonoidHom F F, ∀ x : F, b * f x + a * x = g x := by
    refine' ⟨ { toFun := fun x => b * f x + a * x, map_zero' := _, map_add' := _ }, fun x => rfl ⟩ <;> simp +decide [ hf ];
    · exact Or.inr ( by simpa using hf 0 0 );
    · grind;
  -- By AddChar.sum_eq_ite, this is |F| if ψ = 0 (trivial character) and 0 otherwise.
  have h_sum : ∑ x : F, χ (g x) = if (χ.compAddMonoidHom g) = 0 then (Fintype.card F : ℂ) else 0 := by
    convert AddChar.sum_eq_ite ( χ.compAddMonoidHom g ) using 1;
  unfold walshTransform; aesop;

end ABAPN.Walsh