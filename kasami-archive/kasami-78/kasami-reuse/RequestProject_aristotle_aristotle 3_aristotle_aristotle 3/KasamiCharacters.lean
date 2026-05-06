/-
  KasamiCharacters.lean

  Step 1 of the Kasami Triple-Count proof pathway:
  Additive characters over GF(2^n) and their orthogonality properties.

  This file establishes:
  1. The canonical primitive additive character χ : F → ℂ on a finite field F
     (obtained via trace and roots of unity, from Mathlib).
  2. The orthogonality relation: ∑_x χ(a·x) = 0 for a ≠ 0.
  3. The Walsh transform of a function f : F → F.
  4. Parseval's identity for the Walsh transform.
  5. Connection to the Kasami function kasamiFun.
-/
import Mathlib
import KasamiConjecture

noncomputable section

open Finset BigOperators Complex

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Section 1: The Canonical Additive Character -/

/-- The canonical primitive additive character on a finite field F with values in ℂ.
    This is constructed via the trace map Tr : F → GF(p) composed with a primitive
    p-th root of unity. For F = GF(2^n), this gives χ(α) = (-1)^{Tr(α)}. -/
def kasamiChar : AddChar F ℂ :=
  AddChar.FiniteField.primitiveChar_to_Complex F

/-- The canonical character is primitive: χ(a · -) ≠ 1 for a ≠ 0. -/
theorem kasamiChar_isPrimitive :
    (kasamiChar F).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F

/-! ## Section 2: Character Orthogonality -/

/-- **Orthogonality relation (right-multiplication form).**
    For a ≠ 0: ∑_x χ(x · a) = 0. -/
theorem sum_char_mul_eq_zero (a : F) (ha : a ≠ 0) :
    ∑ x : F, (kasamiChar F) (x * a) = 0 := by
  have hprim := kasamiChar_isPrimitive F
  have h := AddChar.sum_mulShift (ψ := kasamiChar F) a hprim
  simp [ha] at h
  exact h

/-- **Orthogonality relation (left-multiplication form).**
    For a ≠ 0: ∑_x χ(a · x) = 0. -/
theorem sum_char_mul_left_eq_zero (a : F) (ha : a ≠ 0) :
    ∑ x : F, (kasamiChar F) (a * x) = 0 := by
  simp only [show ∀ x : F, a * x = x * a from fun x => mul_comm a x]
  exact sum_char_mul_eq_zero F a ha

/-- **Trivial character sum.**
    ∑_x χ(0 · x) = |F|. -/
theorem sum_char_zero :
    ∑ x : F, (kasamiChar F) (0 * x) = ↑(Fintype.card F) := by
  simp [AddChar.map_zero_eq_one]

/-- Each character value has norm 1. -/
theorem kasamiChar_norm (x : F) :
    ‖(kasamiChar F) x‖ = 1 :=
  AddChar.norm_apply (kasamiChar F) x

/-- Each character value has |χ(x)|² = 1 (as normSq). -/
theorem kasamiChar_normSq (x : F) :
    Complex.normSq ((kasamiChar F) x) = 1 := by
  rw [show Complex.normSq ((kasamiChar F) x) = ‖(kasamiChar F) x‖ ^ 2 from by
    simp [Complex.normSq_eq_norm_sq]]
  rw [kasamiChar_norm]; norm_num

/-! ## Section 3: The Walsh Transform -/

/-- The Walsh transform of f : F → F with respect to the canonical character:
    W_f(a, b) = ∑_{x ∈ F} χ(a·x + b·f(x)). -/
def walshTransform (f : F → F) (a b : F) : ℂ :=
  ∑ x : F, (kasamiChar F) (a * x + b * f x)

/-- The Walsh transform of the Kasami function. -/
def kasamiWalsh (k : ℕ) (a b : F) : ℂ :=
  walshTransform F (kasamiFun F k) a b

/-! ## Section 4: Basic Walsh Transform Properties -/

/-- When b = 0, the Walsh transform reduces to ∑_x χ(a·x). -/
theorem walshTransform_b_zero (f : F → F) (a : F) :
    walshTransform F f a 0 = ∑ x : F, (kasamiChar F) (a * x) := by
  unfold walshTransform
  congr 1; ext x; ring_nf

/-- When a = 0 and b = 0, the Walsh transform equals |F|. -/
theorem walshTransform_zero_zero (f : F → F) :
    walshTransform F f 0 0 = ↑(Fintype.card F) := by
  unfold walshTransform
  simp [AddChar.map_zero_eq_one]

/-- For a ≠ 0 and b = 0, the Walsh transform is 0. -/
theorem walshTransform_ne_zero_b_zero (f : F → F) (a : F) (ha : a ≠ 0) :
    walshTransform F f a 0 = 0 := by
  rw [walshTransform_b_zero]
  exact sum_char_mul_left_eq_zero F a ha

/-! ## Section 5: Parseval's Identity for the Walsh Transform -/

/-
**Parseval's identity for Walsh transforms.**

    ∑_a |W_f(a, b)|² = |F|²

    Proof sketch: expand |W_f(a,b)|² = W_f(a,b) · conj(W_f(a,b)),
    swap the sum over a with the double sum over x, y,
    use orthogonality ∑_a χ(a·(x-y)) = |F| · δ(x,y).
-/
theorem walshTransform_parseval (f : F → F) (b : F) :
    ∑ a : F, Complex.normSq (walshTransform F f a b) =
      (Fintype.card F : ℝ) ^ 2 := by
  unfold walshTransform;
  -- Expand the norm squared and interchange the order of summation.
  have h_expand : ∑ a : F, normSq (∑ x : F, (kasamiChar F) (a * x + b * f x)) = ∑ x : F, ∑ y : F, ∑ a : F, (kasamiChar F) (a * (x - y)) * (kasamiChar F) (b * (f x - f y)) := by
    have h_expand : ∀ a : F, normSq (∑ x : F, (kasamiChar F) (a * x + b * f x)) = ∑ x : F, ∑ y : F, (kasamiChar F) (a * (x - y) + b * (f x - f y)) := by
      intro a
      have h_expand : normSq (∑ x : F, (kasamiChar F) (a * x + b * f x)) = (∑ x : F, (kasamiChar F) (a * x + b * f x)) * (∑ y : F, (kasamiChar F) (-(a * y + b * f y))) := by
        have h_sum : ∀ z : ℂ, normSq z = z * starRingEnd ℂ z := by
          simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        convert h_sum _ using 2;
        simp +decide [ AddChar.neg_apply ];
        exact Finset.sum_congr rfl fun x _ => by rw [ ← AddChar.map_neg_eq_conj ] ; ring;
      rw [ h_expand, Finset.sum_mul ];
      simp +decide only [Finset.mul_sum _ _ _, ← AddChar.map_add_eq_mul] ; congr ; ext ; ring;
    push_cast [ h_expand ];
    simp +decide only [AddChar.map_add_eq_mul];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  -- Apply the orthogonality relation to the inner sum.
  have h_inner : ∀ x y : F, ∑ a : F, (kasamiChar F) (a * (x - y)) = if x = y then (Fintype.card F : ℂ) else 0 := by
    intro x y; split_ifs with h; simp +decide [ h ] ;
    convert sum_char_mul_eq_zero F ( x - y ) ( sub_ne_zero.mpr h ) using 1;
  rw [ ← Complex.ofReal_inj ] ; simp_all +decide [ ← Finset.sum_mul ] ; ring;

/-! ## Section 6: Connection to the Abstract Framework -/

/-- The Almost Bent property stated concretely using the Walsh transform.
    For an AB function, |W_f(a,b)|² ∈ {0, 2^{n+1}} for b ≠ 0. -/
def IsAlmostBent (f : F → F) (n : ℕ) : Prop :=
  Fintype.card F = 2 ^ n ∧
  ∀ a b : F, b ≠ 0 →
    Complex.normSq (walshTransform F f a b) = 0 ∨
    Complex.normSq (walshTransform F f a b) = (2 : ℝ) ^ (n + 1)

end