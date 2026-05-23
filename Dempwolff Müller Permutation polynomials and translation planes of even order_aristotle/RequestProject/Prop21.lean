import Mathlib

/-!
# Proposition 2.1 — Dempwolff & Müller

Formalization of Proposition 2.1(a) from "Permutation polynomials and
translation planes of even order" by U. Dempwolff and P. Müller (Adv. Geom. 2013).

**Setting.** Let `F` be a finite field, `L : F →+ F` an additive map, and `k : ℕ`.
Define `P(x) = L(x) · x ^ k` and the binary operation `x ⊙ y = L(x·y) · x ^ k`.

**Proposition 2.1(a).** If `P` is a bijection on `F`, then:
1. `L` is a bijection.
2. `(F, +, ⊙)` is a weak quasifield, i.e.
   - (WQ1) `x ⊙ 0 = 0` and `0 ⊙ x = 0`;
   - (WQ2) `x ⊙ (y + z) = x ⊙ y + x ⊙ z`;
   - (WQ3) for `a ≠ 0`, both `x ↦ x ⊙ a` and `x ↦ a ⊙ x` are bijective.
3. The cyclic group `μ_c : (x, y) ↦ (c⁻¹ x, cᵏ y)` maps the fiber `V(b)` to `V(b·c)`.
-/

namespace DempwolffMueller

variable {F : Type*} [Field F] [Finite F]

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- `P(x) = L(x) · x ^ k`, the "permutation polynomial map". -/
def P (L : F → F) (k : ℕ) (x : F) : F := L x * x ^ k

/-- The weak-quasifield multiplication `x ⊙ y = L(x · y) · x ^ k`. -/
def qfMul (L : F → F) (k : ℕ) (x y : F) : F := L (x * y) * x ^ k

/-
═══════════════════════════════════════════
Part 1 : L is bijective
═══════════════════════════════════════════

`P(x) = 0` whenever `L(x) = 0`.
-/
omit [Finite F] in
lemma P_eq_zero_of_L_eq_zero (L : F → F) (k : ℕ) {x : F} (h : L x = 0) :
    P L k x = 0 := by
      -- By definition of $P$, we have $P L k x = L x * x^k$.
      simp [P, h]

/-
`P(0) = 0` for additive `L`.
-/
omit [Finite F] in
lemma P_zero (L : F →+ F) (k : ℕ) : P L k 0 = 0 := by
  unfold P; aesop;

/-
If `L(x) = 0` and `P` is injective then `x = 0`.
-/
omit [Finite F] in
lemma eq_zero_of_L_eq_zero_of_P_inj (L : F →+ F) (k : ℕ)
    (hP : Function.Injective (P L k)) {x : F} (hLx : L x = 0) :
    x = 0 := by
      exact hP ( by simp +decide [ *, P ] )

/-
`L` is injective when `P` is injective.
    Proof: if `L a = L b` then `L(a - b) = 0`, so `P(a - b) = 0 = P(0)`,
    giving `a - b = 0`.
-/
omit [Finite F] in
lemma L_injective (L : F →+ F) (k : ℕ) (hP : Function.Injective (P L k)) :
    Function.Injective L := by
      intro a b hab;
      have := @hP ( a - b ) 0 ; simp_all +decide [ sub_eq_iff_eq_add ];
      apply this; simp [P, hab]

/-- `L` is bijective (injective + finite ⟹ bijective). -/
lemma L_bijective (L : F →+ F) (k : ℕ) (hP : Function.Injective (P L k)) :
    Function.Bijective L :=
  Finite.injective_iff_bijective.mp (L_injective L k hP)

/-
═══════════════════════════════════════════
Part 2 : (WQ1) Multiplication by zero
═══════════════════════════════════════════

`x ⊙ 0 = 0`.
-/
omit [Finite F] in
lemma qfMul_zero_right (L : F →+ F) (k : ℕ) (x : F) :
    qfMul L k x 0 = 0 := by
      unfold qfMul;
      simp +decide [ L.map_zero ]

/-
`0 ⊙ x = 0`.
-/
omit [Finite F] in
lemma qfMul_zero_left (L : F →+ F) (k : ℕ) (x : F) :
    qfMul L k 0 x = 0 := by
      unfold qfMul; simp +decide ;

/-
═══════════════════════════════════════════
Part 3 : (WQ2) Left distributivity
═══════════════════════════════════════════

`L(x(y + z)) = L(xy) + L(xz)` — additivity of `L` applied after distributing.
-/
omit [Finite F] in
lemma L_mul_add (L : F →+ F) (x y z : F) :
    L (x * (y + z)) = L (x * y) + L (x * z) := by
      rw [ ← map_add, ← mul_add ]

/-
`x ⊙ (y + z) = x ⊙ y + x ⊙ z`.
-/
omit [Finite F] in
lemma qfMul_add_right (L : F →+ F) (k : ℕ) (x y z : F) :
    qfMul L k x (y + z) = qfMul L k x y + qfMul L k x z := by
      convert congr_arg ( fun w => w * x ^ k ) ( L.map_add ( x * y ) ( x * z ) ) using 1 <;> push_cast [ qfMul ] <;> ring!;

/-
═══════════════════════════════════════════
Part 4 : (WQ3) Right-multiplication is injective
═══════════════════════════════════════════

Key identity: `(x ⊙ a) · a^k = P(x · a)`.
    Used to reduce injectivity of right multiplication to injectivity of `P`.
-/
omit [Finite F] in
lemma qfMul_mul_pow_eq_P (L : F → F) (k : ℕ) (x a : F) :
    qfMul L k x a * a ^ k = P L k (x * a) := by
      unfold qfMul P;
      rw [ mul_assoc, mul_pow ]

/-
For `a ≠ 0`, the map `x ↦ x ⊙ a` is injective.
    Proof: multiply `x ⊙ a = x₁ ⊙ a` by `a^k` to get `P(xa) = P(x₁a)`,
    then use injectivity of `P` and cancel `a`.
-/
omit [Finite F] in
lemma qfMul_right_injective (L : F →+ F) (k : ℕ)
    (hP : Function.Injective (P L k)) {a : F} (ha : a ≠ 0) :
    Function.Injective (fun x => qfMul L k x a) := by
      -- Assume x ⊙ a = x₁ ⊙ a. Multiply both sides by a^k (nonzero) to get P(ax) = P(ax₁).
      intro x x₁ h_eq
      have hP_eq : P L k (x * a) = P L k (x₁ * a) := by
        convert congr_arg ( · * a ^ k ) h_eq using 1 <;> simp +decide [ qfMul_mul_pow_eq_P ];
      grind

/-- For `a ≠ 0`, the map `x ↦ x ⊙ a` is bijective. -/
lemma qfMul_right_bijective (L : F →+ F) (k : ℕ)
    (hP : Function.Injective (P L k)) {a : F} (ha : a ≠ 0) :
    Function.Bijective (fun x => qfMul L k x a) :=
  Finite.injective_iff_bijective.mp (qfMul_right_injective L k hP ha)

/-
═══════════════════════════════════════════
Part 5 : (WQ3) Left-multiplication is injective
═══════════════════════════════════════════

Cancelling `a^k ≠ 0` from both sides of the quasifield product.
    From `L(a·x₁)·a^k = L(a·x₂)·a^k` deduce `L(a·x₁) = L(a·x₂)`.
-/
omit [Finite F] in
lemma L_eq_of_qfMul_eq (L : F →+ F) (k : ℕ) {a x₁ x₂ : F} (ha : a ≠ 0)
    (h : qfMul L k a x₁ = qfMul L k a x₂) :
    L (a * x₁) = L (a * x₂) := by
      exact mul_right_cancel₀ ( pow_ne_zero k ha ) h

/-
For `a ≠ 0`, the map `x ↦ a ⊙ x` is injective.
    Proof: cancel `a^k`, use injectivity of `L`, then cancel `a`.
-/
omit [Finite F] in
lemma qfMul_left_injective (L : F →+ F) (k : ℕ)
    (hP : Function.Injective (P L k)) {a : F} (ha : a ≠ 0) :
    Function.Injective (fun x => qfMul L k a x) := by
      intro x y hxy_eq;
      -- By canceling `a^k`, we obtain `L(a*x₁) = L(a*x₂)`.
      have hL_cancel : L (a * x) = L (a * y) := by
        exact L_eq_of_qfMul_eq L k ha hxy_eq;
      exact ( L_injective L k hP ) hL_cancel |> fun h => mul_left_cancel₀ ha h

/-- For `a ≠ 0`, the map `x ↦ a ⊙ x` is bijective. -/
lemma qfMul_left_bijective (L : F →+ F) (k : ℕ)
    (hP : Function.Injective (P L k)) {a : F} (ha : a ≠ 0) :
    Function.Bijective (fun x => qfMul L k a x) :=
  Finite.injective_iff_bijective.mp (qfMul_left_injective L k hP ha)

/-
═══════════════════════════════════════════
Part 6 : Action (Aₖ) — μ_c maps V(b) to V(bc)
═══════════════════════════════════════════

`b · c · (c⁻¹ · x) = b · x` when `c ≠ 0`.
-/
omit [Finite F] in
lemma mul_inv_mul_cancel {b c x : F} (hc : c ≠ 0) :
    b * c * (c⁻¹ * x) = b * x := by
      simp +decide [ hc, mul_assoc ]

/-
`(b · c) ^ k = b ^ k · c ^ k`.
-/
omit [Finite F] in
lemma mul_pow_comm (b c : F) (k : ℕ) : (b * c) ^ k = b ^ k * c ^ k := by
  rw [mul_pow]

/-
**Action identity.** The second component of `μ_c` applied to `(x, b ⊙ x)` equals
    `(b·c) ⊙ (c⁻¹·x)`, showing that `μ_c` sends the fiber `V(b)` to `V(b·c)`.

    Concretely: `L(b·x) · bᵏ · cᵏ = L(b·c · (c⁻¹·x)) · (b·c)ᵏ`.
-/
omit [Finite F] in
lemma action_identity (L : F →+ F) (k : ℕ) (b c x : F) (hc : c ≠ 0) :
    L (b * x) * b ^ k * c ^ k = L (b * c * (c⁻¹ * x)) * (b * c) ^ k := by
      simp +decide [ mul_assoc, mul_pow, hc ]

/-
═══════════════════════════════════════════
Main theorem: Proposition 2.1(a)
═══════════════════════════════════════════

**Proposition 2.1(a).** If `L` is additive and `P(x) = L(x)·xᵏ` is a bijection
    on the finite field `F`, then `L` is bijective, and `x ⊙ y = L(xy)·xᵏ` defines
    a weak quasifield whose associated translation plane satisfies hypothesis (NF).
-/
theorem proposition_2_1a (L : F →+ F) (k : ℕ) (hP : Function.Bijective (P L k)) :
    Function.Bijective L
    ∧ (∀ x, qfMul L k x 0 = 0)
    ∧ (∀ x, qfMul L k 0 x = 0)
    ∧ (∀ x y z, qfMul L k x (y + z) = qfMul L k x y + qfMul L k x z)
    ∧ (∀ a, a ≠ 0 → Function.Bijective (fun x => qfMul L k x a))
    ∧ (∀ a, a ≠ 0 → Function.Bijective (fun x => qfMul L k a x)) := by
      exact ⟨L_bijective L k hP.injective,
        fun x => qfMul_zero_right L k x,
        fun x => qfMul_zero_left L k x,
        fun x y z => qfMul_add_right L k x y z,
        fun a ha => qfMul_right_bijective L k hP.injective ha,
        fun a ha => qfMul_left_bijective L k hP.injective ha⟩

end DempwolffMueller