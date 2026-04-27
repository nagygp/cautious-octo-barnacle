import Mathlib

/-!
# Boolean Function Cryptography: Definitions and Basic Properties

This file defines the basic objects needed for the theory of Almost Perfect Nonlinear (APN)
and Almost Bent (AB) functions over GF(2)^n.
-/

open Finset BigOperators

set_option maxHeartbeats 800000

/-- The vector space GF(2)^n -/
abbrev V (n : ℕ) := Fin n → ZMod 2

/-- The standard dot product over GF(2) -/
def dot {n : ℕ} (a x : V n) : ZMod 2 := ∑ i : Fin n, a i * x i

/-- The character χ_a(x) = (-1)^{⟨a,x⟩}, taking values in {±1} ⊂ ℤ -/
def chi {n : ℕ} (a x : V n) : ℤ := if dot a x = 0 then 1 else -1

/-- The Walsh-Hadamard coefficient W_f(a,b) = ∑_x χ_a(x) · χ_b(f(x)) -/
def walsh {n : ℕ} (f : V n → V n) (a b : V n) : ℤ :=
  ∑ x : V n, chi a x * chi b (f x)

/-- The derivative character sum D_f(d,b) = ∑_x χ_b(f(x+d) + f(x)) -/
def D {n : ℕ} (f : V n → V n) (d b : V n) : ℤ :=
  ∑ x : V n, chi b (f (x + d) + f x)

/-- The differential count δ_f(a,b) = #{x : f(x+a) + f(x) = b} -/
noncomputable def deltaCount {n : ℕ} (f : V n → V n) (a b : V n) : ℕ :=
  (Finset.univ.filter fun x : V n => f (x + a) + f x = b).card

/-- A function f is Almost Perfect Nonlinear if δ_f(a,b) ≤ 2 for all a ≠ 0 and b. -/
def IsAPN {n : ℕ} (f : V n → V n) : Prop :=
  ∀ a : V n, a ≠ 0 → ∀ b : V n, deltaCount f a b ≤ 2

/-- A function f is Almost Bent if W_f(a,b)² ∈ {0, 2^{n+1}} for all a and b ≠ 0. -/
def IsAB {n : ℕ} (f : V n → V n) : Prop :=
  ∀ a b : V n, b ≠ 0 → (walsh f a b) ^ 2 = 0 ∨ (walsh f a b) ^ 2 = (2 : ℤ) ^ (n + 1)

-- ============================================================================
-- Basic properties of V n
-- ============================================================================

@[simp] lemma V_add_self {n : ℕ} (a : V n) : a + a = 0 := by
  ext i; simp [CharTwo.add_self_eq_zero]

@[simp] lemma V_neg_eq {n : ℕ} (a : V n) : -a = a := by
  ext i; simp [CharTwo.neg_eq]

lemma V_sub_eq_add {n : ℕ} (a b : V n) : a - b = a + b := by
  ext i; simp [sub_eq_add_neg, CharTwo.neg_eq]

lemma card_V (n : ℕ) : Fintype.card (V n) = 2 ^ n := by
  simp [Fintype.card_fun, ZMod.card]

-- ============================================================================
-- Properties of dot
-- ============================================================================

@[simp] lemma dot_zero_left {n : ℕ} (x : V n) : dot 0 x = 0 := by
  simp [dot]

@[simp] lemma dot_zero_right {n : ℕ} (a : V n) : dot a 0 = 0 := by
  simp [dot]

lemma dot_add_left {n : ℕ} (a b x : V n) : dot (a + b) x = dot a x + dot b x := by
  simp [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {n : ℕ} (a x y : V n) : dot a (x + y) = dot a x + dot a y := by
  simp [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

-- ============================================================================
-- Properties of chi
-- ============================================================================

@[simp] lemma chi_zero_left {n : ℕ} (x : V n) : chi 0 x = 1 := by
  simp [chi]

@[simp] lemma chi_zero_right {n : ℕ} (a : V n) : chi a 0 = 1 := by
  simp [chi]

lemma chi_values {n : ℕ} (a x : V n) : chi a x = 1 ∨ chi a x = -1 := by
  simp [chi]; tauto

lemma chi_sq {n : ℕ} (a x : V n) : chi a x ^ 2 = 1 := by
  rcases chi_values a x with h | h <;> simp [h]

lemma chi_mul_self {n : ℕ} (a x : V n) : chi a x * chi a x = 1 := by
  rcases chi_values a x with h | h <;> simp [h]

lemma chi_ne_zero {n : ℕ} (a x : V n) : chi a x ≠ 0 := by
  rcases chi_values a x with h | h <;> simp [h]

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- Multiplicativity of chi: χ_a(x) · χ_b(x) = χ_{a+b}(x) -/
lemma chi_mul_chi {n : ℕ} (a b x : V n) : chi a x * chi b x = chi (a + b) x := by
  simp only [chi, dot_add_left]
  rcases zmod2_cases (dot a x) with ha | ha <;>
  rcases zmod2_cases (dot b x) with hb | hb <;>
  simp [ha, hb] <;> decide

/-- χ_a(x) · χ_a(y) = χ_a(x+y) -/
lemma chi_mul_chi' {n : ℕ} (a x y : V n) : chi a x * chi a y = chi a (x + y) := by
  simp only [chi, dot_add_right]
  rcases zmod2_cases (dot a x) with ha | ha <;>
  rcases zmod2_cases (dot a y) with hb | hb <;>
  simp [ha, hb] <;> decide

/-
============================================================================
Character orthogonality
============================================================================

The fundamental character sum: ∑_x χ_c(x) = 2^n if c = 0, else 0
-/
lemma sum_chi {n : ℕ} (c : V n) :
    ∑ x : V n, chi c x = if c = 0 then (2 : ℤ) ^ n else 0 := by
  by_cases hc : c = 0 <;> simp +decide [ hc ];
  -- Since $c \neq 0$, there exists some $i$ such that $c_i = 1$.
  obtain ⟨i, hi⟩ : ∃ i : Fin n, c i = 1 := by
    exact not_forall_not.mp fun h => hc <| funext fun i => Or.resolve_right ( Fin.exists_fin_two.mp <| by aesop ) <| h i;
  -- By the involution argument, we can pair each $x$ with $x + e_i$.
  have h_pair : ∀ x : V n, chi c (x + Pi.single i 1) = -chi c x := by
    intro x; unfold chi; simp +decide [ *, dot_add_right ] ;
    unfold dot; simp +decide [ *, Finset.sum_apply, Pi.single_apply ] ;
    cases Fin.exists_fin_two.mp ⟨ ∑ i, c i * x i, rfl ⟩ <;> simp_all +decide;
  -- By pairing each $x$ with $x + e_i$, we can rewrite the sum as $\sum_{x} \chi_c(x) = \sum_{x} \chi_c(x + e_i)$.
  have h_sum_pair : ∑ x : V n, chi c x = ∑ x : V n, chi c (x + Pi.single i 1) := by
    rw [ ← Equiv.sum_comp ( Equiv.addRight ( Pi.single i 1 ) ) ] ; aesop;
  norm_num [ h_pair ] at h_sum_pair ; linarith

/-
Character orthogonality: ∑_x χ_a(x) · χ_b(x) = 2^n if a = b, else 0
-/
lemma chi_orthogonality {n : ℕ} (a b : V n) :
    ∑ x : V n, chi a x * chi b x = if a = b then (2 : ℤ) ^ n else 0 := by
  convert sum_chi ( a + b ) using 1;
  · exact Finset.sum_congr rfl fun _ _ => chi_mul_chi _ _ _;
  · split_ifs <;> simp_all +decide [ ← eq_sub_iff_add_eq' ]

/-
============================================================================
Properties of deltaCount
============================================================================

δ_f(0, b) = 2^n if b = 0, else 0
-/
lemma deltaCount_zero_left {n : ℕ} (f : V n → V n) (b : V n) :
    deltaCount f 0 b = if b = 0 then 2 ^ n else 0 := by
  split_ifs <;> simp_all +decide [ deltaCount ];
  aesop

/-
∑_b δ_f(a, b) = 2^n for all a
-/
lemma sum_deltaCount {n : ℕ} (f : V n → V n) (a : V n) :
    ∑ b : V n, (deltaCount f a b : ℤ) = (2 : ℤ) ^ n := by
  norm_cast;
  unfold deltaCount;
  simp +decide only [card_filter];
  rw [ Finset.sum_comm ] ; aesop

/-
Helper: a Finset with a fixed-point-free involution has even cardinality.
-/
lemma even_card_of_fpf_invol {α : Type*} [DecidableEq α] (s : Finset α) (σ : α → α)
    (hσ_maps : ∀ x ∈ s, σ x ∈ s)
    (hσ_inv : ∀ x ∈ s, σ (σ x) = x)
    (hσ_fpf : ∀ x ∈ s, σ x ≠ x) : Even s.card := by
  by_contra h_odd;
  have h_partition : ∃ t : Finset (Finset α), (∀ u ∈ t, u.card = 2 ∧ ∀ x ∈ u, x ∈ s) ∧ (∀ u ∈ t, ∀ v ∈ t, u ≠ v → Disjoint u v) ∧ s = t.biUnion id := by
    refine' ⟨ Finset.image ( fun x => { x, σ x } ) s, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · exact fun x hx => Finset.card_pair ( Ne.symm ( hσ_fpf x hx ) );
    · grind;
    · ext x; aesop;
  obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := h_partition;
  rw [ ht₃, Finset.card_biUnion ] at h_odd <;> aesop

/-- δ_f(a, b) is always even for a ≠ 0. -/
lemma deltaCount_even {n : ℕ} (f : V n → V n) (a : V n) (ha : a ≠ 0) (b : V n) :
    Even (deltaCount f a b) := by
  unfold deltaCount
  apply even_card_of_fpf_invol _ (· + a)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have h1 : x + a + a = x := by rw [add_assoc, V_add_self, add_zero]
    rw [h1, add_comm]; exact hx
  · intro x _
    rw [add_assoc, V_add_self, add_zero]
  · intro x _ h
    apply ha
    calc a = 0 + a := by rw [zero_add]
      _ = (x + x) + a := by rw [V_add_self]
      _ = x + (x + a) := by rw [add_assoc]
      _ = x + x := by rw [h]
      _ = 0 := V_add_self x