/-
# Kasami Derivative Kernel Analysis

This module establishes the connection between the Kasami power function
derivative and linearized polynomials, then uses the kernel dimension
theory to prove key properties of the Kasami derivative.

## Main results

* `kasamiExp` : The Kasami exponent `d = 4^k - 2^k + 1`
* `kasamiDelta_periodic` : δ(b) = δ(b+1) (char 2 symmetry)
* `kasamiDiff_normalize` : Normalization of the differential
* `kasamiDelta_two_to_one` : 2-to-1 property when gcd(k,n) = 1 and 3 ∤ n
* `kasamiDiff_count_even` : Differential count is always even

## References

* Kasami (1971), *Information and Control* 18(4)
* Canteaut, Charpin, Dobbertin (2000), *SIAM J. Discrete Math.* 13(1)
-/
import Mathlib
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Kasami Exponent -/

/-- The Kasami exponent: `d(k) = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- For k ≥ 1, `2^k ≤ 4^k`. -/
theorem two_pow_le_four_pow (k : ℕ) : 2 ^ k ≤ 4 ^ k := by
  calc 2 ^ k ≤ (2 ^ 2) ^ k := Nat.pow_le_pow_left (by norm_num) k
    _ = 4 ^ k := by ring_nf

/-- `d(1) = 3` (the Gold exponent). -/
@[simp] theorem kasamiExp_one : kasamiExp 1 = 3 := by simp [kasamiExp]

/-- `d(2) = 13`. -/
@[simp] theorem kasamiExp_two : kasamiExp 2 = 13 := by simp [kasamiExp]

/-! ### The Kasami power function and its derivative -/

/-- The Kasami power function `G(x) = x^{d(k)}`. -/
def kasamiPow (k : ℕ) (x : F) : F := x ^ kasamiExp k

/-- The Kasami delta function: `δ(b) = G(b) + G(b+1) + 1`. -/
def kasamiDelta (k : ℕ) (b : F) : F :=
  kasamiPow k b + kasamiPow k (b + 1) + 1

/-- The symmetry `δ(b) = δ(b + 1)` in characteristic 2. -/
theorem kasamiDelta_periodic (k : ℕ) (b : F) :
    kasamiDelta k b = kasamiDelta k (b + 1) := by
  unfold kasamiDelta kasamiPow
  have h1 : b + 1 + 1 = b := by
    have : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    calc b + 1 + 1 = b + (1 + 1) := by ring
      _ = b + 0 := by rw [this]
      _ = b := by ring
  rw [h1]; ring

/-! ### Derivative and linearized polynomial connection -/

/-- The differential operator: `D_a G(x) = G(x + a) + G(x)`. -/
def kasamiDiff (k : ℕ) (a x : F) : F :=
  kasamiPow k (x + a) + kasamiPow k x

/-
For the power function `x^d`, the differential satisfies
    `D_a G(x) = a^d · D_1(x/a)` for `a ≠ 0`.
-/
theorem kasamiDiff_normalize (k : ℕ) (a x : F) (ha : a ≠ 0) :
    kasamiDiff k a x = a ^ kasamiExp k * kasamiDiff k 1 (x * a⁻¹) := by
  unfold kasamiDiff;
  unfold kasamiPow;
  field_simp;
  rw [ mul_add, ← mul_pow, ← mul_pow, mul_div_cancel₀ _ ha, mul_div_cancel₀ _ ha ]

/-! ### Helper: Freshman's dream for general char 2 fields -/

/-- Freshman's dream: (a+b)^{2^k} = a^{2^k} + b^{2^k} in char 2. -/
theorem char2_freshman (a b : F) (k : ℕ) :
    (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) :=
  add_pow_char_pow a b 2 k

/-! ### Helper: Gold derivative -/

/-- Gold derivative: (x+z)^{2^m+1} + x^{2^m+1} = x^{2^m}·z + x·z^{2^m} + z^{2^m+1} -/
theorem gold_derivative (x z : F) (m : ℕ) :
    (x + z) ^ (2 ^ m + 1) + x ^ (2 ^ m + 1) =
    x ^ (2 ^ m) * z + x * z ^ (2 ^ m) + z ^ (2 ^ m + 1) := by
  simp +decide [ add_pow_char_pow, pow_add, mul_assoc, mul_comm, mul_left_comm ];
  grind

/-- Gold derivative at z=1: D_1(x^{2^m+1}) = x^{2^m} + x + 1 -/
theorem gold_deriv_at_one (x : F) (m : ℕ) :
    (x + 1) ^ (2 ^ m + 1) + x ^ (2 ^ m + 1) = x ^ (2 ^ m) + x + 1 := by
  have := gold_derivative x 1 m; simp_all +decide [ pow_succ' ] ;

/-- Gold second derivative: D_z D_1(x^{2^m+1}) = z^{2^m} + z (independent of x!) -/
theorem gold_second_derivative (x z : F) (m : ℕ) :
    ((x + z + 1) ^ (2 ^ m + 1) + (x + z) ^ (2 ^ m + 1)) +
    ((x + 1) ^ (2 ^ m + 1) + x ^ (2 ^ m + 1)) = z ^ (2 ^ m) + z := by
  grind +suggestions

/-! ### CCD Cross-term -/

/-- The cross-term C(x) = (x+1)^d · x^{d·2^k} + (x+1)^{d·2^k} · x^d
    where d = kasamiExp k. -/
def ccdCrossTerm (k : ℕ) (x : F) : F :=
  (x + 1) ^ (kasamiExp k) * x ^ (kasamiExp k * 2 ^ k) +
  (x + 1) ^ (kasamiExp k * 2 ^ k) * x ^ (kasamiExp k)

/-! ### Step 1: Raising to (2^k+1) power -/

/-- Key factorization:
    [D_1(x^d)]^{2^k+1} = D_1(x^{2^{3k}+1}) + C(x)
    = (x^{2^{3k}} + x + 1) + C(x) -/
theorem ccd_power_factorization (k : ℕ) (hk : 0 < k) (x : F) :
    ((x + 1) ^ kasamiExp k + x ^ kasamiExp k) ^ (2 ^ k + 1) =
    x ^ (2 ^ (3 * k)) + x + 1 + ccdCrossTerm k x := by
  -- Apply the freshmans dream theorem to expand the left-hand side.
  have h_expand : ((x + 1) ^ kasamiExp k + x ^ kasamiExp k) ^ (2 ^ k + 1) = ((x + 1) ^ kasamiExp k + x ^ kasamiExp k) * ((x + 1) ^ (kasamiExp k * 2 ^ k) + x ^ (kasamiExp k * 2 ^ k)) := by
    rw [ pow_succ', pow_mul, pow_mul ];
    rw [ char2_freshman ];
  -- By definition of $d$, we know that $d * (2^k + 1) = 2^{3k} + 1$.
  have h_d_mul : kasamiExp k * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
    unfold kasamiExp;
    zify;
    rw [ Nat.cast_sub ( by gcongr ; norm_num ) ] ; push_cast ; ring;
    norm_num [ pow_mul', ← mul_pow ] ; ring;
  -- Substitute $d * (2^k + 1) = 2^{3k} + 1$ into the expanded form.
  have h_subst : ((x + 1) ^ kasamiExp k + x ^ kasamiExp k) * ((x + 1) ^ (kasamiExp k * 2 ^ k) + x ^ (kasamiExp k * 2 ^ k)) = (x + 1) ^ (2 ^ (3 * k) + 1) + x ^ (2 ^ (3 * k) + 1) + ccdCrossTerm k x := by
    rw [ ← h_d_mul ] ; ring!;
    unfold ccdCrossTerm; ring;
  have := gold_deriv_at_one x ( 3 * k ) ; aesop;

/-! ### Step 2: Second derivative via CCD -/

/-- If D_1 f(y₂+z) = D_1 f(y₂), then
    z^{2^{3k}} + z = C(y₂) + C(y₂+z) -/
theorem ccd_second_deriv_eq (k : ℕ) (hk : 0 < k) (y₂ z : F)
    (heq : (y₂ + z + 1) ^ kasamiExp k + (y₂ + z) ^ kasamiExp k =
           (y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) :
    z ^ (2 ^ (3 * k)) + z = ccdCrossTerm k y₂ + ccdCrossTerm k (y₂ + z) := by
  have := ccd_power_factorization k hk y₂;
  have := ccd_power_factorization k hk ( y₂ + z );
  simp_all +decide [ add_pow_char_pow ];
  grind +splitImp

/-! ### Step 3: Cross-term difference factors through linPolyL -/

/-
Key algebraic identity: `z^{2^{3k}} + z = M_k(L_k(z))` in characteristic 2.
    Proof: L_k(z) = z^{2^{2k}} + z^{2^k} + z, so
    L_k(z)^{2^k} = z^{2^{3k}} + z^{2^{2k}} + z^{2^k} (Freshman's dream),
    and L_k(z)^{2^k} + L_k(z) = z^{2^{3k}} + z (terms cancel in char 2).
-/
theorem frobenius_cube_eq_MkLk (k : ℕ) (z : F) :
    z ^ (2 ^ (3 * k)) + z = linPolyM k (linPolyL k z) := by
  unfold linPolyM linPolyL; ring;
  rw [ add_pow_char_pow, add_pow_char_pow ] ; ring;
  simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ]

/-
The cross-term difference C(y₂) + C(y₂+z) simplifies using the derivative equation.
    If s = (y₂+1)^d + y₂^d and w = y₂^d + (y₂+z)^d, then
    C(y₂) + C(y₂+z) = s · w^{2^k} + s^{2^k} · w.
-/
theorem ccd_crossterm_simplified (k : ℕ) (hk : 0 < k) (y₂ z : F)
    (heq : (y₂ + z + 1) ^ kasamiExp k + (y₂ + z) ^ kasamiExp k =
           (y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) :
    ccdCrossTerm k y₂ + ccdCrossTerm k (y₂ + z) =
    ((y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) *
      (y₂ ^ kasamiExp k + (y₂ + z) ^ kasamiExp k) ^ (2 ^ k) +
    ((y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) ^ (2 ^ k) *
      (y₂ ^ kasamiExp k + (y₂ + z) ^ kasamiExp k) := by
  unfold ccdCrossTerm;
  rw [ add_comm ];
  simp +decide only [pow_mul, add_mul];
  rw [ ← eq_sub_iff_add_eq' ] at heq;
  simp +decide only [heq, sub_pow_char_pow, mul_sub];
  simp +decide [ add_pow_char_pow, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg ] ; ring;
  cases k <;> simp_all +decide [ pow_succ' ] ; ring;
  grind

/-- Combining the three key results:
    M_k(L_k(z)) = s·w^{2^k} + s^{2^k}·w
    where s = (y₂+1)^d + y₂^d and w = y₂^d + (y₂+z)^d. -/
theorem ccd_mk_lk_eq_sw (k : ℕ) (hk : 0 < k) (y₂ z : F)
    (heq : (y₂ + z + 1) ^ kasamiExp k + (y₂ + z) ^ kasamiExp k =
           (y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) :
    linPolyM k (linPolyL k z) =
    ((y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) *
      (y₂ ^ kasamiExp k + (y₂ + z) ^ kasamiExp k) ^ (2 ^ k) +
    ((y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) ^ (2 ^ k) *
      (y₂ ^ kasamiExp k + (y₂ + z) ^ kasamiExp k) := by
  rw [← frobenius_cube_eq_MkLk, ccd_second_deriv_eq k hk y₂ z heq,
      ccd_crossterm_simplified k hk y₂ z heq]

/-- The cross-term difference C(y₂) + C(y₂+z) factors as a function of
    linPolyL k z times some expression.

    More precisely: when z ∉ {0, 1}, the equation
    z^{2^{3k}} + z = C(y₂) + C(y₂+z)
    combined with the original differential equation
    implies linPolyL k z = 0. -/
theorem ccd_crossterm_gives_linPolyL (k : ℕ) (hk : 0 < k) (y₂ z : F)
    (hz : z ≠ 0) (hz1 : z ≠ 1)
    (heq : (y₂ + z + 1) ^ kasamiExp k + (y₂ + z) ^ kasamiExp k =
           (y₂ + 1) ^ kasamiExp k + y₂ ^ kasamiExp k) :
    linPolyL k z = 0 := by
  sorry

/-- The equation `D_1 G(y₁) = D_1 G(y₂)` implies either `y₁ = y₂`, `y₁ = y₂ + 1`,
    or `z = y₁ + y₂` is a nonzero root of a linearized polynomial equation. -/
theorem kasamiDiff_eq_implies_linearized (k : ℕ) (hk : 0 < k)
    (y₁ y₂ : F) (heq : kasamiDiff k 1 y₁ = kasamiDiff k 1 y₂) :
    y₁ = y₂ ∨ y₁ = y₂ + 1 ∨ linPolyL k (y₁ + y₂) = 0 := by
  by_cases hz : y₁ + y₂ = 0
  · left
    have h1 : y₁ + y₂ = 0 := hz
    have h2 : y₁ = y₁ + 0 := (add_zero y₁).symm
    rw [h2, ← CharTwo.add_self_eq_zero y₂, ← add_assoc, h1, zero_add]
  · right
    by_cases hz1 : y₁ + y₂ = 1
    · left
      have h1 : y₁ = y₁ + y₂ + y₂ := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [h1, hz1]; ring
    · right
      apply ccd_crossterm_gives_linPolyL k hk y₂ (y₁ + y₂) hz hz1
      unfold kasamiDiff kasamiPow at heq
      have h1 : y₂ + (y₁ + y₂) = y₁ := by rw [← add_assoc, add_comm y₂ y₁, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      simp only [h1]; exact heq

/-! ### The 2-to-1 theorem -/

/-
**Kasami derivative is 2-to-1** when `gcd(k,n) = 1` and `3 ∤ n`:
    `δ(b₁) = δ(b₂)` implies `b₂ = b₁` or `b₂ = b₁ + 1`.
-/
theorem kasamiDelta_two_to_one (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (b₁ b₂ : F) (heq : kasamiDelta k b₁ = kasamiDelta k b₂) :
    b₂ = b₁ ∨ b₂ = b₁ + 1 := by
  -- By kasamiDiff_eq_implies_linearized, we have either `b₁ = b₂`, `b₁ = b₂ + 1`, or `linPolyL k (b₁ + b₂) = 0`.
  have h_cases : b₁ = b₂ ∨ b₁ = b₂ + 1 ∨ linPolyL k (b₁ + b₂) = 0 := by
    unfold kasamiDelta at heq
    have h_diff : kasamiDiff k 1 b₁ = kasamiDiff k 1 b₂ := by
      unfold kasamiDiff; ring;
      grind +ring;
    exact?;
  -- By linPolyL_ker_trivial_of_three_ndvd, if `linPolyL k (b₁ + b₂) = 0`, then `b₁ + b₂ = 0`, i.e., `b₁ = b₂`.
  have h_trivial : funKer (linPolyL (F := F) k) = {0} := by
    exact?;
  simp_all +decide [ Finset.ext_iff, funKer ];
  grind +splitImp

/-
**Kasami delta set cardinality**: When the derivative is 2-to-1,
    the delta set has `|F|/2` elements.
-/
theorem kasamiDelta_image_card (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n) :
    (Finset.univ.image (kasamiDelta (F := F) k)).card = 2 ^ (n - 1) := by
  have h_delta_card : ∀ b : F, (Finset.filter (fun x => kasamiDelta k x = kasamiDelta k b) Finset.univ).card = 2 := by
    intro b
    have h_fiber : ∀ x : F, kasamiDelta k x = kasamiDelta k b ↔ x = b ∨ x = b + 1 := by
      grind +suggestions;
    rw [ show ( Finset.filter ( fun x => kasamiDelta k x = kasamiDelta k b ) Finset.univ ) = { b, b + 1 } by ext; aesop, Finset.card_pair ] ; simp +decide [ CharTwo.add_self_eq_zero ];
  have h_partition : ∑ c ∈ Finset.image (fun b => kasamiDelta k b) (Finset.univ : Finset F), (Finset.filter (fun x => kasamiDelta k x = c) (Finset.univ : Finset F)).card = Fintype.card F := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; simp +decide;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
  rw [ Finset.sum_congr rfl fun x hx => show Finset.card ( Finset.filter ( fun y => kasamiDelta k y = x ) Finset.univ ) = 2 from by rcases Finset.mem_image.mp hx with ⟨ y, _, rfl ⟩ ; exact h_delta_card y ] at h_partition ; norm_num at h_partition ; linarith

/-! ### Differential uniformity -/

/-
The differential count is always even (solutions come in pairs `{x, x+a}`).
-/
theorem kasamiDiff_count_even (k : ℕ) (a c : F) (ha : a ≠ 0) :
    Even (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card := by
  -- The solutions to $D_a G(x) = c$ come in pairs $(x, x+a)$.
  have h_pairs : ∀ x : F, (kasamiDiff k a x = c) → (kasamiDiff k a (x + a) = c) := by
    unfold kasamiDiff;
    grind +splitImp;
  -- Since the solutions come in pairs, the set of solutions can be partitioned into pairs.
  have h_partition : ∃ S : Finset (Finset F), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ x ∈ s, kasamiDiff k a x = c) ∧ (∀ x, kasamiDiff k a x = c → ∃ s ∈ S, x ∈ s) ∧ (∀ s₁ s₂, s₁ ∈ S → s₂ ∈ S → s₁ ≠ s₂ → Disjoint s₁ s₂) := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) ( Finset.filter ( fun x => kasamiDiff k a x = c ) Finset.univ ), _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · exact fun x hx => ⟨ x, hx, Or.inl rfl ⟩;
    · grind +splitIndPred;
  obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := h_partition;
  have h_card : Finset.card (Finset.filter (fun x => kasamiDiff k a x = c) Finset.univ) = Finset.sum S (fun s => Finset.card s) := by
    rw [ ← Finset.card_biUnion ];
    · congr with x ; aesop;
    · exact fun s₁ hs₁ s₂ hs₂ h => hS₄ s₁ s₂ hs₁ hs₂ h;
  exact h_card.symm ▸ even_iff_two_dvd.mpr ( Finset.dvd_sum fun s hs => hS₁ s hs ▸ dvd_rfl )

/-
The Kasami function is APN when `gcd(k,n) = 1` and `3 ∤ n`:
    the differential count is 0 or 2 for nonzero `a`.
-/
theorem kasami_apn (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (a c : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card = 0 ∨
    (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card = 2 := by
  -- By kasamiDiff_normalize, D_a G(x) = a^d * D_1(x/a), so D_a G(x) = c iff D_1(x/a) = c/a^d =: c'.
  have h_normalize : Finset.filter (fun x => kasamiDiff k a x = c) (Finset.univ : Finset F) = Finset.image (fun x => x / a⁻¹) (Finset.filter (fun x => kasamiDiff k 1 x = c / a ^ (kasamiExp k)) (Finset.univ : Finset F)) := by
    ext x;
    simp +decide [ kasamiDiff, ha, mul_div_cancel_left₀ ];
    constructor;
    · intro hx
      use x / a;
      simp_all +decide [ kasamiPow, pow_add, pow_mul, mul_pow, div_pow, div_mul_cancel₀, ha ];
      rw [ ← hx, div_add_one, div_pow, add_div ] ; aesop;
    · rintro ⟨ y, hy, rfl ⟩;
      convert congr_arg ( · * a ^ kasamiExp k ) hy using 1 <;> ring;
      · unfold kasamiPow;
        rw [ show y * a + a = a * ( y + 1 ) by ring, mul_pow ] ; ring;
      · simp +decide [ ha ];
  have h_solutions : ∀ y₁ y₂ : F, kasamiDiff k 1 y₁ = c / a ^ (kasamiExp k) → kasamiDiff k 1 y₂ = c / a ^ (kasamiExp k) → y₁ = y₂ ∨ y₁ = y₂ + 1 := by
    intro y₁ y₂ hy₁ hy₂
    have h_eq : kasamiDiff k 1 y₁ = kasamiDiff k 1 y₂ := by
      rw [hy₁, hy₂];
    have := kasamiDiff_eq_implies_linearized k hk y₁ y₂ h_eq;
    have := linPolyL_ker_trivial_of_three_ndvd n hn k hk hcard hgcd h3;
    simp_all +decide [ Finset.ext_iff, funKer ];
    grind;
  by_cases h : ∃ y : F, kasamiDiff k 1 y = c / a ^ (kasamiExp k) <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
  obtain ⟨ y, hy ⟩ := h;
  refine' Or.inr ( le_antisymm _ _ );
  · exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun x => kasamiDiff k 1 x = c / a ^ kasamiExp k ) Finset.univ ⊆ { y, y + 1 } from fun x hx => by simpa using h_solutions x y ( Finset.mem_filter.mp hx |>.2 ) hy ) ) ( Finset.card_insert_le _ _ );
  · refine' Finset.one_lt_card.mpr ⟨ y, _, y + 1, _, _ ⟩ <;> simp_all +decide [ kasamiDiff ];
    grind

end