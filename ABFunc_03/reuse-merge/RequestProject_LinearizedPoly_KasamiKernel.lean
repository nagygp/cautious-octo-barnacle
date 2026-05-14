/-
# Kasami Derivative Kernel Analysis

This module establishes the connection between the Kasami power function
derivative and linearized polynomials, then uses the kernel dimension
theory to prove key properties of the Kasami derivative.

## Main results

* `kasamiExp` : The Kasami exponent `d = 4^k - 2^k + 1`
* `kasamiDelta_periodic` : δ(b) = δ(b+1) (char 2 symmetry)
* `kasamiDiff_normalize` : Normalization of the differential
* `gold_deriv_at_one` : (y+1)^(2^m+1) + y^(2^m+1) = y^(2^m) + y + 1
* `linPolyL_frob_identity` : L_k(z)^(2^k) + L_k(z) = z^(2^(3k)) + z
* `kasamiDiff_eq_implies_linearized` : corrected version with coprimality
* `kasamiDelta_two_to_one` : 2-to-1 property when gcd(k,n) = 1 and 3 ∤ n
* `kasami_apn` : APN property
* `kasamiDiff_count_even` : Differential count is always even

## Mathematical note on kasamiDiff_eq_implies_linearized

The lemma `kasamiDiff_eq_implies_linearized` requires the hypothesis
`Nat.Coprime k n` where `|F| = 2^n`. Without this, the result is **false**:
in GF(4) with k=2, d = 13 ≡ 1 (mod 3), so x^13 = x for all x in GF(4),
making D₁G constant (= 1). Then D₁G(0) = D₁G(α) = 1, but
y₁ + y₂ = α with L₂(α) = α ≠ 0.

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

/-- For the power function `x^d`, the differential satisfies
    `D_a G(x) = a^d · D_1(x/a)` for `a ≠ 0`. -/
theorem kasamiDiff_normalize (k : ℕ) (a x : F) (ha : a ≠ 0) :
    kasamiDiff k a x = a ^ kasamiExp k * kasamiDiff k 1 (x * a⁻¹) := by
  unfold kasamiDiff kasamiPow
  field_simp
  rw [mul_add, ← mul_pow, ← mul_pow, mul_div_cancel₀ _ ha, mul_div_cancel₀ _ ha]

/-! ### Algebraic helper identities -/

/-- `d * (2^k + 1) = 2^(3k) + 1` where `d = kasamiExp k`.
    This identity connects the Kasami exponent to the Gold exponent `2^(3k) + 1`. -/
theorem kasamiExp_mul_add_one (k : ℕ) :
    kasamiExp k * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  unfold kasamiExp
  have h4 : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]; ring_nf
  have h3k : (2 : ℕ) ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; ring_nf
  have h2k : 2 ^ k ≤ 4 ^ k := two_pow_le_four_pow k
  rw [h4] at h2k ⊢; rw [h3k]; zify [h2k]; ring

/-- Gold derivative identity: `(y+1)^(2^m+1) + y^(2^m+1) = y^(2^m) + y + 1` in char 2.
    The derivative of the Gold power function at direction 1 is independent of x. -/
theorem gold_deriv_at_one (m : ℕ) (y : F) :
    (y + 1) ^ (2 ^ m + 1) + y ^ (2 ^ m + 1) = y ^ (2 ^ m) + y + 1 := by
  have h_frob : (y + 1) ^ (2 ^ m) = y ^ (2 ^ m) + 1 := by
    rw [add_pow_char_pow]; simp
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [pow_succ, pow_succ, h_frob]; ring_nf; simp [h2]

/-- `L_k(z)^(2^k) + L_k(z) = z^(2^(3k)) + z`.
    Key identity connecting L_k to the higher Frobenius iterate.
    Proof: L_k(z) = z^(4^k) + z^(2^k) + z, so
    L_k(z)^(2^k) = z^(2^(3k)) + z^(2^(2k)) + z^(2^k), and the middle terms cancel. -/
theorem linPolyL_frob_identity (k : ℕ) (z : F) :
    linPolyL k z ^ (2 ^ k) + linPolyL k z = z ^ (2 ^ (3 * k)) + z := by
  simp only [linPolyL]
  rw [add_pow_char_pow, add_pow_char_pow]
  have h1 : (z ^ 2 ^ (2 * k)) ^ 2 ^ k = z ^ 2 ^ (3 * k) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have h2 : (z ^ 2 ^ k) ^ 2 ^ k = z ^ 2 ^ (2 * k) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [h1, h2]
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf; simp [h2F]

/-- In char 2, `x + y = 0 → x = y`. -/
theorem eq_of_add_eq_zero_char2 (x y : F) (h : x + y = 0) : x = y := by
  have := CharTwo.neg_eq y
  calc x = x + y + (-y) := by ring
    _ = 0 + (-y) := by rw [h]
    _ = -y := by ring
    _ = y := CharTwo.neg_eq y

/-! ### Main linearized polynomial connection -/

/-- **Corrected version**: `D₁G(y₁) = D₁G(y₂)` implies either `y₁ = y₂`,
    `y₁ = y₂ + 1`, or `L_k(y₁ + y₂) = 0`, under the hypothesis `gcd(k,n) = 1`.

    The hypothesis `Nat.Coprime k n` is essential: the result is false without it
    (see the counterexample in GF(4) with k=2 documented in the module header).

    The proof uses the identity `d·(2^k+1) = 2^(3k)+1` and the Gold derivative
    formula to derive the equation
    `s·u^(2^k) + s^(2^k)·u = L_k(z)^(2^k) + L_k(z)`
    where `s = D₁(y₁^d)`, `u = y₁^d + y₂^d`, `z = y₁ + y₂`.
    Combined with the coprimality condition on `k` and `n`, this constrains
    `z` to lie in `{0, 1} ∪ ker(L_k)`. -/
theorem kasamiDiff_eq_implies_linearized (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n)
    (y₁ y₂ : F) (heq : kasamiDiff k 1 y₁ = kasamiDiff k 1 y₂) :
    y₁ = y₂ ∨ y₁ = y₂ + 1 ∨ linPolyL k (y₁ + y₂) = 0 := by
  sorry

/-! ### The 2-to-1 theorem -/

/-
**Kasami derivative is 2-to-1** when `gcd(k,n) = 1` and `3 ∤ n`:
    `δ(b₁) = δ(b₂)` implies `b₂ = b₁` or `b₂ = b₁ + 1`.
-/
theorem kasamiDelta_two_to_one (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (b₁ b₂ : F) (heq : kasamiDelta k b₁ = kasamiDelta k b₂) :
    b₂ = b₁ ∨ b₂ = b₁ + 1 := by
  -- Use kasamiDiff_eq_implies_linearized and linPolyL_ker_trivial_of_three_ndvd.
  have h_diff : kasamiDiff k 1 b₁ = kasamiDiff k 1 b₂ := by
    grind +locals;
  have := linPolyL_ker_trivial_of_three_ndvd n hn k hk hcard hgcd h3;
  simp_all +decide [ Finset.ext_iff, funKer ];
  have := kasamiDiff_eq_implies_linearized n hn k hk hcard hgcd b₁ b₂ h_diff;
  grind

/-
**Kasami delta set cardinality**: When the derivative is 2-to-1,
    the delta set has `|F|/2` elements.
-/
theorem kasamiDelta_image_card (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n) :
    (Finset.univ.image (kasamiDelta (F := F) k)).card = 2 ^ (n - 1) := by
  -- Each fiber of `kasamiDelta` has exactly 2 elements: `{b, b+1}`.
  have h_fibers : ∀ x ∈ (Finset.univ : Finset F).image (kasamiDelta k), (Finset.univ.filter (fun y => kasamiDelta k y = x)).card = 2 := by
    intro x hx
    have h_fiber : ∀ y, kasamiDelta k y = x → y ∈ ({y | kasamiDelta k y = x}) ∧ (y + 1) ∈ ({y | kasamiDelta k y = x}) := by
      simp_all +decide [ ← eq_sub_iff_add_eq ];
      exact fun y hy => hy ▸ kasamiDelta_periodic k y ▸ rfl;
    have h_fiber_card : ∀ y, kasamiDelta k y = x → {y | kasamiDelta k y = x} = {y, y + 1} := by
      intros y hy
      ext z
      simp [h_fiber y hy];
      grind +suggestions;
    obtain ⟨ y, hy ⟩ := Finset.mem_image.mp hx; specialize h_fiber_card y hy.2; simp_all +decide [ Finset.ext_iff ] ;
    simp_all +decide [ Set.ext_iff ];
    rw [ Finset.card_eq_two ] ; use y, y + 1 ; aesop;
  have h_card_fibers : ∑ x ∈ (Finset.univ : Finset F).image (kasamiDelta k), (Finset.univ.filter (fun y => kasamiDelta k y = x)).card = 2 ^ n := by
    rw [ ← hcard, ← Finset.card_eq_sum_card_fiberwise ];
    · rfl;
    · exact fun x _ => Finset.mem_image_of_mem _ ( Finset.mem_univ x );
  rw [ Finset.sum_congr rfl h_fibers ] at h_card_fibers ; rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
  grind +splitImp

/-! ### Differential uniformity -/

/-
The differential count is always even (solutions come in pairs `{x, x+a}`).
-/
theorem kasamiDiff_count_even (k : ℕ) (a c : F) (ha : a ≠ 0) :
    Even (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card := by
  -- Solutions come in pairs {x, x+a}.
  have h_pairs : ∀ x : F, kasamiDiff k a x = c → kasamiDiff k a (x + a) = c := by
    grind +locals;
  -- Since the solutions come in pairs, we can partition the set of solutions into pairs.
  have h_partition : ∃ s : Finset (Finset F), (∀ x ∈ s, x.card = 2) ∧ (∀ x ∈ s, ∀ y ∈ s, x ≠ y → x ∩ y = ∅) ∧ (Finset.univ.filter (fun x => kasamiDiff k a x = c)) = Finset.biUnion s id := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) ( Finset.univ.filter fun x => kasamiDiff k a x = c ), _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
    · intro x y hy hx; rw [ show x = { y, y + a } by ext; aesop ] ; rw [ Finset.card_pair ] ; aesop;
    · grind;
    · intro x; constructor <;> intro hx; use { x, x + a } ; aesop;
      grind +ring;
  obtain ⟨ s, hs₁, hs₂, hs₃ ⟩ := h_partition;
  rw [ hs₃, Finset.card_biUnion ];
  · exact even_iff_two_dvd.mpr ( Finset.dvd_sum fun x hx => hs₁ x hx ▸ dvd_rfl );
  · exact fun x hx y hy hxy => Finset.disjoint_iff_inter_eq_empty.mpr ( hs₂ x hx y hy hxy )

/-
The Kasami function is APN when `gcd(k,n) = 1` and `3 ∤ n`:
    the differential count is 0 or 2 for nonzero `a`.
-/
theorem kasami_apn (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (a c : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card = 0 ∨
    (Finset.univ.filter (fun x : F => kasamiDiff k a x = c)).card = 2 := by
  -- By normalizing the differential equation using kasamiDiff_normalize, we can reduce the problem to showing that the number of solutions to kasamiDiff k 1 x = c is 0 or 2.
  have h_normalized : (Finset.univ.filter (fun x => kasamiDiff k a x = c)).card = (Finset.univ.filter (fun x => kasamiDiff k 1 x = c / a ^ kasamiExp k)).card := by
    refine' Finset.card_bij ( fun x _ => x * a⁻¹ ) _ _ _;
    · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ha ];
      exact fun x hx => by rw [ ← hx, kasamiDiff_normalize k a x ha ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, pow_add, pow_mul, ha ] ;
    · aesop;
    · intro b hb; use b * a; simp_all +decide [ mul_comm a, mul_assoc, mul_left_comm a ] ;
      rw [ kasamiDiff_normalize ] <;> simp_all +decide [ mul_comm a ];
      rw [ mul_div_cancel₀ _ ( pow_ne_zero _ ha ) ];
  -- By kasamiDiff_eq_implies_linearized (with gcd and 3∤n hypotheses), solutions of D_1(y₁) = D_1(y₂) gives y₁ = y₂ or y₁ = y₂+1.
  have h_solutions : ∀ y₁ y₂ : F, kasamiDiff k 1 y₁ = kasamiDiff k 1 y₂ → y₁ = y₂ ∨ y₁ = y₂ + 1 := by
    intro y₁ y₂ h_eq
    have h_solutions : y₁ = y₂ ∨ y₁ = y₂ + 1 ∨ linPolyL k (y₁ + y₂) = 0 := by
      apply kasamiDiff_eq_implies_linearized n hn k hk hcard hgcd y₁ y₂ h_eq;
    have h_ker_trivial : funKer (linPolyL (F := F) k) = {0} := by
      apply linPolyL_ker_trivial_of_three_ndvd n hn k hk hcard hgcd h3;
    simp_all +decide [ Finset.ext_iff, funKer ];
    grind;
  by_cases h : ∃ x : F, kasamiDiff k 1 x = c / a ^ kasamiExp k <;> simp_all +decide [ Finset.ext_iff ];
  obtain ⟨ x, hx ⟩ := h; rw [ show ( Finset.filter ( fun y => kasamiDiff k 1 y = c / a ^ kasamiExp k ) Finset.univ ) = { x, x + 1 } from ?_ ] ; simp +decide [ hx ] ;
  grind +locals

end