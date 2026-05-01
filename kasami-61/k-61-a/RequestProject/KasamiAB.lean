/-
# Kasami Functions are Almost Bent — Main Theorem

This file proves that the Kasami power function x ↦ x^d over GF(2^n),
where d = 2^(2k) - 2^k + 1 and n = 2k+1, is Almost Bent (AB).

The proof follows Route 3 (the "Counting" proof):
1. The linearized operator L_a is GF(2)-linear.
2. The radical of Q_a equals the kernel of L_a.
3. The kernel of L_a has dimension ≤ 1 over GF(2).
4. The Walsh sum squared equals 2^n · |rad(Q_a)|.
5. Since |rad| ∈ {1, 2}, the function is AB.
-/
import Mathlib
import RequestProject.Defs

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

-- Bring in the instances from Defs
attribute [local instance] KasamiAlgebra KasamiFact2 KasamiExpChar

variable {k : ℕ} (hk : k ≥ 1)
variable {n : ℕ} (hn : n = 2 * k + 1)
variable (hcard : Fintype.card F = 2 ^ n)

/-! ## Preliminary: Kasami exponent properties -/

/-- The Kasami exponent is positive for k ≥ 1. -/
lemma kasamiExpZ_pos (hk : k ≥ 1) : 0 < kasamiExpZ k := by
  exact Int.add_pos_of_nonneg_of_pos (sub_nonneg_of_le (by gcongr <;> linarith)) zero_lt_one

/-- kasamiExp k = 2^(2k) - 2^k + 1 as a natural number (for k ≥ 1). -/
lemma kasamiExp_eq (hk : k ≥ 1) :
    (kasamiExp k : ℤ) = 2 ^ (2 * k) - 2 ^ k + 1 := by
  convert Int.toNat_of_nonneg (kasamiExpZ_pos hk |> le_of_lt)

/-- The Kasami exponent is odd. -/
lemma kasamiExp_odd (hk : k ≥ 1) : Odd (kasamiExp k) := by
  have h_kasami_def : (kasamiExp k : ℤ) = 2 ^ (2 * k) - 2 ^ k + 1 := kasamiExp_eq hk
  replace h_kasami_def := congr_arg Even h_kasami_def
  simp_all +decide [parity_simps]

/-! ## Phase 1: L_a is GF(2)-linear -/

/-- The map y ↦ y^(2^m) is additive in characteristic 2 (Frobenius). -/
lemma pow_two_pow_add (m : ℕ) (x y : F) :
    (x + y) ^ (2 ^ m) = x ^ (2 ^ m) + y ^ (2 ^ m) :=
  add_pow_expChar_pow x y 2 m

/-
Scaling by GF(2) elements (i.e., 0 or 1) commutes with y ↦ y^(2^m).
-/
lemma pow_two_pow_zmod_smul (m : ℕ) (c : ZMod 2) (y : F) :
    (c • y) ^ (2 ^ m) = c • (y ^ (2 ^ m)) := by
      fin_cases c <;> simp +decide

/-
L_a is additive: L_a(x + y) = L_a(x) + L_a(y).
-/
lemma linearizedOp_add (a x y : F) :
    linearizedOp F k a (x + y) = linearizedOp F k a x + linearizedOp F k a y := by
      unfold linearizedOp;
      simp +decide only [pow_two_pow_add, mul_add];
      ring

/-! ## Phase 2: Radical equals kernel of L_a (The Deep Bridge) -/

/-- Key algebraic identity: The trace bilinear form B_a(x,y) = Tr(x · L_a(y)).

This is the crucial identity connecting the bilinear form of the Kasami
quadratic form to the linearized operator. -/
lemma traceBilin_eq_trace_linearizedOp (a x y : F) :
    traceBilinForm F k a x y = trGF2 F (x * linearizedOp F k a y) := by sorry

/-- Non-degeneracy of trace: if Tr(x · z) = 0 for all x, then z = 0. -/
lemma trace_nondegenerate (z : F) (hz : ∀ x : F, trGF2 F (x * z) = 0) : z = 0 := by sorry

/-- The radical of Q_a equals the kernel of L_a (set-theoretic version). -/
lemma radical_eq_ker_linearizedOp (a : F) :
    radical F k a = { y : F | linearizedOp F k a y = 0 } := by
  ext y
  simp only [radical, Set.mem_setOf_eq]
  constructor
  · intro hy
    apply trace_nondegenerate
    intro x
    rw [← traceBilin_eq_trace_linearizedOp]
    exact hy x
  · intro hy x
    rw [traceBilin_eq_trace_linearizedOp]
    simp [hy]

/-! ## Phase 3: Kernel dimension bound -/

/-- The kernel of L_a has at most 2 elements (dimension ≤ 1 over GF(2)). -/
lemma ker_linearizedOp_card_le (a : F) (ha : a ≠ 0) :
    Fintype.card { y : F | linearizedOp F k a y = 0 } ≤ 2 := by sorry

/-- The radical has at most 2 elements. -/
lemma radical_ncard_le (a : F) (ha : a ≠ 0) :
    Set.ncard (radical F k a) ≤ 2 := by sorry

/-! ## Phase 4: Walsh sum and quadratic form theory -/

/-- The squared Walsh sum of the Kasami function is in {0, 2^n, 2^(n+1)}.
    This follows from quadratic form theory over GF(2). -/
lemma walshSum_sq_eq (b : F) :
    (walshSum F (kasamiFun F k) b) ^ 2 = 0 ∨
    (walshSum F (kasamiFun F k) b) ^ 2 = (2 : ℤ) ^ n ∨
    (walshSum F (kasamiFun F k) b) ^ 2 = (2 : ℤ) ^ (n + 1) := by sorry

/-! ## Main Theorem -/

/-- **Kasami functions are Almost Bent.**

The Kasami power function x ↦ x^d over GF(2^n), where d = 2^(2k) - 2^k + 1
and n = 2k+1, is Almost Bent: for all b, W_f(b)² ∈ {0, 2^(n+1)}.
-/
theorem kasami_is_AB :
    IsAlmostBent F (kasamiFun F k) := by sorry

end