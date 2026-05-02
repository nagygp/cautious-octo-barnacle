/-
  CCDCounting.lean — The CCD (Canteaut–Charpin–Dobbertin) counting argument

  The CCD counting argument bounds the kernel of the linearised polynomial
  associated with the Kasami exponent.  The three steps are:

  1. **Fixed-Point Inclusion** (Leaf):  Every element `z` in the kernel
     of the linearised polynomial satisfies `z ^ (2 ^ (3 * k)) = z`.
     This is proven in `KasamiPhase1.lean` as `linearized_kernel_subset_cube`.

  2. **GCD Logic**:  Any element of GF(2^n) satisfies `z ^ (2 ^ n) = z`
     (the Frobenius / finite-field identity).  Combined with Step 1, the
     general Frobenius-GCD lemma gives `z ^ (2 ^ gcd(3k, n)) = z`.

  3. **Final Bound**:  When `gcd(3k, n) = 1` the equation becomes
     `z ^ 2 = z`, whose only roots in any field are `0` and `1`.
     Hence the kernel has at most 2 elements, giving radical dimension ≤ 1.
-/
import Mathlib
import RequestProject.KasamiDefs
import RequestProject.KasamiPhase1

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ### §0  Iterated Frobenius helpers -/

/-- Iterating the 2^b-power map: if `z ^ (2^b) = z` then `z ^ (2^(b·q)) = z`
for every natural number `q`. -/
lemma frobenius_iter {F : Type*} [Monoid F] (z : F) (b : ℕ)
    (h : z ^ (2 ^ b) = z) (q : ℕ) :
    z ^ (2 ^ (b * q)) = z := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/-- Euclidean step for Frobenius fixed points:
if `z ^ (2^a) = z` and `z ^ (2^b) = z` then `z ^ (2^(a % b)) = z`. -/
lemma frobenius_mod_step {F : Type*} [Monoid F] (z : F) (a b : ℕ)
    (ha : z ^ (2 ^ a) = z) (hb : z ^ (2 ^ b) = z) :
    z ^ (2 ^ (a % b)) = z := by
  rcases b.eq_zero_or_pos with rfl | hbp
  · simpa using ha
  · have hab : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
    have : z ^ (2 ^ a) = z ^ (2 ^ (a % b)) := by
      conv_lhs => rw [hab, pow_add, pow_mul, frobenius_iter z b hb (a / b)]
    rw [ha] at this; exact this.symm

/-! ### §1  GCD fixed-point theorem (Step 2) -/

/-- **Frobenius-GCD theorem.**  If `z ^ (2^a) = z` and `z ^ (2^b) = z`
in any monoid, then `z ^ (2^(gcd a b)) = z`. -/
theorem frobenius_gcd_fixed {F : Type*} [Monoid F] (z : F) (a b : ℕ)
    (ha : z ^ (2 ^ a) = z) (hb : z ^ (2 ^ b) = z) :
    z ^ (2 ^ (Nat.gcd a b)) = z := by
  induction a, b using Nat.gcd.induction with
  | H0 b => simp; exact hb
  | H1 a b _ ih =>
    rw [Nat.gcd_rec]
    exact ih (frobenius_mod_step z b a hb ha) ha

/-! ### §2  Quadratic fixed-point bound (Step 3) -/

/-- In any field, `z ^ 2 = z` forces `z = 0` or `z = 1`. -/
theorem sq_frob_eq_zero_or_one {F : Type*} [Field F] (z : F)
    (h : z ^ 2 = z) : z = 0 ∨ z = 1 := by
  have h1 : z * (z - 1) = 0 := by
    have := sub_eq_zero.mpr h
    linear_combination this
  exact mul_eq_zero.mp h1 |>.imp id sub_eq_zero.mp

/-- Variant with the exponent written as `2 ^ 1`. -/
theorem pow_two_one_eq_zero_or_one {F : Type*} [Field F] (z : F)
    (h : z ^ (2 ^ 1) = z) : z = 0 ∨ z = 1 :=
  sq_frob_eq_zero_or_one z (by simpa using h)

/-! ### §3  Leaf lemma: Fixed-Point Inclusion

The leaf lemma is proven in `KasamiPhase1.linearized_kernel_subset_cube`:
for the Kasami construction with parameter `k`, every element `z` in the
kernel of `L_k` satisfies `z ^ (2^(3k)) = z`.

We provide a "unwrapped" version below that states the result in terms
of the raw power `z ^ (2 ^ (3 * k)) = z` given `linPolyL k z = 0`. -/

/-- Unwrapped form of the Phase 1 leaf: if `linPolyL k z = 0` then
    `z ^ (2 ^ (3 * k)) = z`. -/
theorem linearized_kernel_subset_cube_raw
    {F : Type*} [CommRing F] [CharP F 2]
    (k : ℕ) (z : F) (hz : linPolyL k z = 0) :
    z ^ (2 ^ (3 * k)) = z := by
  have hmem : z ∈ kerL k := hz
  have hfp := linearized_kernel_subset_cube hmem
  exact hfp

/-! ### §4  The field identity `z ^ (2^n) = z` -/

/-- Every element of a finite field of cardinality `2^n` satisfies `z^(2^n) = z`. -/
theorem field_element_pow_card {F : Type*} [Field F] [Fintype F]
    (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (z : F) :
    z ^ (2 ^ n) = z := by
  have := FiniteField.pow_card z
  rwa [hcard] at this

/-! ### §5  CCD counting argument — Main theorem -/

/-- **CCD counting argument (main theorem).**

Let `F = GF(2^n)` with `n = 2k + 1`.  Suppose:
- (Fixed-Point Inclusion)  `z ^ (2^(3k)) = z`, and
- (Field Property)          `z ^ (2^n) = z`.

Then by the Frobenius-GCD theorem, `z ^ (2^(gcd(3k, n))) = z`.
When `gcd(3k, n) = 1` this gives `z ^ 2 = z`, hence `z ∈ {0, 1}`. -/
theorem ccd_kernel_bound
    {F : Type*} [Field F] [Fintype F]
    (n k : ℕ)
    (_hcard : Fintype.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (z : F)
    (h_cube : z ^ (2 ^ (3 * k)) = z)
    (h_field : z ^ (2 ^ n) = z)
    : z = 0 ∨ z = 1 := by
  have h_gcd_fix : z ^ (2 ^ (Nat.gcd (3 * k) n)) = z :=
    frobenius_gcd_fixed z (3 * k) n h_cube h_field
  rw [hgcd] at h_gcd_fix
  exact pow_two_one_eq_zero_or_one z h_gcd_fix

/-- **CCD counting — cardinality form.**
Under the CCD hypotheses, the set of kernel elements is a subset of `{0, 1}`,
hence has cardinality at most 2. -/
theorem ccd_kernel_card_le_two
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ)
    (hcard : Fintype.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (S : Finset F)
    (hS : ∀ z ∈ S,
      z ^ (2 ^ (3 * k)) = z ∧ z ^ (2 ^ n) = z) :
    S.card ≤ 2 := by
  have hSsub : S ⊆ {0, 1} := by
    intro z hz
    rcases hS z hz with ⟨h1, h2⟩
    rcases ccd_kernel_bound n k hcard hgcd z h1 h2 with rfl | rfl
    · exact Finset.mem_insert_self 0 {1}
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  calc S.card ≤ ({0, 1} : Finset F).card := Finset.card_le_card hSsub
    _ ≤ 2 := by simp

/-- **CCD in the Kasami setting.**
Combining all three steps: for the Kasami construction with `n = 2k+1`
and `gcd(3k, n) = 1`, every element in ker(L_k) is 0 or 1. -/
theorem ccd_kasami
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (k : ℕ) (_hk : 1 ≤ k)
    (n : ℕ) (_hn : n = 2 * k + 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (z : F)
    (hz_kernel : linPolyL k z = 0) :
    z = 0 ∨ z = 1 := by
  have h_cube : z ^ (2 ^ (3 * k)) = z :=
    linearized_kernel_subset_cube_raw k z hz_kernel
  have h_field : z ^ (2 ^ n) = z :=
    field_element_pow_card n hcard z
  exact ccd_kernel_bound n k hcard hgcd z h_cube h_field

/-! ### §6  GCD computation: `gcd(3k, 2k+1) = 1` when `¬(3 ∣ (2k+1))` -/

/-- `gcd(3k, 2k+1)` divides 3. -/
lemma gcd_3k_2k1_dvd_three (k : ℕ) : Nat.gcd (3 * k) (2 * k + 1) ∣ 3 := by
  convert Nat.dvd_sub (Nat.gcd_dvd_right _ _ |> fun x => x.mul_left 3)
    (Nat.gcd_dvd_left _ _ |> fun x => x.mul_left 2) using 1
  rw [Nat.sub_eq_of_eq_add]; ring

/-- When `3` does not divide `n = 2k+1`, we have `gcd(3k, n) = 1`. -/
lemma gcd_3k_n_eq_one (k : ℕ) (hn : ¬(3 ∣ (2 * k + 1))) :
    Nat.gcd (3 * k) (2 * k + 1) = 1 := by
  have div_three : Nat.gcd (3 * k) (2 * k + 1) ∣ 3 := gcd_3k_2k1_dvd_three k
  have := Nat.le_of_dvd (by decide) div_three
  interval_cases _ : Nat.gcd (3 * k) (2 * k + 1) <;> simp_all +decide
  exact hn (‹Nat.gcd (3 * k) (2 * k + 1) = 3› ▸ Nat.gcd_dvd_right _ _)
