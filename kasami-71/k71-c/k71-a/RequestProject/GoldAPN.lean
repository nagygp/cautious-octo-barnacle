/-
  GoldAPN.lean
  
  Proves that the Gold function g(x) = x^{2^k+1} over F_{2^n} is APN
  when gcd(k,n) = 1.
  
  Specifically: for u ≠ 0, the bilinear form
    B_u(x) = u^{2^k} · x + u · x^{2^k}
  has kernel {0, u} (i.e., dimension 1 over F_2).
-/
import Mathlib
import RequestProject.MersenneGCD

set_option maxHeartbeats 4000000

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ### The Gold function and its derivative -/

/-- The Gold exponent function: g(x) = x^{2^k + 1} -/
noncomputable def goldFunc (k : ℕ) (x : F) : F := x ^ (2 ^ k + 1)

/-- The (difference) derivative of the Gold function: Δ_u g(x) = g(x+u) + g(x) -/
noncomputable def goldDiffDeriv (k : ℕ) (u x : F) : F :=
  goldFunc k (x + u) + goldFunc k x

/-- The bilinear form: B_u(x) = u^{2^k}·x + u·x^{2^k}
    This is the "linearized derivative" that captures the APN property. -/
noncomputable def goldBilinear (k : ℕ) (u x : F) : F :=
  u ^ (2 ^ k) * x + u * x ^ (2 ^ k)

/-! ### Expansion of the Gold derivative -/

section GoldExpansion
variable {F : Type*} [Field F] [CharP F 2]

/-
The Gold difference derivative expands as u^{2^k}·x + u·x^{2^k} + u^{2^k+1}
-/
lemma goldDiffDeriv_eq (k : ℕ) (u x : F) :
    goldDiffDeriv k u x = u ^ (2 ^ k) * x + u * x ^ (2 ^ k) + u ^ (2 ^ k + 1) := by
  unfold goldDiffDeriv goldFunc;
  have h_expand : (x + u) ^ (2 ^ k) = x ^ (2 ^ k) + u ^ (2 ^ k) := by
    exact?;
  grind

/-
The bilinear form equals the difference derivative plus g(u)
-/
lemma goldBilinear_eq_diffDeriv_add (k : ℕ) (u x : F) :
    goldBilinear k u x = goldDiffDeriv k u x + goldFunc k u := by
  unfold goldBilinear goldDiffDeriv goldFunc;
  simp +decide [ add_pow_char_pow, pow_add, mul_assoc, mul_comm, mul_left_comm ];
  grind

/-
0 is always in the kernel of B_u
-/
lemma goldBilinear_zero (k : ℕ) (u : F) : goldBilinear k u 0 = 0 := by
  unfold goldBilinear; ring;

/-
u is always in the kernel of B_u (uses char 2)
-/
lemma goldBilinear_self (k : ℕ) (u : F) : goldBilinear k u u = 0 := by
  unfold goldBilinear;
  grind

/-
If B_u(x) = 0 and u ≠ 0 and x ≠ 0, then (x * u⁻¹)^{2^k-1} = 1
-/
lemma goldBilinear_zero_imp_pow_eq_one (k : ℕ) (u x : F) (hu : u ≠ 0) (hx : x ≠ 0)
    (hB : goldBilinear k u x = 0) :
    (x * u⁻¹) ^ (2 ^ k - 1) = 1 := by
  -- From goldBilinear k u x = 0 we have u^{2^k}*x + u*x^{2^k} = 0. Since u ≠ 0, we can factor out u: u*(u^{2^k-1}*x + x^{2^k}) = 0, so u^{2^k-1}*x + x^{2^k} = 0, i.e. x^{2^k} = u^{2^k-1}*x.
  have h_eq : x ^ (2 ^ k) = u ^ (2 ^ k - 1) * x := by
    unfold goldBilinear at hB;
    cases n : 2 ^ k <;> simp_all +decide [ pow_succ', mul_assoc ];
    grind;
  cases n : 2 ^ k <;> simp_all +decide [ pow_succ, pow_mul ];
  rw [ mul_pow, inv_pow, h_eq, mul_inv_cancel₀ ( pow_ne_zero _ hu ) ]

end GoldExpansion

/-! ### Using the Mersenne GCD and coprimality -/

/-- In a group, if gcd(n, |G|) = 1 and x^n = 1, then x = 1 -/
lemma pow_eq_one_of_coprime_card {G : Type*} [Group G] [Fintype G] {x : G} {n : ℕ}
    (hn : Nat.Coprime n (Fintype.card G)) (hx : x ^ n = 1) : x = 1 := by
  have h1 : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Fintype.card G := orderOf_dvd_card
  have h3 : orderOf x ∣ 1 := by
    calc orderOf x ∣ Nat.gcd n (Fintype.card G) := Nat.dvd_gcd h1 h2
    _ = 1 := hn
  rw [Nat.dvd_one] at h3
  exact orderOf_eq_one_iff.mp h3

/-- The units group of F has cardinality |F| - 1 -/
noncomputable instance instFieldDecidableEq (F : Type*) [Field F] [Fintype F] : DecidableEq F :=
  Classical.decEq _

lemma card_units_eq (F : Type*) [Field F] [Fintype F] :
    Fintype.card Fˣ = Fintype.card F - 1 :=
  Fintype.card_units F

/-
The main Gold APN theorem: if gcd(k, n) = 1 where |F| = 2^n, u ≠ 0,
    and B_u(x) = 0, then x = 0 or x = u.

    In other words, the kernel of the linearized derivative has dimension ≤ 1 over F_2.
-/
theorem gold_kernel_dim_le_one (n k : ℕ) (hn : 0 < n) (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (u x : F) (hu : u ≠ 0)
    (hB : goldBilinear k u x = 0) : x = 0 ∨ x = u := by
  by_cases hx : x = 0;
  · exact Or.inl hx;
  · have h_unit : (x * u⁻¹) ^ (2 ^ k - 1) = 1 := by
      exact?;
    have h_unit : (x * u⁻¹) ^ (Fintype.card Fˣ) = 1 := by
      simp +decide [ ← mul_pow, Fintype.card_units ];
      rw [ FiniteField.pow_card_sub_one_eq_one ] ; aesop;
    have h_unit : (x * u⁻¹) ^ Nat.gcd (2 ^ k - 1) (Fintype.card Fˣ) = 1 := by
      rw [ pow_gcd_eq_one ] ; aesop;
    have h_unit : Nat.gcd (2 ^ k - 1) (Fintype.card Fˣ) = 1 := by
      have h_unit : Fintype.card Fˣ = 2 ^ n - 1 := by
        rw [ ← hcard, Fintype.card_units ];
      exact h_unit.symm ▸ coprime_mersenne_of_coprime hcoprime;
    simp_all +decide [ mul_inv_eq_iff_eq_mul₀ ]