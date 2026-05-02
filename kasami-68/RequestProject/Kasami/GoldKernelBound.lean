/-
# Phase 2: The Geometric Bridge (Kernel Bounds)

Proves that when gcd(k, n) = 1, the kernel of the linearized map
L_a(x) = a^(2^k)·x + a·x^(2^k) has exactly 2 elements for a ≠ 0.

## Main Results

- `gcd_mersenne` : gcd(2^a-1, 2^b-1) = 2^(gcd(a,b)) - 1
- `linMap_self` : L_a(a) = 0 (a is always in the kernel)
- `kernel_eq` : ker(L_a) = {0, a} when gcd(k,n) = 1 and a ≠ 0
- `kernel_card` : |ker(L_a)| = 2

Pure algebra and number theory — no character sums.
-/
import RequestProject.Kasami.PolarExpansion

open scoped Classical
set_option maxHeartbeats 800000

open Finset BigOperators

/-! ## GCD of Mersenne Numbers -/

/-
The fundamental Mersenne GCD identity:
    gcd(2^a - 1, 2^b - 1) = 2^(gcd(a,b)) - 1.
-/
theorem gcd_mersenne (a b : ℕ) :
    Nat.gcd (2 ^ a - 1) (2 ^ b - 1) = 2 ^ (Nat.gcd a b) - 1 :=
  Nat.pow_sub_one_gcd_pow_sub_one 2 a b

namespace KasamiData

variable (K : KasamiData)

/-- When gcd(k,n) = 1: gcd(2^k - 1, 2^n - 1) = 1. -/
theorem gcd_mersenne_coprime :
    Nat.gcd (2 ^ K.k - 1) (2 ^ K.n - 1) = 1 := by
  rw [gcd_mersenne K.k K.n]
  have h : Nat.gcd K.k K.n = 1 := K.hk
  rw [h]; simp

/-- Useful: 2 = 0 in F. -/
private lemma two_eq_zero : (2 : K.F) = 0 := CharP.cast_eq_zero K.F 2

/-! ## Kernel Analysis -/

/-- L_a(a) = 0 in characteristic 2. -/
theorem linMap_self (a : K.F) : K.linMap a a = 0 := by
  simp only [linMap]
  have : K.frob a * a + a * K.frob a = 2 * (K.frob a * a) := by ring
  rw [this, two_eq_zero]; ring

/-
For a ≠ 0, nonzero kernel elements give roots of unity:
    L_a(x) = 0 ∧ x ≠ 0 ⟹ (x/a)^(2^k-1) = 1.
-/
theorem kernel_roots_of_unity (a x : K.F) (ha : a ≠ 0) (hx : x ≠ 0)
    (hker : K.linMap a x = 0) :
    (x * a⁻¹) ^ (2 ^ K.k - 1) = 1 := by
  -- From the hypothesis hker, we have that a^(2^k) * x = a * x^(2^k).
  have h_eq : a ^ (2 ^ K.k) * x = a * x ^ (2 ^ K.k) := by
    have h_eq : K.frob a * x + a * K.frob x = 0 := by
      exact hker;
    grind +suggestions;
  -- Dividing both sides by $a * x$ (since $a \neq 0$ and $x \neq 0$), we get $a^{2^k - 1} = x^{2^k - 1}$.
  have h_div : a ^ (2 ^ K.k - 1) = x ^ (2 ^ K.k - 1) := by
    cases n : 2 ^ K.k <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm ];
  simp_all +decide [ mul_pow, mul_comm ]

/-
When gcd(k,n) = 1, the only (2^k-1)-th root of unity in F* is 1.
    Uses: |{x : x^d = 1}| = gcd(d, |F*|) and gcd(2^k-1, 2^n-1) = 1.
-/
theorem unique_root_of_unity (x : K.F) (hx : x ≠ 0)
    (hroot : x ^ (2 ^ K.k - 1) = 1) :
    x = 1 := by
  have h_order : orderOf x ∣ Nat.gcd (2 ^ K.k - 1) (2 ^ K.n - 1) := by
    refine' Nat.dvd_gcd ( orderOf_dvd_iff_pow_eq_one.mpr hroot ) _;
    rw [ orderOf_dvd_iff_pow_eq_one ];
    convert FiniteField.pow_card_sub_one_eq_one x hx using 1;
    rw [ KasamiData.card_F ];
  have h_coprime : Nat.gcd (2 ^ K.k - 1) (2 ^ K.n - 1) = 1 :=
    gcd_mersenne_coprime K;
  aesop

/-- **Main theorem**: ker(L_a) = {0, a} when a ≠ 0 and gcd(k,n) = 1. -/
theorem kernel_eq (a : K.F) (ha : a ≠ 0) :
    ∀ x : K.F, K.linMap a x = 0 ↔ x = 0 ∨ x = a := by
  intro x
  constructor
  · intro hker
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hroot := K.kernel_roots_of_unity a x ha hx hker
      have ha' : a⁻¹ ≠ 0 := inv_ne_zero ha
      have huniq := K.unique_root_of_unity (x * a⁻¹)
        (mul_ne_zero hx ha') hroot
      field_simp at huniq
      exact huniq
  · rintro (rfl | rfl)
    · exact linMap_zero K a
    · exact K.linMap_self _

/-
|ker(L_a)| = 2 when a ≠ 0.
-/
theorem kernel_card (a : K.F) (ha : a ≠ 0) :
    Finset.card (Finset.univ.filter fun x : K.F => K.linMap a x = 0) = 2 := by
  rw [ Finset.card_eq_two ];
  have := K.kernel_eq a ha;
  exact ⟨ 0, a, ha.symm, by ext; aesop ⟩

end KasamiData