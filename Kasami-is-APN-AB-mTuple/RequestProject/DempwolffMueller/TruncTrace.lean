import Mathlib
import RequestProject.DempwolffMueller.TraceNorm
import RequestProject.Core.ExpArith
import RequestProject.DempwolffMueller.ExpArith
import RequestProject.DempwolffMueller.FrobAlg
import RequestProject.DempwolffMueller.AdjointBij

/-!
# Truncated Trace — Definitions and Kernel Analysis

## Definitions
- `truncTrace m x`: The truncated trace `L(x) = ∑_{i=0}^{m-1} x^{2^i}`
- `dicksonF m x`: Dickson-like polynomial `f_m(x) = ∑_{j=0}^{m-1} x^{2^m + 1 - 2^{j+1}}`

## Key results
- `truncTrace_add`: L is additive
- `truncTrace_sq_add_self`: L(x)² + L(x) = x^{2^m} + x (telescoping)
- `truncTrace_ker_trivial`: ker(L) = {0} when gcd(m,n) = 1 and m is odd
-/

namespace DempwolffMueller

set_option maxHeartbeats 800000

open Finset BigOperators

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- The truncated trace map L(x) = ∑_{i=0}^{m-1} x^{2^i}. -/
def truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

/-- The Dickson-like polynomial f_m(x) = ∑_{j=0}^{m-1} x^{2^m + 1 - 2^{j+1}}. -/
noncomputable def dicksonF {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ j ∈ Finset.range m, x ^ (2 ^ m + 1 - 2 ^ (j + 1))

-- ═══════════════════════════════════════════
-- Layer 1: Additivity
-- ═══════════════════════════════════════════

lemma truncTrace_add {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x y : F) :
    truncTrace m (x + y) = truncTrace m x + truncTrace m y := by
  simp only [truncTrace, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_char_pow (p := 2) (n := i) x y

lemma truncTrace_zero {F : Type*} [CommSemiring F] (m : ℕ) :
    truncTrace m (0 : F) = 0 := by simp [truncTrace]

lemma truncTrace_one_eq_one {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (hm : Odd m) : truncTrace m (1 : F) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := hm;
  unfold truncTrace;
  simp_all +decide [ show ( 2 : F ) = 0 by exact CharTwo.two_eq_zero ]

-- ═══════════════════════════════════════════
-- Layer 2: Telescoping identity
-- L(x)² + L(x) = x^{2^m} + x
-- ═══════════════════════════════════════════

lemma truncTrace_sq_add_self {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (x : F) :
    truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x := by
  unfold truncTrace; induction m <;> simp_all +decide [ Finset.sum_range_succ, pow_succ ] ; ring;
  · rw [ mul_two, CharTwo.add_self_eq_zero ];
  · simp_all +decide [ add_mul, mul_add, pow_mul ] ; ring;
    simp_all +decide [ ← add_assoc, ← two_mul, CharTwo.two_eq_zero ];
    simp_all +decide [ add_comm, add_left_comm, add_assoc, sq ];
    simp_all +decide [ ← add_assoc, ← two_mul, CharTwo.two_eq_zero ]

-- ═══════════════════════════════════════════
-- Layer 3: Kernel triviality
-- ═══════════════════════════════════════════

/-- If L(x) = 0 then x^{2^m} = x. -/
lemma frob_fixed_of_truncTrace_zero {F : Type*} [CommRing F] [CharP F 2]
    (m : ℕ) {x : F} (hLx : truncTrace m x = 0) :
    x ^ (2 ^ m) = x := by
  have h_kernel : truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x :=
    truncTrace_sq_add_self m x
  simp [hLx] at h_kernel
  have h : x ^ 2 ^ m + x = 0 := h_kernel.symm
  have := eq_of_sub_eq_zero (show x ^ 2 ^ m - x = 0 by rw [sub_eq_add_neg, CharTwo.neg_eq]; exact h)
  exact this

lemma sq_eq_self_imp {F : Type*} [Field F] {x : F} (h : x ^ 2 = x) :
    x = 0 ∨ x = 1 := by
  have hx : x * (x - 1) = 0 := by
    have h2 := h; rw [sq] at h2; linear_combination h2 - x
  rcases mul_eq_zero.mp hx with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- If gcd(m,n) = 1 and m odd, then L(x) = 0 implies x = 0 in GF(2^n). -/
lemma truncTrace_ker_trivial {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_odd : Odd m) (_hm_pos : 1 < m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) {x : F} (hLx : truncTrace m x = 0) :
    x = 0 := by
  have h_x_two : x ^ 2 = x := by
    have h_x_gcd : x ^ (2 ^ Nat.gcd m n) = x := by
      have h_exp : x ^ (2 ^ m) = x ∧ x ^ (2 ^ n) = x := by
        exact ⟨ frob_fixed_of_truncTrace_zero m hLx, by rw [ ← hn, FiniteField.pow_card ] ⟩;
      have h_exp : ∀ k l : ℕ, x ^ (2 ^ k) = x → x ^ (2 ^ l) = x → x ^ (2 ^ (Nat.gcd k l)) = x := by
        intros k l hk hl
        have h_exp : ∀ a b : ℕ, x ^ (2 ^ a) = x → x ^ (2 ^ b) = x → x ^ (2 ^ (a % b)) = x := by
          intros a b ha hb
          have h_exp : x ^ (2 ^ (a % b)) = x := by
            have h_exp : x ^ (2 ^ a) = (x ^ (2 ^ (a % b))) ^ (2 ^ (b * (a / b))) := by
              rw [ ← pow_mul, ← pow_add, Nat.mod_add_div ]
            have h_exp : ∀ k : ℕ, (x ^ (2 ^ (a % b))) ^ (2 ^ (b * k)) = x ^ (2 ^ (a % b)) := by
              intro k; induction k <;> simp_all +decide [ pow_succ, pow_mul ] ;
              rw [ pow_right_comm, hb ];
            grind;
          exact h_exp;
        induction' l using Nat.strong_induction_on with l ih generalizing k;
        by_cases hl_zero : l = 0;
        · aesop;
        · rw [ Nat.gcd_comm, Nat.gcd_rec ];
          simpa [ Nat.gcd_comm ] using ih ( k % l ) ( Nat.mod_lt _ ( Nat.pos_of_ne_zero hl_zero ) ) l hl ( h_exp k l hk hl );
      exact h_exp m n ( by tauto ) ( by tauto );
    aesop;
  cases eq_or_ne x 0 <;> simp_all +decide [ sq ];
  exact absurd hLx ( by rw [ truncTrace_one_eq_one m hm_odd ] ; simp +decide )

end DempwolffMueller
