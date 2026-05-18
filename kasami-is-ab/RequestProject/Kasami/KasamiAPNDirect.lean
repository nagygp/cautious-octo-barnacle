/-
# Direct proof of Kasami APN via CCD factorization

Decomposes kasami_is_apn into small, composable sub-lemmas using the
Canteaut-Charpin-Dobbertin (2000) factorization approach.

## Key steps:
1. Scale invariance: APN reduces to D_1 being 2-to-1
2. Factorization: 1 + z^d + (z+1)^d = (s+z)(s+t)/(s(s+1))
3. Subfield argument: (s+z)(s+t)=0 → z ∈ GF(2)
4. Second derivative is affine in x, with nonzero constant part for z ∉ GF(2)
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.Char2Algebra

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

variable {n : ℕ}

/-! ### §1: Char 2 Frobenius identities -/

/-- In GF(2^n), x^{2^n} = x. -/
theorem frob_fixed' (hn : n ≠ 0) (x : F2n n) : x ^ (2 ^ n) = x := by
  have hcard : Fintype.card (F2n n) = 2 ^ n := F2n.card n hn
  rw [← hcard]; exact FiniteField.pow_card x

/-
z^{2^k} = z implies z ∈ {0, 1} when gcd(k,n) = 1.
    Proof: z^{2^k-1} = 1 (for z≠0), z^{2^n-1} = 1, so
    ord(z) | gcd(2^k-1, 2^n-1) = 2^{gcd(k,n)}-1 = 1.
-/
theorem frob_k_fixed_implies_gf2 (hn : n ≠ 0) (hgcd : Nat.Coprime k n)
    (z : F2n n) (hz : z ^ (2 ^ k) = z) :
    z = 0 ∨ z = 1 := by
  -- By definition of $F2n$, we know that $z^{2^n} = z$.
  have h_frob : z ^ (2 ^ n) = z := by
    exact?;
  by_cases hz0 : z = 0 <;> simp_all +decide [ pow_eq_zero_iff' ];
  -- Since $z \neq 0$, we have $z^{2^k - 1} = 1$.
  have hz_pow : z ^ (2 ^ k - 1) = 1 := by
    exact mul_left_cancel₀ hz0 <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ; aesop;
  -- Since $z^{2^k - 1} = 1$, we have that the order of $z$ divides $2^k - 1$.
  have h_order_div : orderOf z ∣ 2 ^ k - 1 := by
    exact orderOf_dvd_iff_pow_eq_one.mpr hz_pow;
  -- Since $z^{2^n - 1} = 1$, we have that the order of $z$ divides $2^n - 1$.
  have h_order_div_n : orderOf z ∣ 2 ^ n - 1 := by
    rw [ orderOf_dvd_iff_pow_eq_one ] at *;
    rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ), pow_add, pow_one ] at * ; aesop;
  -- Since $\gcd(2^k - 1, 2^n - 1) = 1$, the order of $z$ must be $1$.
  have h_order_one : orderOf z ∣ Nat.gcd (2 ^ k - 1) (2 ^ n - 1) := by
    exact Nat.dvd_gcd h_order_div h_order_div_n;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ]

/-! ### §2: Kasami exponent as fraction -/

/-
For z ≠ 0: z^d = z * z^{2^{2k}} * (z^{2^k})⁻¹ where d = 4^k - 2^k + 1.
-/
theorem kasami_pow_as_fraction (k : ℕ) (z : F2n n) (hz : z ≠ 0) :
    z ^ (kasamiExp k) = z * z ^ (2 ^ (2 * k)) * (z ^ (2 ^ k))⁻¹ := by
  rw [ kasamiExp_eq ];
  field_simp;
  rw [ ← pow_add, tsub_add_eq_add_tsub ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) ) ];
  rw [ Nat.sub_add_cancel ( show 2 ^ k ≤ 2 ^ ( 2 * k ) + 1 from Nat.le_succ_of_le ( pow_le_pow_right₀ ( by decide ) ( by linarith ) ) ) ] ; ring

/-! ### §3: The key factorization identity -/

/-- **CCD Factorization**: In char 2, for s = z^{2^k}, t = z^{2^{2k}}:
    s*(s+1) * (1 + z^d + (z+1)^d) = (s+z)*(s+t)
    where d = kasamiExp k. -/
theorem ccd_factorization (k : ℕ) (z : F2n n) :
    let s := z ^ (2 ^ k)
    let t := z ^ (2 ^ (2 * k))
    let d := kasamiExp k
    s * (s + 1) * (1 + z ^ d + (z + 1) ^ d) = (s + z) * (s + t) := by
  by_cases h : z = 0 <;> by_cases h' : z + 1 = 0 <;>
    simp_all +decide [add_eq_zero_iff_eq_neg]
  have h_simp : z ^ (kasamiExp k) = z * z ^ (2 ^ (2 * k)) * (z ^ (2 ^ k))⁻¹ ∧
      (z + 1) ^ (kasamiExp k) = (z + 1) * (z + 1) ^ (2 ^ (2 * k)) *
        ((z + 1) ^ (2 ^ k))⁻¹ := by
    exact ⟨kasami_pow_as_fraction k z h,
           kasami_pow_as_fraction k (z + 1) (by grind)⟩
  simp_all +decide [mul_assoc, mul_comm, mul_left_comm]
  field_simp
  rw [add_div', mul_div_assoc']
  · rw [div_eq_iff]
    · nontriviality; ring
      norm_num [pow_mul', add_pow_char_pow]; ring
      rw [show (1 + z) ^ 4 ^ k = (1 + z ^ 4 ^ k) by
        have h_frobenius : ∀ (x y : F2n n), (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
          exact?
        refine' Nat.recOn k _ _ <;> simp_all +decide [pow_succ, pow_mul]
        grind]; ring
      grind
    · simp_all +decide [add_eq_zero_iff_eq_neg]
  · simp_all +decide [add_eq_zero_iff_eq_neg]

/-! ### §4: Factor cases imply GF(2) membership -/

/-- Case 1: s + z = 0 means z^{2^k} = z, hence z ∈ GF(2). -/
theorem factor_case1 (hn : n ≠ 0) (k : ℕ) (hgcd : Nat.Coprime k n)
    (z : F2n n) (hz : z ^ (2 ^ k) + z = 0) :
    z = 0 ∨ z = 1 := by
  have : z ^ (2 ^ k) = z := by
    rwa [add_eq_zero_iff_eq_neg, F2n.neg_eq] at hz
  exact frob_k_fixed_implies_gf2 hn hgcd z this

/-
Case 2: s + t = 0 means z^{2^k} = z^{2^{2k}}, reducing to Case 1
    via the inverse Frobenius.
-/
theorem factor_case2 (hn : n ≠ 0) (k : ℕ) (hgcd : Nat.Coprime k n)
    (z : F2n n) (hz : z ^ (2 ^ k) + z ^ (2 ^ (2 * k)) = 0) :
    z = 0 ∨ z = 1 := by
  have hz_eq : z ^ (2 ^ k) = 0 ∨ z ^ (2 ^ k) = 1 := by
    apply frob_k_fixed_implies_gf2 hn hgcd;
    convert eq_neg_of_add_eq_zero_right hz using 1 ; ring;
    grind +suggestions;
  cases hz_eq <;> simp_all +decide [ pow_eq_zero_iff ];
  have h_order : orderOf z ∣ 2 ^ k - 1 ∧ orderOf z ∣ 2 ^ n - 1 := by
    have h_order : orderOf z ∣ 2 ^ n - 1 := by
      have h_order : z ^ (2 ^ n - 1) = 1 := by
        have h_order : z ^ (Fintype.card (F2n n) - 1) = 1 := by
          rw [ FiniteField.pow_card_sub_one_eq_one ] ; aesop;
        grind +suggestions;
      exact orderOf_dvd_iff_pow_eq_one.mpr h_order;
    have h_order : orderOf z ∣ 2 ^ k := by
      exact orderOf_dvd_iff_pow_eq_one.mpr ‹_›;
    have := Nat.dvd_gcd h_order ‹orderOf z ∣ 2 ^ n - 1›; simp_all +decide [ Nat.Coprime, Nat.Coprime.pow ] ;
    have h_coprime : Nat.gcd (2 ^ k) (2 ^ n - 1) = 1 := by
      exact Nat.Coprime.pow_left _ ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ] using hn );
    aesop;
  have h_order_one : orderOf z ∣ Nat.gcd (2 ^ k - 1) (2 ^ n - 1) := by
    exact Nat.dvd_gcd h_order.left h_order.right;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ]

/-! ### §5: Constant part of second derivative is nonzero -/

/-- For z ∉ GF(2) with gcd(k,n)=1:
    1 + z^d + (z+1)^d ≠ 0. -/
theorem kasami_const_part_nonzero (hn : n ≠ 0) (k : ℕ) (hgcd : Nat.Coprime k n)
    (z : F2n n) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    1 + z ^ kasamiExp k + (z + 1) ^ kasamiExp k ≠ 0 := by
  intro h_eq
  have h_fact := ccd_factorization k z
  simp only at h_fact
  rw [h_eq, mul_zero] at h_fact
  rcases mul_eq_zero.mp h_fact.symm with h1 | h2
  · have := factor_case1 hn k hgcd z h1
    rcases this with rfl | rfl <;> contradiction
  · have := factor_case2 hn k hgcd z h2
    rcases this with rfl | rfl <;> contradiction

end
end Kasami