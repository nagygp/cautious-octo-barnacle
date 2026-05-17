/-
# Gold Radical Cardinality

Proves that the radical of the Gold bilinear form B_a has exactly 2 elements
when n is odd, gcd(k,n)=1, and a ≠ 0.
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace

namespace Kasami

open scoped BigOperators
noncomputable section
open Classical in
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

/-! ### Coprimality helpers -/

theorem coprime_2k_of_odd (k n : ℕ) (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    Nat.Coprime (2 * k) n := by
  exact Nat.Coprime.mul_left (Nat.prime_two.coprime_iff_not_dvd.mpr
    (by simpa [← even_iff_two_dvd] using hn_odd)) hgcd

theorem pow_bijective_of_coprime_order {F : Type*} [Field F] [Fintype F]
    (d : ℕ) (hd : Nat.Coprime d (Fintype.card F - 1)) :
    ∀ (c : F), c ≠ 0 → ∃! z : F, z ≠ 0 ∧ z ^ d = c := by
  intro c hc_ne
  obtain ⟨e, he⟩ : ∃ e : ℕ, d * e ≡ 1 [MOD (Fintype.card F - 1)] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime hd
    rcases k : Fintype.card F - 1 with (_ | _ | k) <;>
      simp_all +decide [Nat.ModEq, Nat.mod_one]
    exact ⟨this.choose, this.choose_spec.2⟩
  use c ^ e
  have hz_pow : ∀ x : F, x ≠ 0 → x ^ (Fintype.card F - 1) = 1 :=
    fun x hx => FiniteField.pow_card_sub_one_eq_one x hx
  refine ⟨⟨pow_ne_zero _ hc_ne, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← Nat.mod_add_div (d * e) (Fintype.card F - 1), he]
    rcases k : Fintype.card F - 1 with (_ | _ | k) <;>
      simp_all +decide [pow_add, pow_mul]
  · intro y hy
    have hy_pow : y ^ (d * e) = c ^ e := by rw [pow_mul, hy.2]
    rw [← hy_pow, ← Nat.mod_add_div (d * e) (Fintype.card F - 1), he]
    rcases k : Fintype.card F - 1 with (_ | _ | k) <;>
      simp_all +decide [pow_add, pow_mul]

theorem mersenne_coprime (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hgcd : Nat.Coprime a b) :
    Nat.Coprime (2 ^ a - 1) (2 ^ b - 1) := by
  have h_mod_simplified : 1 ≡ 2 ^ Nat.gcd a b [MOD Nat.gcd (2 ^ a - 1) (2 ^ b - 1)] := by
    simp_all +decide [← ZMod.natCast_eq_natCast_iff, pow_add]
  exact Nat.dvd_one.mp (Nat.dvd_of_mod_eq_zero <|
    h_mod_simplified.symm ▸ Nat.mod_eq_zero_of_dvd (by aesop))

/-! ### Linearized polynomial kernel analysis -/

theorem radical_exp_coprime (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) :
    Nat.Coprime (2 ^ (2 * k) - 1) (Fintype.card (F2n n) - 1) := by
  rw [hcard]
  exact mersenne_coprime (2 * k) n (by positivity) hn (coprime_2k_of_odd k n hn_odd hgcd)

/-
For z ≠ 0, the linearized equation is equivalent to a power equation.
-/
theorem radical_nonzero_iff (n k : ℕ) (hk : 0 < k) (a z : F2n n) (ha : a ≠ 0) (hz : z ≠ 0) :
    (a ^ (2 ^ k) * z ^ (2 ^ (2 * k)) + a * z = 0) ↔
    z ^ (2 ^ (2 * k) - 1) = (a ^ (2 ^ k - 1))⁻¹ := by
  rw [ show a ^ 2 ^ k = a ^ ( 2 ^ k - 1 ) * a by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ];
  rw [ show z ^ 2 ^ ( 2 * k ) = z ^ ( 2 ^ ( 2 * k ) - 1 ) * z by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ] ; ring;
  constructor <;> intro h <;> simp_all +decide [ ← eq_sub_iff_add_eq', mul_assoc, mul_comm, mul_left_comm ];
  exact eq_inv_of_mul_eq_one_right h

/-
There is exactly one nonzero root of a^{2^k}·z^{2^{2k}} + a·z.
-/
theorem radical_unique_nonzero_root (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (a : F2n n) (ha : a ≠ 0) (hcard : Fintype.card (F2n n) = 2 ^ n) :
    ∃! z : F2n n, z ≠ 0 ∧ a ^ (2 ^ k) * z ^ (2 ^ (2 * k)) + a * z = 0 := by
  -- By radical_nonzero_iff, for z ≠ 0, the original equation ↔ z^{2^{2k}-1} = (a^{2^k-1})⁻¹.
  have h_equiv : ∀ z : F2n n, z ≠ 0 → (a ^ (2 ^ k) * z ^ (2 ^ (2 * k)) + a * z = 0 ↔ z ^ (2 ^ (2 * k) - 1) = (a ^ (2 ^ k - 1))⁻¹) := by
    exact?;
  -- By pow_bijective_of_coprime_order, there exists a unique non-zero z such that z^{2^{2k}-1} = (a^{2^k-1})⁻¹.
  obtain ⟨z₀, hz₀_unique⟩ : ∃! z₀ : F2n n, z₀ ≠ 0 ∧ z₀ ^ (2 ^ (2 * k) - 1) = (a ^ (2 ^ k - 1))⁻¹ := by
    apply pow_bijective_of_coprime_order;
    · convert radical_exp_coprime n k hn hk hn_odd hgcd hcard using 1;
    · aesop;
  exact ⟨ z₀, ⟨ hz₀_unique.1.1, h_equiv z₀ hz₀_unique.1.1 |>.2 hz₀_unique.1.2 ⟩, fun y hy => hz₀_unique.2 y ⟨ hy.1, h_equiv y hy.1 |>.1 hy.2 ⟩ ⟩

/-- The kernel of P(z) = a^{2^k}·z^{2^{2k}} + a·z has exactly 2 elements. -/
theorem radical_linearized_poly_card (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (a : F2n n) (ha : a ≠ 0) (hcard : Fintype.card (F2n n) = 2 ^ n) :
    @Finset.card _ (Finset.univ.filter (fun z : F2n n =>
      a ^ (2 ^ k) * z ^ (2 ^ (2 * k)) + a * z = 0)) = 2 := by
  obtain ⟨z₀, ⟨hz₀_ne, hz₀_root⟩, hz₀_unique⟩ :=
    radical_unique_nonzero_root n k hn hk hn_odd hgcd a ha hcard
  have h_set_eq : Finset.univ.filter (fun z : F2n n =>
      a ^ (2 ^ k) * z ^ (2 ^ (2 * k)) + a * z = 0) = {0, z₀} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert,
               Finset.mem_singleton, true_and]
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · left; exact hx0
      · right; exact hz₀_unique x ⟨hx0, hx⟩
    · rintro (rfl | rfl)
      · simp
      · exact hz₀_root
  rw [h_set_eq]
  exact Finset.card_pair (Ne.symm hz₀_ne)

end
end Kasami