/-
# Power Function AB Equivalence

For power functions f(x) = x^d with gcd(d, 2^n-1) = 1, the one-parameter
AB condition is equivalent to the full (two-parameter) AB condition.

## Main results

* `powMap_bijective_of_coprime` : x ↦ x^d is bijective when gcd(d, 2^n-1) = 1
* `power_fn_ab_implies_fullAB` : One-parameter AB implies full AB for power functions
* `kasami_ab_implies_apn` : Kasami AB implies APN

## References

* Carlet, *Boolean Functions for Cryptography and Coding Theory*, §6.2
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.PowerAPN

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### §1 Power map bijection -/

/-- If gcd(d, 2^n - 1) = 1, then x ↦ x^d is a bijection on F_{2^n}. -/
theorem powMap_bijective_of_coprime {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0)
    (hcoprime : Nat.Coprime d (2 ^ n - 1)) :
    Function.Bijective (fun x : F2n n => x ^ d) := by
  have h_inj : Function.Injective (fun x : F2n n => x ^ d) := by
    have h_bij : Function.Bijective (fun x : (F2n n)ˣ => x ^ d) := by
      have h_bij : ∀ x : (F2n n)ˣ, x ^ d = 1 → x = 1 := by
        intro x hx
        have h_order : orderOf x ∣ d ∧ orderOf x ∣ 2 ^ n - 1 := by
          refine' ⟨ orderOf_dvd_of_pow_eq_one hx, _ ⟩;
          have h_order : orderOf x ∣ Fintype.card (F2n n)ˣ := by
            exact orderOf_dvd_card;
          convert h_order using 1;
          rw [ Fintype.card_units, Kasami.F2n.card n hn ];
        have := Nat.dvd_gcd h_order.1 h_order.2; aesop;
      have h_bij : Function.Injective (fun x : (F2n n)ˣ => x ^ d) := by
        intro x y hxy; specialize h_bij ( x * y⁻¹ ) ; simp_all +decide [ mul_pow ] ;
        simpa using eq_inv_of_mul_eq_one_left h_bij;
      exact ⟨ h_bij, Finite.injective_iff_surjective.mp h_bij ⟩;
    intro x y hxy;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide;
    · rw [ eq_comm ] at hxy ; aesop;
    · have := Fintype.bijective_iff_injective_and_card ( fun x : ( F2n n )ˣ => x ^ d ) ; simp_all +decide [ Function.Injective ] ;
      specialize @this ( Units.mk0 x hx ) ( Units.mk0 y hy ) ; simp_all +decide [ Units.ext_iff ] ;
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

/-- The d-th power map is surjective when gcd(d, 2^n-1) = 1. -/
theorem powMap_surjective_of_coprime {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0)
    (hcoprime : Nat.Coprime d (2 ^ n - 1)) :
    Function.Surjective (fun x : F2n n => x ^ d) :=
  (powMap_bijective_of_coprime hn hd hcoprime).2

/-! ### §2 WHT scaling for power functions -/

/-
For a power function f(x) = x^d with gcd(d, 2^n-1) = 1 and b ≠ 0,
    there exists c with c^d = b, and wht2(f, a, b) = wht(f, a·c⁻¹).
    This shows the two-parameter WHT spectrum equals the one-parameter spectrum.
-/
theorem power_fn_wht2_eq_wht_rescaled {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0)
    (hcoprime : Nat.Coprime d (2 ^ n - 1))
    (a b : F2n n) (hb : b ≠ 0) :
    ∃ c : F2n n, c ≠ 0 ∧
    wht2 (F2n.powMap n d) a b = wht (F2n.powMap n d) (a * c⁻¹) := by
  -- Since gcd(d, 2^n-1) = 1, the map x ↦ x^d is surjective (by powMap_surjective_of_coprime). So there exists c with c^d = b.
  obtain ⟨c, hc⟩ : ∃ c : F2n n, c ^ d = b := by
    have := @powMap_bijective_of_coprime n d hn hd hcoprime;
    exact this.surjective b;
  refine' ⟨ c, _, _ ⟩ <;> simp_all +decide [ wht2, wht ];
  · cases d <;> aesop;
  · -- Since $c \neq 0$, we can substitute $x = c^{-1} y$ in the sum.
    have h_subst : ∀ (f : F2n n → ℤ), ∑ x : F2n n, f x = ∑ y : F2n n, f (c⁻¹ * y) := by
      intro f; exact (by
      rw [ ← Equiv.sum_comp ( Equiv.mulLeft₀ ( c⁻¹ ) ( by aesop ) ) ] ; aesop;);
    convert h_subst _ using 3 ; ring;
    unfold F2n.powMap; simp +decide [ ← hc, mul_pow ] ;
    grind +suggestions

/-! ### §3 Power function one-parameter AB implies full AB -/

/-
For a power function with coprime exponent, one-parameter AB implies full AB.
    Proof: for b ≠ 0, wht2(f, a, b) = wht(f, a·c⁻¹) where c^d = b.
    As a varies, a·c⁻¹ also varies over all of F_{2^n}, so the spectrum
    of wht2(f, ·, b) equals the spectrum of wht(f, ·).
-/
theorem power_fn_ab_implies_fullAB {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0)
    (hcoprime : Nat.Coprime d (2 ^ n - 1))
    (hab : IsAlmostBent (F2n.powMap n d)) :
    IsAlmostBentFull (F2n.powMap n d) := by
  intro a b hb;
  -- By power_fn_wht2_eq_wht_rescaled, there exists c ≠ 0 with wht2(f, a, b) = wht(f, a*c⁻¹).
  obtain ⟨c, hc_ne_zero, hc⟩ : ∃ c : F2n n, c ≠ 0 ∧ wht2 (F2n.powMap n d) a b = wht (F2n.powMap n d) (a * c⁻¹) := by
    exact?;
  exact hc.symm ▸ hab _

/-! ### §4 Kasami-specific results -/

/-- The Kasami exponent is coprime to 2^n - 1 when gcd(k,n) = 1 and n is odd. -/
theorem kasami_exp_coprime_field {n k : ℕ} (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  exact kasamiExp_coprime k n hk hn hn_odd hgcd

/-- The Kasami function: AB (one-parameter) implies APN.
    Combines power function AB equivalence with fullAB_implies_apn. -/
theorem kasami_ab_implies_apn {n k : ℕ} (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hab : IsAlmostBent (kasamiF n k)) :
    ∀ a : F2n n, a ≠ 0 → ∀ c : F2n n,
    (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = c).card ≤ 2 := by
  -- kasamiF n k = F2n.powMap n (kasamiExp k)
  have hfull : IsAlmostBentFull (kasamiF n k) := by
    have : kasamiF n k = F2n.powMap n (kasamiExp k) := rfl
    rw [this]
    exact power_fn_ab_implies_fullAB hn (Nat.pos_iff_ne_zero.mp (kasamiExp_pos k))
      (kasami_exp_coprime_field hk hn hn_odd hgcd) (this ▸ hab)
  exact fullAB_implies_apn hn (kasamiF n k) hfull

end
end Kasami