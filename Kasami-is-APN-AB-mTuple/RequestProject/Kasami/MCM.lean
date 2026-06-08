import RequestProject.Kasami.CharTwoBasics
import RequestProject.Kasami.CrossForm
import RequestProject.Kasami.APN
import RequestProject.Kasami.EvenK
import Mathlib

/-!
# MCM Identity and Kasami APN Proof
-/

set_option maxHeartbeats 1600000

namespace CollisionAnalysis

open Finset Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Lemmas -/

theorem sq_add_eq_iff (t₁ t₂ : F) :
    t₁ ^ 2 + t₁ = t₂ ^ 2 + t₂ ↔ (t₂ = t₁ ∨ t₂ = t₁ + 1) := by
  grind +ring

theorem mcm_identity (k : ℕ) (hk : k ≥ 1) (t : F) :
    ((t + 1) ^ d k + t ^ d k + 1) * (t ^ 2 + t) ^ (2 ^ k) =
    (t ^ (2 ^ k) + t) ^ (2 ^ k + 1) := by
  simp +decide only [d]
  rw [show 2 ^ (2 * k) - 2 ^ k = 2 ^ k * (2 ^ k - 1) by rw [Nat.mul_sub_left_distrib]; ring]
  simp +decide [pow_add, pow_mul, add_pow_char_pow]
  rw [show (t ^ 2 ^ k + 1) ^ (2 ^ k - 1) =
      (t ^ 2 ^ k + 1) ^ (2 ^ k) / (t ^ 2 ^ k + 1) from ?_,
    show (t ^ 2 ^ k) ^ (2 ^ k - 1) =
      (t ^ 2 ^ k) ^ (2 ^ k) / (t ^ 2 ^ k) from ?_]
  · by_cases h : t ^ 2 ^ k + 1 = 0 <;> by_cases h' : t = 0 <;>
      simp_all +decide [add_eq_zero_iff_eq_neg, pow_succ, mul_assoc, div_mul_eq_mul_div]
    · rcases k with (_ | k) <;> simp_all +decide [pow_succ', pow_mul]
      simp_all +decide [mul_pow, pow_right_comm]
    · simp_all +decide [add_pow_char_pow, mul_pow, div_eq_mul_inv]
      field_simp; grind
  · by_cases h : t ^ 2 ^ k = 0 <;> simp_all +decide [pow_succ, mul_assoc]
    · exact ne_of_gt (Nat.sub_pos_of_lt (one_lt_pow₀ one_lt_two (by linarith)))
    · rw [eq_div_iff (pow_ne_zero _ h), ← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]
  · by_cases h : t ^ 2 ^ k + 1 = 0 <;> simp_all +decide [pow_succ, mul_div_cancel_left₀]
    · exact ne_of_gt (Nat.sub_pos_of_lt (one_lt_pow₀ one_lt_two (by linarith)))
    · rw [eq_div_iff h, ← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]

theorem gold_coprime (k n : ℕ) (hcop : Nat.Coprime k n) (hnodd : Odd n) :
    Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
  have h_gcd : Nat.gcd (2 ^ k + 1) (2 ^ n - 1) ∣
      Nat.gcd (2 ^ (2 * k) - 1) (2 ^ n - 1) :=
    Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _)
      (by use 2 ^ k - 1; zify; norm_num; ring)) (Nat.gcd_dvd_right _ _)
  simp_all +decide [Nat.Coprime, Nat.Coprime.symm, Nat.Coprime.gcd_mul_left_cancel,
    Nat.Coprime.gcd_mul_right_cancel]

/-! ## Exponent reduction modulo 2^n - 1 -/

/-
The Kasami exponent d(k) is congruent to d(k % n) modulo 2^n - 1.
This is because 2^a ≡ 2^(a mod n) mod (2^n - 1).
-/
lemma d_mod_card_sub_one (k n : ℕ) (hn : n ≥ 1) :
    d k % (2 ^ n - 1) = d (k % n) % (2 ^ n - 1) := by
  zify [ d ];
  rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ pow_mul' ];
  · rw [ Nat.cast_sub ] <;> norm_num [ pow_two ];
    · -- By Fermat's Little Theorem, we know that $2^n \equiv 1 \pmod{2^n - 1}$.
      have h_fermat : 2 ^ n ≡ 1 [ZMOD (2 ^ n - 1)] := by
        exact Int.modEq_iff_dvd.mpr ⟨ -1, by ring ⟩;
      -- By Fermat's Little Theorem, we know that $2^k \equiv 2^{k \mod n} \pmod{2^n - 1}$.
      have h_fermat_k : 2 ^ k ≡ 2 ^ (k % n) [ZMOD (2 ^ n - 1)] := by
        rw [ ← Nat.mod_add_div k n ] ; simpa [ pow_add, pow_mul ] using Int.ModEq.mul_left _ ( h_fermat.pow _ ) ;
      exact Int.ModEq.add ( Int.ModEq.sub ( h_fermat_k.mul h_fermat_k ) h_fermat_k ) rfl;
    · exact Nat.one_le_pow _ _ ( by decide );
  · exact?;
  · nlinarith [ pow_pos ( zero_lt_two' ℕ ) k ]

/-- sVal k and sVal (k % n) agree on GF(2^n). -/
lemma sVal_periodic {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1)
    (k : ℕ) (t : F) : sVal k t = sVal (k % n) t := by
  unfold sVal
  have hd := d_mod_card_sub_one k n hn
  have hd_pos : 0 < d k := by unfold d; omega
  have hd_pos' : 0 < d (k % n) := by unfold d; omega
  congr 1
  · by_cases ht : t + 1 = 0
    · rw [ht, zero_pow (Nat.ne_of_gt hd_pos), zero_pow (Nat.ne_of_gt hd_pos')]
    · exact DempwolffMueller.pow_eq_pow_of_mod_eq ht (by rw [hcard]; exact hd)
  · by_cases ht : t = 0
    · rw [ht, zero_pow (Nat.ne_of_gt hd_pos), zero_pow (Nat.ne_of_gt hd_pos')]
    · exact DempwolffMueller.pow_eq_pow_of_mod_eq ht (by rw [hcard]; exact hd)

/-- From sVal equality and APN, derive the u equality. -/
private lemma u_eq_of_sVal_eq_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk2 : 1 < k) (hkn : k < n)
    (hnodd : Odd n) (hcop : Nat.Coprime k n)
    (t₁ t₂ : F) (hsval : sVal k t₁ = sVal k t₂) :
    t₁ ^ 2 + t₁ = t₂ ^ 2 + t₂ := by
  have hapn := KasamiEvenK.kasami_is_apn_general hcard k hk2 hkn hnodd hcop
  have h := hapn 1 one_ne_zero t₁ t₂ (show _ from hsval)
  rcases h with rfl | rfl
  · rfl
  · grind

/-- From sVal equality in the k=1 case, derive u equality directly. -/
private lemma u_eq_of_sVal_eq_k1
    (t₁ t₂ : F) (hsval : sVal 1 t₁ = sVal 1 t₂) :
    t₁ ^ 2 + t₁ = t₂ ^ 2 + t₂ := by
  have h_sv1 : sVal 1 t₁ = t₁ ^ 2 + t₁ + 1 := by unfold sVal d; norm_num; grind
  have h_sv2 : sVal 1 t₂ = t₂ ^ 2 + t₂ + 1 := by unfold sVal d; norm_num; grind
  rw [h_sv1, h_sv2] at hsval
  have : t₁ ^ 2 + t₁ + 1 + (t₂ ^ 2 + t₂ + 1) = 0 := by
    rw [hsval]; simp [CharTwo.add_self_eq_zero]
  grind

/-- Derive sVal equality from the cross-product condition. -/
private lemma sVal_eq_of_hcross (k : ℕ) (hk : k ≥ 1) (t₁ t₂ : F)
    (h1 : t₁ ^ 2 + t₁ ≠ 0) (h2 : t₂ ^ 2 + t₂ ≠ 0)
    (hcross : (t₁ ^ (2 ^ k) + t₁) ^ (2 ^ k + 1) * (t₂ ^ 2 + t₂) ^ 2 ^ k =
              (t₂ ^ (2 ^ k) + t₂) ^ (2 ^ k + 1) * (t₁ ^ 2 + t₁) ^ 2 ^ k) :
    sVal k t₁ = sVal k t₂ := by
  have hm1 := mcm_identity k hk t₁
  have hm2 := mcm_identity k hk t₂
  have hu1q : (t₁ ^ 2 + t₁) ^ (2 ^ k) ≠ 0 := pow_ne_zero _ h1
  have hu2q : (t₂ ^ 2 + t₂) ^ (2 ^ k) ≠ 0 := pow_ne_zero _ h2
  suffices h : sVal k t₁ + 1 = sVal k t₂ + 1 by
    have := add_right_cancel h; exact this
  apply mul_left_cancel₀ (mul_ne_zero hu1q hu2q)
  have : ((sVal k t₁ + 1) * (t₁ ^ 2 + t₁) ^ 2 ^ k) *
         (t₂ ^ 2 + t₂) ^ 2 ^ k =
         ((sVal k t₂ + 1) * (t₂ ^ 2 + t₂) ^ 2 ^ k) *
         (t₁ ^ 2 + t₁) ^ 2 ^ k := by
    unfold sVal; rw [hm1, hm2]; exact hcross
  ring_nf; ring_nf at this; exact this

/-- **MCM injectivity** — proved using the Kasami APN theorem.

From the cross-product equation, the MCM identity gives sVal equality.
The Kasami APN theorem (for all valid k) then shows that sVal equality
forces t₁² + t₁ = t₂² + t₂. -/
lemma mcm_inj_core {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 0 < n)
    (t₁ t₂ : F)
    (h1 : t₁ ^ 2 + t₁ ≠ 0) (h2 : t₂ ^ 2 + t₂ ≠ 0)
    (hL1 : t₁ ^ (2 ^ k) + t₁ ≠ 0) (hL2 : t₂ ^ (2 ^ k) + t₂ ≠ 0)
    (hcross : (t₁ ^ (2 ^ k) + t₁) ^ (2 ^ k + 1) * (t₂ ^ 2 + t₂) ^ 2 ^ k =
              (t₂ ^ (2 ^ k) + t₂) ^ (2 ^ k + 1) * (t₁ ^ 2 + t₁) ^ 2 ^ k) :
    t₁ ^ 2 + t₁ = t₂ ^ 2 + t₂ := by
  -- Step 1: derive sVal equality
  have hsval : sVal k t₁ = sVal k t₂ := sVal_eq_of_hcross k hk t₁ t₂ h1 h2 hcross
  -- Step 2: derive n ≥ 3
  have hn3 : n ≥ 3 := by
    rcases n with _ | _ | _ | n
    · omega
    · exfalso; apply h1
      have : t₁ ^ Fintype.card F = t₁ := FiniteField.pow_card t₁
      rw [hcard] at this; simp at this
      rw [show t₁ ^ 2 = t₁ from this]; exact CharTwo.add_self_eq_zero t₁
    · exfalso; simp [Nat.odd_iff] at hnodd
    · omega
  -- Step 3: reduce to k' = k % n < n
  set k' := k % n with hk'_def
  have hk'_lt : k' < n := Nat.mod_lt k (by omega)
  have hk'_pos : k' ≥ 1 := by
    by_contra h_z; push_neg at h_z
    have hmod0 : k % n = 0 := by omega
    have : n ∣ k := Nat.dvd_of_mod_eq_zero hmod0
    have : Nat.gcd k n = n := Nat.gcd_eq_right this
    rw [hcop] at this; omega
  have hcop' : Nat.Coprime k' n := by
    rwa [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, Nat.mod_mod_of_dvd,
         ← Nat.gcd_rec, ← Nat.gcd_comm]
    exact dvd_refl n
  -- sVal k = sVal k' on GF(2^n)
  have hsval' : sVal k' t₁ = sVal k' t₂ := by
    rwa [← sVal_periodic hcard (by omega) k t₁, ← sVal_periodic hcard (by omega) k t₂]
  -- Step 4: conclude using APN
  by_cases hk'1 : k' = 1
  · rw [hk'1] at hsval'; exact u_eq_of_sVal_eq_k1 t₁ t₂ hsval'
  · exact u_eq_of_sVal_eq_apn hcard k' (by omega) hk'_lt hnodd hcop' t₁ t₂ hsval'

/-! ## Main theorem -/

theorem cross_pair_analysis_mcm {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) (t₁ t₂ : F)
    (hs : sVal k t₁ = sVal k t₂)
    (hne : t₂ ≠ t₁) (hne1 : t₂ ≠ t₁ + 1)
    (hs0 : sVal k t₁ ≠ 0) :
    False := by
  by_cases ht1 : t₁ ∈ ({0, 1} : Set F);
  · have hs1 : sVal k t₂ = 1 := by
      rcases ht1 with ( rfl | rfl ) <;> simp_all +decide [ sVal ];
      · rw [ ← hs, zero_pow ( by linarith [ d_pos k hk ] ), add_zero ];
      · simp_all +decide [ ← hs, CharTwo.add_self_eq_zero ];
        exact ne_of_gt ( d_pos k hk );
    have hL : t₂ ^ (2 ^ k) + t₂ = 0 := by
      have hL : ((t₂ + 1) ^ d k + t₂ ^ d k + 1) * (t₂ ^ 2 + t₂) ^ (2 ^ k) = (t₂ ^ (2 ^ k) + t₂) ^ (2 ^ k + 1) := by
        exact mcm_identity k hk t₂;
      unfold sVal at hs1; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      rw [ eq_neg_iff_add_eq_zero ] ; have := CharP.cast_eq_zero_iff F 2 2 ; simp_all +decide [ pow_succ' ] ;
      simp_all +decide [ ← two_mul ];
    have ht2 : t₂ ∈ ({0, 1} : Set F) := by
      apply L_ker_trivial hcard k hcop t₂ hL;
    grind +qlia;
  · by_cases ht2 : t₂ ∈ ({0, 1} : Set F);
    · rcases ht2 with ( rfl | rfl ) <;> simp_all +decide [ CharTwo.add_self_eq_zero ];
      · have hL : (t₁ ^ (2 ^ k) + t₁) ^ (2 ^ k + 1) = 0 := by
          have hL : ((t₁ + 1) ^ d k + t₁ ^ d k + 1) * (t₁ ^ 2 + t₁) ^ (2 ^ k) = 0 := by
            unfold sVal at hs; simp_all +decide [ CharTwo.add_self_eq_zero ] ;
            rw [ zero_pow ( by linarith [ d_pos k hk ] ) ] ; simp +decide [ CharTwo.add_self_eq_zero ] ;
          rw [ ← mcm_identity k hk t₁ ] at * ; aesop;
        have := L_ker_trivial hcard k hcop ( t₁ ) ; simp_all +decide [ L ] ;
      · have h_mcm : ((t₁ + 1) ^ d k + t₁ ^ d k + 1) * (t₁ ^ 2 + t₁) ^ (2 ^ k) = (t₁ ^ (2 ^ k) + t₁) ^ (2 ^ k + 1) := by
          convert mcm_identity k hk t₁ using 1;
        have h_mcm : (t₁ ^ (2 ^ k) + t₁) ^ (2 ^ k + 1) = 0 := by
          unfold sVal at hs; simp_all +decide [ CharTwo.add_self_eq_zero ] ;
          rw [ zero_pow ( by linarith [ d_pos k hk ] ) ] at h_mcm ; simp_all +decide [ CharTwo.add_self_eq_zero ];
          rw [ eq_comm ] at h_mcm ; aesop;
        have := L_ker_trivial hcard k hcop ( t₁ ) ; simp_all +decide [ pow_succ' ] ;
        exact this ( by unfold L; linear_combination' h_mcm );
    · have ht1_ne_zero : t₁ ^ 2 + t₁ ≠ 0 := by grind +extAll
      have ht2_ne_zero : t₂ ^ 2 + t₂ ≠ 0 := by grind
      have hL1_ne_zero : t₁ ^ (2 ^ k) + t₁ ≠ 0 := by
        intro h; have := L_ker_trivial hcard k hcop t₁ h; simp_all +decide
      have hL2_ne_zero : t₂ ^ (2 ^ k) + t₂ ≠ 0 := by
        intro hL2_zero; have := L_ker_trivial hcard k hcop t₂ hL2_zero; aesop
      have h_cross_mult : (t₁ ^ (2 ^ k) + t₁) ^ (2 ^ k + 1) * (t₂ ^ 2 + t₂) ^ (2 ^ k) = (t₂ ^ (2 ^ k) + t₂) ^ (2 ^ k + 1) * (t₁ ^ 2 + t₁) ^ (2 ^ k) := by
        have := mcm_identity k hk t₁; have := mcm_identity k hk t₂; simp_all +decide [ sVal ]
        grind
      have := mcm_inj_core hcard k hk hcop hnodd hn t₁ t₂ ?_ ?_ ?_ ?_ h_cross_mult <;> simp_all +decide [ sq_add_eq_iff ]

end CollisionAnalysis