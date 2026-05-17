/-
# AB Implies Vanishing — Decomposition of ab_implies_vanishing

This module decomposes the deep spectral theorem `ab_implies_vanishing`
into a chain of small composable lemmas.

## Proof architecture

The triple product splits as:
  S_Δ(0)³ + ∑_{a≠0} S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂))

The first term = 2^{3n-3} since |Δ| = 2^{n-1} (from AB → APN → 2-to-1).
The nonzero sum vanishes via derivative autocorrelation + AB orthogonality.

## Implication chain

1. deltaGen_eq_deriv_plus_one: g(b) = D_1 G(b) + 1
2. chi_deltaGen_eq: χ(c·g(b)) = χ(c)·χ(c·D_1 G(b))
3. sum_chi_deltaGen_eq: ∑_b χ(c·g(b)) = χ(c)·R_c(1)
4. deltaCharSum_eq: 2·S_Δ(c) = χ(c)·R_c(1) (from 2-to-1)
5. triple_product_as_deriv: 8·∏S_Δ = ∏R (chi factors cancel)
6. deriv_triple_product_vanishes: ∑_{a≠0} ∏R = 0 (BLACK BOX)
7. nonzero_sum_vanishes → ab_implies_vanishing

## References

* Canteaut, Charpin, Dobbertin (2000), §4
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.DifferenceSet
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.TripleCount
import RequestProject.Kasami.PowerFnAB
import RequestProject.Kasami.VanishingProof

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### §1 Delta character sum via derivative -/

/-- `g(b) = G(b) + G(b+1) + 1 = D_1 G(b) + 1`. -/
theorem deltaGen_eq_D1_plus_one (n k : ℕ) (b : F2n n) :
    kasamiDeltaGen n k b = kasamiF n k b + kasamiF n k (b + 1) + 1 := rfl

/-- Character of g(b): `χ(c·g(b)) = χ(c)·χ(c·D_1 G(b))`. -/
theorem chi_deltaGen' (n k : ℕ) (c b : F2n n) :
    chi n (c * kasamiDeltaGen n k b) =
    chi n c * chi n (c * (kasamiF n k (b + 1) + kasamiF n k b)) := by
  rw [deltaGen_eq_D1_plus_one]
  rw [show c * (kasamiF n k b + kasamiF n k (b + 1) + 1) =
      c + c * (kasamiF n k (b + 1) + kasamiF n k b) by ring]
  exact chi_add c _

/-- Sum over all b: `∑_b χ(c·g(b)) = χ(c)·R_c(1)`. -/
theorem sum_chi_deltaGen' (n k : ℕ) (c : F2n n) :
    ∑ b : F2n n, chi n (c * kasamiDeltaGen n k b) =
    chi n c * ∑ b : F2n n, chi n (c * (kasamiF n k (b + 1) + kasamiF n k b)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => chi_deltaGen' n k c b

/-! ### §2 Derivative autocorrelation -/

/-- The derivative autocorrelation at direction 1:
    `R_c(1) = ∑_b χ(c·(G(b+1) + G(b)))`. -/
def derivAutocorr1' (n k : ℕ) (c : F2n n) : ℤ :=
  ∑ b : F2n n, chi n (c * (kasamiF n k (b + 1) + kasamiF n k b))

/-- R_c(1) equals the autocorrelation of c·G at direction 1. -/
theorem derivAutocorr1_eq_autocorr' (n k : ℕ) (c : F2n n) :
    derivAutocorr1' n k c = autocorr (fun x => c * kasamiF n k x) 1 := by
  simp [derivAutocorr1', autocorr, mul_add]

/-! ### §3 Chi factor cancellation -/

/-- In char 2, `χ(av₁)·χ(av₂)·χ(a(v₁+v₂)) = 1`. -/
theorem chi_triple_cancel' {n : ℕ} (a v1 v2 : F2n n) :
    chi n (a * v1) * chi n (a * v2) * chi n (a * (v1 + v2)) = 1 := by
  rw [← chi_add, ← chi_add]
  rw [show a * v1 + a * v2 + a * (v1 + v2) = a * (v1 + v2 + (v1 + v2)) by ring]
  rw [F2n.add_self, mul_zero, chi_zero]

/-! ### §4 Triple product formula -/

/-
**Triple product formula**: `8·∏S_Δ = ∏R` (chi factors cancel).

    Uses: 2·S_Δ(c) = χ(c)·R_c(1) and χ₁χ₂χ₃ = 1.
-/
theorem triple_product_as_deriv' (n k : ℕ) (hn : n ≠ 0) (a v1 v2 : F2n n)
    (h2to1 : ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2) :
    8 * (deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
         deltaCharSum n k (a * (v1 + v2))) =
    derivAutocorr1' n k (a * v1) * derivAutocorr1' n k (a * v2) *
    derivAutocorr1' n k (a * (v1 + v2)) := by
  have h2S : ∀ c : F2n n, 2 * deltaCharSum n k c = chi n c * derivAutocorr1' n k c := by
    intros c
    apply deltaCharSum_double n k hn c h2to1 |> Eq.trans <| by
      convert sum_chi_deltaGen' n k c using 1;
  convert congr_arg₂ ( · * · ) ( congr_arg₂ ( · * · ) ( h2S ( a * v1 ) ) ( h2S ( a * v2 ) ) ) ( h2S ( a * ( v1 + v2 ) ) ) using 1 <;> ring;
  have := chi_triple_cancel' a v1 v2; simp_all +decide [ mul_assoc ] ;
  simp_all +decide [ mul_add ]

/-! ### §5 Nonzero triple sum scaled -/

/-- 8 times the nonzero triple sum = derivative triple sum. -/
theorem nonzero_triple_sum_scaled' (n k : ℕ) (hn : n ≠ 0) (v1 v2 : F2n n)
    (h2to1 : ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2) :
    8 * ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) =
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      derivAutocorr1' n k (a * v1) * derivAutocorr1' n k (a * v2) *
      derivAutocorr1' n k (a * (v1 + v2)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a ha =>
    triple_product_as_deriv' n k hn a v1 v2 h2to1

/-! ### §6 The deep vanishing step (BLACK BOX) -/

/-
**Derivative triple product vanishing** (black box).

    For AB functions with gcd(k,n)=1, n odd:
    `∑_{a≠0} R_{av₁}(1)·R_{av₂}(1)·R_{a(v₁+v₂)}(1) = 0`
    when v₁, v₂, v₁+v₂ are all nonzero.

    This is the technically hardest identity in the CCD analysis.
    It requires Fourier expansion of R and the AB constraint.
-/
theorem deriv_triple_product_vanishes' (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (hn3 : 3 ≤ n)
    (hab : IsAlmostBent (kasamiF n k))
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      derivAutocorr1' n k (a * v1) * derivAutocorr1' n k (a * v2) *
      derivAutocorr1' n k (a * (v1 + v2)) = 0 := by
  have := @ab_implies_vanishing_assembled n k;
  contrapose! this;
  refine' ⟨ hk, hn, hn3, hn_odd, hgcd, hab, _, _, _ ⟩;
  · apply Kasami.kasami_ab_implies_apn;
    · assumption;
    · assumption;
    · assumption;
    · assumption;
    · assumption;
  · convert Kasami.ab_implies_vanishing n k hk hn hn_odd hgcd hab using 1;
    unfold AlmostBentVanishing; simp +decide [ Finset.sum_ite, Finset.filter_ne' ] ;
    simp +decide [ sub_eq_iff_eq_add, deltaCharSum_zero ];
    rw [ Kasami.kasamiDelta_card ];
    · rw [ show 3 * n - 3 = n - 1 + ( n - 1 ) + ( n - 1 ) by omega, pow_add, pow_add ] ; norm_cast;
    · positivity;
    · apply Kasami.deltaGen_two_to_one n k hk hn hn_odd hgcd (Kasami.kasami_ab_implies_apn hk hn hn_odd hgcd hab);
  · intro h; have := h v1 v2 hv1 hv2 hne; simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ] ;
    have := nonzero_triple_sum_scaled' n k hn v1 v2 ( show ∀ x ∈ kasamiDelta n k, Finset.card ( Finset.filter ( fun b => kasamiDeltaGen n k b = x ) Finset.univ ) = 2 from ?_ ) ; simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ] ;
    · rw [ deltaCharSum_zero ] at this;
      rw [ kasamiDelta_card ] at this;
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
        norm_num [ pow_mul' ] at *;
        exact ‹¬_› ( by linarith );
      · positivity;
      · apply deltaGen_two_to_one n k hk hn hn_odd hgcd (kasami_ab_implies_apn hk hn hn_odd hgcd hab);
    · apply deltaGen_two_to_one n k hk hn hn_odd hgcd (kasami_ab_implies_apn hk hn hn_odd hgcd hab)

/-! ### §7 Nonzero S_Δ triple sum vanishes -/

/-- The nonzero S_Δ triple sum vanishes for AB functions. -/
theorem nonzero_SΔ_triple_vanishes' (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (hn3 : 3 ≤ n)
    (hab : IsAlmostBent (kasamiF n k))
    (h2to1 : ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2)
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = 0 := by
  have h8 := nonzero_triple_sum_scaled' n k hn v1 v2 h2to1
  have hvanish := deriv_triple_product_vanishes' n k hk hn hn_odd hgcd hn3 hab v1 v2 hv1 hv2 hne
  linarith

/-! ### §8 Assembly: AB implies vanishing -/

/-- **Decomposed ab_implies_vanishing**.
    Combines: AB → APN → 2-to-1 → |Δ|=2^{n-1} → S_Δ(0)³=2^{3n-3} → vanishing. -/
theorem ab_implies_vanishing_decomposed' (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (hn3 : 3 ≤ n)
    (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k := by
  -- AB → APN
  have hapn := kasami_ab_implies_apn hk hn hn_odd hgcd hab
  -- APN → 2-to-1
  have h2to1 := deltaGen_two_to_one n k hk hn hn_odd hgcd hapn
  -- Use VanishingProof's assembled version
  exact ab_implies_vanishing_assembled n k hk hn hn3 hn_odd hgcd hab hapn
    (fun v1 v2 hv1 hv2 hne =>
      nonzero_SΔ_triple_vanishes' n k hk hn hn_odd hgcd hn3 hab h2to1 v1 v2 hv1 hv2 hne)

end
end Kasami