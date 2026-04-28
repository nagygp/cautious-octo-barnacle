/-
# AB Implies APN — Decomposition for Power Functions

This module decomposes the proof that AB implies APN specifically for
power functions f(x) = x^d where gcd(d, 2^n - 1) = 1.

The key insight: for power functions, the derivative character sums
G_a(c) satisfy a symmetry G_a(c) = G_1(c·a^d), which makes
∑_b N_a(b)² constant across all a ≠ 0, enabling the bound N_a(b) ≤ 2.

## References
- Carlet (2021), Proposition 6.12
- Canteaut, Charpin, Dobbertin (2000), §4
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.APNFromAB

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Step 1: Power function derivative symmetry -/

/-
For the power function f(x) = x^d, the derivative character sum
    G_a(c) = ∑_x χ(c·(f(x+a)+f(x))) satisfies the scaling identity
    G_a(c) = G_1(c·a^d) when a ≠ 0 and gcd(d, 2^n-1) = 1.

    This follows from the substitution x → a·x, using
    (ax+a)^d + (ax)^d = a^d·((x+1)^d + x^d).
-/
theorem power_fn_deriv_charsum_scaling {n : ℕ} (d : ℕ) (hd : d ≠ 0)
    (a : F2n n) (ha : a ≠ 0) (c : F2n n) :
    ∑ x : F2n n, chi n (c * ((x + a) ^ d + x ^ d)) =
    ∑ x : F2n n, chi n (c * a ^ d * ((x + 1) ^ d + x ^ d)) := by
  -- Apply the substitution $x \to a * x$ to the sum.
  have h_subst : ∑ x : F2n n, chi n (c * ((x + a) ^ d + x ^ d)) = ∑ x : F2n n, chi n (c * ((a * x + a) ^ d + (a * x) ^ d)) := by
    have h_subst : Function.Bijective (fun x : F2n n => a * x) := by
      exact ⟨ mul_right_injective₀ ha, mul_left_surjective₀ ha ⟩;
    exact?;
  exact h_subst.trans ( Finset.sum_congr rfl fun x hx => by rw [ show ( a * x + a ) ^ d = a ^ d * ( x + 1 ) ^ d by rw [ ← mul_pow ] ; ring ] ; rw [ show ( a * x ) ^ d = a ^ d * x ^ d by rw [ mul_pow ] ] ; ring )

/-! ### Step 2: WHT reparametrization for power functions -/

/-
For the power function f(x) = x^d with gcd(d, 2^n-1)=1,
    the WHT of c·f satisfies: wht(c·f, a) = wht(f, a·c^{-e})
    where de ≡ 1 mod (2^n-1).

    In simpler terms: the AB property is inherited by scalar multiples.
-/
theorem power_fn_scaled_wht {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hcoprime : Nat.Coprime d (2^n - 1))
    (c : F2n n) (hc : c ≠ 0) (a : F2n n) :
    ∃ b : F2n n, (∑ x : F2n n, chi n (a * x + c * x ^ d)) =
                 (∑ x : F2n n, chi n (b * x + x ^ d)) := by
  obtain ⟨r, hr⟩ : ∃ r : F2n n, r ^ d = c := by
    -- Since $c \neq 0$, we can take $r = c^{e}$ where $e$ is the multiplicative inverse of $d$ modulo $2^n - 1$.
    obtain ⟨e, he⟩ : ∃ e : ℕ, d * e ≡ 1 [MOD (2 ^ n - 1)] := by
      have := Nat.exists_mul_mod_eq_one_of_coprime hcoprime;
      rcases k : 2 ^ n - 1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
      exact ⟨ _, this.choose_spec.2 ⟩;
    use c ^ e;
    rw [ ← pow_mul, mul_comm, ← Nat.mod_add_div ( d * e ) ( 2 ^ n - 1 ), he ];
    have h_order : c ^ (2 ^ n - 1) = 1 := by
      have h_order : c ^ (Fintype.card (F2n n) - 1) = 1 := by
        exact FiniteField.pow_card_sub_one_eq_one c hc;
      rwa [ F2n.card n hn ] at h_order;
    rcases k : 2 ^ n - 1 with ( _ | _ | k ) <;> simp_all +decide [ pow_add, pow_mul ];
  by_cases hr0 : r = 0;
  · aesop;
  · use a * r⁻¹;
    apply Finset.sum_bij (fun x _ => r * x);
    · simp;
    · aesop;
    · exact fun x _ => ⟨ r⁻¹ * x, Finset.mem_univ _, by rw [ mul_inv_cancel_left₀ hr0 ] ⟩;
    · simp +decide [ hr, mul_pow, mul_assoc, hr0 ]

/-
Scalar multiples of an AB power function are also AB.
-/
theorem power_fn_scaled_ab {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hcoprime : Nat.Coprime d (2^n - 1))
    (f : F2n n → F2n n) (hf_def : ∀ x, f x = x ^ d)
    (hab : IsAlmostBent f) (c : F2n n) (hc : c ≠ 0) :
    IsAlmostBent (fun x => c * f x) := by
  intro a
  obtain ⟨b, hb⟩ := power_fn_scaled_wht hn d hd hcoprime c hc a
  have h_abs : wht (fun x => c * f x) a ^ 2 = wht f b ^ 2 := by
    unfold wht; aesop;
  exact (by
  exact h_abs.symm ▸ hab b)

/-! ### Step 3: Wiener-Khinchin for scaled function -/

/-- For AB function g, the autocorrelation sum satisfies
    ∑_t R_g(t)² = 2·(2^n)². -/
theorem scaled_autocorr_sq_sum {n : ℕ} (hn : n ≠ 0)
    (g : F2n n → F2n n) (hg : IsAlmostBent g) :
    ∑ t : F2n n, (∑ x : F2n n, chi n (g (x + t) + g x)) ^ 2 =
    2 * (2 ^ n : ℤ) ^ 2 := by
  exact ab_autocorr_sq_sum hn g hg

/-! ### Step 4: Derivative sum bound from AB -/

/-
For each c ≠ 0 with c·f AB, ∑_{t≠0} G_t(c)² = 2^{2n}.
-/
theorem deriv_charsum_sq_sum_nonzero {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (c : F2n n) (hc : c ≠ 0)
    (h_ab_cf : IsAlmostBent (fun x => c * f x)) :
    ∑ t ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      (∑ x : F2n n, chi n (c * (f (x + t) + f x))) ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  convert ab_autocorr_sq_nonzero_sum hn ( fun x => c * f x ) h_ab_cf using 1;
  unfold autocorr; simp +decide [ mul_add ] ;

/-! ### Step 5: Constant ∑_b N_a(b)² for power functions -/

/-
For the Kasami power function with AB, ∑_b N_a(b)² = 2^{n+1}
    for all a ≠ 0.
-/
theorem kasami_deriv_sq_sum_eq {n : ℕ} (hn : n ≠ 0) (k : ℕ) (hk : k ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hab : IsAlmostBent (kasamiF n k))
    (a : F2n n) (ha : a ≠ 0) :
    ∑ b : F2n n, (derivCount (kasamiF n k) a b : ℤ) ^ 2 = 2 ^ (n + 1) := by
  -- By the properties of the Kasami function, we know that $\sum_{c \neq 0} G_a(c)^2$ is the same for all $a \neq 0$.
  have h_sum_eq : ∀ a b : F2n n, a ≠ 0 → b ≠ 0 → ∑ c ∈ Finset.univ.filter (· ≠ 0), (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 = ∑ c ∈ Finset.univ.filter (· ≠ 0), (∑ x : F2n n, chi n (c * (kasamiF n k (x + b) + kasamiF n k x))) ^ 2 := by
    intros a b ha hb
    have h_scale : ∀ c : F2n n, ∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x)) = ∑ x : F2n n, chi n (c * a ^ (kasamiExp k) * (kasamiF n k (x + 1) + kasamiF n k x)) := by
      intros c
      apply power_fn_deriv_charsum_scaling (kasamiExp k) (by
      exact?) a ha c;
    have h_scale_b : ∀ c : F2n n, ∑ x : F2n n, chi n (c * (kasamiF n k (x + b) + kasamiF n k x)) = ∑ x : F2n n, chi n (c * b ^ (kasamiExp k) * (kasamiF n k (x + 1) + kasamiF n k x)) := by
      intros c
      apply power_fn_deriv_charsum_scaling (kasamiExp k) (by
      exact?) b hb c;
    apply Finset.sum_bij (fun c hc => c * a ^ (kasamiExp k) / b ^ (kasamiExp k));
    · simp +contextual [ ha, hb, div_eq_mul_inv ];
    · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ha, hb ];
    · intro c hc; use c * b ^ kasamiExp k / a ^ kasamiExp k; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
      simp +decide [ mul_left_comm ( a ^ kasamiExp k ), mul_assoc, ha, hb ];
    · simp_all +decide [ mul_assoc, mul_div_cancel₀ ];
      simp +decide [ ← mul_assoc, div_mul_cancel₀ _ ( pow_ne_zero _ hb ) ];
  -- By the properties of the Kasami function, we know that $\sum_{a \neq 0} G_a(c)^2 = (2^n)^2$ for each $c \neq 0$.
  have h_sum_eq_c : ∀ c : F2n n, c ≠ 0 → ∑ a ∈ Finset.univ.filter (· ≠ 0), (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 = (2 ^ n : ℤ) ^ 2 := by
    intros c hc_nonzero
    have h_sum_eq_c_step : IsAlmostBent (fun x => c * kasamiF n k x) := by
      apply power_fn_scaled_ab hn (kasamiExp k) (by
      exact Nat.ne_of_gt ( kasamiExp_pos k )) (by
      exact?) (kasamiF n k) (by
      exact?) hab c hc_nonzero;
    convert deriv_charsum_sq_sum_nonzero hn ( fun x => kasamiF n k x ) c hc_nonzero h_sum_eq_c_step using 1;
  -- By combining the results from h_sum_eq and h_sum_eq_c, we can conclude that $\sum_{c \neq 0} G_a(c)^2 = (2^n)^2$ for any $a \neq 0$.
  have h_sum_eq_final : ∀ a : F2n n, a ≠ 0 → ∑ c ∈ Finset.univ.filter (· ≠ 0), (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 = (2 ^ n : ℤ) ^ 2 := by
    intros a ha
    have h_sum_eq_final : ∑ c ∈ Finset.univ.filter (· ≠ 0), ∑ a ∈ Finset.univ.filter (· ≠ 0), (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 = (2 ^ n - 1) * (2 ^ n : ℤ) ^ 2 := by
      rw [ Finset.sum_congr rfl fun c hc => h_sum_eq_c c <| Finset.mem_filter.mp hc |>.2 ] ; norm_num [ Finset.filter_ne' ];
      rw [ Nat.cast_sub ] <;> norm_num [ F2n.card n hn ];
      exact?;
    have h_sum_eq_final : ∑ c ∈ Finset.univ.filter (· ≠ 0), ∑ a ∈ Finset.univ.filter (· ≠ 0), (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 = (2 ^ n - 1) * ∑ c ∈ Finset.univ.filter (· ≠ 0), (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 := by
      rw [ Finset.sum_comm ];
      rw [ Finset.sum_congr rfl fun x hx => h_sum_eq x a ( Finset.mem_filter.mp hx |>.2 ) ha ] ; norm_num [ Finset.filter_ne' ];
      rw [ Nat.cast_sub ( Fintype.card_pos ) ] ; norm_num [ Kasami.F2n.card n hn ] ; ring;
    nlinarith [ Nat.pow_le_pow_right two_pos ( Nat.pos_of_ne_zero hn ) ];
  have h_sum_eq_final : ∑ c : F2n n, (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 = (2 ^ n : ℤ) ^ 2 + (2 ^ n : ℤ) ^ 2 := by
    convert congr_arg ( · + ( 2 ^ n ) ^ 2 ) ( h_sum_eq_final a ha ) using 1;
    simp +decide [ Finset.filter_ne', Finset.sum_erase ];
    rw [ show ( Fintype.card ( F2n n ) : ℤ ) = 2 ^ n by exact_mod_cast F2n.card n hn ] ; norm_num [ chi_zero ];
  have := deriv_parseval hn ( kasamiF n k ) a;
  exact mul_left_cancel₀ ( pow_ne_zero n two_ne_zero ) ( by rw [ h_sum_eq_final ] at this; ring_nf at this ⊢; linarith )

/-! ### Step 6: APN from constant derivative sum -/

/-- Given ∑_b N_a(b)² = 2^{n+1} and N_a(b) even, N_a(b) ≤ 2. -/
theorem apn_from_deriv_sq {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n)
    (a : F2n n) (ha : a ≠ 0)
    (h_even : ∀ b, Even (derivCount f a b))
    (h_sum : ∑ b : F2n n, derivCount f a b = 2 ^ n)
    (h_sq : ∑ b : F2n n, (derivCount f a b) ^ 2 ≤ 2 ^ (n + 1)) :
    ∀ b : F2n n, derivCount f a b ≤ 2 := by
  exact even_sum_sq_bound hn _ h_even h_sum h_sq

/-- The Kasami function with the AB property is APN. -/
theorem ab_implies_apn {n : ℕ} (hn : n ≠ 0) (k : ℕ) (hk : k ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hab : IsAlmostBent (kasamiF n k)) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2 := by
  intro a ha b
  have h_even := derivCount_even (kasamiF n k) a ha
  have h_sum := derivCount_sum (kasamiF n k) a
  rw [F2n.card n hn] at h_sum
  have h_sq_sum := kasami_deriv_sq_sum_eq hn k hk hn_odd hgcd hab a ha
  have h_sq_le : ∑ b : F2n n, (derivCount (kasamiF n k) a b) ^ 2 ≤ 2 ^ (n + 1) := by
    exact_mod_cast h_sq_sum.le
  exact apn_from_deriv_sq hn _ a ha h_even h_sum h_sq_le b

end
end Kasami