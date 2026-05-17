/-
# Two-Parameter Walsh Transform and Full AB Theory

For the Kasami function (power function), the one-parameter AB condition
is equivalent to the full (two-parameter) AB condition, which implies APN.

## Main results

* `wht2` : Two-parameter Walsh–Hadamard transform
* `wht2_parseval_full` : ∑_a ∑_b W_f(a,b)² = (2^n)³
* `scaled_fn_isAlmostBent` : Full AB implies each component is AB
* `derivCount_sq_ge_two_pow` : Even-constraint lower bound on ∑ N_a(c)²
* `fullAB_implies_apn` : Full AB condition implies APN

## References

* Carlet, *Boolean Functions for Cryptography and Coding Theory*, §6.2
* Chabaud, Vaudenay (1995)
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.APNFromAB

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### §1 Two-parameter Walsh transform -/

/-- The two-parameter Walsh–Hadamard transform:
    W_f(a, b) = ∑_x χ(a·x + b·f(x)). -/
def wht2 {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (a * x + b * f x)

/-- The one-parameter WHT is wht2 at b = 1. -/
theorem wht_eq_wht2 {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    wht f a = wht2 f a 1 := by
  simp [wht, wht2]

/-- wht2 f a 0 reduces to a character sum of x. -/
theorem wht2_zero_b {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    wht2 f a 0 = if a = 0 then (2 ^ n : ℤ) else 0 := by
  simp [wht2]; exact chi_sum hn a

/-- For fixed b, wht2 f · b equals wht of the function b·f. -/
theorem wht2_eq_wht_scale {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) :
    wht2 f a b = wht (fun x => b * f x) a := by
  simp [wht2, wht]

/-! ### §2 Full AB condition -/

/-- The **full** Almost Bent condition: for all b ≠ 0, W_f(a,b)² ∈ {0, 2^{n+1}}. -/
def IsAlmostBentFull {n : ℕ} (f : F2n n → F2n n) : Prop :=
  ∀ (a b : F2n n), b ≠ 0 →
    wht2 f a b ^ 2 = 0 ∨ wht2 f a b ^ 2 = (2 ^ (n + 1) : ℤ)

/-- One-parameter AB implies full AB for the b=1 component. -/
theorem isAlmostBent_implies_component {n : ℕ} (f : F2n n → F2n n)
    (hf : IsAlmostBent f) (a : F2n n) :
    wht2 f a 1 ^ 2 = 0 ∨ wht2 f a 1 ^ 2 = (2 ^ (n + 1) : ℤ) := by
  rw [← wht_eq_wht2]; exact hf a

/-! ### §3 Two-parameter Parseval -/

/-- **Two-parameter Parseval**: ∑_a ∑_b W_f(a,b)² = (2^n)³.
    Each fixed b gives ∑_a W_f(a,b)² = (2^n)², and there are 2^n values of b. -/
theorem wht2_parseval_full {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, ∑ b : F2n n, wht2 f a b ^ 2 = (2 ^ n : ℤ) ^ 3 := by
  rw [Finset.sum_comm]
  have h_parseval : ∀ b : F2n n, ∑ a : F2n n, (wht2 f a b) ^ 2 = (2 ^ n : ℤ) ^ 2 := by
    intro b
    convert wht_parseval hn (fun x => b * f x) using 1
  simp only [h_parseval, Finset.sum_const, Finset.card_univ]
  rw [F2n.card n hn]; push_cast; ring

/-! ### §4 Key helper lemma: Full AB implies each component is AB -/

/-- If `f` is fully AB, then for `b ≠ 0`, the scaled function `b·f` is almost bent
    (in the one-parameter sense). -/
theorem scaled_fn_isAlmostBent {n : ℕ} (f : F2n n → F2n n)
    (hf : IsAlmostBentFull f) (b : F2n n) (hb : b ≠ 0) :
    IsAlmostBent (fun x => b * f x) := by
  intro a
  rw [show wht (fun x => b * f x) a = wht2 f a b from (wht2_eq_wht_scale f a b).symm]
  exact hf a b hb

/-! ### §5 Even-constraint lower bound -/

/-- If N is even and positive, then N² ≥ 2·N. -/
theorem even_pos_sq_ge_double (N : ℕ) (heven : Even N) (hpos : 0 < N) :
    2 * N ≤ N ^ 2 := by
  obtain ⟨m, rfl⟩ := heven
  have : m ≥ 1 := by omega
  nlinarith

/-
If all `N(c)` are even with `∑_c N(c) = 2^n`, then `∑_c N(c)² ≥ 2^{n+1}`.
    Proof: each nonzero N(c) ≥ 2, so N(c)² ≥ 2·N(c). Summing gives ∑N² ≥ 2·∑N = 2^{n+1}.
-/
theorem derivCount_sq_ge_two_pow {n : ℕ} (hn : n ≠ 0)
    (N : F2n n → ℕ) (h_even : ∀ c, Even (N c))
    (h_sum : ∑ c : F2n n, N c = 2 ^ n) :
    2 ^ (n + 1) ≤ ∑ c : F2n n, N c ^ 2 := by
  have h_sum_sq_ge_double_sum : ∑ c, N c ^ 2 ≥ 2 * ∑ c, N c := by
    rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun c _ => if h : N c = 0 then by simp +decide [ h ] else by nlinarith only [ Nat.pos_of_ne_zero h, even_pos_sq_ge_double ( N c ) ( h_even c ) ( Nat.pos_of_ne_zero h ) ] ;
  convert h_sum_sq_ge_double_sum.le using 1 ; rw [ h_sum ] ; ring

/-! ### §6 Total second moment computation -/

/-- The autocorrelation of a scaled function equals the derivative character sum. -/
theorem autocorr_scaled_eq {n : ℕ} (f : F2n n → F2n n) (b a : F2n n) :
    autocorr (fun x => b * f x) a =
    ∑ x : F2n n, chi n (b * (f (x + a) + f x)) := by
  simp [autocorr, mul_add]

/-
The derivative character sum squared, summed over all b, equals
    2^n times the second moment of the derivative distribution.
    This is deriv_parseval rewritten in terms of autocorrelation.
-/
theorem deriv_parseval_as_autocorr {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    (2 ^ n : ℤ) * ∑ c : F2n n, (derivCount f a c : ℤ) ^ 2 =
    ∑ b : F2n n, (autocorr (fun x => b * f x) a) ^ 2 := by
  convert deriv_parseval hn f a using 3;
  -- By definition of autocorrelation, we have:
  apply autocorr_scaled_eq

/-- For each b ≠ 0 and fullAB f, ∑_{a≠0} autocorr(b·f, a)² = (2^n)².
    From ab_autocorr_sq_sum: ∑_a autocorr² = 2·(2^n)² and autocorr(0)² = (2^n)². -/
theorem ab_autocorr_sq_nonzero_sum_scaled {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hf : IsAlmostBentFull f) (b : F2n n) (hb : b ≠ 0) :
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      autocorr (fun x => b * f x) a ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  exact ab_autocorr_sq_nonzero_sum hn _ (scaled_fn_isAlmostBent f hf b hb)

/-- The autocorrelation of the zero-scaled function (b=0) is always 2^n. -/
theorem autocorr_zero_scaled {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    autocorr (fun _ : F2n n => (0 : F2n n)) a = (2 ^ n : ℤ) := by
  simp [autocorr, chi_zero, F2n.card n hn]

/-
Total second moment: ∑_{a≠0} ∑_c N_a(c)² = (2^n - 1)·2^{n+1}.
    This is the key quantitative step for fullAB → APN.
-/
theorem total_deriv_sq_eq {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBentFull f) :
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      ∑ c : F2n n, (derivCount f a c : ℤ) ^ 2 =
    ((2 ^ n : ℤ) - 1) * 2 ^ (n + 1) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a ∈ Finset.univ.filter (fun a => a ≠ 0), ∑ b : F2n n, (autocorr (fun x => b * f x) a) ^ 2 = ∑ b : F2n n, ∑ a ∈ Finset.univ.filter (fun a => a ≠ 0), (autocorr (fun x => b * f x) a) ^ 2 := by
    exact Finset.sum_comm;
  -- For $b = 0$, we have $\sum_{a \neq 0} (autocorr (fun x => 0 * f x) a)^2 = (2^n - 1) * (2^n)^2$.
  have h_zero : ∑ a ∈ Finset.univ.filter (fun a => a ≠ 0), (autocorr (fun x => (0 : F2n n) * f x) a) ^ 2 = (2 ^ n - 1) * (2 ^ n) ^ 2 := by
    have h_zero : ∀ a : F2n n, a ≠ 0 → autocorr (fun x => (0 : F2n n) * f x) a = (2 ^ n : ℤ) := by
      intros a ha
      simp [autocorr];
      rw [ F2n.card n hn, chi_zero ] ; norm_num;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ h_zero x ( Finset.mem_filter.mp hx |>.2 ) ] ] ; norm_num [ Finset.filter_ne' ];
    rw [ Nat.cast_sub ] <;> norm_num [ F2n.card n hn ];
    exact?;
  -- For $b \neq 0$, we have $\sum_{a \neq 0} (autocorr (fun x => b * f x) a)^2 = (2^n)^2$.
  have h_nonzero : ∀ b : F2n n, b ≠ 0 → ∑ a ∈ Finset.univ.filter (fun a => a ≠ 0), (autocorr (fun x => b * f x) a) ^ 2 = (2 ^ n) ^ 2 := by
    exact?;
  -- By combining the results from h_fubini, h_zero, and h_nonzero, we get the desired equality.
  have h_combined : ∑ a ∈ Finset.univ.filter (fun a => a ≠ 0), ∑ b : F2n n, (autocorr (fun x => b * f x) a) ^ 2 = (2 ^ n - 1) * (2 ^ n) ^ 2 + (2 ^ n - 1) * (2 ^ n) ^ 2 := by
    rw [ h_fubini, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ ( 0 : F2n n ) ) ];
    rw [ Finset.sum_congr rfl fun x hx => h_nonzero x <| by simpa using hx ] ; norm_num [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ, F2n.card n hn ];
    convert h_zero using 1;
    norm_num [ autocorr ];
  have h_final : (2 ^ n : ℤ) * ∑ a ∈ Finset.univ.filter (fun a => a ≠ 0), ∑ c : F2n n, (derivCount f a c : ℤ) ^ 2 = (2 ^ n - 1) * (2 ^ n) ^ 2 + (2 ^ n - 1) * (2 ^ n) ^ 2 := by
    rw [ ← h_combined, Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun x hx => deriv_parseval_as_autocorr hn f x;
  exact mul_left_cancel₀ ( pow_ne_zero n two_ne_zero ) ( by linear_combination' h_final )

/-! ### §7 Full AB → APN -/

/-
**Full AB implies APN**: proof that the full (two-parameter) AB condition
    implies differential uniformity ≤ 2.

    **Proof strategy:**
    1. From evenness: ∑_c N_a(c)² ≥ 2^{n+1} for each a ≠ 0
    2. From fullAB: ∑_{a≠0} ∑_c N_a(c)² = (2^n - 1)·2^{n+1}
    3. Since there are 2^n - 1 terms each ≥ 2^{n+1} summing to (2^n-1)·2^{n+1},
       each term equals 2^{n+1}
    4. By even_sum_sq_bound: N_a(c) ≤ 2
-/
theorem fullAB_implies_apn {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBentFull f) :
    ∀ a : F2n n, a ≠ 0 → ∀ c : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = c).card ≤ 2 := by
  -- By combining the results from `derivCount_sq_ge_two_pow`, `total_deriv_sq_eq`, and `even_sum_sq_bound`,
  -- we can conclude that for any nonzero `a`, `N_a(c) ≤ 2`.
  intros a ha c
  have h_even : Even (Finset.card (Finset.filter (fun x => f (x + a) + f x = c) Finset.univ)) := by
    convert derivCount_even f a ha c using 1;
  have h_sum : ∑ c : F2n n, (Finset.card (Finset.filter (fun x => f (x + a) + f x = c) Finset.univ)) ^ 2 = 2 ^ (n + 1) := by
    have h_total_deriv_sq_eq : ∑ a ∈ Finset.univ.filter (fun a => a ≠ 0), (∑ c : F2n n, (Finset.card (Finset.filter (fun x => f (x + a) + f x = c) (Finset.univ : Finset (F2n n)))) ^ 2) = ((2 ^ n : ℤ) - 1) * 2 ^ (n + 1) := by
      convert total_deriv_sq_eq hn f hf using 1;
      norm_cast;
    have h_each_term_eq : ∀ a ∈ Finset.univ.filter (fun a => a ≠ 0), ∑ c : F2n n, (Finset.card (Finset.filter (fun x => f (x + a) + f x = c) (Finset.univ : Finset (F2n n)))) ^ 2 ≥ 2 ^ (n + 1) := by
      intros a ha
      apply derivCount_sq_ge_two_pow hn (fun c => Finset.card (Finset.filter (fun x => f (x + a) + f x = c) Finset.univ)) (fun c => derivCount_even f a (by
      exact Finset.mem_filter.mp ha |>.2) c) (by
      convert derivCount_sum f a using 1;
      exact F2n.card n hn ▸ rfl);
    have h_each_term_eq : ∀ a ∈ Finset.univ.filter (fun a => a ≠ 0), ∑ c : F2n n, (Finset.card (Finset.filter (fun x => f (x + a) + f x = c) (Finset.univ : Finset (F2n n)))) ^ 2 = 2 ^ (n + 1) := by
      contrapose! h_total_deriv_sq_eq;
      have h_card : Finset.card (Finset.univ.filter (fun a : F2n n => a ≠ 0)) = 2 ^ n - 1 := by
        simp +decide [ Finset.filter_ne', Finset.card_univ, F2n.card n hn ];
      have h_card : ∑ a ∈ Finset.univ.filter (fun a : F2n n => a ≠ 0), (∑ c : F2n n, (Finset.card (Finset.filter (fun x => f (x + a) + f x = c) (Finset.univ : Finset (F2n n)))) ^ 2) > ∑ a ∈ Finset.univ.filter (fun a : F2n n => a ≠ 0), 2 ^ (n + 1) := by
        exact Finset.sum_lt_sum ( fun x hx => h_each_term_eq x hx ) ⟨ h_total_deriv_sq_eq.choose, h_total_deriv_sq_eq.choose_spec.1, lt_of_le_of_ne ( h_each_term_eq _ h_total_deriv_sq_eq.choose_spec.1 ) ( Ne.symm h_total_deriv_sq_eq.choose_spec.2 ) ⟩;
      simp_all +decide [ Finset.sum_const, nsmul_eq_mul ];
      norm_cast;
      grind +splitImp;
    exact h_each_term_eq a ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ha ⟩ );
  -- Apply the lemma `even_sum_sq_bound` to conclude that $N_a(c) \leq 2$.
  apply even_sum_sq_bound hn (fun c => (Finset.card (Finset.filter (fun x => f (x + a) + f x = c) Finset.univ))) (fun c => by
    convert derivCount_even f a ha c using 1) (by
  convert derivCount_sum f a using 1;
  exact?) (by
  exact h_sum.le) c

end
end Kasami