/-
# Fourth Moment Identity and Derivative Infrastructure

This module builds infrastructure connecting Walsh–Hadamard transform values
to derivative distributions, following the proof writing guide's approach of
decomposing into small, self-contained lemmas.

## Key results
- `derivCount`: the derivative distribution N_a(b)
- `derivCount_sum`: ∑_b N_a(b) = |F|
- `derivCount_even`: N_a(b) is always even for a ≠ 0
- `autocorr`: the autocorrelation R(t) = ∑_x χ(D_t f(x))
- `wht_sq_as_autocorr`: W_f(a)² = ∑_t χ(at)·R(t)
- `fourth_moment_eq_autocorr_sq`: ∑_a W_f(a)^4 = 2^n · ∑_t R(t)²

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*], §6.2
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Derivative distribution -/

/-- The derivative distribution: `N_f(a,b) = |{x : f(x+a) + f(x) = b}|`. -/
noncomputable def derivCount {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℕ :=
  (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card

/-- The sum ∑_b N_f(a,b) = |F|. -/
theorem derivCount_sum {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, derivCount f a b = Fintype.card (F2n n) := by
  unfold derivCount
  simp only [Finset.card_filter]
  rw [← Finset.card_univ]
  rw [Finset.sum_comm]
  simp

/-- ∑_b N_f(a,b) = 2^n (cast to ℤ). -/
theorem derivCount_sum_int {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, (derivCount f a b : ℤ) = (2 ^ n : ℤ) := by
  have h := derivCount_sum f a
  rw [F2n.card n hn] at h
  exact_mod_cast h

/-
Solutions come in pairs: if x solves D_a f(x) = b, so does x + a (in char 2).
-/
theorem derivCount_even {n : ℕ} (f : F2n n → F2n n) (a : F2n n) (ha : a ≠ 0)
    (b : F2n n) : Even (derivCount f a b) := by
  -- In characteristic 2, solutions come in pairs: if x solves D_a f(x) = b, so does x + a.
  have h_pair : ∀ x : F2n n, f (x + a) + f x = b → f ((x + a) + a) + f (x + a) = b := by
    grind;
  -- Define an involution ι(x) = x + a on the solution set; it has no fixed points (since a ≠ 0), so the set has even cardinality.
  have h_involution : ∃ s : Finset (F2n n), derivCount f a b = s.card ∧ ∀ x ∈ s, x + a ∈ s ∧ x ≠ x + a := by
    refine' ⟨ Finset.filter ( fun x => f ( x + a ) + f x = b ) Finset.univ, _, _ ⟩ <;> aesop;
  obtain ⟨ s, hs₁, hs₂ ⟩ := h_involution; rw [ hs₁ ] ;
  -- Since $s$ is a finite set, we can partition it into pairs $\{x, x+a\}$.
  have h_partition : ∃ t : Finset (Finset (F2n n)), (∀ x ∈ t, x.card = 2) ∧ (∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint x y) ∧ s = Finset.biUnion t id := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) s, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · grind +extAll;
    · ext x; aesop;
  obtain ⟨ t, ht₁, ht₂, rfl ⟩ := h_partition; rw [ Finset.card_biUnion ] <;> aesop;

/-! ### Autocorrelation -/

/-- The autocorrelation: `R(t) = ∑_x χ(f(x+t) + f(x))` -/
def autocorr {n : ℕ} (f : F2n n → F2n n) (t : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (f (x + t) + f x)

/-- R(0) = 2^n. -/
theorem autocorr_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    autocorr f (0 : F2n n) = (2 ^ n : ℤ) := by
  simp [autocorr, F2n.add_self, chi_zero, F2n.card n hn]

/-- The scaled autocorrelation: `R_c(t) = ∑_x χ(c · (f(x+t) + f(x)))` -/
def autocorrScaled {n : ℕ} (f : F2n n → F2n n) (c t : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (c * (f (x + t) + f x))

/-! ### WHT² as Fourier transform of autocorrelation -/

/-
Key identity: `W_f(a)² = ∑_t χ(at) · R(t)`.
-/
theorem wht_sq_as_autocorr {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    wht f a ^ 2 = ∑ t : F2n n, chi n (a * t) * autocorr f t := by
  unfold wht autocorr;
  simp +decide only [pow_two, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx; rw [ Finset.sum_mul _ _ _ ] ; refine' Finset.sum_bij ( fun y hy => y - x ) _ _ _ _ <;> simp +decide ; ring;
  · exact fun b => ⟨ b + x, by ring ⟩;
  · intro y; rw [ ← chi_add, ← chi_add ] ; ring;
    simp +decide [ sub_eq_add_neg, add_assoc ]

/-! ### Fourth moment = 2^n · ∑ R(t)² (Wiener-Khinchin) -/

/-
The Wiener-Khinchin identity:
    `∑_a W_f(a)^4 = 2^n · ∑_t R(t)²`.
-/
theorem fourth_moment_eq_autocorr_sq {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a ^ 4 = (2 ^ n : ℤ) * ∑ t : F2n n, autocorr f t ^ 2 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, ∑ t : F2n n, ∑ u : F2n n, chi n (a * (t + u)) * autocorr f t * autocorr f u = ∑ t : F2n n, ∑ u : F2n n, ∑ a : F2n n, chi n (a * (t + u)) * autocorr f t * autocorr f u := by
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  -- By the orthogonality relation, we know that $\sum_{a} \chi(a(t+u)) = 2^n$ if $t+u = 0$ and $0$ otherwise.
  have h_ortho : ∀ t u : F2n n, ∑ a : F2n n, chi n (a * (t + u)) = if t + u = 0 then (2 ^ n : ℤ) else 0 := by
    intro t u; split_ifs with h; simp_all +decide [ ← mul_add ] ;
    · rw [ F2n.card ] ; norm_num [ chi_zero ];
      assumption;
    · convert chi_orthogonality hn ( t + u ) h using 1;
      ac_rfl;
  convert h_fubini using 1;
  · refine' Finset.sum_congr rfl fun a ha => _;
    rw [ show wht f a ^ 4 = ( wht f a ^ 2 ) ^ 2 by ring, wht_sq_as_autocorr ];
    simp +decide only [mul_comm, pow_two, Finset.mul_sum _ _ _, mul_left_comm, mul_assoc];
    simp +decide only [← chi_add, mul_add];
  · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_ortho, sq ];
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, Finset.sum_ite, add_eq_zero_iff_eq_neg ]

/-! ### AB autocorrelation sum -/

/-- For AB functions: ∑_t R(t)² = 2 · (2^n)².
    Combines `ab_fourth_moment` and `fourth_moment_eq_autocorr_sq`. -/
theorem ab_autocorr_sq_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) :
    ∑ t : F2n n, autocorr f t ^ 2 = 2 * (2 ^ n : ℤ) ^ 2 := by
  have h4 := ab_fourth_moment hn f hf
  have hWK := fourth_moment_eq_autocorr_sq hn f
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  nlinarith

/-- For AB functions: ∑_{t≠0} R(t)² = (2^n)².
    Follows from ∑_t R(t)² = 2·(2^n)² and R(0)² = (2^n)². -/
theorem ab_autocorr_sq_nonzero_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) :
    ∑ t ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0), autocorr f t ^ 2 =
    (2 ^ n : ℤ) ^ 2 := by
  have h_total := ab_autocorr_sq_sum hn f hf
  have h_zero := autocorr_zero hn f
  have hsplit : ∑ t : F2n n, autocorr f t ^ 2 =
    autocorr f 0 ^ 2 + ∑ t ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0), autocorr f t ^ 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0)]
    congr 1
    apply Finset.sum_congr
    · ext x; simp [Finset.mem_erase]
    · intros; rfl
  rw [h_zero] at hsplit
  linarith

/-! ### Bound on autocorrelation -/

/-
|R(t)| ≤ 2^n for all t.
-/
theorem autocorr_abs_le {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (t : F2n n) :
    |autocorr f t| ≤ 2 ^ n := by
  convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| ?_ using 1;
  · infer_instance;
  · exact le_trans ( Finset.sum_le_sum fun _ _ => show |_| ≤ 1 by rw [ chi_abs ] ) ( by norm_num [ F2n.card n hn ] )

/-! ### Even distribution bound -/

/-
For even N(b) with ∑ N(b) = 2^n and ∑ N(b)² ≤ 2^{n+1}, each N(b) ≤ 2.
-/
theorem even_sum_sq_bound {n : ℕ} (hn : n ≠ 0)
    (N : F2n n → ℕ) (h_even : ∀ b, Even (N b))
    (h_sum : ∑ b : F2n n, N b = 2 ^ n)
    (h_sq : ∑ b : F2n n, (N b) ^ 2 ≤ 2 ^ (n + 1)) :
    ∀ b : F2n n, N b ≤ 2 := by
  contrapose! h_sq;
  obtain ⟨ b, hb ⟩ := h_sq;
  have h_contra : ∑ b, N b ^ 2 ≥ N b ^ 2 + 2 * (∑ b ∈ Finset.univ.erase b, N b) := by
    rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ b ) ];
    rw [ add_comm, Finset.mul_sum _ _ _ ];
    gcongr;
    by_cases hi : N ‹_› = 0;
    · norm_num [ hi ];
    · nlinarith only [ Nat.pos_of_ne_zero hi, show N ‹_› ≥ 2 from Nat.le_of_dvd ( Nat.pos_of_ne_zero hi ) ( even_iff_two_dvd.mp ( h_even _ ) ) ];
  rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ b ), pow_succ' ] at * ; nlinarith [ Nat.pow_le_pow_left hb 2 ]

end
end Kasami