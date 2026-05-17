/-
# Two-Parameter Walsh Transform and Full AB Theory

For the Kasami function (power function), the one-parameter AB condition
is equivalent to the full (two-parameter) AB condition, which implies APN.

## Main results

* `wht2` : Two-parameter Walsh–Hadamard transform
* `wht2_parseval_full` : ∑_a ∑_b W_f(a,b)² = (2^n)³
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

/-! ### §4 Derivative-WHT connection -/

/-- The derivative Parseval for component function b·f:
    2^n · ∑_c N_a(c)² = ∑_d (∑_x χ(d·b·D_a f(x)))².

    This extends deriv_parseval to the b·f case. -/
theorem deriv_parseval_scaled {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (b a : F2n n) :
    (2 ^ n : ℤ) * ∑ c : F2n n, (derivCount (fun x => b * f x) a c : ℤ) ^ 2 =
    ∑ d : F2n n, (∑ x : F2n n, chi n (d * (b * f (x + a) + b * f x))) ^ 2 := by
  exact deriv_parseval hn (fun x => b * f x) a

/-! ### §5 Full AB → APN -/

/-- **Full AB implies APN**: proof that the full (two-parameter) AB condition
    implies differential uniformity ≤ 2.

    Proof sketch: For each b ≠ 0, the function g_b = b·f is "almost bent" in the
    one-parameter sense (W_{g_b}(a)² ∈ {0, 2^{n+1}}). This gives
    ∑_t R_{g_b}(t)² = 2·(2^n)² for each b ≠ 0. Summing over b gives control
    over ∑_b ∑_t R_{g_b}(t)² which bounds ∑_c N_a(c)² via deriv_parseval. -/
theorem fullAB_implies_apn {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBentFull f) :
    ∀ a : F2n n, a ≠ 0 → ∀ c : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = c).card ≤ 2 := by
  sorry

end
end Kasami
