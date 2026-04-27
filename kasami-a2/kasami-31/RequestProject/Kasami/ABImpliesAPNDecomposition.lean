/-
# Decomposition of `ab_deriv_char_sum_sq_nonzero_le`

## Goal

Prove: for an AB power function `f(x) = x^d` (with `gcd(d, 2^n-1) = 1`) and `a ≠ 0`:
    `∑_{c ≠ 0} S(c,a)² ≤ (2^n)²`
where `S(c,a) = ∑_x χ(c · (f(x+a) + f(x)))`.

## Why the general statement is insufficient

The original `ab_deriv_char_sum_sq_nonzero_le` in `ABImpliesAPN.lean` is stated for
*any* `IsAlmostBent f`. However, the AB property as defined (`∀ a, wht f a ^ 2 ∈ {0, 2^{n+1}}`)
only constrains the Walsh spectrum of the component function `x ↦ Tr(f(x))`.
The inequality involves `S(c,a)` for ALL nonzero `c`, which involves Tr(c·f(x)) —
a different component function for each `c`.

For a **power function** `f(x) = x^d` with `gcd(d, 2^n-1) = 1`, the substitution
`x ↦ c^{1/(d)} · x` shows that all component functions have the same Walsh spectrum,
so the AB property propagates to all components. This is the key structural
property that makes the proof work.

## Proof outline (for power functions)

1. **Substitution**: For `f(x) = x^d` and `a ≠ 0`, substitute `x = a·y`:
   `D_a f(x) = (x+a)^d + x^d = a^d · ((y+1)^d + y^d) = a^d · D_1 f(y)`

2. **Character sum**: `S(c,a) = ∑_x χ(c·D_a f(x)) = ∑_y χ((c·a^d)·D_1 f(y)) = T(c·a^d)`
   where `T(m) = ∑_y χ(m · D_1 f(y))`.

3. **Bijection on c**: Since `a ≠ 0`, the map `c ↦ c·a^d` is a bijection on `F*`.
   So `∑_{c≠0} S(c,a)² = ∑_{c≠0} T(c·a^d)² = ∑_{m≠0} T(m)²`.

4. **Bijection on a**: Since `gcd(d, 2^n-1) = 1`, the map `a ↦ a^d` bijects `F*`.
   For `c = 1`: `S(1,a) = T(a^d)`, so `∑_{a≠0} S(1,a)² = ∑_{m≠0} T(m)²`.

5. **Autocorrelation link**: `S(1,a) = R(a) = autocorr f a` (by definition).
   By `ab_autocorr_sq_nonzero_sum`: `∑_{a≠0} R(a)² = (2^n)²`.

6. **Assembly**: `∑_{c≠0} S(c,a)² = ∑_{m≠0} T(m)² = ∑_{a≠0} R(a)² = (2^n)² ≤ (2^n)²`. ✓

## Reused lemmas (already proved)

| Lemma | File | Used in |
|-------|------|---------|
| `ab_autocorr_sq_nonzero_sum` | `FourthMoment.lean` | Step 5 |
| `kasamiExp_coprime` | `KasamiExponent.lean` | Step 4 (gcd) |
| `kasamiExp_permutation` | `KasamiExponent.lean` | Step 4 (bijectivity) |
| `deriv_char_sum_zero` | `ABImpliesAPN.lean` | `c = 0` term |
| `deriv_char_sum_sq_split` | `ABImpliesAPN.lean` | Splitting the sum |
| `chi_add` | `AdditiveCharacter.lean` | Character multiplicativity |
| `F2n.card` | `Basic.lean` | Cardinality |

## New sub-lemmas (sorry'd unless proved below)

| # | Lemma | Status |
|---|-------|--------|
| L1 | `powMap_deriv_eq` | sorry'd |
| L2 | `powMap_char_sum_eq` | sorry'd |
| L3 | `Finset_sum_sq_bij_mul` | sorry'd |
| L4 | `Finset_sum_sq_bij_pow` | sorry'd |
| L5 | `charSumSq_nonzero_eq_autocorrSq_nonzero` | sorry'd |
| L6 | `ab_deriv_char_sum_sq_nonzero_eq_powMap` | sorry'd (assembly) |
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.APNFromAB
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.ABImpliesAPN

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ## Notation and auxiliary definitions -/

/-- The derivative `D_a f(x) = f(x + a) + f(x)`. -/
def deriv {n : ℕ} (f : F2n n → F2n n) (a : F2n n) (x : F2n n) : F2n n :=
  f (x + a) + f x

/-- `T(m) = ∑_y χ(m · D_1 f(y))` — the character sum of the unit derivative scaled by `m`. -/
def unitDerivCharSum {n : ℕ} (f : F2n n → F2n n) (m : F2n n) : ℤ :=
  ∑ y : F2n n, chi n (m * deriv f 1 y)

/-! ## Sub-lemma L1: Power map derivative substitution -/

/-- **L1**: For `f(x) = x^d` and `a ≠ 0`:
    `(x + a)^d + x^d = a^d · ((x·a⁻¹ + 1)^d + (x·a⁻¹)^d)`.

    In other words, `D_a f(x) = a^d · D_1 f(x · a⁻¹)`.

    Proof: factor out `a^d` from `(x+a)^d + x^d = a^d · ((x/a + 1)^d + (x/a)^d)`. -/
theorem powMap_deriv_eq {n : ℕ} (d : ℕ) (a : F2n n) (ha : a ≠ 0) (x : F2n n) :
    (x + a) ^ d + x ^ d = a ^ d * ((x * a⁻¹ + 1) ^ d + (x * a⁻¹) ^ d) := by
  sorry

/-! ## Sub-lemma L2: Character sum change of variables -/

/-- **L2**: For the power function `f(x) = x^d` and `a ≠ 0`:
    `∑_x χ(c · D_a f(x)) = ∑_y χ((c · a^d) · D_1 f(y))`.

    Proof: substitute `x = a · y` (which bijects `F_{2^n}` since `a ≠ 0`),
    then apply L1 to simplify `D_a f(a·y) = a^d · D_1 f(y)`. -/
theorem powMap_char_sum_eq {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (a : F2n n) (ha : a ≠ 0) (c : F2n n) :
    ∑ x : F2n n, chi n (c * ((x + a) ^ d + x ^ d)) =
    ∑ y : F2n n, chi n (c * a ^ d * ((y + 1) ^ d + y ^ d)) := by
  sorry

/-! ## Sub-lemma L3: Sum over `c ≠ 0` is invariant under multiplication -/

/-- **L3**: For any `g : F_{2^n} → ℤ` and `a ≠ 0`:
    `∑_{c ≠ 0} g(c · a)² = ∑_{m ≠ 0} g(m)²`.

    Proof: `c ↦ c · a` is a bijection on `F_{2^n}*` (since `a ≠ 0`). -/
theorem Finset_sum_sq_bij_mul {n : ℕ} (g : F2n n → ℤ) (a : F2n n) (ha : a ≠ 0) :
    ∑ c ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0), g (c * a) ^ 2 =
    ∑ m ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0), g m ^ 2 := by
  sorry

/-! ## Sub-lemma L4: Sum over `a ≠ 0` is invariant under the power map -/

/-- **L4**: For any `g : F_{2^n} → ℤ` and `d` coprime to `2^n - 1`:
    `∑_{a ≠ 0} g(a^d)² = ∑_{m ≠ 0} g(m)²`.

    Proof: `a ↦ a^d` is a bijection on `F_{2^n}*` (since `gcd(d, 2^n-1) = 1`). -/
theorem Finset_sum_sq_bij_pow {n : ℕ} (hn : n ≠ 0) (g : F2n n → ℤ) (d : ℕ)
    (hd : Function.Bijective (F2n.powMap n d)) :
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0), g (a ^ d) ^ 2 =
    ∑ m ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0), g m ^ 2 := by
  sorry

/-! ## Sub-lemma L5: Connect the two sums -/

/-- **L5**: For a power AB function `f(x) = x^d` with `a ≠ 0` and `d` coprime to `2^n - 1`:
    `∑_{c ≠ 0} S(c,a)² = ∑_{t ≠ 0} R(t)²`
    where `S(c,a) = ∑_x χ(c · D_a f(x))` and `R(t) = autocorr f t`.

    Proof: By L2, `S(c,a) = T(c · a^d)`. By L3, `∑_{c≠0} T(c·a^d)² = ∑_{m≠0} T(m)²`.
    By L2 with `c = 1`, `S(1,t) = T(t^d)`. By L4, `∑_{t≠0} T(t^d)² = ∑_{m≠0} T(m)²`.
    And `S(1,t) = R(t) = autocorr f t` by definition. -/
theorem charSumSq_nonzero_eq_autocorrSq_nonzero {n : ℕ} (hn : n ≠ 0)
    (d : ℕ) (hd : d ≠ 0) (hbij : Function.Bijective (F2n.powMap n d))
    (a : F2n n) (ha : a ≠ 0) :
    ∑ c ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      (∑ x : F2n n, chi n (c * ((x + a) ^ d + x ^ d))) ^ 2 =
    ∑ t ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      autocorr (F2n.powMap n d) t ^ 2 := by
  sorry

/-! ## Sub-lemma L6: The final bound for power functions -/

/-- **L6 (Assembly)**: For an AB power function `f(x) = x^d` with
    `gcd(d, 2^n-1) = 1`, `a ≠ 0`:
    `∑_{c ≠ 0} S(c,a)² = (2^n)²`.

    Uses:
    - `charSumSq_nonzero_eq_autocorrSq_nonzero` (L5) to reduce to `∑_{t≠0} R(t)²`
    - `ab_autocorr_sq_nonzero_sum` (already proved in `FourthMoment.lean`) for the value

    Note: this gives EQUALITY, which is stronger than the ≤ in the original statement. -/
theorem ab_deriv_char_sum_sq_nonzero_eq_powMap {n : ℕ} (hn : n ≠ 0)
    (d : ℕ) (hd : d ≠ 0) (hbij : Function.Bijective (F2n.powMap n d))
    (hf : IsAlmostBent (F2n.powMap n d))
    (a : F2n n) (ha : a ≠ 0) :
    ∑ c ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      (∑ x : F2n n, chi n (c * ((x + a) ^ d + x ^ d))) ^ 2 =
    (2 ^ n : ℤ) ^ 2 := by
  rw [charSumSq_nonzero_eq_autocorrSq_nonzero hn d hd hbij a ha]
  exact ab_autocorr_sq_nonzero_sum hn _ hf

/-! ## Filling the original sorry for the Kasami function -/

/-- The original `ab_deriv_char_sum_sq_nonzero_le` specialized to the Kasami function.
    This version adds the power-function hypotheses that make the proof go through. -/
theorem ab_deriv_char_sum_sq_nonzero_le_kasami {n k : ℕ} (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hf : IsAlmostBent (kasamiF n k))
    (a : F2n n) (ha : a ≠ 0) :
    ∑ c ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 ≤
    (2 ^ n : ℤ) ^ 2 := by
  -- kasamiF n k = F2n.powMap n (kasamiExp k), so we unfold:
  have h_unfold : ∀ x : F2n n, kasamiF n k (x + a) + kasamiF n k x =
      (x + a) ^ kasamiExp k + x ^ kasamiExp k := by
    intro x; simp [kasamiF, F2n.powMap]
  simp_rw [h_unfold]
  have hbij := kasamiExp_permutation k n hk hn hn_odd hgcd
  have hd_ne : kasamiExp k ≠ 0 := Nat.pos_iff_ne_zero.mp (kasamiExp_pos k)
  -- Now use the powMap version (which gives equality, hence ≤)
  have h_eq := ab_deriv_char_sum_sq_nonzero_eq_powMap hn (kasamiExp k) hd_ne hbij hf a ha
  linarith

/-! ## Alternative: AB implies APN for the Kasami function -/

/-- AB implies APN for the Kasami function (bypassing the general sorry). -/
theorem ab_implies_apn_kasami {n k : ℕ} (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hf : IsAlmostBent (kasamiF n k)) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2 := by
  intro a ha b
  -- Follow the same proof structure as `ab_implies_apn'` in ABImpliesAPN.lean
  have h_even : ∀ b', Even (derivCount (kasamiF n k) a b') :=
    derivCount_even (kasamiF n k) a ha
  have h_sum : ∑ b', derivCount (kasamiF n k) a b' = 2 ^ n := by
    have := derivCount_sum (kasamiF n k) a
    rwa [F2n.card n hn] at this
  -- The key: use our power-function-specific bound
  have h_unfold : ∀ x, kasamiF n k (x + a) + kasamiF n k x =
      (x + a) ^ kasamiExp k + x ^ kasamiExp k := by
    intro x; simp [kasamiF, F2n.powMap]
  have hbij := kasamiExp_permutation k n hk hn hn_odd hgcd
  have hd_ne : kasamiExp k ≠ 0 := Nat.pos_iff_ne_zero.mp (kasamiExp_pos k)
  -- Get the character sum bound
  have h_char_bound : ∑ c ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 ≤
      (2 ^ n : ℤ) ^ 2 :=
    ab_deriv_char_sum_sq_nonzero_le_kasami hk hn hn_odd hgcd hf a ha
  -- Now follow the same assembly as `ab_implies_apn'`
  have h_total_bound : ∑ c : F2n n,
      (∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))) ^ 2 ≤
      2 * (2 ^ n : ℤ) ^ 2 := by
    rw [deriv_char_sum_sq_split hn]
    linarith
  -- From Parseval, get sum-of-squares bound on N_a
  have h_parseval := deriv_parseval hn (kasamiF n k) a
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  have h_sq_int : ∑ b' : F2n n, (derivCount (kasamiF n k) a b' : ℤ) ^ 2 ≤ 2 ^ (n + 1) := by
    have h1 : (2 ^ n : ℤ) * ∑ b', (derivCount (kasamiF n k) a b' : ℤ) ^ 2 ≤
        2 * (2 ^ n : ℤ) ^ 2 := by linarith
    have h2 : ∑ b', (derivCount (kasamiF n k) a b' : ℤ) ^ 2 ≤ 2 * 2 ^ n := by nlinarith
    linarith [show (2 : ℤ) * 2 ^ n = 2 ^ (n + 1) by ring]
  -- Cast to ℕ
  have h_sq_nat : ∑ b' : F2n n, (derivCount (kasamiF n k) a b') ^ 2 ≤ 2 ^ (n + 1) := by
    have : ∀ b' : F2n n, (derivCount (kasamiF n k) a b' : ℤ) ^ 2 =
        ((derivCount (kasamiF n k) a b') ^ 2 : ℕ) := by
      intro b'; push_cast; ring
    simp only [this] at h_sq_int
    exact_mod_cast h_sq_int
  exact even_sum_sq_bound hn _ h_even h_sum h_sq_nat b

end
end Kasami
