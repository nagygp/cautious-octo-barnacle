/-
  QuadraticFourier.lean — Walsh transform integer‑value logic for Almost Bent functions

  Key result: If W is an integer satisfying W² = 2^(n+1) with n odd,
  then W = ± 2^((n+1)/2).

  Also: radical‑parity logic showing that for a quadratic form over GF(2)
  with radical dimension s, the parity of n + s determines the Walsh spectrum.
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ### §1  Walsh integer‑value lemma -/

/-
If `W² = 2 ^ (n + 1)` for some integer `W` and *odd* natural number `n`,
then `W = 2 ^ ((n + 1) / 2)` or `W = -(2 ^ ((n + 1) / 2))`.
-/
theorem walsh_int_values {W : ℤ} {n : ℕ} (hn : Odd n) (hW : W ^ 2 = (2 : ℤ) ^ (n + 1)) :
    W = 2 ^ ((n + 1) / 2) ∨ W = -(2 ^ ((n + 1) / 2)) := by
  exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [ hW, ← pow_mul', Nat.mul_div_cancel' <| even_iff_two_dvd.mp <| hn.add_odd odd_one ] ;

/-! ### §2  Radical‑parity logic -/

/-
The radical dimension `s` of a non‑degenerate quadratic form over GF(2^n)
must satisfy `n + s ≡ 0 [MOD 2]` (i.e., `n` and `s` have the same parity)
in order for the Walsh transform to take values in `{0, ± 2^((n+s)/2)}`.

Here we state the *parity* consequence only.
-/
theorem radical_parity_logic {n s : ℕ} (_hn : 0 < n) (_hs : s ≤ n)
    (hspec : ∃ W : ℤ, W ^ 2 = (2 : ℤ) ^ (n + s)) :
    Even (n + s) := by
  obtain ⟨ W, hW ⟩ := hspec; have := congr_arg Int.natAbs hW; norm_num [ Int.natAbs_pow ] at this; replace this := congr_arg ( fun x => x.factorization 2 ) this; simp_all +decide [ Nat.factorization_pow ] ;
  exact this ▸ even_two_mul _

/-! ### §3  Walsh spectrum from radical dimension -/

/-
Given:
  • a quadratic form on GF(2^n) with radical of dimension `s`,
  • `n + s` is even,
the Walsh‑transform values lie in `{0, 2^((n+s)/2), -(2^((n+s)/2))}`.

We state the *integer* consequence: every Walsh value `W` satisfies
`W = 0 ∨ W ^ 2 = 2 ^ (n + s)`.
-/
theorem walsh_spectrum_from_radical {n s : ℕ} (_hn : 0 < n) (_hs : s ≤ n)
    (_heven : Even (n + s))
    (W : ℤ) (hW : W ^ 2 ∣ (2 : ℤ) ^ (n + s) ∧ (2 : ℤ) ^ (n + s) ∣ W ^ 2) :
    W = 0 ∨ W ^ 2 = (2 : ℤ) ^ (n + s) := by
  exact Or.inr ( Int.le_antisymm ( Int.le_of_dvd ( by positivity ) hW.1 ) ( Int.le_of_dvd ( sq_pos_of_ne_zero ( by rintro rfl; exact absurd hW.2 ( by norm_cast; aesop ) ) ) hW.2 ) )

/-! ### §4  AB spectrum characterisation -/

/-- A function `f : GF(2^n) → GF(2^n)` is **Almost Bent** (AB) when every
non‑trivial Walsh‑transform value `W` satisfies `W ∈ {0, ± 2^((n+1)/2)}`.
Equivalently, `W² ∈ {0, 2^(n+1)}` for all Walsh coefficients.
We encode the integer condition only. -/
def IsAlmostBent (n : ℕ) (spectrum : Finset ℤ) : Prop :=
  ∀ W ∈ spectrum, W = 0 ∨ W ^ 2 = (2 : ℤ) ^ (n + 1)

/-- For an AB function over GF(2^n) with n odd, the non‑zero Walsh values
are exactly `± 2^((n+1)/2)`. -/
theorem ab_spectrum_values {n : ℕ} (hn : Odd n) {spectrum : Finset ℤ}
    (hab : IsAlmostBent n spectrum) {W : ℤ} (hW : W ∈ spectrum) (hne : W ≠ 0) :
    W = 2 ^ ((n + 1) / 2) ∨ W = -(2 ^ ((n + 1) / 2)) := by
  have h := hab W hW
  rcases h with h0 | hsq
  · exact absurd h0 hne
  · exact walsh_int_values hn hsq