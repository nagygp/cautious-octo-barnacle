/-
  QuadraticFourier.lean — Universal Fourier-analytic utility lemmas

  This is a standalone module with no Kasami-specific content.
  It provides the bridge lemmas that translate between:
    • squared Walsh–Hadamard norms and sign/square-root decompositions,
    • parity constraints on exponents from integrality.

  These lemmas can be reused in any context involving power-of-two
  Walsh–Hadamard spectral analysis over finite fields of characteristic 2.
-/
import Mathlib

open Int

set_option maxHeartbeats 800000

/-! ## Step 1 — Value-Set Transition (Sign & Square Root)

The Walsh–Hadamard coefficient `W` satisfies `W^2 = 2^(n+1)`.
We want to conclude `W ∈ {2^((n+1)/2), -2^((n+1)/2)}`.
-/

/-
Helper: `2 ^ (n+1) = (2 ^ ((n+1)/2)) ^ 2` when `n+1` is even.
-/
lemma pow_eq_sq_of_even {n : ℕ} (h : Even (n + 1)) :
    (2 : ℤ) ^ (n + 1) = (2 ^ ((n + 1) / 2)) ^ 2 := by
  rw [ ← pow_mul', Nat.mul_div_cancel' ( even_iff_two_dvd.mp h ) ]

/-
Helper: `2 ^ (n+1)` is NOT a perfect square in `ℤ` when `n+1` is odd.
-/
lemma not_sq_of_odd {n : ℕ} (h : ¬ Even (n + 1)) :
    ∀ W : ℤ, W ^ 2 ≠ 2 ^ (n + 1) := by
  intro W hW; replace hW := congr_arg ( fun x => x.natAbs ) hW; norm_num [ Int.natAbs_pow ] at hW; ( have := congr_arg ( fun x => x.factorization 2 ) hW; norm_num at this; );
  grind

/-- **walsh_set_from_sq**: A Walsh coefficient whose square equals `2^(n+1)`
must be `±2^((n+1)/2)`.

* `→` direction: factor `W^2 = (2^((n+1)/2))^2` and apply `sq_eq_sq_iff_eq_or_eq_neg`.
* `←` direction: substitute and simplify.
* When `n+1` is odd both sides are false (vacuously true).
-/
theorem walsh_set_from_sq (n : ℕ) (W : ℤ) :
    W ^ 2 = 2 ^ (n + 1) ↔ (W = 2 ^ ((n + 1) / 2) ∨ W = -(2 ^ ((n + 1) / 2))) := by
  sorry

/-! ## Step 2 — Parity Constraint (Odd `n` logic)

For an Almost-Bent function over `GF(2^n)` with `n` odd, the Walsh–Hadamard
values satisfy `|W_Q|^2 = 2^{n+s}` where `s = dim(rad(Q))`.
Since `W_Q ∈ ℤ`, the exponent `n + s` must be even (otherwise `2^{n+s}` is
not a perfect square).  When `n` is odd this forces `s` to be odd as well.
-/

/-
**radical_parity_constraint**: If `W^2 = 2^(n+s)` has an integer solution,
then `n + s` must be even (the exponent of a power-of-two perfect square is even).
-/
theorem radical_parity_constraint (n s : ℕ) (W : ℤ) (hW : W ^ 2 = 2 ^ (n + s)) :
    Even (n + s) := by
  apply_fun fun x => x.natAbs at hW;
  apply_fun fun x => x.factorization 2 at hW ; simp_all +decide [ Int.natAbs_pow ];
  exact hW ▸ even_two_mul _

/-- Corollary: when `n` is odd, the radical dimension `s` must also be odd. -/
theorem radical_dim_odd_of_n_odd (n s : ℕ) (W : ℤ)
    (hW : W ^ 2 = 2 ^ (n + s)) (hn : ¬ Even n) : ¬ Even s := by
  sorry