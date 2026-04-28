/-
# Decomposition of `ccd_crossterm_gives_linPolyL`

This module decomposes the deepest algebraic step in the CCD (Canteaut–Charpin–
Dobbertin) proof — `ccd_crossterm_gives_linPolyL` — into small, composable
sub-lemmas following a "one function does one thing" philosophy.

## Decomposition Summary

| # | Lemma                          | Status | Mathlib / project reuse             |
|---|--------------------------------|--------|--------------------------------------|
| 1 | `Mk_Lk_eq`                    | ✅     | uses `add_pow_char_pow` (Mathlib)    |
| 2 | `deriv_eq_implies_B'_eq`       | ✅     | uses `CharTwo.add_self_eq_zero` (Mathlib) |
| 3 | `crossterm_diff_eq_bilinear`   | ✅     | uses `add_pow_char_pow` (Mathlib)    |
| 4 | `bilinear_Mk_factor`          | ✅     | uses `linPolyM` from `Defs.lean`     |
| 5 | `deriv_w_ne_zero`              | ❌     | may need `Nat.Coprime.pow_left_bijective` (Mathlib) |
| 6 | `Mk_eq_wMk_implies_Lk_zero`   | ❌     | deepest step, CCD paper Proposition 2 |

### Mathlib lemmas standing on the shoulders of

* `add_pow_char_pow` — Freshman's dream: `(a + b)^{p^k} = a^{p^k} + b^{p^k}`
* `CharTwo.add_self_eq_zero` — `a + a = 0` in characteristic 2
* `CharP.cast_eq_zero` — `(p : R) = 0` when `CharP R p`
* `Nat.Coprime.pow_left_bijective` — `x ↦ x^n` is bijective when `gcd(n, |G|) = 1`

### Project-internal lemmas used

* `linPolyL` / `linPolyM` — from `LinearizedPoly/Defs.lean`
* `linPolyL_linearized` / `linPolyM_linearized` — from `LinearizedPoly/Defs.lean`
* `funKer` — from `LinearizedPoly/Kernel.lean`
* `ccd_second_deriv_eq` — from `LinearizedPoly/KasamiKernel.lean` (already proved)
* `ccd_power_factorization` — from `LinearizedPoly/KasamiKernel.lean` (already proved)

## Proof outline

Given the hypothesis `heq` :
  `(y₂ + z + 1)^d + (y₂ + z)^d = (y₂ + 1)^d + y₂^d`
we want to show `linPolyL k z = 0`.

**Step 1** (`Mk_Lk_eq`):  M_k(L_k(z)) = z^{2^{3k}} + z.

**Step 2** (`ccd_second_deriv_eq`, in KasamiKernel.lean):
  z^{2^{3k}} + z = C(y₂) + C(y₂ + z).

**Step 3** (`crossterm_diff_eq_bilinear`):
  C(y) + C(y+z) = δ · w^{2^k} + δ^{2^k} · w
  where  δ = (y+z)^d + y^d,  w = (y+1)^d + y^d.

**Step 4** (`bilinear_Mk_factor`):  For w ≠ 0:
  δ · w^{2^k} + δ^{2^k} · w  =  w^{2^k+1} · M_k(δ / w).

**Step 5** (`deriv_w_ne_zero`):  w ≠ 0 (uses injectivity of x ↦ x^d).

**Step 6** (`Mk_eq_wMk_implies_Lk_zero`):  From
  M_k(L_k(z)) = w^{2^k+1} · M_k(δ/w), conclude L_k(z) = 0.

Steps 5–6 remain `sorry`; they are the genuinely deep algebraic core
of the CCD theorem.

## References

* Canteaut, Charpin, Dobbertin (2000), *SIAM J. Discrete Math.* 13(1), 105–138
* Dobbertin (1999), *IEEE Trans. Inform. Theory* 45(4), 1271–1275
-/

import Mathlib
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Kasami exponent `d(k) = 2^{2k} − 2^k + 1`. -/
private def d (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- CCD Cross-term `C(x) = (x+1)^d · x^{d·2^k} + (x+1)^{d·2^k} · x^d`. -/
private def C (k : ℕ) (x : F) : F :=
  (x + 1) ^ (d k) * x ^ (d k * 2 ^ k) +
  (x + 1) ^ (d k * 2 ^ k) * x ^ (d k)

/-! ================================================================
    §1  Step 1 — M_k ∘ L_k  identity  (PROVED)
    ================================================================ -/

/-- **M_k(L_k(z)) = z^{2^{3k}} + z**.

    This is a pure algebraic identity in characteristic 2, proved by
    expanding via Freshman's dream (`add_pow_char_pow` from Mathlib)
    and char-2 cancellation (`CharTwo.add_self_eq_zero` from Mathlib).

    Concretely:
      `(z^{2^{2k}} + z^{2^k} + z)^{2^k} + (z^{2^{2k}} + z^{2^k} + z)`
      `= z^{2^{3k}} + z^{2^{2k}} + z^{2^k} + z^{2^{2k}} + z^{2^k} + z`
      `= z^{2^{3k}} + z`.  -/
theorem Mk_Lk_eq (k : ℕ) (z : F) :
    linPolyM k (linPolyL k z) = z ^ (2 ^ (3 * k)) + z := by
  unfold linPolyM linPolyL;
  have h_expand : (z ^ (2 ^ (2 * k)) + z ^ (2 ^ k) + z) ^ (2 ^ k) = z ^ (2 ^ (2 * k) * 2 ^ k) + z ^ (2 ^ k * 2 ^ k) + z ^ (2 ^ k) := by
    simp +decide [ pow_mul, add_pow_char_pow ];
  ring_nf at *;
  grind

/-! ================================================================
    §2  Step 3 — Cross-term difference expansion  (PROVED)
    ================================================================ -/

/-- **Char-2 rearrangement of heq**.
    From `B' + A' = B + A`, derive `B' = B + δ` where `δ = A' + A`.
    Uses `CharTwo.add_self_eq_zero` from Mathlib. -/
theorem deriv_eq_implies_B'_eq (k : ℕ) (y z : F)
    (heq : (y + z + 1) ^ d k + (y + z) ^ d k =
           (y + 1) ^ d k + y ^ d k) :
    (y + z + 1) ^ d k = (y + 1) ^ d k + ((y + z) ^ d k + y ^ d k) := by
  grind

/-- **Cross-term difference = bilinear form in δ and w**.

    `C(y) + C(y+z) = δ · w^{2^k} + δ^{2^k} · w`

    where `δ = (y+z)^d + y^d` and `w = (y+1)^d + y^d`.

    Proved by substituting `B' = B + δ`, `A' = A + δ`
    (from `deriv_eq_implies_B'_eq`), applying Freshman's dream
    (`add_pow_char_pow`), and char-2 cancellation. -/
theorem crossterm_diff_eq_bilinear (k : ℕ) (y z : F)
    (heq : (y + z + 1) ^ d k + (y + z) ^ d k =
           (y + 1) ^ d k + y ^ d k) :
    C k y + C k (y + z) =
      ((y + z) ^ d k + y ^ d k) * ((y + 1) ^ d k + y ^ d k) ^ (2 ^ k) +
      ((y + z) ^ d k + y ^ d k) ^ (2 ^ k) * ((y + 1) ^ d k + y ^ d k) := by
  unfold C;
  simp_all +decide [ add_comm, add_left_comm, add_assoc, pow_mul ];
  have h_simp : ∀ (a b : F), (a + b) ^ 2 ^ k = a ^ 2 ^ k + b ^ 2 ^ k :=
    fun a b => add_pow_expChar_pow a b 2 k
  grind

/-! ================================================================
    §3  Step 4 — Factoring through M_k  (PROVED)
    ================================================================ -/

/-- **Bilinear form factors through M_k** (for `w ≠ 0`).

    `δ · w^{2^k} + δ^{2^k} · w = w^{2^k+1} · M_k(δ / w)`

    Set `t = δ / w`, so `δ = t · w`.  Then:
      `t·w·w^{2^k} + (t·w)^{2^k}·w = t·w^{2^k+1} + t^{2^k}·w^{2^k+1}`
      `= w^{2^k+1} · (t + t^{2^k}) = w^{2^k+1} · M_k(t)`.

    Uses `linPolyM` from `LinearizedPoly/Defs.lean`. -/
theorem bilinear_Mk_factor (k : ℕ) (δ w : F) (hw : w ≠ 0) :
    δ * w ^ (2 ^ k) + δ ^ (2 ^ k) * w =
      w ^ (2 ^ k + 1) * linPolyM k (δ / w) := by
  unfold linPolyM; rw [ pow_add, pow_one ] ; ring;
  simp +decide [ hw, mul_assoc, mul_comm w ]

/-! ================================================================
    §4  Step 5 — w ≠ 0  (SORRY)
    ================================================================ -/

/-- **Derivative value is nonzero**.

    When `z ≠ 0`, `z ≠ 1`, and `heq` holds, the derivative value
    `w = (y+1)^d + y^d` is nonzero.

    The argument uses injectivity of `x ↦ x^d` on `F*`
    (from `Nat.Coprime.pow_left_bijective` in Mathlib, applied to
    the multiplicative group), though stating this correctly requires
    knowing `gcd(d, |F*|) = 1`.

    **Note**: This lemma as stated may need additional hypotheses
    (e.g., `Fintype.card F = 2^n` and `Nat.Coprime k n`) to ensure
    `x ↦ x^d` is injective.  In the w = 0 case one can still
    conclude `L_k(z) = 0` by a separate argument.  The case split
    is encapsulated in `Mk_eq_wMk_implies_Lk_zero` below. -/
theorem deriv_w_ne_zero (k : ℕ) (hk : 0 < k) (y z : F) (hz : z ≠ 0) (hz1 : z ≠ 1)
    (heq : (y + z + 1) ^ d k + (y + z) ^ d k =
           (y + 1) ^ d k + y ^ d k) :
    (y + 1) ^ d k + y ^ d k ≠ 0 := by
  sorry

/-! ================================================================
    §5  Step 6 — The deepest algebraic conclusion  (SORRY)
    ================================================================ -/

/-- **The deepest algebraic conclusion** — CCD Proposition 2 core.

    Given `z ∉ {0, 1}` and the derivative equation `heq`, conclude
    `L_k(z) = 0`.

    This is the deepest step of the Canteaut–Charpin–Dobbertin proof.
    The full argument requires:

    1. Using `Mk_Lk_eq`:  `M_k(L_k(z)) = z^{2^{3k}} + z`.
    2. Using `ccd_second_deriv_eq` (KasamiKernel.lean):
       `z^{2^{3k}} + z = C(y) + C(y+z)`.
    3. Using `crossterm_diff_eq_bilinear`:
       `C(y) + C(y+z) = δ·w^{2^k} + δ^{2^k}·w`.
    4. Case-splitting on `w = 0` vs `w ≠ 0`:
       - If `w ≠ 0`: use `bilinear_Mk_factor` to get
         `M_k(L_k(z)) = w^{2^k+1} · M_k(δ/w)`, then exploit the
         Kasami exponent structure `d·(2^k+1) = 2^{3k}+1` to show
         `w^{2^k+1} · M_k(δ/w) = M_k(E)` for an explicit `E`,
         and conclude `L_k(z) = 0`.
       - If `w = 0`: then `C(y) = C(y+z) = 0` so `z^{2^{3k}}+z = 0`,
         i.e., `M_k(L_k(z)) = 0`. Combined with the polynomial
         structure of the Kasami exponent, this still yields `L_k(z) = 0`.

    Both cases require polynomial-identity reasoning over `GF(2)` that
    is specific to the Kasami exponent `d = 2^{2k} − 2^k + 1`.  -/
theorem Mk_eq_wMk_implies_Lk_zero (k : ℕ) (hk : 0 < k) (y z : F)
    (hz : z ≠ 0) (hz1 : z ≠ 1)
    (heq : (y + z + 1) ^ d k + (y + z) ^ d k =
           (y + 1) ^ d k + y ^ d k) :
    linPolyL k z = 0 := by
  sorry

/-! ================================================================
    §6  Assembly
    ================================================================ -/

/-- **Assembly** — `ccd_crossterm_gives_linPolyL` from sublemmas.

    Delegates to `Mk_eq_wMk_implies_Lk_zero`, which encapsulates
    Steps 1–6.  When the sorry in Step 6 is filled, this theorem
    becomes sorry-free and can replace the sorry in
    `KasamiKernel.lean : ccd_crossterm_gives_linPolyL`. -/
theorem ccd_crossterm_gives_linPolyL' (k : ℕ) (hk : 0 < k) (y₂ z : F)
    (hz : z ≠ 0) (hz1 : z ≠ 1)
    (heq : (y₂ + z + 1) ^ d k + (y₂ + z) ^ d k =
           (y₂ + 1) ^ d k + y₂ ^ d k) :
    linPolyL k z = 0 :=
  Mk_eq_wMk_implies_Lk_zero k hk y₂ z hz hz1 heq

end
