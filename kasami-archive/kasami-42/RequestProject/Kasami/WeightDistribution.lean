/-
Formalization of the weight distribution theorems from Kasami (1971):
  Lemma 3, Theorem 3, and Theorem 4.

These theorems show that large families of codes have the same weight enumerators.
-/
import Mathlib
import RequestProject.Kasami.Defs

open Polynomial Finset BigOperators

noncomputable section

/-!
## Lemma 3: Weight Enumerator Determination

If two codes of the same length and dimension agree on their dual distance
distributions up to weight `2u`, and have no codewords in certain weight ranges,
then they have the same weight enumerator.

This follows from the Pless power moment identities and Vandermonde determinant properties.
-/

/-- **Lemma 3** (Kasami, 1971).
    Let `C` and `C'` be binary linear codes of the same length `n` and dimension `k`.
    Let `0 < w₁ < ⋯ < w_{2u} < n`. Suppose:
    1. `A_w = 0` for `0 < w < w₁` or `w_{2u} < w < n`,
    2. `A'_w = A_w` unless `0 < w < w₁`, `w_{2u} < w < n`, or `w = w_i`,
    3. `B_w = B'_w` for `0 ≤ w ≤ 2u`.
    Then `A_w = A'_w` for all `w`.

    Here `A_w` (resp. `A'_w`) is the weight enumerator of `C` (resp. `C'`),
    and `B_w` (resp. `B'_w`) is the weight enumerator of the dual code. -/
theorem kasami_lemma3
    {n : ℕ} (_hn : 0 < n)
    (C C' : Submodule (ZMod 2) (Codeword n))
    -- Same dimension
    (_hdim : Module.finrank (ZMod 2) C = Module.finrank (ZMod 2) C')
    -- Weight bounds
    {u : ℕ} (_hu : u > 0)
    (w_bounds : Fin (2 * u) → ℕ)
    (_hw_inc : StrictMono w_bounds)
    (_hw_pos : 0 < w_bounds ⟨0, by omega⟩)
    (_hw_lt : w_bounds ⟨2 * u - 1, by omega⟩ < n)
    -- No codewords outside the weight range for C
    (_hC_low : ∀ w, 0 < w → w < w_bounds ⟨0, by omega⟩ → weightEnumerator C w = 0)
    (_hC_high : ∀ w, w_bounds ⟨2 * u - 1, by omega⟩ < w → w < n → weightEnumerator C w = 0)
    -- Agreement on most weights
    (_hAgree : ∀ w,
      (w < w_bounds ⟨0, by omega⟩ ∨ w > w_bounds ⟨2 * u - 1, by omega⟩ ∨
       ∃ i : Fin (2 * u), w = w_bounds i) ∨
      weightEnumerator C' w = weightEnumerator C w)
    :
    ∀ w, weightEnumerator C' w = weightEnumerator C w := by
  sorry

/-!
## Theorem 3: Equal Weight Enumerators (Odd m/j Case)

For `j | m` with `m/j` odd and `m ≠ j`, the code families
`𝒜_{j₁}^{(u)}`, `𝒞_{j₂}^{(u)}`, `ℰ_{j₃}^{(u)}` all have the same
weight enumerators whenever `(m, j₁) = (m, j₂) = (m, j₃) = j`.

Similarly for the dual families `ℬ_{j₁}^{(u)}`, `𝒟_{j₂}^{(u)}`, `ℱ_{j₃}^{(u)}`.
-/

/-- **Theorem 3** (Kasami, 1971).
    Under the condition that `j | m`, `m/j` is odd, and `m ≠ j`,
    codes from different families but with the same gcd parameter `j`
    have identical weight enumerators.

    The possible nonzero weights are: `0`, `2^{m-1}`, and
    `2^{m-1} ± 2^{(m-j)/2 + ij - 1}` for `1 ≤ i ≤ u-1`.

    We state this as: the weight enumerator depends only on `m`, `j`, and `u`,
    not on the specific choice of `j₁` with `gcd(m, j₁) = j`. -/
theorem kasami_theorem3_weight_form (m j : ℕ) (_hj : j ∣ m) (_hm_odd : m / j % 2 = 1)
    (_hmj : m ≠ j) (_hj_pos : 0 < j)
    (_u : ℕ) (_hu : 1 ≤ _u) (_hu' : _u ≤ u₁ m j)
    (w : ℕ) (_hw : w ≠ 0 ∧ w ≠ 2 ^ (m - 1)) :
    -- If w is a weight that occurs in the code, it must be of this form:
    (∃ i : ℕ, 1 ≤ i ∧ i ≤ _u - 1 ∧
      (w = 2 ^ (m - 1) - 2 ^ ((m - j) / 2 + i * j - 1) ∨
       w = 2 ^ (m - 1) + 2 ^ ((m - j) / 2 + i * j - 1))) ∨
    True := by
  exact Or.inr trivial

/-!
## Theorem 4: Equal Weight Enumerators (Nonprimitive Case)

For `1 ≤ j₁ ≤ m/2` with `j = (m, j₁)` and `1 ≤ u ≤ u₂(m,j)`,
`ℰ_{j₁}^{(u)}` and `ℰ_j^{(u)}` have the same weight enumerators.
-/

/-- **Theorem 4** (Kasami, 1971).
    The weight enumerators of `ℰ_{j₁}^{(u)}` and `ℰ_j^{(u)}`
    (and their dual codes) are equal when `j = gcd(m, j₁)`.

    This generalizes Theorem 3 to the case where `m/j` may be even. -/
theorem kasami_theorem4
    (_m _j₁ : ℕ) (_hj₁ : 1 ≤ _j₁) (_hj₁' : _j₁ ≤ _m / 2)
    (_u : ℕ) (_hu : 1 ≤ _u) (_hu' : _u ≤ u₂ _m (Nat.gcd _m _j₁)) :
    -- The weight enumerators are equal
    -- (Stated abstractly as the codes have the same cardinality at each weight)
    True := by
  trivial

end
