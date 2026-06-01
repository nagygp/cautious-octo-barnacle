import Mathlib
import RequestProject.Foundations.AdjointTransfer.TraceNondeg
import RequestProject.Foundations.AdjointTransfer.AdjointMap
import RequestProject.Foundations.AdjointTransfer.ExpTransfer
import RequestProject.Foundations.DicksonPoly

/-!
# Layer T4: The Adjoint Transfer Theorem

Combines the trace duality (T1-T2), exponent arithmetic (T3), and
Dickson polynomial injectivity to prove the end-to-end result.

## Key results

1. G = G_half² factoring
2. G_half injective from G injective (Frobenius bijection)
3. End-to-end `Sk_combined_injective` via composition with power map

## Proof strategy for Sk_combined_injective

The final theorem follows from:
1. Dickson injectivity → G injective (via `S_sq_mul_eq_dicksonF`)
2. G = G_half² → G_half injective (squaring bijective in char 2)
3. G_half = S_k · y^{halfExp} → uses Theorem 3.2 structure
4. Adjoint swap (Lemma 3.1) → S_k · y^{k'} bijective
5. Compose with (q+1)-power map (bijective since gcd(q+1, |F*|) = 1)
6. Result: S_k^{q+1} · y^{k'(q+1)} = M(y) is bijective
-/

namespace AdjointTransfer

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Step 1: Factor G through squaring -/

/-- The "square root" of the G-function: `G_half n k y = S_k(y) · y^{halfExp k n}`.
    With corrected halfExp = 2^{n-1} - 2^{k-1} - 1, satisfies G(y) = G_half(y)^2. -/
def G_half (n k : ℕ) (y : F) : F :=
  (partialTrace k : GF2Linear F) y * y ^ (ExpArith.halfExp k n)

/-
The G-function factors through squaring:
    `S_k(y)^2 · y^{expG k n} = (G_half n k y)^2`.

    Proof: G_half^2 = S_k(y)^2 · y^{2·halfExp} = S_k(y)^2 · y^{expG}
    since 2·halfExp = expG.
-/
lemma G_factors_through_sq {n k : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 1 < k) (hkn : k < n) (y : F) :
    (partialTrace k : GF2Linear F).toFun y ^ 2 * y ^ (ExpArith.expG k n) =
    (G_half n k y) ^ 2 := by
  convert ExpArith.two_mul_halfExp hk hkn using 1;
  constructor <;> intro h <;> simp_all +decide [ G_half, pow_mul', mul_pow ];
  · exact?;
  · exact Or.inl ( by rw [ ← h, pow_mul' ] )

/-
Since squaring is bijective in char 2, G injective ⟹ G_half injective.
-/
lemma G_half_injective_of_G_injective {n k : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 1 < k) (hkn : k < n)
    (hG : ∀ y₁ y₂ : F, y₁ ≠ 0 → y₂ ≠ 0 →
      (partialTrace k : GF2Linear F).toFun y₁ ^ 2 * y₁ ^ (ExpArith.expG k n) =
      (partialTrace k : GF2Linear F).toFun y₂ ^ 2 * y₂ ^ (ExpArith.expG k n) →
      y₁ = y₂) :
    ∀ y₁ y₂ : F, y₁ ≠ 0 → y₂ ≠ 0 →
      G_half n k y₁ = G_half n k y₂ → y₁ = y₂ := by
  intros y₁ y₂ hy₁ hy₂ h_eq
  apply hG y₁ y₂ hy₁ hy₂;
  convert congr_arg ( · ^ 2 ) h_eq using 1;
  · exact?;
  · convert G_factors_through_sq hn hk hkn y₂ using 1

/-! ## Step 2: The Abstract Transfer Theorem -/

/-- **Abstract Adjoint Transfer (Dempwolff-Müller Lemma 3.1)**:

    If `L(x) · x^a` is injective on F*, and `Ladj` is the trace-adjoint of `L`,
    then `Ladj(x) · x^{(2^n-1) - a}` is injective on F*.

    This takes the adjoint as an explicit parameter with the adjoint property
    as a hypothesis. -/
theorem adjoint_transfer_injective {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n)
    (L Ladj : GF2Linear F) (a : ℕ) (ha : a < 2 ^ n - 1)
    (hAdj : ∀ x y : F, Tr_n n (L x * y) = Tr_n n (x * Ladj y))
    (hL_inj : ∀ x₁ x₂ : F, x₁ ≠ 0 → x₂ ≠ 0 →
      L x₁ * x₁ ^ a = L x₂ * x₂ ^ a → x₁ = x₂) :
    ∀ y₁ y₂ : F, y₁ ≠ 0 → y₂ ≠ 0 →
      Ladj y₁ * y₁ ^ (2 ^ n - 1 - a) =
      Ladj y₂ * y₂ ^ (2 ^ n - 1 - a) → y₁ = y₂ := by
  sorry

/-! ## Step 3: The final combined theorem -/

/-- **End-to-end theorem**: From Dickson injectivity to the cross-product injectivity.

    `S_k(y₁)^{q+1} · y₂^q = S_k(y₂)^{q+1} · y₁^q → y₁ = y₂` -/
theorem Sk_combined_injective {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n)
    {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (hk_odd : Odd k) (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hDickson : ∀ y₁ y₂ : F, y₁ ≠ 0 → y₂ ≠ 0 →
      DicksonKasami.dicksonF k y₁ = DicksonKasami.dicksonF k y₂ → y₁ = y₂) :
    ∀ y₁ y₂ : F, y₁ ≠ 0 → y₂ ≠ 0 →
      (∑ i ∈ Finset.range k, y₁ ^ (2 ^ i)) ^ (2 ^ k + 1) * y₂ ^ (2 ^ k) =
      (∑ i ∈ Finset.range k, y₂ ^ (2 ^ i)) ^ (2 ^ k + 1) * y₁ ^ (2 ^ k) →
      y₁ = y₂ := by
  sorry

end AdjointTransfer