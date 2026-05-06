/-
  Kasami/KasamiAB.lean

  The Kasami function is Almost Bent (AB).

  This file combines:
  1. Kasami APN (from APN.lean)
  2. Power APN → AB for odd n (from APNtoAB.lean)
  to conclude that the Kasami function is AB.

  Reference: Budaghyan, Theorem 23 ("is almost bent when k is odd");
             Bracken–Byrne–Markin–McGuire, Theorem 3.
-/
import Mathlib
import RequestProject.Kasami.APN
import RequestProject.Kasami.APNtoAB
import RequestProject.Theorem23.Counting

noncomputable section

open Finset Classical FourierSpectralBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Kasami is AB -/

/-- The Kasami delta is the same as the explicit power expression. -/
lemma kasamiDelta_eq_pow (k : ℕ) (a x : F) :
    kasamiDelta F k a x = (x + a) ^ kasamiExp k + x ^ kasamiExp k := by
  simp [kasamiDelta, kasamiFun]

/-- **Kasami AB Theorem.**
    The Kasami function `f(x) = x^{4^k - 2^k + 1}` is Almost Bent over
    `GF(2^n)` when `gcd(k, n) = 1`, `n` is odd, and `k ≥ 1`.

    The Walsh spectrum of the Kasami function is `{0, ±2^{(n+1)/2}}`.

    Proof chain:
    1. `kasami_is_APN` (APN.lean): The Kasami function is APN.
    2. `power_APN_implies_AB` (APNtoAB.lean): For power functions with n odd,
       APN implies AB.
    3. Compose to get AB.

    Reference: Budaghyan, Theorem 23;
               Bracken–Byrne–Markin–McGuire, Theorem 3. -/
theorem kasami_is_AB (k n : ℕ) (hk : 0 < k) (hn : 1 ≤ n)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    IsAB ψ (fun x => kasamiFun F k x) n := by
  constructor
  · exact hcard
  · -- The Kasami function is a power function with exponent d = kasamiExp k
    -- Step 1: Kasami is APN
    have h_apn := kasami_is_APN F k n hk hcard hcoprime
    -- Step 2: Rewrite Kasami APN in terms of the power function
    have h_apn' : ∀ a : F, a ≠ 0 → ∀ v : F,
        (Finset.univ.filter fun x =>
          (x + a) ^ kasamiExp k + x ^ kasamiExp k = v).card ≤ 2 := by
      intro a ha v
      have := h_apn a ha v
      simp only [kasamiDelta, kasamiFun] at this
      exact this
    -- Step 3: Apply power_APN_implies_AB
    exact power_APN_implies_AB n hn_odd hn hcard (kasamiExp k) ψ hψ h_apn'

end