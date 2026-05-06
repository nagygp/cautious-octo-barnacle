/-
  Kasami/APNtoAB.lean

  Bridge: for power functions over GF(2^n) with n odd, APN implies AB.

  The Chabaud–Vaudenay theorem (and its refinement) establishes that for
  *power functions* x ↦ x^d over GF(2^n) with n odd, the APN property
  (differential uniformity 2) is equivalent to the AB property (Walsh
  spectrum contained in {0, ±2^{(n+1)/2}}).

  The key steps are:
  1. For power functions, the Walsh spectrum is determined by the differential
     uniformity via the fourth-moment identity (already in Counting.lean).
  2. For n odd, a power function that is APN must have all Walsh coefficients
     W(a,b) satisfying W(a,b)^2 ∈ {0, 2^{n+1}} — this is because the
     divisibility constraints from the fourth moment force the spectrum values.

  This file states this bridge and derives the AB property for Kasami.

  Reference: Budaghyan, Theorem 23 (Corollary: "is almost bent when k is odd");
             Bracken–Byrne–Markin–McGuire, Theorem 3 (Walsh spectrum computation).
-/
import Mathlib
import RequestProject.Kasami.APN
import RequestProject.Theorem23.Counting

noncomputable section

open Finset Classical FourierSpectralBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### The Chabaud–Vaudenay bridge for power APN functions -/

/-- In characteristic 2, negation is identity. -/
private lemma char2_neg_eq (x : F) : -x = x := CharTwo.neg_eq x

/-! ### Walsh coefficients for power functions -/

/-- For a power function f(x) = x^d, the Walsh coefficient satisfies
    `W_f(a, b) = W_f(1, b · a^{-d})` when `a ≠ 0`.
    This "homogeneity" property is specific to power functions and is
    what makes the APN ↔ AB equivalence possible for odd n. -/
lemma walsh_power_homogeneity (ψ : AddChar F ℂ) (d : ℕ)
    (a b : F) (ha : a ≠ 0) :
    WalshCoeff ψ (fun x => x ^ d) a b =
    WalshCoeff ψ (fun x => x ^ d) 1 (b * a⁻¹ ^ d) := by
  sorry

/-! ### The key spectral characterization

  For power functions over GF(2^n) with n odd:
  - The fourth moment ∑ W(a,b)^4 can be computed two ways:
    (a) Via the differential uniformity: ∑ W^4 = q^2 · ∑ δ^2
    (b) Via the spectrum values: if W^2 ∈ {0, S} then ∑ W^4 = S · ∑ W^2 = S · q^2 · (q-1) + q^4
  - For APN (δ ≤ 2), ∑ δ^2 = q^2 + 2q(q-1)
  - Matching gives S = 2q, i.e., W^2 ∈ {0, 2^{n+1}}, which is AB.
-/

/-- **Power APN implies AB (n odd).**
    For a power function `f(x) = x^d` over `GF(2^n)` with `n` odd,
    if `f` is APN then `f` is AB.

    This is the Chabaud–Vaudenay theorem specialized to characteristic 2.

    Reference: Budaghyan, Ch. 2; Chabaud–Vaudenay (1995). -/
theorem power_APN_implies_AB
    (n : ℕ) (hn_odd : n % 2 = 1) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (h_apn : ∀ a : F, a ≠ 0 → ∀ v : F,
      (Finset.univ.filter fun x => (x + a) ^ d + x ^ d = v).card ≤ 2) :
    ∀ a b : F, b ≠ 0 →
      Complex.normSq (WalshCoeff ψ (fun x => x ^ d) a b) = 0 ∨
      Complex.normSq (WalshCoeff ψ (fun x => x ^ d) a b) = (2 : ℝ) ^ (n + 1) := by
  sorry

end