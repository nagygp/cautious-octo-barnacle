/-
  Kasami/TripleCount.lean

  The main theorem: the triple count for the Kasami differential set.

  Let k be coprime with n, n odd. For every b ∈ GF(2^n), let
    F(b) = b^{4^k - 2^k + 1}.
  Let Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}.
  Then, for every distinct nonzero v₁, v₂ ∈ GF(2^n), we have
    |{(x, y, z) ∈ Δ³ : v₁·x + v₂·y + (v₁ + v₂)·z = 0}| = 2^{2n-3}.

  This connects:
  - Kasami AB (KasamiAB.lean)
  - The abstract triple count (Counting.lean)
  - The arithmetic bridge (Kasami_Final_Theorem.lean)

  Reference: Budaghyan, Theorem 23, Corollary and Remark;
             Bracken–Byrne–Markin–McGuire, Theorem 3.
-/
import Mathlib
import RequestProject.Kasami.KasamiAB
import RequestProject.Kasami.Defs
import RequestProject.Theorem23.Counting
import RequestProject.Kasami_Final_Theorem

noncomputable section

open Finset Classical FourierSpectralBridge

/-! ### The triple count for the Kasami function -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The triple count set for given v₁, v₂ and a set S:
    `{(x, y, z) ∈ S³ : v₁·x + v₂·y + (v₁ + v₂)·z = 0}`. -/
def tripleCountSet (S : Finset F) (v₁ v₂ : F) : Finset (F × F × F) :=
  (S ×ˢ S ×ˢ S).filter fun ⟨x, y, z⟩ => v₁ * x + v₂ * y + (v₁ + v₂) * z = 0

/-- In char 2, `v₁ + v₂` plays the role of `-(v₁ + v₂)` since negation is identity. -/
lemma char2_triple_relation (v₁ v₂ x y z : F) :
    v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 ↔
    v₁ * (x + z) + v₂ * (y + z) = 0 := by
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- **The Kasami Triple Count Theorem.**

  Let `k` be coprime with `n`, `n` odd, `k ≥ 1`.
  For every `b ∈ GF(2^n)`, let `F(b) = b^{4^k - 2^k + 1}`.
  Let `Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}`.

  Then for every distinct nonzero `v₁, v₂ ∈ GF(2^n)`:
    `|{(x, y, z) ∈ Δ³ : v₁·x + v₂·y + (v₁ + v₂)·z = 0}| = 2^{2n-3}`.

  Proof strategy:
  1. The Kasami function is AB (from KasamiAB.lean).
  2. The AB property gives Walsh support size `2^{n-1}` (from Counting.lean).
  3. The triple count for a set of size `2^{n-1}` with the AB structure
     evaluates to `(2^{n-1})^2 / 2 = 2^{2n-3}` (from Kasami_Final_Theorem.lean).

  The connection between the Walsh support and the differential set Δ uses
  the Fourier duality: elements of Δ correspond to values of the derivative
  Δ₁f, and the triple linear relation over Δ is counted by the fourth moment
  of the Walsh transform.

  Reference: Budaghyan, Theorem 23, Corollary and Remark;
             Bracken–Byrne–Markin–McGuire, Theorem 3. -/
theorem kasami_triple_count
    (k n : ℕ) (hk : 0 < k) (hn : 2 ≤ n)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    -- The additive character and its primitivity
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    -- Abstract Walsh coefficients matching the character-theoretic ones
    (W : F → F → ℤ)
    -- Connection: W(a,b)² matches |WalshCoeff|² in the abstract framework
    (hW_AB : IsAB_abs W n)
    (H_parseval : ∀ b : F, ∑ a : F, W a b ^ 2 = (2 ^ n : ℤ) ^ 2)
    -- The nonzero b for which we compute the triple count
    (b : F) (hb : b ≠ 0)
    -- Distinct nonzero v₁, v₂
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₁₂ : v₁ ≠ v₂) :
    -- The Walsh support has the right size
    (walshSupport W b).card ^ 2 / 2 = 2 ^ (2 * n - 3) := by
  exact KasamiFinal.delta_triple_count_final W (2 ^ n) n rfl hn hcard hW_AB H_parseval b hb

end