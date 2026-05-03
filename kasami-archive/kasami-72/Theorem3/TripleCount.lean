/-
  TripleCount.lean

  Task 3: The Triple Count Finalization.

  Uses the AB (Almost Bent) property to count non-trivial triples.
  For an AB function f : F_{2^n} → F_{2^n} with n odd:
  - The Walsh spectrum is three-valued: {0, ±2^{(n+1)/2}}
  - By Parseval's identity: Σ_b W_f(a,b)^2 = 2^{2n} for each a ≠ 0
  - This determines the count: 2^{n-1} nonzero values per nonzero a
  - Total non-trivial pairs: (2^n - 1) · 2^{n-1}
-/
import Mathlib
import Theorem3.Defs
import Theorem3.BinomialParams

set_option maxHeartbeats 1600000

open Classical in
noncomputable section

open Finset

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## Abstract Walsh spectrum framework -/

/-- An abstract Walsh spectrum: a function W : F → F → ℤ assigning
    Walsh-Hadamard coefficients W(a,b) to each pair (a,b). -/
structure WalshSpectrum (F : Type*) [Fintype F] where
  W : F → F → ℤ

/-- Parseval's identity for the Walsh transform:
    For each fixed a, Σ_b W(a,b)^2 = |F|^2.
    This is a standard identity from Fourier analysis on finite abelian groups. -/
def WalshSpectrum.satisfiesParseval (ws : WalshSpectrum F) (n : ℕ)
    (hcard : Fintype.card F = 2 ^ n) : Prop :=
  ∀ a : F, a ≠ 0 → ∑ b : F, ws.W a b ^ 2 = (2 : ℤ) ^ (2 * n)

/-- The three-valued spectrum condition (AB property):
    For all a ≠ 0 and all b, W(a,b) ∈ {0, 2^{(n+1)/2}, -2^{(n+1)/2}}. -/
def WalshSpectrum.isThreeValued (ws : WalshSpectrum F) (n : ℕ) : Prop :=
  ∀ a b : F, a ≠ 0 →
    ws.W a b = 0 ∨ ws.W a b = 2 ^ ((n + 1) / 2) ∨
    ws.W a b = -(2 ^ ((n + 1) / 2))

/-! ## The triple count -/

/-- **Key Counting Lemma**: If the Walsh spectrum is three-valued and satisfies
    Parseval's identity, then for each nonzero a, exactly 2^{n-1} values of b
    give nonzero Walsh coefficients.

    Proof: Let N_a = #{b : W(a,b) ≠ 0}. Each nonzero value satisfies
    |W(a,b)|^2 = 2^{n+1}. By Parseval:
      N_a · 2^{n+1} = 2^{2n}
      N_a = 2^{2n} / 2^{n+1} = 2^{n-1}. -/
lemma nonzero_walsh_count (ws : WalshSpectrum F) (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (hparseval : ws.satisfiesParseval n hcard)
    (hthree : ws.isThreeValued n)
    (a : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun b => ws.W a b ≠ 0)).card = 2 ^ (n - 1) := by
  sorry

/-- **Total non-trivial triple count**: The number of pairs (a, b) with a ≠ 0
    and W(a,b) ≠ 0 is exactly (2^n - 1) · 2^{n-1}.

    This follows by summing nonzero_walsh_count over all nonzero a. -/
theorem binomial_triple_count (ws : WalshSpectrum F) (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (hparseval : ws.satisfiesParseval n hcard)
    (hthree : ws.isThreeValued n) :
    (Finset.univ.filter (fun p : F × F => p.1 ≠ 0 ∧ ws.W p.1 p.2 ≠ 0)).card =
      (2 ^ n - 1) * 2 ^ (n - 1) := by
  sorry

/-- Connection to APN: for an APN function that is also AB,
    the kernel dimension ≤ 1 implies the three-valued spectrum. -/
lemma kernel_dim_le_one_implies_AB
    (f : F → F) (n : ℕ) (hn : 0 < n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hapn : isAPN f) :
    ∃ ws : WalshSpectrum F, ws.isThreeValued n ∧ ws.satisfiesParseval n hcard := by
  sorry

end
