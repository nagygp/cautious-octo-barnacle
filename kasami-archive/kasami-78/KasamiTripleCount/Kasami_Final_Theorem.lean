/-
  Kasami_Final_Theorem.lean

  The Kasami Triple-Count Theorem, combining all components:

  1. KasamiFourier.lean — Fourier identity: |F| · |tripleSet| = tripleSpectral
  2. KasamiSpectral.lean — APN, AB, |Δ| = 2^(n-1), spectral collapse

  The final proof:
    |F| · |tripleSet| = tripleSpectral = |Δ|³ = (2^{n-1})³ = 2^{3n-3} = 2^n · 2^{2n-3}
    ⟹ |tripleSet| = 2^{2n-3}

  Reference:
  - Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions", Theorem 3
  - Budaghyan, "Construction and Analysis of Cryptographic Functions", Theorem 2.3
-/
import KasamiTripleCount.KasamiSpectral

noncomputable section

open Finset BigOperators Complex

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The Kasami Triple-Count Theorem -/

/-- **The Kasami Triple-Count Theorem.**

    For the Kasami function f(x) = x^(4^k − 2^k + 1) over GF(2^n) with
    gcd(k,n) = 1, n odd, and n ≥ 3:

      |{(x, y, z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}| = 2^{2n−3}

    for all distinct nonzero v₁, v₂ ∈ F.

    Proof:
    1. Fourier identity: |F| · |tripleSet| = tripleSpectral
    2. Spectral collapse (AB): tripleSpectral = |Δ|³ = (2^{n-1})³ = 2^{3n-3}
    3. |Δ| = 2^{n-1} (from APN, via 2-to-1 derivative)
    4. Cancel |F| = 2^n: |tripleSet| = 2^{3n-3}/2^n = 2^{2n-3}
-/
theorem kasami_triple_count
    {n : ℕ} (k : ℕ)
    (hn : 3 ≤ n)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (tripleSet F k v₁ v₂).card = 2 ^ (2 * n - 3) := by
  have hk : 1 ≤ k := by
    by_contra h; push_neg at h; interval_cases k
    simp [Nat.Coprime] at hcoprime; omega
  -- Step 1: Fourier identity
  have hfourier := fourier_triple_identity F k v₁ v₂
  -- Step 2: Spectral collapse
  have hspectral := tripleSpectral_eq_deltaCube F k hn hk hn_odd hcard hcoprime
    v₁ v₂ hv₁ hv₂ hne
  -- Step 3: Delta cardinality
  have hdelta := kasamiDelta_card F k hn hk hcard hcoprime
  -- Combine
  rw [hspectral] at hfourier
  rw [hdelta] at hfourier
  rw [hcard] at hfourier
  -- Extract ℕ equation from ℂ equation
  have hinj : (2 ^ n) * (tripleSet F k v₁ v₂).card = (2 ^ (n - 1)) ^ 3 := by
    exact_mod_cast hfourier
  -- Arithmetic
  rw [pow_cube_identity n (by omega), pow_split n hn] at hinj
  exact mul_left_cancel₀ (by positivity) hinj

/-! ## The Conjecture (restated with n-odd hypothesis) -/

/-- **Kasami Triple-Count Conjecture** (with the necessary n-odd hypothesis).

    The original conjecture statement requires adding `n % 2 = 1` since the
    AB property (and hence the spectral collapse) only holds for odd n.

    For even n, the Kasami function is still APN but not AB; the Walsh spectrum
    takes values in {0, ±2^{n/2}, ±2^{(n+2)/2}} instead. -/
theorem kasami_triple_count_conjecture
    (n : ℕ) (k : ℕ)
    (hn : 3 ≤ n)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (tripleSet F k v₁ v₂).card = 2 ^ (2 * n - 3) :=
  kasami_triple_count F k hn hn_odd hcard hcoprime v₁ v₂ hv₁ hv₂ hne

end
