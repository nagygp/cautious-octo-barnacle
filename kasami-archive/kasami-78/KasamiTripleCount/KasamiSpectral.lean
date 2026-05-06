/-
  KasamiSpectral.lean

  Spectral properties of the Kasami function:
  - APN (Almost Perfect Nonlinear) property
  - AB (Almost Bent) property
  - |Δ| = 2^(n-1) under APN
  - Spectral collapse: tripleSpectral = |Δ|³ under AB

  Reference:
  - Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions", Theorem 3
  - Budaghyan, "Construction and Analysis of Cryptographic Functions", Theorem 2.3
-/
import Mathlib
import KasamiTripleCount.KasamiDefs
import KasamiTripleCount.KasamiCharacters
import KasamiTripleCount.KasamiFourier

noncomputable section

open Finset BigOperators Complex

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## APN Property of the Kasami Function -/

/-- The differential count for the Kasami function:
    `δ_f(u,v) = |{x : f(x+u) + f(x) = v}|`. -/
def kasamiDiffCount (k : ℕ) (u v : F) : ℕ :=
  (Finset.univ.filter fun x =>
    kasamiFun F k (x + u) + kasamiFun F k x = v).card

/-- **Kasami APN Theorem** (Bracken–Byrne–Markin–McGuire, Theorem 3;
    Budaghyan, Theorem 2.3).

    The Kasami function x^(4^k − 2^k + 1) is APN over GF(2^n)
    when gcd(k, n) = 1 and n ≥ 3. -/
theorem kasami_is_APN
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    ∀ u : F, u ≠ 0 → ∀ v : F, kasamiDiffCount F k u v ≤ 2 := by
  sorry

/-! ## AB Property: APN Power Functions are AB for Odd n -/

/-- **APN power functions are AB for odd n.**
    |W_f(a,b)|² ∈ {0, 2^{n+1}} for b ≠ 0.

    Reference: Chabaud–Vaudenay (1994), Nyberg (1994). -/
theorem APN_power_implies_AB_odd
    {n : ℕ} (d : ℕ) (hn_odd : n % 2 = 1) (hn : 3 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (hAPN : ∀ u : F, u ≠ 0 → ∀ v : F,
      (Finset.univ.filter fun x => (x + u) ^ d + x ^ d = v).card ≤ 2)
    (a b : F) (hb : b ≠ 0) :
    Complex.normSq (∑ x : F, (kasamiChar F) (a * x + b * x ^ d)) = 0 ∨
    Complex.normSq (∑ x : F, (kasamiChar F) (a * x + b * x ^ d)) =
      (2 : ℝ) ^ (n + 1) := by
  sorry

/-! ## Delta Cardinality Under APN -/

/-
Under APN, each value in Δ has exactly 2 preimages under
    b ↦ f(b) + f(b+1) + 1.
-/
lemma kasamiDelta_preimage_two
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (d : F) (hd : d ∈ kasamiDelta F k) :
    (Finset.univ.filter fun b =>
      kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d).card = 2 := by
  -- By APN, each nonempty fiber has at most 2 elements.
  have h_fiber_le_two (d : F) :
      (Finset.univ.filter fun b => (kasamiFun F k b) + (kasamiFun F k (b + 1)) + 1 = d).card ≤ 2 := by
        have := @kasami_is_APN F;
        convert this k hn hk hcard hcoprime 1 ( show ( 1 : F ) ≠ 0 from by aesop ) ( d + 1 ) using 1;
        simp +decide [ kasamiFun, kasamiDiffCount ];
        congr! 1;
        grind;
  -- Since $d \in \Delta$, there exists $b \in F$ such that $f(b) + f(b+1) + 1 = d$.
  obtain ⟨b, hb⟩ : ∃ b : F, (kasamiFun F k b) + (kasamiFun F k (b + 1)) + 1 = d := by
    unfold kasamiDelta at hd; aesop;
  refine' le_antisymm ( h_fiber_le_two d ) _;
  refine' Finset.one_lt_card.mpr ⟨ b, _, b + 1, _, _ ⟩ <;> simp_all +decide [ add_assoc ];
  grind

/-- The fiber sum identity. -/
lemma kasamiDelta_fiber_sum (k : ℕ) :
    ∑ d ∈ kasamiDelta F k,
      (Finset.univ.filter fun b =>
        kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d).card =
      Fintype.card F := by
  simp +decide only [card_filter]
  rw [Finset.sum_comm]
  simp +decide [kasamiDelta]

/-- **Delta cardinality**: |Δ| = 2^(n-1) under APN. -/
theorem kasamiDelta_card
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    (kasamiDelta F k).card = 2 ^ (n - 1) := by
  have hfiber := kasamiDelta_preimage_two F k hn hk hcard hcoprime
  have hsum := kasamiDelta_fiber_sum F k
  have hsum2 : (kasamiDelta F k).card * 2 = Fintype.card F := by
    rw [← hsum]
    rw [Finset.sum_congr rfl (fun d hd => hfiber d hd)]
    simp [Finset.sum_const]
  rw [hcard] at hsum2
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    have hn1 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn1]
    rw [pow_succ]
  omega

/-! ## Spectral Collapse: tripleSpectral = |Δ|³ under AB -/

/-- **Vanishing of nonzero-frequency contributions** under AB.

    For the Kasami function with AB spectrum, the spectral sum over a ≠ 0 vanishes.
    This uses the three-design property of the AB Walsh spectrum. -/
theorem tripleSpectral_nonzero_vanish
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    ∑ a ∈ Finset.univ.filter (· ≠ (0 : F)),
      deltaFourier F k (v₁ * a) *
      deltaFourier F k (v₂ * a) *
      deltaFourier F k ((v₁ + v₂) * a) = 0 := by
  sorry

/-- The triple spectral sum equals |Δ|³. -/
theorem tripleSpectral_eq_deltaCube
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    tripleSpectral F k v₁ v₂ =
      ↑((kasamiDelta F k).card ^ 3 : ℕ) := by
  unfold tripleSpectral
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F))]
  have hvanish := tripleSpectral_nonzero_vanish F k hn hk hn_odd hcard hcoprime
    v₁ v₂ hv₁ hv₂ hne
  have herase : Finset.univ.erase (0 : F) = Finset.univ.filter (· ≠ (0 : F)) := by
    ext a; simp [Finset.mem_erase, Finset.mem_filter]
  rw [herase, hvanish, add_zero]
  simp only [mul_zero, deltaFourier_zero]
  push_cast; ring

/-! ## Arithmetic Lemmas -/

/-- (2^{n-1})³ = 2^{3n-3} for n ≥ 1. -/
lemma pow_cube_identity (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ (n - 1)) ^ 3 = 2 ^ (3 * n - 3) := by
  rw [← Nat.pow_mul]; congr 1; omega

/-- 2^{3n-3} = 2^n · 2^{2n-3} for n ≥ 3. -/
lemma pow_split (n : ℕ) (hn : 3 ≤ n) :
    2 ^ (3 * n - 3) = 2 ^ n * 2 ^ (2 * n - 3) := by
  rw [← pow_add]; congr 1; omega

end