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
import RequestProject.KasamiDefs
import RequestProject.KasamiCharacters
import RequestProject.KasamiFourier

noncomputable section

open Finset BigOperators Complex

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Characteristic 2 helper lemmas -/

/-- In characteristic 2, x + x = 0. -/
lemma charTwo_add_self (x : F) : x + x = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  calc x + x = 2 * x := by ring
  _ = 0 * x := by rw [h2]
  _ = 0 := by ring

/-- In characteristic 2, -x = x. -/
lemma charTwo_neg (x : F) : -x = x :=
  neg_eq_of_add_eq_zero_left (charTwo_add_self F x)

/-- In characteristic 2, x - y = x + y. -/
lemma charTwo_sub (x y : F) : x - y = x + y := by
  rw [sub_eq_add_neg, charTwo_neg]

/-- In characteristic 2, (b+1)+1 = b. -/
lemma charTwo_add_one_add_one (b : F) : (b + 1) + 1 = b := by
  have h11 : (1 : F) + 1 = 0 := by
    have h : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have : (2 : F) = 1 + 1 := by norm_num
    rw [this] at h; exact h
  have : b + 1 + 1 = b + (1 + 1) := by ring
  rw [this, h11, add_zero]

/-- b ≠ b + 1 in any nontrivial ring. -/
lemma ne_add_one (b : F) : b ≠ b + 1 := by
  intro h
  have : b + 1 - b = b - b := by rw [← h]
  simp at this

/-! ## APN Property of the Kasami Function -/

/-- The differential count for the Kasami function:
    `δ_f(u,v) = |{x : f(x+u) + f(x) = v}|`. -/
def kasamiDiffCount (k : ℕ) (u v : F) : ℕ :=
  (Finset.univ.filter fun x =>
    kasamiFun F k (x + u) + kasamiFun F k x = v).card

/-- **Kasami APN Theorem**.
    The Kasami function x^(4^k − 2^k + 1) is APN over GF(2^n)
    when gcd(k, n) = 1 and n ≥ 3. -/
theorem kasami_is_APN
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    ∀ u : F, u ≠ 0 → ∀ v : F, kasamiDiffCount F k u v ≤ 2 := by
  sorry

/-! ## AB Property: APN Power Functions are AB for Odd n -/

/-- **APN power functions are AB for odd n.** -/
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

/-- The derivative g(b) = f(b) + f(b+1) + 1 gives the same value for b and b+1
    in characteristic 2 (since (b+1)+1 = b). -/
lemma derivative_symmetric (k : ℕ) (b : F) :
    kasamiFun F k (b + 1) + kasamiFun F k ((b + 1) + 1) + 1 =
    kasamiFun F k b + kasamiFun F k (b + 1) + 1 := by
  rw [charTwo_add_one_add_one]; ring

/-
The fiber of the derivative map has ≤ 2 elements (from APN).
-/
lemma kasamiDelta_fiber_le_two
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (d : F) :
    (Finset.univ.filter fun b =>
      kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d).card ≤ 2 := by
  convert kasami_is_APN F k hn hk hcard hcoprime 1 one_ne_zero ( d - 1 ) using 1;
  refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide [ add_comm, add_left_comm, add_assoc ];
  · grind;
  · grind

/-- b and b+1 are both in any fiber containing b. -/
lemma kasamiDelta_fiber_pair (k : ℕ) (b d : F)
    (hb : kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d) :
    b + 1 ∈ (Finset.univ.filter fun b' =>
      kasamiFun F k b' + kasamiFun F k (b' + 1) + 1 = d) := by
  simp only [mem_filter, mem_univ, true_and]
  have h11 : (b + 1 : F) + 1 = b := charTwo_add_one_add_one F b
  rw [h11, show kasamiFun F k (b + 1) + kasamiFun F k b + 1 =
    kasamiFun F k b + kasamiFun F k (b + 1) + 1 from by ring, hb]

/-
Each nonempty fiber has at least 2 elements.
-/
lemma kasamiDelta_fiber_ge_two (k : ℕ) (d : F)
    (hd : d ∈ kasamiDelta F k) :
    2 ≤ (Finset.univ.filter fun b =>
      kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d).card := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : F, kasamiFun F k b₀ + kasamiFun F k (b₀ + 1) + 1 = d := by
    unfold kasamiDelta at hd; aesop;
  refine' Finset.one_lt_card.2 ⟨ b₀, _, b₀ + 1, _, _ ⟩ <;> simp_all +decide;
  rw [ ← hb₀, charTwo_add_one_add_one ];
  ring

/-- Under APN, each value in Δ has exactly 2 preimages. -/
lemma kasamiDelta_preimage_two
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (d : F) (hd : d ∈ kasamiDelta F k) :
    (Finset.univ.filter fun b =>
      kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d).card = 2 := by
  have hle := kasamiDelta_fiber_le_two F k hn hk hcard hcoprime d
  have hge := kasamiDelta_fiber_ge_two F k d hd
  omega

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
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]; ring
  omega

/-! ## Spectral Collapse: tripleSpectral = |Δ|³ under AB -/

/-- **Vanishing of nonzero-frequency contributions** under AB. -/
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