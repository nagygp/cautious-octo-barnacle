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

/-! ## APN Property of the Kasami Function

The Kasami function f(x) = x^(4^k − 2^k + 1) is APN when gcd(k,n) = 1.

The proof reduces to showing the derivative equation has ≤ 2 solutions:
1. Normalize: substitute y = x/u to get a shifted linearized equation
2. Factor: the linearized polynomial factors through Frobenius compositions
3. Bound: the kernel has at most 2 elements when gcd(k,n) = 1

Reference: Bracken–Byrne–Markin–McGuire, Theorem 3 (normalization + factorization);
           Budaghyan, Theorem 2.3 (APN for the full Kasami family).
-/

/-- The differential count for the Kasami function:
    `δ_f(u,v) = |{x : f(x+u) + f(x) = v}|`. -/
def kasamiDiffCount (k : ℕ) (u v : F) : ℕ :=
  (Finset.univ.filter fun x =>
    kasamiFun F k (x + u) + kasamiFun F k x = v).card

/-- **Kasami APN Theorem** (Bracken–Byrne–Markin–McGuire, Theorem 3;
    Budaghyan, Theorem 2.3).

    The Kasami function x^(4^k − 2^k + 1) is APN over GF(2^n)
    when gcd(k, n) = 1 and n ≥ 3.

    Proof outline:
    - The derivative D_u f(x) = f(x+u)+f(x) reduces to a linearized
      polynomial equation after normalizing by y = x/u.
    - The resulting polynomial y^{2^{2k}} + y^{2^k} + y factors through
      compositions of Frobenius-type maps.
    - When gcd(k,n) = 1, the kernel of each factor has bounded dimension
      over GF(2), yielding at most 2 solutions.
    - The key step uses that gcd(2k, n) | gcd(k, n) = 1, so the
      iterated Frobenius y ↦ y^{2^k} acts as an automorphism on GF(2^n),
      forcing the kernel to be trivial or of dimension 1 over GF(2). -/
theorem kasami_is_APN
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    ∀ u : F, u ≠ 0 → ∀ v : F, kasamiDiffCount F k u v ≤ 2 := by
  sorry

/-! ## AB Property: APN Power Functions are AB for Odd n

For power functions f(x) = x^d over GF(2^n) with n odd,
APN is equivalent to AB. This follows from:
- The Walsh transform of power functions has special structure
- The fourth moment identity + Parseval + positivity force 3-valued spectrum
- For n odd, the cross-correlation values are constrained to {-1, -1±2^{(n+1)/2}}

Reference: Chabaud–Vaudenay (1994), Nyberg (1994).
-/

/-- **APN power functions are AB for odd n.**
    The Walsh spectrum of an APN power function x^d over GF(2^n) with n odd
    takes values in {0, ±2^{(n+1)/2}}, i.e., |W_f(a,b)|² ∈ {0, 2^{n+1}}.

    Proof outline:
    - For power functions, W_f(a,b) = W_f(1, b·a^{-d}) when a ≠ 0.
    - Parseval: ∑_b |W(1,b)|² = 2^{2n}.
    - Fourth moment from APN: ∑_b |W(1,b)|⁴ = 2^{n+1} · ∑_b |W(1,b)|².
    - Combined: all nonzero |W(1,b)|² equal 2^{n+1}.
    - For n odd, this gives |W_f(a,b)| ∈ {0, 2^{(n+1)/2}}. -/
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

/-! ## Delta Cardinality Under APN

Under APN, the derivative map b ↦ f(b+1) + f(b) is 2-to-1 on its image.
Therefore |Δ| = |F|/2 = 2^{n-1}.
-/

/-- Under APN, each value in Δ has exactly 2 preimages. -/
lemma kasamiDelta_preimage_two
    {n : ℕ} (k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n)
    (d : F) (hd : d ∈ kasamiDelta F k) :
    (Finset.univ.filter fun b =>
      kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d).card = 2 := by
  -- Each fiber has ≤ 2 elements (from APN)
  have hAPN := kasami_is_APN F k hn hk hcard hcoprime
  -- The derivative at u=1 gives: f(x+1)+f(x) = v has ≤ 2 solutions
  have h_le : ∀ d' ∈ kasamiDelta F k,
      (Finset.univ.filter fun b =>
        kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d').card ≤ 2 := by
    intro d' _
    have := hAPN 1 one_ne_zero (d' - 1)
    unfold kasamiDiffCount at this
    convert this using 2; ext x; simp [kasamiFun]; ring_nf
    constructor <;> intro h <;> linarith
  -- The total of all fibers equals |F|
  have hsum : ∑ d' ∈ kasamiDelta F k,
      (Finset.univ.filter fun b =>
        kasamiFun F k b + kasamiFun F k (b + 1) + 1 = d').card =
      Fintype.card F := by
    simp +decide only [card_filter]
    rw [Finset.sum_comm]
    simp +decide [kasamiDelta]
  -- Each fiber has ≥ 2 elements (each d has at least b and b+1 mapping to it)
  -- Combined with ≤ 2, we get = 2
  sorry

/-- The fiber sum identity. -/
omit [CharP F 2] in
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

/-! ## Spectral Collapse: tripleSpectral = |Δ|³ under AB

The key deep cancellation: for distinct nonzero v₁, v₂, the sum
∑_{a≠0} δ̂(v₁a)·δ̂(v₂a)·δ̂((v₁+v₂)a) = 0 under AB.

This uses the three-design property of the AB Walsh spectrum.
-/

/-- **Vanishing of nonzero-frequency contributions** under AB.

    For the Kasami function with AB spectrum, the spectral sum over a ≠ 0 vanishes.

    Proof outline:
    - δ̂(c) = (1/2)·∑_b χ(c·g(b)) where g(b) = f(b+1)+f(b)+1
    - Under AB, each δ̂(c) for c ≠ 0 is expressed via Walsh support sums
    - The triple product cancels due to equidistribution in the AB spectrum
    - This is the three-design property: AB Walsh supports form a 3-design
      in the dual group. -/
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
