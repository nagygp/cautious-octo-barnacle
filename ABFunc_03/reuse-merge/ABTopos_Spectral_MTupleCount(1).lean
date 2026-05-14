import Mathlib

/-!
# Generalized m-Tuple Count Theory — Full Proofs

## Theorem KR₁ (APN Cardinality) — §2, fully proved
  |Δ(f)| = 2^{n-1}

## Theorem KR₂ (Spectral Identity) — §3
  2ⁿ · κ_m = δᵐ

KR₂ uses Mathlib's `AddChar` (providing `AddChar.sum_mulShift` for character
orthogonality). All lemmas including `fourier_counting_formula` are fully proved.

## Derived Results — §§5–8, fully proved
  - Primal, Dual, Equivalence, Complete Package

## References
- [Kasami 1971], [Chabaud–Vaudenay 1994], [BBMM 2006, Thm 3]
-/

open Finset BigOperators

noncomputable section

-- ════════════════════════════════════════════════════════════════════
-- §1  DEFINITIONS
-- ════════════════════════════════════════════════════════════════════

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

def differentialMap (f : 𝔽 → 𝔽) (a : 𝔽) : 𝔽 → 𝔽 :=
  fun x => f (x + a) + f x

def IsAPN (f : 𝔽 → 𝔽) : Prop :=
  ∀ a : 𝔽, a ≠ 0 → ∀ b : 𝔽,
    (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card ≤ 2

def differentialSet (f : 𝔽 → 𝔽) : Finset 𝔽 :=
  univ.image (fun x => f x + f (x + 1) + 1)

def mTupleSet (f : 𝔽 → 𝔽) (m : ℕ) (coeffs : Fin m → 𝔽) : Finset (Fin m → 𝔽) :=
  univ.filter fun x =>
    (∀ i, x i ∈ differentialSet 𝔽 f) ∧ ∑ i, coeffs i * x i = 0

def mTupleCount (f : 𝔽 → 𝔽) (m : ℕ) (coeffs : Fin m → 𝔽) : ℕ :=
  (mTupleSet 𝔽 f m coeffs).card

-- ════════════════════════════════════════════════════════════════════
-- §1b  UTILITIES
-- ════════════════════════════════════════════════════════════════════

theorem differentialSet_card_eq (f : 𝔽 → 𝔽) :
    (differentialSet 𝔽 f).card = (univ.image (differentialMap 𝔽 f 1)).card := by
  have h : differentialSet 𝔽 f =
      (univ.image (differentialMap 𝔽 f 1)).image (· + 1) := by
    simp only [image_image, differentialSet]
    congr 1; ext x; simp [differentialMap]; ring
  rw [h]; exact card_image_of_injOn (fun _ _ _ _ heq => add_right_cancel heq)

-- ════════════════════════════════════════════════════════════════════
-- §2  KR₁ — APN CARDINALITY   [FULLY PROVED]
-- ════════════════════════════════════════════════════════════════════

section KR1
variable [CharP 𝔽 2]

theorem char2_cancel (x a : 𝔽) : x + a + a = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem differential_pairing (f : 𝔽 → 𝔽) (a x : 𝔽) :
    differentialMap 𝔽 f a (x + a) = differentialMap 𝔽 f a x := by
  unfold differentialMap; rw [char2_cancel 𝔽 x a]; ring

theorem shift_ne (a : 𝔽) (ha : a ≠ 0) (x : 𝔽) : x + a ≠ x := by
  intro h; apply ha
  have := congr_arg (· + (-x)) h; simp at this; exact this

theorem apn_fiber_ge_two (f : 𝔽 → 𝔽) (a : 𝔽) (ha : a ≠ 0)
    (b x₀ : 𝔽) (hx₀ : differentialMap 𝔽 f a x₀ = b) :
    2 ≤ (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card := by
  have hxa : differentialMap 𝔽 f a (x₀ + a) = b := by
    rw [differential_pairing]; exact hx₀
  calc (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card
      ≥ ({x₀, x₀ + a} : Finset 𝔽).card := by
        apply card_le_card; intro y hy
        simp only [mem_insert, mem_singleton] at hy
        exact mem_filter.mpr ⟨mem_univ _,
          by rcases hy with rfl | rfl <;> assumption⟩
    _ = 2 := card_pair (shift_ne 𝔽 a ha x₀).symm

theorem apn_fiber_eq_two (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f)
    (a : 𝔽) (ha : a ≠ 0) (b : 𝔽) (hne : ∃ x, differentialMap 𝔽 f a x = b) :
    (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card = 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  exact le_antisymm (hAPN a ha b) (apn_fiber_ge_two 𝔽 f a ha b x₀ hx₀)

theorem apn_all_image_fibers_eq_two (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f)
    (a : 𝔽) (ha : a ≠ 0) (b : 𝔽)
    (hb : b ∈ univ.image (differentialMap 𝔽 f a)) :
    (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card = 2 := by
  obtain ⟨x₀, _, hx₀⟩ := mem_image.mp hb
  exact apn_fiber_eq_two 𝔽 f hAPN a ha b ⟨x₀, hx₀⟩

theorem apn_image_card (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f) (a : 𝔽) (ha : a ≠ 0) :
    (univ.image (differentialMap 𝔽 f a)).card = Fintype.card 𝔽 / 2 := by
  have h := card_eq_sum_card_image (differentialMap 𝔽 f a) univ
  rw [card_univ] at h
  have h2 : (univ.image (differentialMap 𝔽 f a)).card * 2 = Fintype.card 𝔽 := by
    rw [h, sum_const_nat (apn_all_image_fibers_eq_two 𝔽 f hAPN a ha)]
  omega

/-- ### KR₁ — APN Cardinality
    For APN f over GF(2ⁿ), |Δ(f)| = 2^{n-1}. -/
theorem apn_differentialSet_card (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f)
    (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card 𝔽 = 2 ^ n) :
    (differentialSet 𝔽 f).card = 2 ^ (n - 1) := by
  rw [differentialSet_card_eq, apn_image_card 𝔽 f hAPN 1 one_ne_zero, hcard]
  cases n with | zero => omega | succ n => simp [pow_succ]

end KR1

-- ════════════════════════════════════════════════════════════════════
-- §3  KR₂ — SPECTRAL IDENTITY
-- ════════════════════════════════════════════════════════════════════

/-!
### Infrastructure

We use Mathlib's `AddChar`:
  - `AddChar.map_add_eq_mul`  — ψ(x+y) = ψ(x)·ψ(y)
  - `AddChar.map_zero_eq_one` — ψ(0) = 1
  - `AddChar.sum_mulShift`    — ∑ x, ψ(x·b) = if b=0 then |𝔽| else 0

All character-theory and Fourier lemmas are fully proved from Mathlib.
-/

variable (ψ : AddChar 𝔽 ℂ)

/-- δ̂_ψ(a) = ∑_{x ∈ Δ} ψ(a·x). -/
def deltaHat (f : 𝔽 → 𝔽) (a : 𝔽) : ℂ :=
  ∑ x ∈ differentialSet 𝔽 f, ψ (a * x)

/-- δ̂(0) = |Δ(f)|. -/
theorem deltaHat_zero (f : 𝔽 → 𝔽) :
    deltaHat 𝔽 ψ f 0 = ↑(differentialSet 𝔽 f).card := by
  simp [deltaHat, AddChar.map_zero_eq_one]

/-- AB spectral flatness: ∑_{a≠0} ∏ᵢ δ̂(cᵢ·a) = 0. -/
def IsAB_spectrallyFlat (f : 𝔽 → 𝔽) : Prop :=
  ∀ (m : ℕ) (coeffs : Fin m → 𝔽), (∀ i, coeffs i ≠ 0) →
    ∑ a ∈ univ.filter (· ≠ (0 : 𝔽)), ∏ i, deltaHat 𝔽 ψ f (coeffs i * a) = 0

/-
**Fourier counting formula** [FULLY PROVED].
    κ = (1/|𝔽|) · ∑_a ∏ᵢ δ̂(cᵢ · a).
-/
theorem fourier_counting_formula
    (hψ : ψ.IsPrimitive) (f : 𝔽 → 𝔽) (m : ℕ)
    (coeffs : Fin m → 𝔽) (hcoeffs : ∀ i, coeffs i ≠ 0) :
    (mTupleCount 𝔽 f m coeffs : ℂ) =
      (↑(Fintype.card 𝔽))⁻¹ *
        ∑ a : 𝔽, ∏ i, deltaHat 𝔽 ψ f (coeffs i * a) := by
  field_simp;
  -- Expand the product inside the sum.
  have h_expand : ∑ a : 𝔽, ∏ i, deltaHat 𝔽 ψ f (coeffs i * a) = ∑ a : 𝔽, ∑ x : Fin m → 𝔽, if (∀ i, x i ∈ differentialSet 𝔽 f) then ψ (a * ∑ i, coeffs i * x i) else 0 := by
    have h_expand : ∀ a : 𝔽, ∏ i : Fin m, deltaHat 𝔽 ψ f (coeffs i * a) = ∑ x : Fin m → 𝔽, if ∀ i, x i ∈ differentialSet 𝔽 f then ∏ i : Fin m, ψ (coeffs i * a * x i) else 0 := by
      intro a
      simp [deltaHat];
      rw [ Finset.prod_sum ];
      rw [ ← Finset.sum_filter ];
      refine' Finset.sum_bij ( fun p hp => fun i => p i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide;
      · simp +contextual [ funext_iff ];
      · exact fun b hb => ⟨ fun i _ => b i, hb, rfl ⟩;
    simp +decide only [h_expand];
    refine' Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun x hx => _;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, AddChar.map_add_eq_mul ];
    induction' ( Finset.univ : Finset ( Fin m ) ) using Finset.induction <;> simp_all +decide [ Finset.prod_insert, Finset.sum_insert ];
    split_ifs at * <;> simp_all +decide [ AddChar.map_add_eq_mul ];
  -- Apply the orthogonality relation of the character ψ.
  have h_orthogonality : ∀ x : Fin m → 𝔽, (∑ a : 𝔽, ψ (a * ∑ i, coeffs i * x i)) = if ∑ i, coeffs i * x i = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
    intro x
    by_cases h_sum_zero : ∑ i, coeffs i * x i = 0;
    · simp +decide [ h_sum_zero ];
    · have := AddChar.sum_eq_zero_of_ne_one ( show ψ ≠ 1 from ?_ );
      · convert this using 1;
        · exact Equiv.sum_comp ( Equiv.mulRight₀ _ h_sum_zero ) _;
        · exact if_neg h_sum_zero;
      · rintro rfl; simp_all +decide [ AddChar.IsPrimitive ] ;
        exact hψ ( show ( 1 : 𝔽 ) ≠ 0 by simp +decide ) ( by ext; simp +decide [ AddChar.mulShift ] );
  rw [ h_expand, Finset.sum_comm ];
  simp +decide [ Finset.sum_ite, h_orthogonality ];
  exact congr_arg Finset.card ( by ext; simp +decide [ mTupleSet ] )

/-- Splitting at a = 0. -/
theorem fourier_sum_split (f : 𝔽 → 𝔽) (m : ℕ) (coeffs : Fin m → 𝔽) :
    ∑ a : 𝔽, ∏ i, deltaHat 𝔽 ψ f (coeffs i * a) =
      ∏ i, deltaHat 𝔽 ψ f (coeffs i * 0) +
        ∑ a ∈ univ.filter (· ≠ (0 : 𝔽)),
          ∏ i, deltaHat 𝔽 ψ f (coeffs i * a) := by
  rw [← add_sum_erase univ _ (mem_univ 0)]
  congr 1; apply sum_congr _ (fun _ _ => rfl)
  ext a; simp [mem_erase, mem_filter, and_comm]

/-- At a = 0 the product = |Δ|^m. -/
theorem fourier_zero_term (f : 𝔽 → 𝔽) (m : ℕ) (coeffs : Fin m → 𝔽) :
    ∏ i : Fin m, deltaHat 𝔽 ψ f (coeffs i * 0) =
      ↑((differentialSet 𝔽 f).card ^ m) := by
  simp only [mul_zero, deltaHat_zero]; push_cast; simp [prod_const]

/-- ### KR₂ — Spectral Identity (ℂ) -/
theorem spectral_identity_complex
    (hψ : ψ.IsPrimitive) (f : 𝔽 → 𝔽) (m : ℕ)
    (coeffs : Fin m → 𝔽) (hcoeffs : ∀ i, coeffs i ≠ 0)
    (hAB : IsAB_spectrallyFlat 𝔽 ψ f) :
    (↑(Fintype.card 𝔽) : ℂ) * ↑(mTupleCount 𝔽 f m coeffs) =
      ↑((differentialSet 𝔽 f).card ^ m) := by
  rw [fourier_counting_formula 𝔽 ψ hψ f m coeffs hcoeffs, fourier_sum_split,
      hAB m coeffs hcoeffs, add_zero, fourier_zero_term]
  have hne : (↑(Fintype.card 𝔽) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- ### KR₂ — Spectral Identity (ℕ) -/
theorem spectral_identity
    (hψ : ψ.IsPrimitive) (f : 𝔽 → 𝔽) (m : ℕ)
    (coeffs : Fin m → 𝔽) (hcoeffs : ∀ i, coeffs i ≠ 0)
    (hAB : IsAB_spectrallyFlat 𝔽 ψ f) :
    Fintype.card 𝔽 * mTupleCount 𝔽 f m coeffs =
      (differentialSet 𝔽 f).card ^ m := by
  exact_mod_cast spectral_identity_complex 𝔽 ψ hψ f m coeffs hcoeffs hAB

-- ════════════════════════════════════════════════════════════════════
-- §4  ARITHMETIC   [FULLY PROVED]
-- ════════════════════════════════════════════════════════════════════

private theorem sub_bound (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m ≤ (m - 1) * n := by
  calc m ≤ (m - 1) + (m - 1) := by omega
    _ = (m - 1) * 2 := by ring
    _ ≤ (m - 1) * n := Nat.mul_le_mul_left _ (by omega)

theorem power_of_power (n m : ℕ) :
    (2 ^ (n - 1)) ^ m = 2 ^ (m * (n - 1)) := by
  rw [← pow_mul]; ring_nf

theorem exponent_identity (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m * (n - 1) = n + ((m - 1) * n - m) := by
  zify [show 1 ≤ n by omega, show 1 ≤ m by omega, sub_bound n m hn hm]; ring

theorem exponent_split (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    2 ^ (m * (n - 1)) = 2 ^ n * 2 ^ ((m - 1) * n - m) := by
  rw [← pow_add, exponent_identity n m hn hm]

theorem power_split (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    (2 ^ (n - 1)) ^ m = 2 ^ n * 2 ^ ((m - 1) * n - m) := by
  rw [power_of_power, exponent_split n m hn hm]

theorem parseval_arithmetic (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    2 ^ n * 2 ^ ((m - 1) * n - m) = (2 ^ (n - 1)) ^ m :=
  (power_split n m hn hm).symm

-- ════════════════════════════════════════════════════════════════════
-- §5  PRIMAL   [FULLY PROVED]
-- ════════════════════════════════════════════════════════════════════

theorem primal_mTupleCount
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hδ : δ = 2 ^ (n - 1)) (hKR₂ : 2 ^ n * κ = δ ^ m) :
    κ = 2 ^ ((m - 1) * n - m) := by
  rw [hδ, power_split n m hn hm] at hKR₂
  exact mul_left_cancel₀ (by positivity) hKR₂

theorem triple_count (n δ κ : ℕ) (hn : 3 ≤ n)
    (hδ : δ = 2 ^ (n - 1)) (hKR₂ : 2 ^ n * κ = δ ^ 3) :
    κ = 2 ^ (2 * n - 3) := by
  simpa using primal_mTupleCount n 3 δ κ hn (by omega) hδ hKR₂

theorem quadruple_count (n δ κ : ℕ) (hn : 3 ≤ n)
    (hδ : δ = 2 ^ (n - 1)) (hKR₂ : 2 ^ n * κ = δ ^ 4) :
    κ = 2 ^ (3 * n - 4) := by
  simpa using primal_mTupleCount n 4 δ κ hn (by omega) hδ hKR₂

theorem quintuple_count (n δ κ : ℕ) (hn : 3 ≤ n)
    (hδ : δ = 2 ^ (n - 1)) (hKR₂ : 2 ^ n * κ = δ ^ 5) :
    κ = 2 ^ (4 * n - 5) := by
  simpa using primal_mTupleCount n 5 δ κ hn (by omega) hδ hKR₂

-- ════════════════════════════════════════════════════════════════════
-- §6  DUAL   [FULLY PROVED]
-- ════════════════════════════════════════════════════════════════════

theorem dual_count_product (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    2 ^ n * 2 ^ ((m - 1) * n - m) = 2 ^ (m * n - m) := by
  rw [← pow_add]; congr 1
  zify [show 1 ≤ n by omega, show 1 ≤ m by omega, sub_bound n m hn hm,
        show m ≤ m * n by nlinarith]; ring

theorem recover_delta (d n m : ℕ) (hm : m ≠ 0) (hn : 1 ≤ n)
    (h : d ^ m = 2 ^ (m * n - m)) : d = 2 ^ (n - 1) := by
  have key : 2 ^ (m * n - m) = (2 ^ (n - 1)) ^ m := by
    rw [← pow_mul]; congr 1
    zify [show 1 ≤ m by omega, show m ≤ m * n by nlinarith, hn]; ring
  rw [key] at h; exact Nat.pow_left_injective hm h

theorem dual_theorem (n m δ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * 2 ^ ((m - 1) * n - m) = δ ^ m) :
    δ = 2 ^ (n - 1) := by
  rw [dual_count_product n m hn hm] at hKR₂
  exact recover_delta δ n m (by omega) (by omega) hKR₂.symm

theorem two_pow_injective (a b : ℕ) (h : 2 ^ a = 2 ^ b) : a = b :=
  Nat.pow_right_injective (by omega) h

theorem dual_C_forced (n m C : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hC_le : C ≤ (m - 1) * n)
    (hδ : 2 ^ (n + ((m - 1) * n - C)) = 2 ^ ((n - 1) * m)) :
    C = m := by
  have := Nat.pow_right_injective (show 2 ≤ 2 by omega) hδ
  zify [show 1 ≤ n by omega, show 1 ≤ m by omega,
        sub_bound n m hn hm, hC_le] at *; linarith

theorem dual_C_eq_m (n m δ C : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hC_le : C ≤ (m - 1) * n)
    (hKR₂ : 2 ^ n * 2 ^ ((m - 1) * n - C) = δ ^ m)
    (hδ : δ = 2 ^ (n - 1)) : C = m := by
  rw [hδ, ← pow_mul, ← pow_add] at hKR₂
  exact dual_C_forced n m C hn hm hC_le hKR₂

-- ════════════════════════════════════════════════════════════════════
-- §7  EQUIVALENCE   [FULLY PROVED]
-- ════════════════════════════════════════════════════════════════════

theorem primal_dual_equivalence
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * κ = δ ^ m) :
    κ = 2 ^ ((m - 1) * n - m) ↔ δ = 2 ^ (n - 1) :=
  ⟨fun hκ => by rw [hκ] at hKR₂; exact dual_theorem n m δ hn hm hKR₂,
   fun hδ => primal_mTupleCount n m δ κ hn hm hδ hKR₂⟩

theorem kasami_triple_equivalence
    (n δ κ : ℕ) (hn : 3 ≤ n) (hKR₂ : 2 ^ n * κ = δ ^ 3) :
    κ = 2 ^ (2 * n - 3) ↔ δ = 2 ^ (n - 1) := by
  have h := primal_dual_equivalence n 3 δ κ hn (by omega) hKR₂
  exact ⟨fun hκ => h.mp (by simpa using hκ), fun hδ => by simpa using h.mpr hδ⟩

-- ════════════════════════════════════════════════════════════════════
-- §8  COMPLETE PACKAGE   [FULLY PROVED]
-- ════════════════════════════════════════════════════════════════════

theorem mTupleCount_complete_package
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * κ = δ ^ m) :
    (2 ^ n * 2 ^ ((m - 1) * n - m) = (2 ^ (n - 1)) ^ m) ∧
    (κ = 2 ^ ((m - 1) * n - m) ↔ δ = 2 ^ (n - 1)) ∧
    (κ = 2 ^ ((m - 1) * n - m) →
      ∀ C, C ≤ (m - 1) * n → κ = 2 ^ ((m - 1) * n - C) → C = m) := by
  refine ⟨parseval_arithmetic n m hn hm,
         primal_dual_equivalence n m δ κ hn hm hKR₂, ?_⟩
  intro hκ C hCle hκC
  have hsub := sub_bound n m hn hm
  have heq := two_pow_injective _ _ (hκ ▸ hκC)
  omega

-- ════════════════════════════════════════════════════════════════════
-- §9  INTEGRATED THEOREM
-- ════════════════════════════════════════════════════════════════════

/-- For APN + AB-flat f over GF(2ⁿ), κ_m(f) = 2^{(m-1)n - m}. -/
theorem integrated_mTupleCount [CharP 𝔽 2]
    (hψ : ψ.IsPrimitive)
    (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f) (hAB : IsAB_spectrallyFlat 𝔽 ψ f)
    (n : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (m : ℕ) (hm : 2 ≤ m)
    (coeffs : Fin m → 𝔽) (hcoeffs : ∀ i, coeffs i ≠ 0) :
    mTupleCount 𝔽 f m coeffs = 2 ^ ((m - 1) * n - m) := by
  have hδ := apn_differentialSet_card 𝔽 f hAPN n (by omega) hcard
  have hKR₂ := spectral_identity 𝔽 ψ hψ f m coeffs hcoeffs hAB
  rw [hcard] at hKR₂
  exact primal_mTupleCount n m _ _ hn hm hδ hKR₂

-- ════════════════════════════════════════════════════════════════════
-- §10  AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

-- KR₁ (no sorry)
#print axioms char2_cancel
#print axioms differential_pairing
#print axioms apn_fiber_ge_two
#print axioms apn_fiber_eq_two
#print axioms apn_image_card
#print axioms apn_differentialSet_card

-- Arithmetic (no sorry)
#print axioms power_of_power
#print axioms exponent_identity
#print axioms power_split

-- Primal / Dual / Equivalence (no sorry)
#print axioms primal_mTupleCount
#print axioms dual_theorem
#print axioms primal_dual_equivalence
#print axioms mTupleCount_complete_package

-- KR₂ chain
#print axioms deltaHat_zero
#print axioms fourier_sum_split
#print axioms fourier_zero_term
#print axioms spectral_identity_complex
#print axioms spectral_identity

-- Integrated
#print axioms integrated_mTupleCount

end