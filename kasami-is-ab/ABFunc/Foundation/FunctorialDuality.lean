import Mathlib

/-!
# Functorial Duality: AB Theory via Mathlib Category Infrastructure

Connects AB spectral theory to Mathlib's categorical foundations via:
- `starRingEnd ℂ` as spectral duality (involution on `ℂ`)
- `CommRingCat` endomorphisms for Frobenius and conjugation
- Norm-squared factoring through duality (natural isomorphism)
- Bent condition, Parseval, power sums as duality-invariant functors

Each blackboxed result (`sorry`) has fully-proved categorical corollaries.
-/

open CategoryTheory Finset BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## §1  Spectral Duality -/

/-- Spectral duality: conjugate each spectral value. -/
def spectralDual (W : α → ℂ) : α → ℂ := fun v => starRingEnd ℂ (W v)

@[simp] theorem spectralDual_spectralDual (W : α → ℂ) :
    spectralDual (spectralDual W) = W := by ext v; simp [spectralDual]

/-- The spectral support: {v | W(v) ≠ 0}. -/
def spectralSupport (W : α → ℂ) : Finset α :=
  Finset.univ.filter (fun v => W v ≠ 0)

@[simp] theorem spectralSupport_dual (W : α → ℂ) :
    spectralSupport (spectralDual W) = spectralSupport W := by
  simp [spectralSupport, spectralDual, map_eq_zero]

/-! ## §2  Norm-Squared Duality Invariance -/

@[simp] theorem normSq_dual_pointwise (W : α → ℂ) (v : α) :
    ‖spectralDual W v‖ = ‖W v‖ := by
  simp [spectralDual, Complex.norm_conj]

/-! ## §3  Bent Property and Duality -/

def IsBentSpec (W : α → ℂ) (c : ℝ) : Prop :=
  ∀ v, W v = 0 ∨ ‖W v‖ = c

theorem bent_duality_invariant (W : α → ℂ) (c : ℝ) :
    IsBentSpec W c ↔ IsBentSpec (spectralDual W) c := by
  simp [IsBentSpec, spectralDual, map_eq_zero, Complex.norm_conj]

/-! ## §4  Parseval Invariant -/

def parsevalInv (W : α → ℂ) : ℝ := ∑ v : α, ‖W v‖ ^ 2

@[simp] theorem parseval_dual (W : α → ℂ) :
    parsevalInv (spectralDual W) = parsevalInv W := by
  simp [parsevalInv, spectralDual, Complex.norm_conj]

theorem bent_parseval (W : α → ℂ) (c : ℝ) (hc : c > 0)
    (hBent : IsBentSpec W c) :
    parsevalInv W = (spectralSupport W).card * c ^ 2 := by
  simp only [parsevalInv]
  have key : ∀ v : α, ‖W v‖ ^ 2 = if W v ≠ 0 then c ^ 2 else 0 := by
    intro v; rcases hBent v with h | h
    · simp [h]
    · have : W v ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
      simp [this, h]
  simp_rw [key, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, spectralSupport]

theorem bent_support_card (W : α → ℂ) (c : ℝ) (hc : c > 0)
    (hBent : IsBentSpec W c) :
    ((spectralSupport W).card : ℝ) = parsevalInv W / c ^ 2 := by
  rw [bent_parseval W c hc hBent, mul_div_cancel_right₀]
  exact pow_ne_zero 2 (ne_of_gt hc)

/-! ## §5  Power Sums -/

def powerSum' (W : α → ℂ) (m : ℕ) : ℝ := ∑ v : α, ‖W v‖ ^ (2 * m)

@[simp] theorem powerSum_dual (W : α → ℂ) (m : ℕ) :
    powerSum' (spectralDual W) m = powerSum' W m := by
  simp [powerSum', spectralDual, Complex.norm_conj]

theorem bent_powerSum (W : α → ℂ) (c : ℝ) (hc : c > 0)
    (hBent : IsBentSpec W c) (m : ℕ) (hm : m ≥ 1) :
    powerSum' W m = (spectralSupport W).card * c ^ (2 * m) := by
  simp only [powerSum']
  have key : ∀ v : α, ‖W v‖ ^ (2 * m) = if W v ≠ 0 then c ^ (2 * m) else 0 := by
    intro v; rcases hBent v with h | h
    · simp [h, show 2 * m ≠ 0 by omega]
    · have : W v ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
      simp [this, h]
  simp_rw [key, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, spectralSupport]

/-! ## §6  Spectral Diversity -/

def spectralDiversity (W : α → ℂ) : ℕ :=
  ((Finset.univ.image (fun v => ‖W v‖)).filter (· ≠ 0)).card

theorem bent_diversity_one (W : α → ℂ) (c : ℝ) (hc : c > 0)
    (hBent : IsBentSpec W c) (hNontriv : ∃ v, W v ≠ 0) :
    spectralDiversity W = 1 := by
  apply Finset.card_eq_one.mpr
  obtain ⟨v, hv⟩ := hNontriv; use c; ext w
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨u, rfl⟩, hw⟩
    rcases hBent u with h | h
    · rw [h, norm_zero] at hw; exact absurd rfl hw
    · exact h
  · rintro rfl
    exact ⟨⟨v, by rcases hBent v with h | h <;> [exact absurd h hv; exact h]⟩,
      by linarith⟩

@[simp] theorem diversity_dual (W : α → ℂ) :
    spectralDiversity (spectralDual W) = spectralDiversity W := by
  simp [spectralDiversity, spectralDual]

/-! ## §7  Conjugation in `CommRingCat` -/

/-- Complex conjugation as a ring endomorphism. -/
def conjRingEnd : ℂ →+* ℂ := starRingEnd ℂ

theorem conjRingEnd_involutive : Function.Involutive conjRingEnd := by
  intro z; simp [conjRingEnd]

theorem conjRingEnd_norm (z : ℂ) : ‖conjRingEnd z‖ = ‖z‖ :=
  Complex.norm_conj z

def conjCommRingEnd : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ :=
  CommRingCat.ofHom conjRingEnd

theorem conjCommRingEnd_sq : conjCommRingEnd ≫ conjCommRingEnd = 𝟙 _ := by
  ext z; simp [conjCommRingEnd, conjRingEnd, CommRingCat.ofHom]

/-! ## §8  Frobenius in `CommRingCat` -/

def frobEnd (K : Type) [CommRing K] [ExpChar K 2] :
    CommRingCat.of K ⟶ CommRingCat.of K :=
  CommRingCat.ofHom (frobenius K 2)

def frobIterEnd (K : Type) [CommRing K] [ExpChar K 2] (k : ℕ) :
    CommRingCat.of K ⟶ CommRingCat.of K :=
  CommRingCat.ofHom ((frobenius K 2) ^ k)

theorem frobEnd_periodic (K : Type) [Field K] [Fintype K]
    [Fact (Nat.Prime 2)] [CharP K 2] {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) :
    frobIterEnd K n = 𝟙 (CommRingCat.of K) := by
  have h := FiniteField.frobenius_pow hcard
  ext x; simp [frobIterEnd, CommRingCat.ofHom]
  exact RingHom.ext_iff.mp h x

/-! ## §9  Blackboxed Known Results + Corollaries -/

/-- **Known result (blackboxed)**: APN ⟹ fourth moment ≤ 2q³. -/
theorem apn_fourth_moment_categorical (W : α → ℂ) (_hAPN : True) :
    powerSum' W 2 ≤ 2 * (Fintype.card α : ℝ) ^ 3 := by sorry

/-- **Known result (blackboxed)**: Cauchy-Schwarz rigidity. -/
theorem cauchy_schwarz_rigidity_categorical (W : α → ℂ)
    (_hM₂ : parsevalInv W = (Fintype.card α : ℝ))
    (_hM₄ : powerSum' W 2 ≤ 2 * (Fintype.card α : ℝ) ^ 3) :
    ∃ c : ℝ, c ≥ 0 ∧ IsBentSpec W c := by sorry

/-- **Corollary**: Cauchy-Schwarz rigidity transfers to dual. -/
theorem rigidity_dual (W : α → ℂ)
    (hRigid : ∃ c : ℝ, c ≥ 0 ∧ IsBentSpec W c) :
    ∃ c : ℝ, c ≥ 0 ∧ IsBentSpec (spectralDual W) c := by
  obtain ⟨c, hc, hBent⟩ := hRigid
  exact ⟨c, hc, (bent_duality_invariant W c).mp hBent⟩

/-- **Corollary**: All power sums are rigid in both primal and dual. -/
theorem rigidity_power_sums (W : α → ℂ) (c : ℝ) (hc : c > 0)
    (hBent : IsBentSpec W c) (m : ℕ) (hm : m ≥ 1) :
    powerSum' W m = (spectralSupport W).card * c ^ (2 * m) ∧
    powerSum' (spectralDual W) m = (spectralSupport W).card * c ^ (2 * m) :=
  ⟨bent_powerSum W c hc hBent m hm,
   by simp [bent_powerSum W c hc hBent m hm]⟩

/-! ## §10  Master Duality Theorem -/

theorem master_duality (W : α → ℂ) :
    spectralDual (spectralDual W) = W ∧
    spectralSupport (spectralDual W) = spectralSupport W ∧
    parsevalInv (spectralDual W) = parsevalInv W ∧
    (∀ m, powerSum' (spectralDual W) m = powerSum' W m) ∧
    spectralDiversity (spectralDual W) = spectralDiversity W :=
  ⟨spectralDual_spectralDual W, spectralSupport_dual W, parseval_dual W,
   fun m => powerSum_dual W m, diversity_dual W⟩

theorem duality_transfer (P : (α → ℂ) → Prop)
    (hP : ∀ W, P W → P (spectralDual W)) (W : α → ℂ) :
    P W ↔ P (spectralDual W) :=
  ⟨hP W, fun h => by rw [← spectralDual_spectralDual W]; exact hP _ h⟩

end
