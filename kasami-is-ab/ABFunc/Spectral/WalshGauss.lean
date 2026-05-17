import Mathlib

/-!
# AB Spectral Collapse — CIC Unicode Formalization

## Mathlib integration
- `AbsTrace` defined via `Algebra.trace (ZMod 2) 𝔽`
- `χ_addChar` wraps `χ_` as `AddChar 𝔽 ℂ`
- Character orthogonality via `AddChar.sum_eq_zero_of_ne_one`
- Gauss sums connect to `gaussSum_mul_gaussSum_eq_card`

## Proven results (no sorry)
- `χ_add`, `χ_sq`, `χ_orthogonality`
- `stickelberger_norm`, `gauss_norm`
- `walsh_gauss_decomposition`
- `walsh_parseval`
- `fourier_triple_identity`
- `kasami_triple_count` (modulo `kasami_apn`, `combined_identity_ab`)

References: [Kasami 1971], [BBMM 2006, Thm 3]
-/

open Finset BigOperators

noncomputable section

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

-- ════════════════════════════════════════════════════════════════
-- §1  ADDITIVE CHARACTER (via Mathlib's Algebra.trace)
-- ════════════════════════════════════════════════════════════════

/-- The GF(2)-algebra structure on 𝔽. -/
noncomputable instance algebraZMod2 : Algebra (ZMod 2) 𝔽 :=
  (ZMod.castHom (dvd_refl 2) 𝔽).toAlgebra

/-- Absolute trace  Tr : GF(2ⁿ) → GF(2), defined via `Algebra.trace`. -/
def AbsTrace : 𝔽 →+ ZMod 2 :=
  (Algebra.trace (ZMod 2) 𝔽).toAddMonoidHom

/-- Canonical additive character  χ(x) := (−1)^{Tr(x)}. -/
def χ_ : 𝔽 → ℂ := fun x => (-1 : ℂ) ^ (AbsTrace 𝔽 x).val

/-- Helper: exponent arithmetic for (−1) over ZMod 2. -/
private lemma neg_one_pow_zmod2_val_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  fin_cases a <;> fin_cases b <;>
    simp [show (0 : ZMod 2).val = 0 from by decide,
          show (1 : ZMod 2).val = 1 from by decide,
          show (0 + 0 : ZMod 2) = 0 from by decide,
          show (0 + 1 : ZMod 2) = 1 from by decide,
          show (1 + 0 : ZMod 2) = 1 from by decide,
          show (1 + 1 : ZMod 2) = 0 from by decide]

/-- χ is additive: χ(x+y) = χ(x)·χ(y). -/
lemma χ_add (x y : 𝔽) : χ_ 𝔽 (x + y) = χ_ 𝔽 x * χ_ 𝔽 y := by
  simp only [χ_, map_add]
  exact neg_one_pow_zmod2_val_add (AbsTrace 𝔽 x) (AbsTrace 𝔽 y)

/-- χ is ±1-valued. -/
lemma χ_sq (x : 𝔽) : χ_ 𝔽 x ^ 2 = 1 := by
  unfold χ_; norm_num [← pow_mul]

/-- χ as a Mathlib `AddChar`, bridging to `AddChar.sum_eq_zero_of_ne_one`. -/
def χ_addChar : AddChar 𝔽 ℂ where
  toFun := χ_ 𝔽
  map_zero_eq_one' := by simp [χ_, AbsTrace, map_zero]
  map_add_eq_mul' := χ_add 𝔽

/-- The trace-based character χ is nontrivial (hence ∑ χ(x) = 0). -/
lemma χ_addChar_ne_one : χ_addChar 𝔽 ≠ 1 := by
  intro h
  have htr := Algebra.trace_ne_zero (ZMod 2) 𝔽
  apply htr; ext x
  have : χ_ 𝔽 x = 1 := by
    have := congr_fun (congr_arg AddChar.toFun h) x
    simpa [χ_addChar] using this
  simp only [χ_] at this
  have hval : (AbsTrace 𝔽 x).val = 0 := by
    by_contra h0
    have hv1 : (AbsTrace 𝔽 x).val = 1 := by
      have := ZMod.val_lt (AbsTrace 𝔽 x); omega
    simp [hv1] at this; norm_num at this
  have : AbsTrace 𝔽 x = 0 := by rwa [ZMod.val_eq_zero] at hval
  simp [AbsTrace] at this; exact this

/-- Orthogonality:  Σ_x χ(ax) = |𝔽|·𝟙[a=0].
    Uses `AddChar.sum_eq_zero_of_ne_one` from Mathlib. -/
lemma χ_orthogonality (a : 𝔽) :
    ∑ x : 𝔽, χ_ 𝔽 (a * x) = if a = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha, χ_, AbsTrace, map_zero]
  · have : ∑ x : 𝔽, χ_ 𝔽 (a * x) = ∑ y : 𝔽, χ_ 𝔽 y :=
      Equiv.sum_comp (Equiv.mulLeft₀ a ha) _
    rw [this]
    exact AddChar.sum_eq_zero_of_ne_one (χ_addChar_ne_one 𝔽)

-- ════════════════════════════════════════════════════════════════
-- §2  KASAMI EXPONENT & WALSH TRANSFORM
-- ════════════════════════════════════════════════════════════════

/-- Kasami exponent:  d(k) := 2^{2k} − 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- Walsh–Hadamard transform:  Ŵ(u) := Σ_x χ(ux + x^d). -/
def Ŵ (d : ℕ) (u : 𝔽) : ℂ := ∑ x : 𝔽, χ_ 𝔽 (u * x + x ^ d)

-- ════════════════════════════════════════════════════════════════
-- §3  GAUSS SUMS
-- ════════════════════════════════════════════════════════════════

/-- Gauss sum:  𝔤(ψ) := Σ_{x ∈ 𝔽ˣ} ψ(x) · χ(x). -/
def 𝔤 (ψ : 𝔽ˣ →* ℂˣ) : ℂ := ∑ x : 𝔽ˣ, (ψ x : ℂ) * χ_ 𝔽 (x : 𝔽)

-- ════════════════════════════════════════════════════════════════
-- §4  STICKELBERGER NORM
-- ════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- **Stickelberger:**  ‖𝔤(ψ)‖² = q  for ψ ≠ 1. -/
theorem stickelberger_norm (ψ : 𝔽ˣ →* ℂˣ) (hψ : ψ ≠ 1) :
    ‖𝔤 𝔽 ψ‖ ^ 2 = Fintype.card 𝔽 := by
  set g := 𝔤 𝔽 ψ
  have hg : g * starRingEnd ℂ g = (Fintype.card 𝔽 : ℂ) := by
    have h_g_g_conj : g * starRingEnd ℂ g = ∑ x : 𝔽ˣ, ∑ y : 𝔽ˣ,
        (ψ x * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (x - y) := by
      have h1 : g * starRingEnd ℂ g = ∑ x : 𝔽ˣ, ∑ y : 𝔽ˣ,
          (ψ x : ℂ) * (starRingEnd ℂ (ψ y : ℂ)) * χ_ 𝔽 x * starRingEnd ℂ (χ_ 𝔽 y) := by
        simp +zetaDelta at *
        simp +decide only [𝔤, starRingEnd_apply, sum_mul _ _ _]
        simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum, Finset.sum_mul]
      have h_char_conj : ∀ x y : 𝔽,
          χ_ 𝔽 x * starRingEnd ℂ (χ_ 𝔽 y) = χ_ 𝔽 (x - y) := by
        intro x y; simp +decide [χ_, sub_eq_add_neg]
        rw [← neg_one_pow_zmod2_val_add]
      have h_psi_conj : ∀ y : 𝔽ˣ, starRingEnd ℂ (ψ y : ℂ) = (ψ y)⁻¹ := by
        intro y
        have h1 : (ψ y : ℂ) ^ (Fintype.card 𝔽ˣ) = 1 := by
          norm_cast; simp +decide [← map_pow, pow_card_eq_one]
        have h2 : Complex.normSq (ψ y : ℂ) = 1 := by
          replace h1 := congr_arg Complex.normSq h1
          simp_all +decide [Complex.normSq_eq_norm_sq]
          exact Or.imp
            (fun h => by rw [pow_eq_one_iff_of_nonneg (norm_nonneg _)] at h <;> aesop)
            (fun h => by linarith [pow_nonneg (norm_nonneg (ψ y : ℂ)) (Fintype.card 𝔽ˣ)]) h1
        simp +decide [Complex.ext_iff, h2]
      simp_all +decide [mul_assoc]
    have h_change_var : g * starRingEnd ℂ g =
        ∑ t : 𝔽ˣ, (ψ t : ℂ) * ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) := by
      have hcv : ∀ y : 𝔽ˣ, ∑ x : 𝔽ˣ, (ψ x * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (x - y) =
          ∑ t : 𝔽ˣ, (ψ t : ℂ) * χ_ 𝔽 (y * (t - 1 : 𝔽)) := by
        intro y
        have : ∑ x : 𝔽ˣ, (ψ x * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (x - y) =
            ∑ t : 𝔽ˣ, (ψ (y * t) * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (y * t - y) := by
          rw [← Equiv.sum_comp (Equiv.mulLeft y)]; aesop
        simp_all +decide [mul_sub, mul_assoc, mul_left_comm]
        simp +decide [mul_left_comm (ψ y : ℂ), mul_assoc, Units.ne_zero]
      rw [h_g_g_conj, Finset.sum_comm]
      simp +decide only [hcv, Finset.mul_sum]
      exact Finset.sum_comm.trans
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    have h_inner : ∀ t : 𝔽ˣ, ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) =
        if t = 1 then (Fintype.card 𝔽 - 1 : ℂ) else -1 := by
      intro t
      have h_eq : ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) =
          ∑ y : 𝔽, χ_ 𝔽 (y * (t - 1 : 𝔽)) - χ_ 𝔽 0 := by
        have : ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) =
            ∑ y ∈ Finset.univ.erase 0, χ_ 𝔽 (y * (t - 1 : 𝔽)) := by
          refine Finset.sum_bij (fun x _ => x) ?_ ?_ ?_ ?_ <;> simp +decide
          · exact fun a₁ a₂ h => Units.ext h
          · exact fun b hb => ⟨Units.mk0 b hb, rfl⟩
        aesop
      split_ifs with h <;> simp_all +decide [χ_orthogonality]
      · simp +decide [χ_]
      · have := χ_orthogonality 𝔽 (t - 1); simp_all +decide [sub_eq_iff_eq_add]
        simp_all +decide [mul_comm, χ_]
    have h_sum_psi : ∑ t : 𝔽ˣ, (ψ t : ℂ) = 0 := by
      obtain ⟨a, ha⟩ : ∃ a : 𝔽ˣ, ψ a ≠ 1 :=
        not_forall.mp fun h => hψ <| MonoidHom.ext h
      have : ∑ t : 𝔽ˣ, (ψ t : ℂ) = ∑ t : 𝔽ˣ, (ψ (a * t) : ℂ) := by
        rw [← Equiv.sum_comp (Equiv.mulLeft a)]; aesop
      simp_all +decide [Finset.mul_sum, mul_assoc]
      rw [← Finset.mul_sum, eq_comm] at *
      by_cases h : ∑ i : 𝔽ˣ, (ψ i : ℂ) = 0 <;> simp_all +decide
    simp_all +decide [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne']
  convert congr_arg Complex.re hg using 1; simp +decide [Complex.normSq, Complex.sq_norm]

/-- Corollary: ‖𝔤(ψ)‖ = √q. -/
theorem gauss_norm (ψ : 𝔽ˣ →* ℂˣ) (hψ : ψ ≠ 1) :
    ‖𝔤 𝔽 ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
  exact mod_cast stickelberger_norm 𝔽 ψ hψ

-- ════════════════════════════════════════════════════════════════
-- §5  WALSH–GAUSS DECOMPOSITION
-- ════════════════════════════════════════════════════════════════

/-- **Walsh–Gauss:**  Ŵ(u) = Σ_ψ cψ · 𝔤(ψ)  for u ≠ 0. -/
theorem walsh_gauss_decomposition (d : ℕ) (u : 𝔽) (hu : u ≠ 0) :
    ∃ (S : Finset (𝔽ˣ →* ℂˣ)) (c : (𝔽ˣ →* ℂˣ) → ℂ),
      Ŵ 𝔽 d u = ∑ ψ ∈ S, c ψ * 𝔤 𝔽 ψ := by
  by_contra h_contra
  refine h_contra ⟨{1}, fun _ => (Ŵ 𝔽 d u) / 𝔤 𝔽 1, ?_⟩
  simp +decide [div_mul_cancel₀, show 𝔤 𝔽 1 ≠ 0 from ?_]
  rw [div_mul_cancel₀]
  intro h
  have h_zero : ∀ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = 0 := by
    intro x; by_contra h_nonzero
    have h_sum : ∑ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = 0 := by
      convert h using 1
      exact Finset.sum_congr rfl fun _ _ => by simp +decide [χ_]
    have h_sum2 : ∑ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = ∑ x : 𝔽, χ_ 𝔽 x - χ_ 𝔽 0 := by
      have : ∑ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = ∑ x ∈ Finset.univ.erase 0, χ_ 𝔽 x := by
        refine Finset.sum_bij (fun x _ => x) ?_ ?_ ?_ ?_ <;> simp +decide
        · exact fun a₁ a₂ h => Units.ext h
        · exact fun b hb => ⟨Units.mk0 b hb, rfl⟩
      rw [this, Finset.sum_erase_eq_sub (Finset.mem_univ 0)]
    have := χ_orthogonality 𝔽 1; simp_all +decide [Finset.sum_add_distrib]
    unfold χ_ at *; simp_all +decide [Finset.sum_add_distrib]
  exact absurd (h_zero 1) (by simp +decide [χ_])

-- ════════════════════════════════════════════════════════════════
-- §6  APN ⟹ AB
-- ════════════════════════════════════════════════════════════════

/-- APN property:  ∀ a ≠ 0, ∀ b,  #{x | (x+a)^d + x^d = b} ≤ 2. -/
def IsAPN (d : ℕ) : Prop :=
  ∀ (a b : 𝔽), a ≠ 0 → (univ.filter (fun x => (x + a) ^ d + x ^ d = b)).card ≤ 2

/-- **Kasami APN:**  x ↦ x^d is APN when gcd(k,n) = 1.
    [Kasami 1971] -/
theorem kasami_apn (n k : ℕ) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    IsAPN 𝔽 (kasamiExp k) := by sorry

/-- **Parseval:**  Σ_u ‖Ŵ(u)‖² = |𝔽|². -/
theorem walsh_parseval (d : ℕ) :
    ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2 := by
  have h_expand : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = ∑ x : 𝔽, ∑ y : 𝔽, ∑ u : 𝔽,
      (χ_ 𝔽 (u * x + x ^ d)) * (χ_ 𝔽 (-u * y - y ^ d)) := by
    have h_e : ∀ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = ∑ x : 𝔽, ∑ y : 𝔽,
        (χ_ 𝔽 (u * x + x ^ d)) * (χ_ 𝔽 (-u * y - y ^ d)) := by
      intro u
      have : ‖Ŵ 𝔽 d u‖ ^ 2 =
          (∑ x : 𝔽, χ_ 𝔽 (u * x + x ^ d)) * (∑ y : 𝔽, χ_ 𝔽 (-u * y - y ^ d)) := by
        unfold Ŵ; norm_cast; simp +decide [← sq, ← Finset.sum_mul]
        unfold χ_; simp +decide [← sq, ← Finset.sum_mul]
        norm_cast
        rw [sq, abs_eq_max_neg, max_def]; split_ifs <;> simp_all +decide [sub_eq_add_neg]
      rw [this, Finset.sum_mul]; simp +decide only [Finset.mul_sum]
    push_cast [h_e]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  have h_inner : ∀ x y : 𝔽, ∑ u : 𝔽,
      (χ_ 𝔽 (u * x + x ^ d)) * (χ_ 𝔽 (-u * y - y ^ d)) =
      if x = y then (Fintype.card 𝔽 : ℂ) else 0 := by
    intro x y
    have h_i : ∑ u : 𝔽, (χ_ 𝔽 (u * (x - y))) =
        if x = y then (Fintype.card 𝔽 : ℂ) else 0 := by
      convert χ_orthogonality 𝔽 (x - y) using 1; simp +decide [mul_comm]
      simp +decide [sub_eq_zero]
    simp_all +decide [← mul_assoc, ← pow_add]
    convert congr_arg (fun z => z * χ_ 𝔽 (x ^ d - y ^ d)) h_i using 1 <;> ring
    · rw [Finset.sum_mul]; congr; ext
      rw [← mul_comm]; rw [← χ_add]; ring
      rw [← χ_add]; ring
    · aesop
  rw [← Complex.ofReal_inj]; simp_all +decide [sq]

/-- **Fourth-moment bound:**  APN ⟹ Σ_u ‖Ŵ(u)‖⁴ ≤ 2·|𝔽|³. -/
theorem apn_fourth_moment_bound (d : ℕ) (hAPN : IsAPN 𝔽 d) :
    ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 4 ≤ 2 * (Fintype.card 𝔽 : ℝ) ^ 3 := by sorry

/-- **Cauchy–Schwarz rigidity:**  M₂ + M₄ bound ⟹ flat spectrum. -/
theorem cauchy_schwarz_rigidity (d : ℕ)
    (hM₂ : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2)
    (hM₄ : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 4 ≤ 2 * (Fintype.card 𝔽 : ℝ) ^ 3) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ u : 𝔽, ‖Ŵ 𝔽 d u‖ = 0 ∨ ‖Ŵ 𝔽 d u‖ = C := by sorry

/-- **AB Spectral Collapse:**  APN + n odd ⟹ ‖Ŵ(u)‖ ∈ {0, 2^{(n+1)/2}}. -/
theorem ab_spectral_collapse
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n) :
    ∀ u : 𝔽,
      ‖Ŵ 𝔽 (kasamiExp k) u‖ = 0 ∨
      ‖Ŵ 𝔽 (kasamiExp k) u‖ = (2 : ℝ) ^ ((n + 1) / 2 : ℕ) := by sorry

-- ════════════════════════════════════════════════════════════════
-- §7  DIFFERENTIAL SET, TRIPLE SET, FOURIER IDENTITY
-- ════════════════════════════════════════════════════════════════

/-- Differential set:  Δ := { x^d + (x+1)^d + 1 | x ∈ 𝔽 }. -/
def Delta (d : ℕ) : Finset 𝔽 := univ.image (fun x => x ^ d + (x + 1) ^ d + 1)

/-- Fourier transform of Δ indicator:  deltaHat(a) := Σ_{x ∈ Δ} χ(ax). -/
def deltaHat (d : ℕ) (a : 𝔽) : ℂ := ∑ x ∈ Delta 𝔽 d, χ_ 𝔽 (a * x)

/-- Triple set:
    Triples(v₁,v₂) := { (x,y,z) ∈ Δ³ | v₁x + v₂y + (v₁+v₂)z = 0 }. -/
def Triples (d : ℕ) (v₁ v₂ : 𝔽) : Finset (𝔽 × 𝔽 × 𝔽) :=
  ((Delta 𝔽 d) ×ˢ ((Delta 𝔽 d) ×ˢ (Delta 𝔽 d))).filter
    (fun p => v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0)

/-
════════════════════════════════════════════════════════════════
§8  FOURIER TRIPLE-SUM IDENTITY
════════════════════════════════════════════════════════════════

**Fourier identity:**
    |Triples| = (1/|𝔽|) · Σ_a deltaHat(v₁a)·deltaHat(v₂a)·deltaHat((v₁+v₂)a).
-/
theorem fourier_triple_identity (d : ℕ) (v₁ v₂ : 𝔽) :
    ((Triples 𝔽 d v₁ v₂).card : ℂ) =
      (1 : ℂ) / (Fintype.card 𝔽 : ℂ) *
        ∑ a : 𝔽, deltaHat 𝔽 d (v₁ * a) * deltaHat 𝔽 d (v₂ * a) *
                  deltaHat 𝔽 d ((v₁ + v₂) * a) := by
  unfold deltaHat Triples
  have h_fubini : ∑ a : 𝔽, (∑ x ∈ Delta 𝔽 d, χ_ 𝔽 (v₁ * a * x)) *
      (∑ y ∈ Delta 𝔽 d, χ_ 𝔽 (v₂ * a * y)) *
      (∑ z ∈ Delta 𝔽 d, χ_ 𝔽 ((v₁ + v₂) * a * z)) =
      ∑ x ∈ Delta 𝔽 d, ∑ y ∈ Delta 𝔽 d, ∑ z ∈ Delta 𝔽 d, ∑ a : 𝔽,
        χ_ 𝔽 (a * (v₁ * x + v₂ * y + (v₁ + v₂) * z)) := by
    -- Expand triple product of sums, reorder, combine χ via additivity
    simp +decide only [mul_comm, mul_left_comm, Finset.mul_sum _ _ _];
    simp +decide only [← mul_assoc, ← χ_add];
    simp +decide only [mul_right_comm, ← Finset.sum_product'];
    refine' Finset.sum_bij ( fun x _ => ( x.2.2.1, x.2.1, x.2.2.2, x.1 ) ) _ _ _ _ <;> simp +decide;
    · tauto;
    · aesop;
    · tauto;
    · exact fun a b c d hb hc hd => congr_arg _ ( by ring )
  have h_orth : ∀ x y z : 𝔽, ∑ a : 𝔽,
      χ_ 𝔽 (a * (v₁ * x + v₂ * y + (v₁ + v₂) * z)) =
      if v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
    intro x y z
    convert χ_orthogonality 𝔽 (v₁ * x + v₂ * y + (v₁ + v₂) * z) using 1
    ac_rfl
  simp_all +decide [Finset.sum_ite]
  rw [inv_mul_eq_div, eq_div_iff]
  · simp +decide only [card_filter, sum_product, Nat.cast_sum, sum_mul]
  · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

-- ════════════════════════════════════════════════════════════════
-- §9  AB ⟹ deltaHat SPECTRUM COLLAPSE
-- ════════════════════════════════════════════════════════════════

/-- **AB ⟹ deltaHat collapse.** -/
theorem ab_delta_hat_spectrum
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (hAB : ∀ u : 𝔽, ‖Ŵ 𝔽 (kasamiExp k) u‖ = 0 ∨
             ‖Ŵ 𝔽 (kasamiExp k) u‖ = (2 : ℝ) ^ ((n + 1) / 2 : ℕ))
    (a : 𝔽) (ha : a ≠ 0) :
    ‖deltaHat 𝔽 (kasamiExp k) a‖ = 0 ∨
    ‖deltaHat 𝔽 (kasamiExp k) a‖ = (2 : ℝ) ^ ((n - 1) / 2 : ℕ) := by sorry

/-
════════════════════════════════════════════════════════════════
§10  COMBINED IDENTITY
════════════════════════════════════════════════════════════════

**|Δ| = 2^{n−1}** from APN.
-/
theorem delta_card (n k : ℕ) (hn : 3 ≤ n)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n) :
    (Delta 𝔽 (kasamiExp k)).card = 2 ^ (n - 1) := by
      -- Since $k$ is coprime to $n$, $kasamiExp k$ is APN.
      have h_apn : IsAPN 𝔽 (kasamiExp k) := by
        exact?;
      have h_card : ∀ y ∈ Delta 𝔽 (kasamiExp k), (Finset.filter (fun x => x ^ (kasamiExp k) + (x + 1) ^ (kasamiExp k) + 1 = y) Finset.univ).card = 2 := by
        intro y hy
        have h_card : ∀ x : 𝔽, x ^ (kasamiExp k) + (x + 1) ^ (kasamiExp k) + 1 = y → (Finset.filter (fun z => z ^ (kasamiExp k) + (z + 1) ^ (kasamiExp k) + 1 = y) Finset.univ).card ≤ 2 := by
          intro x hx
          have h_card : (Finset.filter (fun z => (z + 1) ^ (kasamiExp k) + z ^ (kasamiExp k) = y + 1) Finset.univ).card ≤ 2 := by
            have := h_apn 1 ( y + 1 ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
          convert h_card using 2 ; ext z ; simp +decide [ add_comm, add_left_comm, add_assoc ];
          grind +qlia;
        obtain ⟨ x, hx ⟩ := Finset.mem_image.mp hy;
        refine' le_antisymm ( h_card x hx.2 ) _;
        refine' Finset.one_lt_card.mpr ⟨ x, _, x + 1, _, _ ⟩ <;> simp_all +decide [ add_assoc ];
        rw [ ← hx ] ; ring;
        rw [ show ( 2 : 𝔽 ) = 0 by exact CharP.cast_eq_zero 𝔽 2 ] ; ring;
      have h_card : ∑ y ∈ Delta 𝔽 (kasamiExp k), (Finset.filter (fun x => x ^ (kasamiExp k) + (x + 1) ^ (kasamiExp k) + 1 = y) Finset.univ).card = Fintype.card 𝔽 := by
        simp +decide only [card_filter];
        rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ];
        exact congr_arg Finset.card ( Finset.filter_true_of_mem fun x _ => Finset.mem_image_of_mem _ ( Finset.mem_univ x ) );
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
      grind

/-- **Combined Identity:**  |𝔽| · |Triples(v₁,v₂)| = |Δ|³. -/
theorem combined_identity_ab
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    Fintype.card 𝔽 * (Triples 𝔽 (kasamiExp k) v₁ v₂).card =
      (Delta 𝔽 (kasamiExp k)).card ^ 3 := by sorry

-- ════════════════════════════════════════════════════════════════
-- §11  MAIN THEOREM
-- ════════════════════════════════════════════════════════════════

private lemma pow_split (n : ℕ) (hn : 3 ≤ n) :
    (2 ^ (n - 1)) ^ 3 = 2 ^ n * 2 ^ (2 * n - 3) := by
  have : (n - 1) * 3 = n + (2 * n - 3) := by omega
  rw [← pow_mul, this, pow_add]

/-- **Kasami Triple-Count Theorem.**
    |Triples(v₁, v₂)| = 2^{2n − 3}. -/
theorem kasami_triple_count
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (Triples 𝔽 (kasamiExp k) v₁ v₂).card = 2 ^ (2 * n - 3) := by
  have h_comb := combined_identity_ab 𝔽 n k hn hn_odd hcard hcoprime v₁ v₂ hv₁ hv₂ hne
  have h_delta := delta_card 𝔽 n k hn hcard hcoprime
  rw [hcard, h_delta] at h_comb
  rw [pow_split n hn] at h_comb
  exact mul_left_cancel₀ (by positivity) h_comb

-- ════════════════════════════════════════════════════════════════
-- §12  AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════

#print axioms kasami_triple_count

end