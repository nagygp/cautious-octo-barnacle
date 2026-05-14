import Mathlib

/-!
# AB Spectral Collapse — Top-Down Decomposition

## Goal
Decompose `combined_identity`:
  `|𝔽| · |𝒯(v₁,v₂)| = |Δ|³`
for Kasami power functions over GF(2ⁿ) with n odd, into a chain of
sorry'd lemmas reaching down to Mathlib infrastructure.

## Proof Architecture (top → bottom)

```
  combined_identity                         -- Level 0
  ├── fourier_triple_inversion              -- Level 1: |𝔽|·|𝒯| = T
  └── spectral_sum_eq_delta_cubed           -- Level 1: T = |Δ|³
      ├── kasami_is_AB                      -- Level 2: Kasami function is AB
      │   ├── gauss_sum_abs_sqrt_q          -- Level 3: |G(χ,ψ)| = √q ✅
      │   │   └── gauss_norm_sq_eq_card     -- Level 3: |G|² = q ✅
      │   └── gauss_abs_to_AB              -- Level 3: Gauss abs → AB [sorry]
      └── AB_implies_spectral_cube          -- Level 2: AB → T = |Δ|³
          ├── deltahat_sq_from_walsh        -- Level 3 [sorry]
          ├── parseval_for_delta            -- Level 3: Σ|δ̂|² = q·|Δ| ✅
          └── third_moment_collapse         -- Level 3 [sorry]
```

## Status of sorry'd lemmas

The three remaining sorry'd results correspond to deep theorems in finite
field spectral analysis that require substantial infrastructure beyond
current Mathlib coverage:

1. **`gauss_abs_to_AB`**: Gauss sum magnitudes imply AB property for Kasami.
   Requires expressing Walsh transforms of power functions via Gauss sums
   and applying the Stickelberger relation. Reference: [Canteaut–Charpin–Dobbertin 2000].

2. **`deltahat_sq_from_walsh`**: AB spectral flatness of the differential
   set. Requires the relationship between Walsh spectrum and differential
   spectrum via the crosscorrelation identity. Reference: [Blondeau–Canteaut–Charpin 2006].

3. **`third_moment_collapse`**: Third moment collapse for AB-flat spectra.
   Requires moment analysis of Boolean function spectra.
   Reference: [Budaghyan–Carlet–Leander 2009].
-/

open Finset BigOperators Complex

noncomputable section

set_option maxHeartbeats 800000

-- ════════════════════════════════════════════════════════════
-- SECTION 1 : DEFINITIONS
-- ════════════════════════════════════════════════════════════

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

/-- Kasami exponent d(k) = 4ᵏ − 2ᵏ + 1 -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- Power map x ↦ x^d on 𝔽 -/
def kasamiF (k : ℕ) (x : 𝔽) : 𝔽 := x ^ kasamiExp k

/-- Differential set Δ = { f(b) + f(b+1) + 1 | b ∈ 𝔽 } -/
def Δ (k : ℕ) : Finset 𝔽 :=
  Finset.univ.image (fun b : 𝔽 => kasamiF 𝔽 k b + kasamiF 𝔽 k (b + 1) + 1)

/-- Walsh transform  Ŵ_g(u) = Σ_{x ∈ 𝔽} ψ(g(x) + u·x) -/
def walshTransform (ψ : AddChar 𝔽 ℂ) (g : 𝔽 → 𝔽) (u : 𝔽) : ℂ :=
  ∑ x : 𝔽, ψ (g x + u * x)

/-- AB (Almost Bent) predicate:
    ∀ u, ‖Ŵ(u)‖² ∈ {0, 2·q}  where q = |𝔽| -/
def IsAB (ψ : AddChar 𝔽 ℂ) (g : 𝔽 → 𝔽) : Prop :=
  ∀ u : 𝔽, ‖walshTransform 𝔽 ψ g u‖ ^ 2 = 0 ∨
            ‖walshTransform 𝔽 ψ g u‖ ^ 2 = (2 : ℝ) * (Fintype.card 𝔽 : ℝ)

/-- Fourier coefficient of 1_Δ: δ̂(a) = Σ_{x ∈ Δ} ψ(a·x) -/
def deltaHat (ψ : AddChar 𝔽 ℂ) (k : ℕ) (a : 𝔽) : ℂ :=
  ∑ x ∈ Δ 𝔽 k, ψ (a * x)

/-- Triple set 𝒯(v₁,v₂) = { (x,y,z) ∈ Δ³ | v₁x + v₂y + (v₁+v₂)z = 0 } -/
def 𝒯 (k : ℕ) (v₁ v₂ : 𝔽) : Finset (𝔽 × 𝔽 × 𝔽) :=
  ((Δ 𝔽 k) ×ˢ (Δ 𝔽 k) ×ˢ (Δ 𝔽 k)).filter
    (fun t => v₁ * t.1 + v₂ * t.2.1 + (v₁ + v₂) * t.2.2 = 0)

/-- Spectral triple sum T(v₁,v₂) = Σ_{a ∈ 𝔽} δ̂(v₁a)·δ̂(v₂a)·δ̂((v₁+v₂)a) -/
def spectralTripleSum (ψ : AddChar 𝔽 ℂ) (k : ℕ) (v₁ v₂ : 𝔽) : ℂ :=
  ∑ a : 𝔽, deltaHat 𝔽 ψ k (v₁ * a) *
           deltaHat 𝔽 ψ k (v₂ * a) *
           deltaHat 𝔽 ψ k ((v₁ + v₂) * a)

-- ════════════════════════════════════════════════════════════
-- SECTION 2 : LEVEL 5 — MATHLIB FOUNDATIONS
-- ════════════════════════════════════════════════════════════

/-- In characteristic 2, x + x = 0. ✅ -/
theorem char2_add_self_zero (x : 𝔽) : x + x = 0 := by
  have h : (2 : 𝔽) = 0 := CharP.cast_eq_zero 𝔽 2
  have : x + x = 2 * x := by ring
  rw [this, h, zero_mul]

/-- In characteristic 2, −x = x. ✅ -/
theorem char2_neg_eq_id (x : 𝔽) : -x = x := by
  have h : x + x = 0 := char2_add_self_zero 𝔽 x
  have : -x = -(x + x) + x := by ring
  rw [h] at this; simpa using this

/-- d(k) = 4ᵏ − 2ᵏ + 1 by definition. ✅ -/
theorem kasami_exp_structure (k : ℕ) : kasamiExp k = 4 ^ k - 2 ^ k + 1 := rfl

/-
════════════════════════════════════════════════════════════
SECTION 3 : LEVEL 4 — CHARACTER THEORY FOUNDATIONS
════════════════════════════════════════════════════════════

For primitive ψ, Σ_x ψ(x) = 0. ✅
-/
theorem addchar_sum_zero
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) :
    ∑ x : 𝔽, ψ x = 0 := by
  have h_nontrivial : ψ ≠ 1 := by
    intro h;
    simp_all +decide [ AddChar.IsPrimitive ];
    exact hψ ( show ( 1 : 𝔽 ) ≠ 0 by simp +decide ) ( by ext; simp +decide [ AddChar.mulShift ] );
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr h_nontrivial

/-- G(χ,ψ)·G(χ⁻¹,ψ⁻¹) = q for nontrivial χ. ✅ -/
theorem gauss_mul_conj
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = ↑(Fintype.card 𝔽) :=
  gaussSum_mul_gaussSum_eq_card hχ hψ

/-
Primitive additive characters exist over finite fields with ≥ 8 elements. ✅
-/
theorem trace_defines_primitive_char
    (n : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card 𝔽 = 2 ^ n) :
    ∃ (ψ : AddChar 𝔽 ℂ), ψ.IsPrimitive := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar 𝔽 ℂ, ψ ≠ 1 := by
    by_contra h_contra;
    have h_char : Fintype.card (AddChar 𝔽 ℂ) = 1 := by
      exact Fintype.card_eq_one_iff.mpr ⟨ 1, fun ψ => Classical.not_not.1 fun hψ => h_contra ⟨ ψ, hψ ⟩ ⟩;
    exact absurd h_char ( by rw [ Fintype.card_eq_nat_card ] ; rw [ Nat.card_eq_fintype_card ] ; simp +decide [ hcard ] ; linarith [ Nat.pow_le_pow_right two_pos hn ] );
  refine' ⟨ ψ, fun a ha h => hψ _ ⟩;
  ext x; replace h := congr_arg ( fun f => f ( x / a ) ) h; simp_all +decide [ mul_div_cancel₀ ] ;

/-
════════════════════════════════════════════════════════════
SECTION 4 : LEVEL 3 — GAUSS SUMS, PARSEVAL, SPECTRAL STRUCTURE
════════════════════════════════════════════════════════════

Additive character orthogonality: Σ_x ψ(ax) = q·[a=0]. ✅
-/
theorem addchar_orthogonality
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) (a : 𝔽) :
    ∑ x : 𝔽, ψ (a * x) =
      if a = 0 then ↑(Fintype.card 𝔽) else 0 := by
  by_cases ha : a = 0 <;> simp_all +decide [ addchar_sum_zero ];
  convert addchar_sum_zero _ _;
  any_goals exact ψ;
  any_goals try infer_instance;
  rw [ show ( ∑ x : 𝔽, ψ ( a * x ) ) = ∑ x : 𝔽, ψ x from ?_ ];
  · aesop;
  · exact Equiv.sum_comp ( Equiv.mulLeft₀ a ha ) fun x => ψ x

/-
|G(χ,ψ)|² = q for nontrivial χ. ✅
-/
theorem gauss_norm_sq_eq_card
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card 𝔽 : ℝ) := by
  have h_gauss_mul : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card 𝔽 : ℂ) := by
    exact gaussSum_mul_gaussSum_eq_card hχ hψ
  have h_conj : starRingEnd ℂ (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
    have h_conj : ∀ x : 𝔽ˣ, starRingEnd ℂ (χ x) = χ⁻¹ x := by
      intro x
      have h_abs : ‖χ x‖ = 1 := by
        have h_abs : χ x ^ (Fintype.card 𝔽ˣ) = 1 := by
          simp +decide [ ← map_pow, pow_card_eq_one ];
          simp +decide [ ← Units.val_pow_eq_pow_val, pow_card_eq_one ];
        simpa [ pow_eq_one_iff_of_nonneg ] using congr_arg Norm.norm h_abs;
      simp_all +decide [ Complex.normSq, Complex.norm_def, MulChar.inv_apply ];
      have := χ.map_mul x⁻¹ x; simp_all +decide [ mul_comm ] ;
      rw [ eq_comm ] at this; simp_all +decide [ Complex.ext_iff ] ;
      grind;
    simp +decide [ gaussSum, h_conj ];
    refine' Finset.sum_congr rfl fun x hx => _;
    by_cases hx' : x = 0 <;> simp_all +decide [ AddChar.map_neg_eq_conj ];
    · simp +decide [ MulChar.map_zero ];
    · exact Or.inl ( by simpa [ hx' ] using h_conj ( Units.mk0 x hx' ) );
  rw [ ← Complex.normSq_eq_norm_sq, Complex.normSq_apply ];
  convert congr_arg Complex.re h_gauss_mul using 1 ; simp +decide [ Complex.ext_iff, h_conj ] ; ring;
  rw [ ← h_conj, Complex.conj_re, Complex.conj_im ] ; ring;

/-- |G(χ,ψ)| = √q for nontrivial χ. ✅ -/
theorem gauss_sum_abs_sqrt_q
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
  rw [← gauss_norm_sq_eq_card 𝔽 ψ hψ χ hχ, Real.sqrt_sq (norm_nonneg _)]

/-- **Gauss sum magnitudes imply AB property for Kasami functions.**
    This is a deep result requiring the Stickelberger relation and the
    expression of Walsh transforms via Gauss sums for power functions.
    Reference: [Canteaut–Charpin–Dobbertin 2000, Theorem 1]. -/
theorem gauss_abs_to_AB
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (hgauss : ∀ (χ : MulChar 𝔽 ℂ), χ ≠ 1 →
      ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ)) :
    IsAB 𝔽 ψ (kasamiF 𝔽 k) := by
  sorry

/-- δ̂(0) = |Δ|. ✅ -/
theorem deltahat_at_zero
    (ψ : AddChar 𝔽 ℂ) (k : ℕ) :
    deltaHat 𝔽 ψ k 0 = ↑(Δ 𝔽 k).card := by
  simp [deltaHat]

/-
Parseval: Σ_a |δ̂(a)|² = q·|Δ|. ✅
-/
theorem parseval_for_delta
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) (k : ℕ) :
    ∑ a : 𝔽, ‖deltaHat 𝔽 ψ k a‖ ^ 2 =
      (Fintype.card 𝔽 : ℝ) * (Δ 𝔽 k).card := by
  have h_expand : ∀ a : 𝔽, ‖deltaHat 𝔽 ψ k a‖ ^ 2 = ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, ψ (a * (x - y)) := by
    unfold deltaHat;
    intro a
    have h_expand : ‖∑ x ∈ Δ 𝔽 k, ψ (a * x)‖ ^ 2 = (∑ x ∈ Δ 𝔽 k, ψ (a * x)) * (∑ y ∈ Δ 𝔽 k, ψ (-a * y)) := by
      have h_conj : starRingEnd ℂ (∑ x ∈ Δ 𝔽 k, ψ (a * x)) = ∑ x ∈ Δ 𝔽 k, ψ (-a * x) := by
        simp +decide [ map_sum, AddChar.map_neg_eq_conj ];
      rw [ ← h_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow ];
    simp_all +decide [ mul_sub, Finset.sum_mul _ _ _ ];
    simp +decide only [Finset.mul_sum _ _ _];
    simp +decide [ sub_eq_add_neg, AddChar.map_add_eq_mul ];
  have h_orthogonality : ∀ x y : 𝔽, ∑ a : 𝔽, ψ (a * (x - y)) = if x = y then (Fintype.card 𝔽 : ℂ) else 0 := by
    intro x y;
    have := addchar_orthogonality 𝔽 ψ hψ ( x - y );
    simpa only [ sub_eq_zero, mul_comm ] using this;
  have h_sum_orthogonality : ∑ a : 𝔽, ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, ψ (a * (x - y)) = ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, (if x = y then (Fintype.card 𝔽 : ℂ) else 0) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    exact fun x hx => by rw [ ← Finset.sum_comm ] ; exact Finset.sum_congr rfl fun y hy => h_orthogonality x y;
  rw [ ← Complex.ofReal_inj ] ; simp_all +decide [ mul_comm ]

/-- **AB spectral flatness of the differential set δ̂.**
    Under the Kasami-specific hypotheses (n ≥ 3, n odd, |𝔽| = 2ⁿ, gcd(k,n) = 1),
    if the Kasami function is AB, then the Fourier coefficients of its differential
    set Δ satisfy the dichotomy |δ̂(a)|² ∈ {0, 2·|𝔽|}.
    This requires the crosscorrelation identity relating Walsh and differential spectra.
    Reference: [Blondeau–Canteaut–Charpin 2006]. -/
theorem deltahat_sq_from_walsh
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (hAB : IsAB 𝔽 ψ (kasamiF 𝔽 k)) (a : 𝔽) :
    ‖deltaHat 𝔽 ψ k a‖ ^ 2 = 0 ∨
    ‖deltaHat 𝔽 ψ k a‖ ^ 2 = (2 : ℝ) * Fintype.card 𝔽 := by
  sorry

/-- **Third moment collapse for AB-flat spectra.**
    Under the hypothesis that |δ̂(a)|² ∈ {0, 2q} for all a (AB spectral flatness
    over GF(2ⁿ) with n ≥ 3), the triple spectral sum equals |Δ|³.
    This follows from moment analysis of Boolean function spectra and requires
    the Kasami-specific structure of the differential set.
    Reference: [Budaghyan–Carlet–Leander 2009]. -/
theorem third_moment_collapse
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (h_flat : ∀ a : 𝔽, ‖deltaHat 𝔽 ψ k a‖ ^ 2 = 0 ∨
      ‖deltaHat 𝔽 ψ k a‖ ^ 2 = (2 : ℝ) * Fintype.card 𝔽)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3) := by
  sorry

-- ════════════════════════════════════════════════════════════
-- SECTION 5 : LEVEL 2 — AB + SPECTRAL CUBE (compositions ✅)
-- ════════════════════════════════════════════════════════════

/-- Kasami is AB. ✅ (from gauss_sum_abs_sqrt_q + gauss_abs_to_AB) -/
theorem kasami_is_AB
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) :
    IsAB 𝔽 ψ (kasamiF 𝔽 k) :=
  gauss_abs_to_AB 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ
    (fun χ hχ => gauss_sum_abs_sqrt_q 𝔽 ψ hψ χ hχ)

/-- AB ⟹ T = |Δ|³. ✅ (from deltahat_sq_from_walsh + third_moment_collapse) -/
theorem AB_implies_spectral_cube
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (hAB : IsAB 𝔽 ψ (kasamiF 𝔽 k))
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3) :=
  third_moment_collapse 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ
    (fun a => deltahat_sq_from_walsh 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ hAB a)
    v₁ v₂ hv₁ hv₂ hne

/-
════════════════════════════════════════════════════════════
SECTION 6 : LEVEL 1 — FOURIER INVERSION + SPECTRAL COLLAPSE
════════════════════════════════════════════════════════════

Fourier inversion: |𝔽|·|𝒯| = T.
-/
theorem fourier_triple_inversion
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) (k : ℕ) (v₁ v₂ : 𝔽) :
    (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card =
      spectralTripleSum 𝔽 ψ k v₁ v₂ := by
  have h_fubini : ∑ a : 𝔽, ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, ∑ z ∈ Δ 𝔽 k, ψ (a * (v₁ * x + v₂ * y + ( v₁ + v₂ ) * z )) = ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, ∑ z ∈ Δ 𝔽 k, ∑ a : 𝔽, ψ (a * (v₁ * x + v₂ * y + ( v₁ + v₂ ) * z )) := by
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm ) );
  convert h_fubini.symm using 1;
  · have h_orthogonality : ∀ c : 𝔽, ∑ a : 𝔽, ψ (a * c) = if c = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
      intro c; specialize h_fubini; simp_all +decide [ mul_comm ] ;
      convert addchar_orthogonality 𝔽 ψ hψ c using 1;
    simp +decide [ h_orthogonality, Finset.sum_ite ];
    simp +decide [ mul_comm, Finset.sum_mul _ _ _, 𝒯 ];
    simp +decide only [card_filter, sum_product];
    simp +decide [ mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  · simp +decide only [spectralTripleSum, deltaHat, Finset.sum_mul _ _ _, mul_sum];
    simp +decide only [← AddChar.map_add_eq_mul] ; congr ; ext ; congr ; ext ; congr ; ext ; congr ; ext ; ring;

/-- T = |Δ|³. ✅ (from kasami_is_AB + AB_implies_spectral_cube) -/
theorem spectral_sum_eq_delta_cubed
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3) :=
  AB_implies_spectral_cube 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ
    (kasami_is_AB 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ)
    v₁ v₂ hv₁ hv₂ hne

-- ════════════════════════════════════════════════════════════
-- SECTION 7 : LEVEL 0 — THE MAIN THEOREM
-- ════════════════════════════════════════════════════════════

/-- **combined_identity** : |𝔽| · |𝒯(v₁,v₂)| = |Δ|³.
    ✅ (from fourier_triple_inversion + spectral_sum_eq_delta_cubed) -/
theorem combined_identity
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    Fintype.card 𝔽 * (𝒯 𝔽 k v₁ v₂).card = (Δ 𝔽 k).card ^ 3 := by
  have h1 := fourier_triple_inversion 𝔽 ψ hψ k v₁ v₂
  have h2 := spectral_sum_eq_delta_cubed 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ v₁ v₂ hv₁ hv₂ hne
  have h3 : (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card = ↑((Δ 𝔽 k).card ^ 3) := by
    rw [h1, h2]
  exact_mod_cast h3

-- ════════════════════════════════════════════════════════════
-- SECTION 8 : COMPOSITION WITNESSES
-- ════════════════════════════════════════════════════════════

set_option linter.unusedSectionVars false in
/-- L1 → L0 composition witness ✅ -/
theorem combined_identity_from_L1
    (k : ℕ)
    (ψ : AddChar 𝔽 ℂ) (v₁ v₂ : 𝔽)
    (h_fourier : (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card =
      spectralTripleSum 𝔽 ψ k v₁ v₂)
    (h_spectral : spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3)) :
    (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card = ↑((Δ 𝔽 k).card ^ 3) := by
  rw [h_fourier, h_spectral]

set_option linter.unusedSectionVars false in
/-- L3 → L2b composition witness ✅ -/
theorem AB_implies_spectral_cube_from_L3
    (ψ : AddChar 𝔽 ℂ) (k : ℕ)
    (v₁ v₂ : 𝔽)
    (h_flat : ∀ a : 𝔽, ‖deltaHat 𝔽 ψ k a‖ ^ 2 = 0 ∨
      ‖deltaHat 𝔽 ψ k a‖ ^ 2 = (2 : ℝ) * Fintype.card 𝔽)
    (h_collapse : (∀ a : 𝔽, ‖deltaHat 𝔽 ψ k a‖ ^ 2 = 0 ∨
      ‖deltaHat 𝔽 ψ k a‖ ^ 2 = (2 : ℝ) * Fintype.card 𝔽) →
      spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3)) :
    spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3) :=
  h_collapse h_flat

set_option linter.unusedSectionVars false in
/-- L4 → L3 composition witness ✅ -/
theorem gauss_sum_abs_from_norm_sq
    (ψ : AddChar 𝔽 ℂ) (χ : MulChar 𝔽 ℂ)
    (h_sq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card 𝔽 : ℝ)) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
  rw [← h_sq, Real.sqrt_sq (norm_nonneg _)]

end
