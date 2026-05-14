import Mathlib
import ABTopos.Spectral.KasamiCIC

/-!
# Conjectures Renforçantes — Théorie des Moments Spectraux

Formalisation Lean 4 des conjectures C₁–C₁₁ du document
`mTuple-count/CIC_Conjectures.md`.

Ces résultats renforcent la théorie m-tuple count en :
  1. Généralisant la décomposition du cube sum (m=3) à tout m ∈ ℕ
  2. Établissant l'identité de Parseval comme cas m=2
  3. Prouvant la récurrence M_{m+2} = c² · M_m
  4. Comptant le support spectral (s₊ + s₋)
  5. Étendant la dualité moment-comptage à tout m ≥ 1

## Dépendances
- `ABTopos.Spectral.KasamiCIC` : Spec, moment, sPos, sNeg, IsThreeValued, etc.
-/

open Finset BigOperators

noncomputable section

/-
════════════════════════════════════════════════════════════════
§1  DÉCOMPOSITION GÉNÉRALE DU m-IÈME MOMENT (C₁)
════════════════════════════════════════════════════════════════

**C₁ — General m-th Moment Decomposition (m ≥ 1).**
    For a three-valued spectrum {0, +c, −c}:
      M_m = s₊ · c^m + s₋ · (−c)^m

    Requires m ≥ 1 because 0^0 = 1 in Lean.
-/
theorem three_valued_moment_general {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) (m : ℕ) (hm : 1 ≤ m) :
    X.moment m = (X.sPos c : ℂ) * c ^ m + (X.sNeg c : ℂ) * (-c) ^ m := by
  unfold Spec.moment Spec.sPos Spec.sNeg;
  rw [ Finset.sum_congr rfl fun v hv => show X.W v ^ m = ( if X.W v = c then c ^ m else 0 ) + ( if X.W v = -c then ( -c ) ^ m else 0 ) from ?_, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite ];
  · simp +decide [ Finset.sum_const, nsmul_eq_mul ];
  · rcases h3 v with ( h | h | h ) <;> simp +decide [ h ];
    · cases m <;> aesop;
    · grind +splitIndPred;
    · exact fun h => ⟨ by linear_combination' -h / 2, by linarith ⟩

/-
════════════════════════════════════════════════════════════════
§2  MOMENTS PAIRS ET IMPAIRS (C₂, C₃)
════════════════════════════════════════════════════════════════

**C₂ — Even Moments (k ≥ 1).**
    M_{2k} = (s₊ + s₋) · c^{2k}.
-/
theorem three_valued_even_moment {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) (k : ℕ) (hk : 1 ≤ k) :
    X.moment (2 * k) = ((X.sPos c : ℂ) + (X.sNeg c : ℂ)) * c ^ (2 * k) := by
  convert three_valued_moment_general X c h3 ( 2 * k ) ( by linarith ) using 1 ; ring;
  norm_num [ pow_mul' ]

/-
**C₃ — Odd Moments.**
    M_{2k+1} = (s₊ − s₋) · c^{2k+1}.
-/
theorem three_valued_odd_moment {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) (k : ℕ) :
    X.moment (2 * k + 1) =
      ((X.sPos c : ℂ) - (X.sNeg c : ℂ)) * c ^ (2 * k + 1) := by
  convert three_valued_moment_general X c h3 ( 2 * k + 1 ) ( by linarith ) using 1 ; ring;
  norm_num [ pow_mul' ]

-- ════════════════════════════════════════════════════════════════
-- §3  IDENTITÉ DE PARSEVAL (C₄)
-- ════════════════════════════════════════════════════════════════

/-- **C₄ — Parseval Identity (Second Moment).**
    M₂ = (s₊ + s₋) · c².

    For AB functions on GF(2ⁿ) with c = 2^{(n+1)/2},
    M₂ = |G|² = 2^{2n} is the classical Parseval identity. -/
theorem parseval_three_valued {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) :
    X.moment 2 = ((X.sPos c : ℂ) + (X.sNeg c : ℂ)) * c ^ 2 :=
  three_valued_even_moment X c h3 1 le_rfl

-- ════════════════════════════════════════════════════════════════
-- §4  RÉCURRENCE DES MOMENTS (C₅)
-- ════════════════════════════════════════════════════════════════

/-- **C₅ — Moment Recurrence (m ≥ 1).**
    M_{m+2} = c² · M_m for three-valued spectra. -/
theorem moment_recurrence {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) (m : ℕ) (hm : 1 ≤ m) :
    X.moment (m + 2) = c ^ 2 * X.moment m := by
  rw [three_valued_moment_general X c h3 (m + 2) (by omega),
      three_valued_moment_general X c h3 m hm]
  ring

-- ════════════════════════════════════════════════════════════════
-- §5  SUPPORT SPECTRAL (C₆)
-- ════════════════════════════════════════════════════════════════

/-- The **spectral support**: the number of nonzero Walsh coefficients. -/
def Spec.support {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) : ℕ :=
  (univ.filter (fun v : X.carrier => X.W v ≠ 0)).card

/-- **C₆ — Support Size.**
    For a three-valued spectrum with c ≠ 0: support = s₊ + s₋. -/
theorem support_eq_sPos_add_sNeg {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (hc : c ≠ 0) (h3 : X.IsThreeValued c) :
    X.support = X.sPos c + X.sNeg c := by
  unfold Spec.support Spec.sPos Spec.sNeg
  rw [← Finset.card_union_of_disjoint]
  · congr with v; specialize h3 v; aesop
  · rw [Finset.disjoint_left]; intro v hv₁ hv₂; simp_all +decide [eq_neg_iff_add_eq_zero]

-- ════════════════════════════════════════════════════════════════
-- §6  DUALITÉ MOMENT-COMPTAGE GÉNÉRALISÉE (C₇)
-- ════════════════════════════════════════════════════════════════

/-- The **generalized normalized m-tuple count**:
      κ_m(X) := M_m(X) / |carrier|^{m−1} -/
def Spec.κ {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (m : ℕ) : ℂ :=
  X.moment m / (Fintype.card X.carrier : ℂ) ^ (m - 1)

/-- **C₇ — Generalized Moment-Count Duality.**
    M_m = |G|^{m−1} · κ_m. -/
theorem generalized_moment_count_duality {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (m : ℕ)
    (hG : (Fintype.card X.carrier : ℂ) ≠ 0) :
    X.moment m = (Fintype.card X.carrier : ℂ) ^ (m - 1) * X.κ m := by
  simp [Spec.κ]; field_simp

/-- κ₃ equals the generalized κ at m = 3. -/
theorem κ₃_eq_κ_3 {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) :
    X.κ₃ = X.κ 3 := by
  simp [Spec.κ₃, Spec.κ]

/-
════════════════════════════════════════════════════════════════
§7  RÉCURRENCE DU COMPTAGE κ (C₈)
════════════════════════════════════════════════════════════════

**C₈ — κ Recurrence.**
    κ_{m+2} = (c² / |G|²) · κ_m for three-valued spectra.
-/
theorem κ_recurrence {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) (m : ℕ) (hm : 1 ≤ m)
    (hG : (Fintype.card X.carrier : ℂ) ≠ 0) :
    X.κ (m + 2) = c ^ 2 / (Fintype.card X.carrier : ℂ) ^ 2 * X.κ m := by
  unfold Spec.κ;
  rw [ moment_recurrence X c h3 m hm, div_mul_div_comm ];
  rw [ ← pow_add, show m + 2 - 1 = 2 + ( m - 1 ) by omega ]

-- ════════════════════════════════════════════════════════════════
-- §8  COHÉRENCE AVEC LE CUBE SUM (C₁₀)
-- ════════════════════════════════════════════════════════════════

/-- **C₁₀ — Cube Sum Consistency (pure algebra).** -/
theorem cube_sum_from_general' (sp sn : ℕ) (c : ℂ) :
    (sp : ℂ) * c ^ 3 + (sn : ℂ) * (-c) ^ 3 =
    ((sp : ℂ) - (sn : ℂ)) * c ^ 3 := by
  ring

/-- The general moment at m=3 equals the cube sum formula. -/
theorem moment_3_eq_cube_sum {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) :
    X.moment 3 = ((X.sPos c : ℂ) - (X.sNeg c : ℂ)) * c ^ 3 := by
  rw [three_valued_moment_general X c h3 3 (by omega)]
  ring

-- ════════════════════════════════════════════════════════════════
-- §9  CHAÎNE D'ÉQUIVALENCES SPECTRALES (C₁₁)
-- ════════════════════════════════════════════════════════════════

/-- **C₁₁ — Three-Valued Implies Bent.**
    ThreeValued(c) ⟹ Bent(c) ⟹ diversity = 1 ⟹ Discrete -/
theorem three_valued_implies_bent {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℝ) (hc : c > 0)
    (h3 : X.IsThreeValued (c : ℂ)) :
    X.IsBent c :=
  three_valued_is_bent' X c hc h3

/-- The full spectral collapse chain for Kasami functions. -/
theorem kasami_spectral_chain {n : ℕ} (K : KasamiData n) :
    K.spec.IsBent K.c ∧
    K.spec.diversity = 1 ∧
    (postnikov K.spec K.nz).IsDiscrete :=
  ⟨kasami_bent K, kasami_diversity_one' K, kasami_discrete K⟩

-- ════════════════════════════════════════════════════════════════
-- §10  MOMENT ZÉRO ET MOMENT UN (complétude)
-- ════════════════════════════════════════════════════════════════

/-- The zeroth moment M₀ = |carrier|. -/
theorem moment_zero {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) :
    X.moment 0 = (Fintype.card X.carrier : ℂ) := by
  simp [Spec.moment]

/-- The first moment M₁ = (s₊ − s₋) · c for three-valued spectra. -/
theorem moment_one_three_valued {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (h3 : X.IsThreeValued c) :
    X.moment 1 = ((X.sPos c : ℂ) - (X.sNeg c : ℂ)) * c := by
  have := three_valued_odd_moment X c h3 0
  simpa using this

/-
The carrier partitions into three disjoint sets for c ≠ 0.
-/
theorem carrier_partition {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (X : Spec 𝔽) (c : ℂ) (hc : c ≠ 0) (h3 : X.IsThreeValued c) :
    (Fintype.card X.carrier : ℂ) = (X.sPos c : ℂ) + (X.sNeg c : ℂ) +
      ((univ.filter (fun v : X.carrier => X.W v = 0)).card : ℂ) := by
  norm_cast;
  rw [ Spec.sPos, Spec.sNeg ];
  rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
  · exact congr_arg Finset.card ( Finset.ext fun x => by specialize h3 x; aesop );
  · simp +contextual [ Finset.disjoint_left, hc ];
    rintro v ( hv | hv ) <;> simp_all +decide [ neg_eq_iff_add_eq_zero ];
  · simp +decide [ Finset.disjoint_left, hc ];
    grobner

-- ════════════════════════════════════════════════════════════════
-- §11  AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════

#print axioms three_valued_moment_general
#print axioms three_valued_even_moment
#print axioms three_valued_odd_moment
#print axioms parseval_three_valued
#print axioms moment_recurrence
#print axioms support_eq_sPos_add_sNeg
#print axioms generalized_moment_count_duality
#print axioms κ₃_eq_κ_3
#print axioms κ_recurrence
#print axioms moment_3_eq_cube_sum
#print axioms kasami_spectral_chain
#print axioms carrier_partition

end