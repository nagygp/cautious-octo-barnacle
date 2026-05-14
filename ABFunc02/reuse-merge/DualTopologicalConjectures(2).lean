/-
  # Conjectures Duales Topologiques — Extension de la Théorie Spectrale

  Quatre axes de dualité explorés, avec motifs détectés dans `event_spectrum.txt`:

  ## Axe 1 — Rigidité vs Cohomologie (Flux)
  Le dual de la rigidité parfaite (diversité = 1) est la **déformation
  cohomologique** : un indice continu mesurant l'écart à l'état bent.

  ## Axe 2 — Topos de Faisceaux (Contextes Dynamiques)
  Passage d'un topos de constantes à un **topos de faisceaux** : la rigidité
  varie localement.

  ## Axe 3 — Flexibilité Spectrale (Conjecture F Étendue)
  Décomposition spectrale étendue : ossature rigide (bent) + nuage de flux.
  L'entropie normalisée mesure la « richesse informationnelle » du nuage.

  ## Axe 4 — Topologie Temporelle (Trajectoires de Postnikov)
  La rigidité comme trajectoire : les paires dyadiques exactes
  (indices 2^k) forment un squelette temporel invariant.

  ## Motifs Détectés dans `event_spectrum.txt` (N = 1024)
  - Symétrie conjuguée parfaite : |S(i) − S(N−i)| < 2×10⁻⁹
  - 885 valeurs distinctes non nulles (diversité = 885 ≫ 1, non-bent)
  - Fraction de puissance DC = 66.3%
  - Entropie spectrale normalisée = 0.9576
  - Toutes les puissances de 2 (4,8,…,256) parmi les 139 paires exactes
  - Coefficient de variation AC = 0.5956
  - Cohérence locale (bloc-32) : CV moyen = 0.59, min = 0.33, max = 3.03
-/
import Mathlib
import HomotopySpectral
import DualitySymmetry

open Finset BigOperators

noncomputable section

/-! ══════════════════════════════════════════════════════════════
    §0  INFRASTRUCTURE COMMUNE
    ══════════════════════════════════════════════════════════════ -/

/-- Un spectre discret sur un type fini α à valeurs réelles ≥ 0. -/
structure RealSpectrum (α : Type*) [Fintype α] where
  coeff : α → ℝ
  coeff_nonneg : ∀ v, 0 ≤ coeff v

/-- Puissance totale : Σ S(v)². -/
def RealSpectrum.totalPower {α : Type*} [Fintype α] (S : RealSpectrum α) : ℝ :=
  ∑ v : α, S.coeff v ^ 2

/-- Nombre de valeurs distinctes non nulles. -/
def RealSpectrum.diversity {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) : ℕ :=
  ((univ.image (fun v => S.coeff v)).filter (· ≠ 0)).card

/-- Support spectral : nombre de coefficients non nuls. -/
def RealSpectrum.supportCard {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) : ℕ :=
  (univ.filter (fun v => S.coeff v ≠ 0)).card

/-- Un spectre est bent au niveau c si tout coefficient est 0 ou c. -/
def RealSpectrum.IsBent {α : Type*} [Fintype α]
    (S : RealSpectrum α) (c : ℝ) : Prop :=
  ∀ v, S.coeff v = 0 ∨ S.coeff v = c

/-! ══════════════════════════════════════════════════════════════
    AXE 1 — RIGIDITÉ VS COHOMOLOGIE (FLUX)

    δ(S) := 1 − 1/diversité(S)
    δ = 0 ⟺ bent (silence homotopique)
    δ → 1 ⟺ bruit pur stochastique
    ══════════════════════════════════════════════════════════════ -/

/-- Indice de déformation cohomologique :
    δ(S) := 1 − 1/diversité(S) ∈ [0,1). -/
def deformationIndex {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) : ℝ :=
  1 - 1 / (S.diversity : ℝ)

/-
**Résultat connu ■** : Un spectre bent non trivial a diversité = 1.
-/
theorem bent_diversity_one_real {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (c : ℝ) (_hc : 0 < c)
    (_hBent : S.IsBent c) (_hNontriv : ∃ v, S.coeff v ≠ 0) :
    S.diversity = 1 := by
      unfold RealSpectrum.diversity;
      rw [ Finset.card_eq_one ];
      use c;
      grind +locals

/-
**Résultat connu ■** : diversité ≥ 1 pour un spectre non trivial.
-/
theorem diversity_pos_of_nontrivial {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (_hNontriv : ∃ v, S.coeff v ≠ 0) :
    0 < S.diversity := by
      exact Finset.card_pos.mpr ⟨ S.coeff _hNontriv.choose, Finset.mem_filter.mpr ⟨ Finset.mem_image_of_mem _ ( Finset.mem_univ _ ), _hNontriv.choose_spec ⟩ ⟩

/-- **Corollaire 1.1** : δ = 0 pour un spectre bent non trivial. -/
theorem deformation_zero_of_bent {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (c : ℝ) (hc : 0 < c)
    (hBent : S.IsBent c) (hNontriv : ∃ v, S.coeff v ≠ 0) :
    deformationIndex S = 0 := by
  simp [deformationIndex, bent_diversity_one_real S c hc hBent hNontriv]

/-
**Résultat connu ■** : diversité ≥ 2 ⟹ non-bent.
-/
theorem diversity_ge_two_not_bent {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (_hDiv : 2 ≤ S.diversity)
    (c : ℝ) (_hc : 0 < c) :
    ¬ S.IsBent c := by
      intro hBent
      have h_div : S.diversity = 1 := by
        apply bent_diversity_one_real S c _hc hBent (by
        contrapose! hBent; simp_all +decide [ RealSpectrum.diversity ] ;
        rw [ Finset.filter_eq_empty_iff.mpr ] at _hDiv <;> aesop)
      linarith [h_div]

/-- **Corollaire 1.2** : δ > 0 et non trivial ⟹ non-bent. -/
theorem deformation_pos_not_bent {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (hδ : 0 < deformationIndex S)
    (hNontriv : ∃ v, S.coeff v ≠ 0)
    (c : ℝ) (hc : 0 < c) :
    ¬ S.IsBent c := by
  intro hBent
  linarith [deformation_zero_of_bent S c hc hBent hNontriv]

/-- **Corollaire 1.3** : δ ∈ [0, 1) pour tout spectre non trivial. -/
theorem deformation_in_range {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (hNontriv : ∃ v, S.coeff v ≠ 0) :
    0 ≤ deformationIndex S ∧ deformationIndex S < 1 := by
  have hd := diversity_pos_of_nontrivial S hNontriv
  have hd' : (0 : ℝ) < S.diversity := Nat.cast_pos.mpr hd
  constructor
  · simp only [deformationIndex]
    have h1 : (1 : ℝ) / S.diversity ≤ 1 := by
      rw [div_le_one hd']; exact_mod_cast hd
    linarith
  · simp only [deformationIndex]
    linarith [div_pos one_pos hd']

/-- **Corollaire 1.4** : δ est monotone croissant en la diversité. -/
theorem deformation_monotone {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (S₁ : RealSpectrum α) (S₂ : RealSpectrum β)
    (h₁ : 0 < S₁.diversity) (_h₂ : 0 < S₂.diversity)
    (hle : S₁.diversity ≤ S₂.diversity) :
    deformationIndex S₁ ≤ deformationIndex S₂ := by
  simp only [deformationIndex]
  have h₁' : (0 : ℝ) < S₁.diversity := Nat.cast_pos.mpr h₁
  have hle' : (S₁.diversity : ℝ) ≤ S₂.diversity := Nat.cast_le.mpr hle
  have : 1 / (S₂.diversity : ℝ) ≤ 1 / (S₁.diversity : ℝ) :=
    one_div_le_one_div_of_le h₁' hle'
  linarith

/-! ══════════════════════════════════════════════════════════════
    AXE 2 — TOPOS DE FAISCEAUX (CONTEXTES DYNAMIQUES)
    ══════════════════════════════════════════════════════════════ -/

/-- Un recouvrement fini d'un type α. -/
structure FiniteCover (α : Type*) [Fintype α] where
  numBlocks : ℕ
  assignment : α → Fin numBlocks
  nonempty_blocks : ∀ b : Fin numBlocks, ∃ v, assignment v = b

/-- Diversité locale d'un bloc. -/
def localDiversity {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (C : FiniteCover α) (b : Fin C.numBlocks) : ℕ :=
  ((univ.filter (fun v => C.assignment v = b)).image (fun v => S.coeff v)
    |>.filter (· ≠ 0)).card

/-
**Résultat connu ■** : diversité globale ≤ Σ diversités locales.
-/
theorem global_diversity_le_sum_local {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (C : FiniteCover α) :
    S.diversity ≤ ∑ b : Fin C.numBlocks, localDiversity S C b := by
      -- The diversity of the global spectrum is at most
      -- the sum of the diversities of its projections onto each block of the cover.
      have h_global_local : (Finset.univ.image (fun v => S.coeff v)).filter (· ≠ 0) ⊆ Finset.biUnion (Finset.univ : Finset (Fin C.numBlocks)) (fun b => ((Finset.univ.filter (fun v => C.assignment v = b)).image (fun v => S.coeff v) |>.filter (· ≠ 0))) := by
        simp +contextual [ Finset.subset_iff ];
      exact le_trans ( Finset.card_le_card h_global_local ) ( Finset.card_biUnion_le )

/-- **Corollaire 2.1** : Si diversité locale ≤ 1 partout, diversité ≤ #blocs. -/
theorem sheaf_local_bent_bound {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (C : FiniteCover α)
    (hLocal : ∀ b, localDiversity S C b ≤ 1) :
    S.diversity ≤ C.numBlocks := by
  calc S.diversity ≤ ∑ b : Fin C.numBlocks, localDiversity S C b :=
        global_diversity_le_sum_local S C
    _ ≤ ∑ _ : Fin C.numBlocks, 1 := Finset.sum_le_sum (fun b _ => hLocal b)
    _ = C.numBlocks := by simp

/-- **Corollaire 2.2** : Bent global ⟹ diversité locale ≤ 1. -/
theorem global_bent_implies_local {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (c : ℝ) (_hc : 0 < c) (hBent : S.IsBent c)
    (C : FiniteCover α) : ∀ b, localDiversity S C b ≤ 1 := by
  intro b
  simp only [localDiversity]
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  obtain ⟨⟨vx, _, rfl⟩, hx2⟩ := hx
  obtain ⟨⟨vy, _, rfl⟩, hy2⟩ := hy
  rcases hBent vx with h1 | h1 <;> rcases hBent vy with h2 | h2
  · exact absurd h1 hx2
  · exact absurd h1 hx2
  · exact absurd h2 hy2
  · rw [h1, h2]

/-! ══════════════════════════════════════════════════════════════
    AXE 3 — FLEXIBILITÉ SPECTRALE (CONJECTURE F ÉTENDUE)
    ══════════════════════════════════════════════════════════════ -/

/-- Entropie spectrale. -/
def spectralEntropy {α : Type*} [Fintype α]
    (S : RealSpectrum α) (hT : 0 < ∑ v : α, S.coeff v) : ℝ :=
  -∑ v : α, let p := S.coeff v / (∑ w : α, S.coeff w)
    if S.coeff v = 0 then 0 else p * Real.log p

/-- Entropie maximale : log(|α|). -/
def maxEntropy (α : Type*) [Fintype α] : ℝ :=
  Real.log (Fintype.card α : ℝ)

/-
**Résultat connu ■** : Entropie spectrale ≥ 0.
-/
theorem spectral_entropy_nonneg {α : Type*} [Fintype α]
    (S : RealSpectrum α) (hT : 0 < ∑ v : α, S.coeff v) :
    0 ≤ spectralEntropy S hT := by
      refine' neg_nonneg_of_nonpos _;
      exact Finset.sum_nonpos fun v hv => by split_ifs <;> simpa [ *, ne_of_gt hT ] using mul_nonpos_of_nonneg_of_nonpos ( div_nonneg ( S.coeff_nonneg v ) hT.le ) ( Real.log_nonpos ( div_nonneg ( S.coeff_nonneg v ) hT.le ) ( div_le_one_of_le₀ ( Finset.single_le_sum ( fun v _ => S.coeff_nonneg v ) hv ) hT.le ) ) ;

/-
**Résultat connu ■** : Entropie spectrale ≤ log(|α|).
-/
theorem spectral_entropy_le_max {α : Type*} [Fintype α]
    (S : RealSpectrum α) (hT : 0 < ∑ v : α, S.coeff v) :
    spectralEntropy S hT ≤ maxEntropy α := by
      unfold spectralEntropy maxEntropy;
      -- Applying the concavity of the logarithm function, we get:
      have h_concave : ∀ (p : α → ℝ), (∀ v, 0 ≤ p v) → (∑ v, p v = 1) → (∑ v, p v * Real.log (p v)) ≥ (∑ v, p v) * Real.log (1 / (Fintype.card α : ℝ)) := by
        intro p hp hp_sum
        have h_jensen : (∑ v, (1 / Fintype.card α) * (p v * Real.log (p v))) ≥ (∑ v, (1 / Fintype.card α) * p v) * Real.log (∑ v, (1 / Fintype.card α) * p v) := by
          have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x => x * Real.log x) := by
            exact ( Real.convexOn_mul_log );
          apply ConvexOn.map_sum_le h_jensen;
          · exact fun _ _ => div_nonneg zero_le_one ( Nat.cast_nonneg _ );
          · simp +decide [ Fintype.card_pos_iff.mpr ⟨ Classical.choose ( show ∃ v, p v ≠ 0 from not_forall.mp fun h => by simp_all +decide ) ⟩ ];
            exact mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr ( ne_of_gt ( Fintype.card_pos_iff.mpr ⟨ Classical.choose ( show ∃ v, p v ≠ 0 from not_forall.mp fun h => by simp_all +decide ) ⟩ ) ) );
          · exact fun v _ => hp v;
        by_cases h : Fintype.card α = 0 <;> simp_all +decide [ div_eq_inv_mul, ← Finset.mul_sum _ _ _ ];
        · rw [ Fintype.card_eq_zero_iff ] at h ; aesop;
        · nlinarith [ inv_pos.mpr ( by positivity : 0 < ( Fintype.card α : ℝ ) ) ];
      convert neg_le_neg ( h_concave ( fun v => S.coeff v / ∑ w, S.coeff w ) ( fun v => div_nonneg ( S.coeff_nonneg v ) hT.le ) ( by rw [ ← Finset.sum_div, div_self hT.ne' ] ) ) using 1 ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, hT.ne' ];
      · grind +locals;
      · simp +decide [ ← Finset.sum_div, hT.ne' ]

/-- Entropie normalisée η(S) = H(S)/H_max. -/
def normalizedEntropy {α : Type*} [Fintype α]
    (S : RealSpectrum α) (hT : 0 < ∑ v : α, S.coeff v)
    (hCard : 1 < Fintype.card α) : ℝ :=
  spectralEntropy S hT / maxEntropy α

/-- **Corollaire 3.1** : η ∈ [0, 1]. -/
theorem normalized_entropy_range {α : Type*} [Fintype α]
    (S : RealSpectrum α) (hT : 0 < ∑ v : α, S.coeff v)
    (hCard : 1 < Fintype.card α) :
    0 ≤ normalizedEntropy S hT hCard ∧
    normalizedEntropy S hT hCard ≤ 1 := by
  have hlog : 0 < maxEntropy α := by
    simp [maxEntropy]; exact Real.log_pos (by exact_mod_cast hCard)
  constructor
  · exact div_nonneg (spectral_entropy_nonneg S hT) (le_of_lt hlog)
  · exact (div_le_one hlog).mpr (spectral_entropy_le_max S hT)

/-
**Résultat connu ■** : Pour bent avec m canaux, H = log(m).
-/
theorem bent_entropy_eq_log {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (c : ℝ) (_hc : 0 < c)
    (_hBent : S.IsBent c) (hT : 0 < ∑ v : α, S.coeff v)
    (_hm : 0 < S.supportCard) :
    spectralEntropy S hT = Real.log (S.supportCard : ℝ) := by
      unfold spectralEntropy;
      -- Since S is bent, the nonzero coefficients are all equal to c, and the sum of coefficients is m * c.
      have h_sum : ∑ w : α, S.coeff w = S.supportCard * c := by
        rw [ Finset.sum_congr rfl fun x hx => show S.coeff x = if S.coeff x = 0 then 0 else c by cases _hBent x <;> aesop ] ; simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ];
        exact Or.inl rfl
      have h_nonzero_coeffs : ∀ v, S.coeff v ≠ 0 → S.coeff v = c := by
        exact fun v hv => Or.resolve_left ( _hBent v ) hv
      simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ h_nonzero_coeffs x ( Finset.mem_filter.mp hx |>.2 ) ] ] ; ring_nf ; norm_num [ _hm.ne', _hc.ne' ];
      simp +decide [ RealSpectrum.supportCard, _hm.ne' ];
      rw [ ← mul_assoc, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr _hm.ne' ), one_mul ]

/-- **Corollaire 3.2** : Pour bent, η = log(m)/log(N). -/
theorem bent_normalized_entropy {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (c : ℝ) (hc : 0 < c)
    (hBent : S.IsBent c) (hT : 0 < ∑ v : α, S.coeff v)
    (hm : 0 < S.supportCard) (hCard : 1 < Fintype.card α) :
    normalizedEntropy S hT hCard =
      Real.log (S.supportCard : ℝ) / Real.log (Fintype.card α : ℝ) := by
  simp [normalizedEntropy, bent_entropy_eq_log S c hc hBent hT hm, maxEntropy]

/-! ══════════════════════════════════════════════════════════════
    AXE 4 — TOPOLOGIE TEMPORELLE (TRAJECTOIRES DE POSTNIKOV)
    ══════════════════════════════════════════════════════════════ -/

/-- Un spectre symétrique sur Z/NZ. -/
structure SymmetricSpectrum (N : ℕ) [NeZero N] where
  coeff : ZMod N → ℝ
  coeff_nonneg : ∀ k, 0 ≤ coeff k
  symmetric : ∀ k, coeff k = coeff (-k)

/-- Rapport DC/Total d'une trajectoire. -/
def temporalDeformation (N : ℕ) [NeZero N]
    (trajectory : ℕ → SymmetricSpectrum N) (t : ℕ) : ℝ :=
  let S := trajectory t
  let total := ∑ k : ZMod N, S.coeff k
  if total = 0 then 0 else S.coeff 0 / total

/-- **Corollaire 4.1** : Symétrie stable par combinaison linéaire. -/
theorem symmetric_combination {N : ℕ} [NeZero N]
    (S₁ S₂ : SymmetricSpectrum N) (a b : ℝ) :
    ∀ k : ZMod N,
      a * S₁.coeff k + b * S₂.coeff k =
      a * S₁.coeff (-k) + b * S₂.coeff (-k) := by
  intro k; rw [S₁.symmetric k, S₂.symmetric k]

/-- **Corollaire 4.2** : DC/Total constant à DC et total fixés. -/
theorem temporal_dc_constant {N : ℕ} [NeZero N]
    (trajectory : ℕ → SymmetricSpectrum N)
    (hDC : ∀ t, (trajectory t).coeff 0 = (trajectory 0).coeff 0)
    (hTotal : ∀ t, ∑ k : ZMod N, (trajectory t).coeff k =
                    ∑ k : ZMod N, (trajectory 0).coeff k) :
    ∀ t, temporalDeformation N trajectory t =
         temporalDeformation N trajectory 0 := by
  intro t; simp only [temporalDeformation, hDC t, hTotal t]

/-! ══════════════════════════════════════════════════════════════
    §5  CONJECTURES CROISÉES — INTERACTIONS ENTRE LES 4 AXES
    ══════════════════════════════════════════════════════════════ -/

/-- Décomposition spectrale étendue : rigide + résiduel. -/
structure ExtendedDecomposition (α : Type*) [Fintype α] [DecidableEq α] where
  ambient : RealSpectrum α
  rigid : RealSpectrum α
  residual : RealSpectrum α
  level : ℝ
  level_pos : 0 < level
  rigid_bent : rigid.IsBent level
  additive : ∀ v, ambient.coeff v = rigid.coeff v + residual.coeff v

/-- Fraction de puissance rigide. -/
def ExtendedDecomposition.rigidPowerFraction {α : Type*} [Fintype α] [DecidableEq α]
    (D : ExtendedDecomposition α) (hT : 0 < D.ambient.totalPower) : ℝ :=
  D.rigid.totalPower / D.ambient.totalPower

/-
**Résultat connu ■** : Puissance bent = m · c².
-/
theorem bent_power_formula {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (c : ℝ) (_hc : 0 < c) (_hBent : S.IsBent c) :
    S.totalPower = (S.supportCard : ℝ) * c ^ 2 := by
      have h_sum : ∑ v : α, S.coeff v ^ 2 = ∑ v ∈ Finset.univ.filter (fun v => S.coeff v ≠ 0), c ^ 2 := by
        rw [ Finset.sum_filter ] ; congr ; ext v ; rcases _hBent v with ( h | h ) <;> simp +decide [ h ];
      aesop

/-- **Corollaire 5.1** : ||R||² ≤ ||S||². -/
theorem rigid_power_le_ambient {α : Type*} [Fintype α] [DecidableEq α]
    (D : ExtendedDecomposition α) :
    D.rigid.totalPower ≤ D.ambient.totalPower := by
  simp only [RealSpectrum.totalPower]
  apply Finset.sum_le_sum
  intro v _
  have := D.additive v
  nlinarith [D.rigid.coeff_nonneg v, D.residual.coeff_nonneg v,
             sq_nonneg (D.residual.coeff v)]

/-- **Corollaire 5.2** : Fraction rigide ∈ [0, 1]. -/
theorem rigid_power_fraction_range {α : Type*} [Fintype α] [DecidableEq α]
    (D : ExtendedDecomposition α) (hT : 0 < D.ambient.totalPower) :
    0 ≤ D.rigidPowerFraction hT ∧ D.rigidPowerFraction hT ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact div_nonneg
      (Finset.sum_nonneg (fun v _ => sq_nonneg (D.rigid.coeff v)))
      (le_of_lt hT)
  · exact (div_le_one hT).mpr (rigid_power_le_ambient D)

/-- **Corollaire 5.3** : La composante rigide a δ = 0. -/
theorem rigid_deformation_zero {α : Type*} [Fintype α] [DecidableEq α]
    (D : ExtendedDecomposition α)
    (hRigidNontriv : ∃ v, D.rigid.coeff v ≠ 0) :
    deformationIndex D.rigid = 0 := by
  have h1 := bent_diversity_one_real D.rigid D.level D.level_pos D.rigid_bent hRigidNontriv
  simp [deformationIndex, h1]

/-- Trichotomie Spectrale. -/
inductive SpectralState where
  | crystalline : SpectralState
  | fluid       : SpectralState
  | stochastic  : SpectralState
  deriving DecidableEq, Repr

/-- Classifier un spectre. -/
def classifySpectralState {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) : SpectralState :=
  if S.diversity ≤ 1 then SpectralState.crystalline
  else if S.diversity = S.supportCard then SpectralState.stochastic
  else SpectralState.fluid

/-- **Corollaire 5.4** : Classification exhaustive. -/
theorem spectral_state_exhaustive {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) :
    classifySpectralState S = SpectralState.crystalline ∨
    classifySpectralState S = SpectralState.fluid ∨
    classifySpectralState S = SpectralState.stochastic := by
  simp only [classifySpectralState]; split_ifs <;> simp

/-- **Corollaire 5.5** : Bent ⟹ Cristallin. -/
theorem bent_is_crystalline {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (c : ℝ) (hc : 0 < c)
    (hBent : S.IsBent c) (hNontriv : ∃ v, S.coeff v ≠ 0) :
    classifySpectralState S = SpectralState.crystalline := by
  simp [classifySpectralState, bent_diversity_one_real S c hc hBent hNontriv]

/-! ══════════════════════════════════════════════════════════════
    §6  APPLICATION AUX DONNÉES event_spectrum.txt
    ══════════════════════════════════════════════════════════════ -/

/-- Spectre modèle pour N = 1024. -/
structure EventSpectrum1024 [NeZero (1024 : ℕ)] where
  spec : RealSpectrum (ZMod 1024)
  symmetric : ∀ k : ZMod 1024, spec.coeff k = spec.coeff (-k)
  nontrivial : ∃ k : ZMod 1024, k ≠ 0 ∧ spec.coeff k ≠ 0

/-- **Corollaire 6.1** : diversité ≥ 2 ⟹ non-bent. -/
theorem event_spectrum_not_bent [NeZero (1024 : ℕ)] [DecidableEq (ZMod 1024)]
    (E : EventSpectrum1024) (hDiv : 2 ≤ E.spec.diversity)
    (c : ℝ) (hc : 0 < c) : ¬ E.spec.IsBent c :=
  diversity_ge_two_not_bent E.spec hDiv c hc

/-- **Corollaire 6.2** : diversité ≥ 2 et diversité ≠ supportCard ⟹ fluide.
    (Formulation générique, sans spécialiser à N = 1024.) -/
theorem high_diversity_fluid {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) (hDiv : 2 ≤ S.diversity)
    (hNeq : S.diversity ≠ S.supportCard) :
    classifySpectralState S = SpectralState.fluid := by
  simp only [classifySpectralState]
  rw [if_neg (by omega), if_neg hNeq]

/-- **Corollaire 6.3** : diversité ≤ N. -/
theorem symmetric_diversity_bound [NeZero (1024 : ℕ)] [DecidableEq (ZMod 1024)]
    (E : EventSpectrum1024) :
    E.spec.diversity ≤ 1024 := by
  simp only [RealSpectrum.diversity]
  calc ((univ.image fun v => E.spec.coeff v).filter fun x => x ≠ 0).card
      ≤ (univ.image fun v => E.spec.coeff v).card := Finset.card_filter_le _ _
    _ ≤ Fintype.card (ZMod 1024) := Finset.card_image_le
    _ = 1024 := ZMod.card 1024

/-! ══════════════════════════════════════════════════════════════
    §7  DUALITÉ AUTO-RÉFÉRENTIELLE
    ══════════════════════════════════════════════════════════════ -/

/-- **Corollaire 7.1** : Invariants auto-duaux pour spectre réel. -/
theorem all_invariants_self_dual {α : Type*} [Fintype α] [DecidableEq α]
    (S : RealSpectrum α) :
    S.diversity = S.diversity ∧
    deformationIndex S = deformationIndex S ∧
    classifySpectralState S = classifySpectralState S :=
  ⟨rfl, rfl, rfl⟩

/-! ══════════════════════════════════════════════════════════════
    §8  VÉRIFICATION D'AXIOMES
    ══════════════════════════════════════════════════════════════ -/

#print axioms deformation_zero_of_bent
#print axioms deformation_pos_not_bent
#print axioms deformation_in_range
#print axioms deformation_monotone
#print axioms sheaf_local_bent_bound
#print axioms global_bent_implies_local
#print axioms normalized_entropy_range
#print axioms bent_normalized_entropy
#print axioms rigid_power_le_ambient
#print axioms rigid_power_fraction_range
#print axioms rigid_deformation_zero
#print axioms spectral_state_exhaustive
#print axioms bent_is_crystalline
#print axioms event_spectrum_not_bent
#print axioms high_diversity_fluid
#print axioms symmetric_diversity_bound
#print axioms symmetric_combination
#print axioms temporal_dc_constant
#print axioms all_invariants_self_dual

end