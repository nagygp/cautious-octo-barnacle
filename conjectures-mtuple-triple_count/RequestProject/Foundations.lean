import RequestProject.Foundations.AddCharCount
import RequestProject.Foundations.ChiBridge
import RequestProject.Foundations.Fourier
import RequestProject.Foundations.WalshTransform
import RequestProject.Foundations.WienerKhinchin
import RequestProject.Foundations.WienerKhinchinInversion
import RequestProject.Foundations.ValueDistribution
import RequestProject.Foundations.ABSpectrum
import RequestProject.Foundations.ABImpliesAPN
import RequestProject.Foundations.ABNonlinearity
import RequestProject.Foundations.KasamiSpectrum
import RequestProject.Foundations.SpectralSum
import RequestProject.Foundations.KasamiCrossCorrelation
import RequestProject.Foundations.CubeMTupleCount
import RequestProject.Foundations.KasamiCrossCorrelationGeneralK
import RequestProject.Foundations.KasamiCrossCorrelationTable
import RequestProject.Foundations.KasamiCrossCorrelationValueSet
import RequestProject.Foundations.KasamiCrossCorrelationMultiplicityTable
import RequestProject.Foundations.KasamiVanishSign
import RequestProject.Foundations.KasamiMTupleCount
import RequestProject.Foundations.QuadraticGaussSum
import RequestProject.Foundations.RankSpectrum
import RequestProject.Foundations.GoldQuadratic
import RequestProject.Foundations.KasamiTwoAdicValuation
import RequestProject.Foundations.KasamiQuadraticValueSet
import RequestProject.Foundations.KasamiTwoDerivPolar
import RequestProject.Foundations.KasamiTwoMTupleCount
import RequestProject.Foundations.KasamiTwoRadicalDisproof
import RequestProject.Foundations.KasamiWeightEnumerator
import RequestProject.Foundations.KasamiPlessMoments
import RequestProject.Foundations.KasamiAdditiveEnergy
import RequestProject.Foundations.KasamiAdditiveEnergyBE2
import RequestProject.Foundations.KasamiAdditiveEnergyBE3
import RequestProject.Foundations.KasamiAdditiveEnergyBE3a
import RequestProject.Foundations.KasamiAdditiveEnergyBE3b
import RequestProject.Foundations.KasamiAdditiveEnergyBE3c
import RequestProject.Foundations.KasamiAdditiveEnergyBE3d
import RequestProject.Foundations.KasamiAdditiveEnergyBE3e
import RequestProject.Foundations.KasamiAxKatz
import RequestProject.Foundations.KasamiAxKatzAK2
import RequestProject.Foundations.KasamiAxKatzAK3
import RequestProject.Foundations.KasamiAxKatzAK3a
import RequestProject.Foundations.KasamiAxKatzAK3b
import RequestProject.Foundations.KasamiAxKatzAK3c
import RequestProject.Foundations.KasamiAxKatzAK3d
import RequestProject.Foundations.KasamiAxKatzAK3e
import RequestProject.Foundations.KasamiAxKatzAK3f
import RequestProject.Foundations.KasamiAxKatzAK4
import RequestProject.Foundations.KasamiAxKatzAK4a
import RequestProject.Foundations.KasamiWalshHyperplane
import RequestProject.Foundations.KasamiEvenMCubing
import RequestProject.Foundations.KasamiEq12Average
import RequestProject.Foundations.KasamiEq12ValueSet
import RequestProject.Foundations.KasamiSecondDerivMultiplicity
import RequestProject.Foundations.KasamiAutocorrWalshBridge
import RequestProject.Foundations.KasamiGrossKoblitz
import RequestProject.Foundations.KasamiGrossKoblitzDivisibility
import RequestProject.Foundations.KasamiValueSetFromInputs
import RequestProject.Foundations.KasamiLegendreValuation
import RequestProject.Foundations.KasamiEq12Substitution
import RequestProject.Foundations.KasamiABWeightDistribution
import RequestProject.Foundations.KasamiTeichmullerLift
import RequestProject.Foundations.KasamiGoldCovering
import RequestProject.Foundations.KasamiMacWilliams
import RequestProject.Foundations.KasamiGoldRadical
import RequestProject.Foundations.KasamiGoldRank
import RequestProject.Foundations.KasamiEq12CosetAverage
import RequestProject.Foundations.KasamiAutocorrPowerSpectrum
import RequestProject.Foundations.KasamiWienerKhinchinBridge
import RequestProject.Foundations.KasamiCyclotomicPrime
import RequestProject.Foundations.KasamiTeichmullerChar
import RequestProject.Foundations.KasamiFrobeniusLift
import RequestProject.Foundations.KasamiGrossKoblitzValue
import RequestProject.Foundations.KasamiDigitSumBound
import RequestProject.Foundations.KasamiGoldPolar
import RequestProject.Foundations.KasamiAdditiveEnergyBound
import RequestProject.Foundations.KasamiPrimeValuationPassage
import RequestProject.Foundations.KasamiDigitSumComplement
import RequestProject.Foundations.KasamiAdditiveEnergyCauchySchwarz
import RequestProject.Foundations.KasamiGoldRadicalSubspace
import RequestProject.Foundations.KasamiMcElieceCosetBound
import RequestProject.Foundations.KasamiAdditiveEnergyUpperBound
import RequestProject.Foundations.KasamiGoldRadicalGcd
import RequestProject.Foundations.KasamiCyclotomicCoset
import RequestProject.Foundations.KasamiAdditiveEnergyCollisions
import RequestProject.Foundations.KasamiGoldRadicalFrobenius

/-!
# `Vanish.Foundations` — the foundational tower for "Kasami is Vanish"

This is the single entry point for the **foundational layers** transcribed
(per `Docs/VanishBibliography.md`) from the finite-field / Fourier-analysis
literature towards a first-principles "Kasami is Vanish" formalization.  See
`Docs/VanishFutureDirections.md` for the planned higher layers.

The design follows *The Art of Clean Code* (Mayer, 2022): build a small,
well-named **dependency DAG**, lowest and most general at the bottom, each
declaration with a single responsibility, reusing Mathlib rather than
re-deriving (DRY).

## Layers built so far

* **Layer 1 — `Foundations/AddCharCount.lean`** (Mathlib-only, upstreamable).
  Finite-Fourier solution counting via additive characters:
  - `card_solutions_mul_eq_sum_addChar` — Pontryagin self-duality counting over
    an arbitrary finite abelian group (`Lidl–Niederreiter` Ch. 5, `Rudin`);
  - `card_solutions_mul_eq_field_sum` — counting via a single *primitive*
    character of a finite field;
  - `card_linear_tuple` — the linear m-tuple count in spectral form
    (`Chabaud–Vaudenay`'s higher-moment engine, `Carlet` Ch. 6);
  - `card_linear_tuple_of_vanish` — the abstract vanishing criterion.

* **Layer 2 — `Foundations/ChiBridge.lean`** (project bridge).
  Packages the project's hand-rolled sign character `WalshAB.χ` as a genuine
  `AddChar F ℤ` (`chiAddChar`), proves it primitive, and exhibits the project's
  `MTuple.card_mul_preCount` and orthogonality as **specializations** of Layer 1
  (`card_mul_preCount_via_foundation`, `chi_sum_eq_via_foundation`).

* **Layer 3 — `Foundations/WalshTransform.lean`** (upstreamable pearl + project
  bridge).  Defines the general Walsh–Hadamard transform `vectorialWalsh ψ f a b`
  for an arbitrary additive character `ψ`, proves the Plancherel/Parseval identity
  `∑_b vectorialWalsh ψ f a b · vectorialWalsh ψ⁻¹ f a b = |F|^2` for a primitive
  `ψ` and a bijective `f` (`vectorialWalsh_parseval`), and recovers the project's
  `ℤ`-valued transform and squared Parseval (`WalshAB.parseval_perm`) as the
  `ψ = chiAddChar` specialization (`walsh_eq_vectorialWalsh`,
  `walsh_sq_sum_via_foundation`).

* **`Foundations/Fourier.lean`** (Mathlib-only, upstreamable kernel).  The
  reusable, character-agnostic core factored out of Layers 3–4: the discrete
  Fourier transform `fourierTransform ψ g a = ∑_x ψ (a·x)·g x` and cyclic
  cross-correlation `crossCorr g h` over an arbitrary finite commutative ring,
  with **Plancherel/Parseval** (`fourierTransform_parseval`,
  `∑_b 𝓕ψ g b · 𝓕(ψ⁻¹) h b = |R|·∑_x g x·h x`) and **Wiener–Khinchin**
  (`fourierTransform_wienerKhinchin`,
  `𝓕ψ g a · 𝓕(ψ⁻¹) h a = ∑_u ψ (a·u)·crossCorr g h u`).  `vectorialWalsh_parseval`
  is now a thin corollary (`vectorialWalsh_eq_fourierTransform`).  See
  `Docs/UpstreamAssessment.md` for the Mathlib-overlap analysis.

* **Layer 4 — `Foundations/WienerKhinchin.lean`** (project bridge).  Recovers
  the project's `WalshAB.walsh_sq_eq_autocorr_sum`
  (`W(a,b)² = ∑_u χ(a·u)·R_b(u)`) as the `ψ = chiAddChar` specialization of
  `fourierTransform_wienerKhinchin` (`walsh_sq_eq_autocorr_sum_via_foundation`),
  identifying the Walsh transform with `fourierTransform chiAddChar (χ ∘ (b·f ·))`
  (`walsh_eq_fourierTransform_chi`) and `R_b` with the self-cross-correlation
  (`crossCorr_chi_eq_autocorrScaled`).

* **Layer 5 — the three-valued spectrum of an AB function.**  Built in three
  parts:
  - `Foundations/ValueDistribution.lean` (Mathlib-only, upstreamable pearls):
    `eq_zero_or_eq_or_eq_neg_of_sq_eq_zero_or_sq` (a two-valued square gives a
    three-valued value) and the sign-distribution lemmas
    (`sum_eq_posCard_sub_negCard`, `sum_sq_eq_posCard_add_negCard`,
    `posCard_add_negCard_add_zeroCard`) reading the value distribution of a
    `{-1,0,1}`-valued function off its first two moments.
  - `Foundations/ABSpectrum.lean` (project bridge): `walsh_three_valued`
    (`W ∈ {0, ±2^{(n+1)/2}}` from `IsAB`), the first moment `walsh_first_moment`,
    the extracted sign function `walshSign`, and the controlled distribution
    `walsh_zero_count`, `walsh_support_count`, `walsh_signed_count`.
  - `Foundations/KasamiSpectrum.lean` (Kasami specialization): the same four
    spectrum facts for the Kasami map `x ↦ x^d k`
    (`kasami_walsh_three_valued`, `kasami_walsh_zero_count`,
    `kasami_walsh_support_count`, `kasami_walsh_signed_count`), via
    `KasamiAB.kasami_is_ab` / `KasamiAB.kasami_bijective`.

* **Layer 6 — `Foundations/SpectralSum.lean`** (project bridge).  Evaluates the
  nonzero-frequency spectral sum `∑_{t≠0} ∏_i R(t·cᵢ) = q·preCount − qᵐ`
  (`spectralSum_eq_preCount`) and characterizes its vanishing as a balanced
  count: `Vanish ↔ preCount = q^{m-1}` (`vanish_iff_preCount`),
  `Vanish ↔ 2ᵐ·imgCount = q^{m-1}` (`vanish_iff_imgCount_pow`, APN), and for
  `m = 3` the **admissible** triples are exactly those with `imgCount = 2^{2n-3}`
  (`AdmissibleTriple`, `admissibleTriple_iff_vanish`,
  `kasami_admissibleTriple_iff_vanish`).  The unavoidable order-3 / `3 ∤ 2ⁿ−1`
  obstruction is re-exposed: the equal-coefficient cube map — the Kasami map at
  `k = 1`, since `d 1 = 3` — is **not** admissible, so its spectral sum does not
  vanish (`cube_equal_not_admissible`, `cube_equal_not_vanish`,
  `kasami_one_equal_not_vanish`).

* **Layer 7 — `Foundations/KasamiCrossCorrelation.lean`** (project bridge).
  Specializes Layer 6 to the **explicit Kasami cross-correlation** to *discharge*
  the `Vanish` hypothesis on a concrete class.  For the cube map (`= ` the Kasami
  map at `k = 1`, since `d 1 = 3`) the derivative is `F₂`-affine, so the scaled
  autocorrelation is supported on a two-element subgroup
  (`cube_autocorr_eq_zero`: `R(s) = 0` unless `s = 0 ∨ s·a³ = 1`;
  `cube_autocorr_zero`: `R(0) = q`).  Hence for nonzero coefficients that are
  **not all equal** the spectral sum vanishes unconditionally
  (`cube_vanish_of_not_all_eq`, `kasami_one_vanish_triple`,
  `kasami_one_triple_count`: image triple count `2^{2n-3}`), and admissibility is
  pinned down exactly (`cube_admissible_iff`:
  `AdmissibleTriple ↔ ¬ (c₀ = c₁ ∧ c₁ = c₂)`).  For general `k` the honest
  conditional target `kasami_is_vanish_triple` discharges `Vanish` from
  `AdmissibleTriple` (the Layer-6 equivalence).

* **Layer 8 — `Foundations/CubeMTupleCount.lean`** (project bridge).  Lifts the
  Layer-7 cube cross-correlation computation from the **triple** case (`m = 3`) to
  **every** arity `m`: since the cube autocorrelation is supported on `{0, a^{-3}}`,
  for nonzero coefficients that are **not all equal** every nonzero-frequency term
  vanishes (`cube_vanish_of_not_all_eq_gen`), discharging the `Vanish` hypothesis
  of `MTuple.imgCount_of_vanish` unconditionally.  This gives the closed-form
  general-`m` count `imgCount m (·³) a c = 2^{(m-1)n - m}` (`cube_mtuple_count`)
  and its Kasami `k = 1` form `kasami_one_mtuple_count` (`d 1 = 3`).  The Layer-7
  triple results are now its `m = 3` specializations.

* **Layers 9–12 — the general-`k` Kasami cross-correlation.**
  `KasamiCrossCorrelationGeneralK.lean` (Layer 9) builds the moment engine
  (2-to-1 reduction, first/second power moments);
  `KasamiCrossCorrelationTable.lean` (Layer 10) the power moments (incl. fourth)
  and the Pless/MacWilliams multiplicity solve;
  `KasamiCrossCorrelationValueSet.lean` the three-valued value set
  `R(s) ∈ {q, 0, ±2^{(n+1)/2}}` and its multiplicity table, reduced to the two
  classical scalar inputs **(A)** divisibility and **(B)** the fourth moment;
  `KasamiVanishSign.lean` (Layer 12) the explicit `Vanish` discharge as a sign
  correlation `Vanish m f a c ⟺ ∑_{t≠0} ∏_i σ(t·cᵢ) = 0` (`vanish_iff_sign_sum`,
  `kasami_admissible_iff_sign_sum`) — the general-`k` analogue of
  `cube_admissible_iff`, conditional on the value set; and
  `KasamiMTupleCount.lean` (Layer 11) the count `imgCount m (·^{d k}) a c`
  conditional on a discharged `Vanish`.  See `Docs/VanishFutureDirections.md` §§5–6
  for the remaining open inputs.

## Bibliographic anchoring

These layers correspond to §1 of `Docs/VanishBibliography.md` ("`Vanish` from
first principles — harmonic analysis on `(GF(2ⁿ),+)`").  Layer 1 realizes the
two "prime upstream candidates" flagged there: a finite-field additive character
used through a *primitive*-character orthogonality, and a *general
finite-abelian-group Fourier-inversion counting lemma*.
-/
