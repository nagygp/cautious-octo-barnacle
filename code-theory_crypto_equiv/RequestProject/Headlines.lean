import RequestProject.Core.KasamiAB
import RequestProject.DiffUniformity.KasamiDiffUniformity
import RequestProject.DiffUniformity.CharSumMonomialWeil
import RequestProject.DiffUniformity.CharSumRojasLeonReduction
import RequestProject.DiffUniformity.FlystelWalshDeepReduction
import RequestProject.CodingTheory.HartmannTzeng2D
import RequestProject.DiffUniformity.FlystelWalshFourthMoment
import RequestProject.DiffUniformity.FlystelWalshSCV
import RequestProject.CodingTheory.PlotkinConstruction
import RequestProject.DiffUniformity.FlystelWalshCollisionBound
import RequestProject.DiffUniformity.FlystelWalshFlatnessBound
import RequestProject.CodingTheory.PlotkinDimension
import RequestProject.Topology.HammingMetric
import RequestProject.CodingTheory.DirectSum
import RequestProject.Physics.FreeEnergyAdditive
import RequestProject.Geometry.ProjectiveEquivalence
import RequestProject.Walsh.ChabaudVaudenayGlobal
import RequestProject.Steiner
import RequestProject.Dobbertin1999

/-!
# Kasami APN & AB — headline entry point

This module is the single, discoverable entry point for the two first-principles
results of the Kasami development.  It lives at the top of the self-contained
module tree `RequestProject/`, whose layered layout is
described in `RequestProject/README.md`.

Throughout, `F` is a finite field of characteristic two with
`Fintype.card F = 2 ^ n`, and `d k = 2^{2k} − 2^k + 1` is the Kasami exponent
(`CollisionAnalysis.d`).  The standing Kasami hypotheses are `1 ≤ k < n`,
`gcd(k, n) = 1` and `n` odd.

## The two headlines

* `kasami_is_apn` — the Kasami power map `x ↦ x ^ d k` is **APN**
  (almost perfect nonlinear): every nonzero derivative is at most two-to-one.
* `kasami_is_ab` — the Kasami power map is **AB** (almost bent): its Walsh
  squares take values in `{0, 2^{n+1}}`.

Both are proved from first principles; see `RequestProject/Core/KasamiAB.lean`
(assembly), `RequestProject/Core/KasamiAPN.lean` / `Core/KasamiEvenK.lean`
(the APN core) and `RequestProject/Walsh/` (the moment method for AB).

## Abstract foundation

The APN statement is also available as a specialization of the
characteristic-free differential-uniformity foundation
(`RequestProject/DiffUniformity/DifferentialUniformity.lean`):
`kasami_is_apn_diffUnif` says the Kasami map has differential uniformity exactly
two, and the bridges `walshIsAPN_iff_diffUnif_le_two` /
`kasamiIsAPN_iff_diffUnif_le_two` identify the project's APN predicates with that
abstract notion.

On the parity hypotheses: `Odd n` is genuinely required by the present AB proof
(and by the Gold-permutation step of the APN proof); the underlying
Müller–Cohen–Matthews permutation input (`DempwolffMueller.theorem_3_2`) needs
only `Odd k` and `gcd(k, n) = 1`, with no condition on the parity of `n`.
-/

namespace Kasami.Headlines

/-- **Kasami is APN.** The Kasami power map `x ↦ x ^ d k` over `GF(2ⁿ)`
(`1 ≤ k < n`, `gcd(k,n)=1`, `n` odd) is almost perfect nonlinear: every nonzero
derivative fibre has at most two points. -/
alias kasami_is_apn := KasamiAB.kasami_is_apn_pred

/-- **Kasami is APN, differential-uniformity form.** The Kasami power map has
differential uniformity exactly two (`APNLib.IsAPN`). -/
alias kasami_is_apn_diffUnif := APNLib.kasami_isAPN_diffUnif

/-- **Kasami is AB.** The Kasami power map `x ↦ x ^ d k` over `GF(2ⁿ)`
(`1 ≤ k < n`, `gcd(k,n)=1`, `n` odd) is almost bent: its Walsh squares lie in
`{0, 2^{n+1}}`.

This uses `WalshAB.IsAB`, which quantifies over every **input** mask `a ≠ 0`
(all output masks `b`).  For the literature-standard almost-bent condition,
quantifying over every **output** mask `b ≠ 0` (all input masks `a`, including
`a = 0`), see `kasami_is_ab_outputMask`; for the Kasami permutation the two
forms are equivalent. -/
alias kasami_is_ab := KasamiAB.kasami_is_ab

/-- **Kasami is AB — literature-faithful (output-mask) form.** For every nonzero
output mask `b` and every input mask `a` (including `a = 0`), the Walsh square
of `x ↦ x ^ d k` lies in `{0, 2^{n+1}}`.  This is the standard almost-bent
condition on the component functions `Tr (b · x^{d k})`, `b ≠ 0`. -/
alias kasami_is_ab_outputMask := KasamiAB.kasami_is_ab_outputMask

end Kasami.Headlines

/-! ## Character-sum gates and Hartmann–Tzeng headlines

Three further headline results extend the Flystel/Walsh character-sum layer and
the coding-theory layer. Each is `sorry`-free and depends only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace CharSumGates.Headlines

/-- **Monomial Weil bound (Track 1).** For a primitive additive character `ψ` of
a finite field and any `d ≥ 1`, the one-variable character sum of the monomial
`x ↦ x^d` obeys the Weil bound `‖∑_x ψ(x^d)‖ ≤ (d−1)·√q`. This discharges,
unconditionally, the general `d`-th-root character-orthogonality hypothesis that
was the sole remaining gap of the Gauss-sum gate. -/
alias weilBoundOne_monomial := APN.CharSumBounds.weilBoundOne_monomial

/-- **`d`-th-root character orthogonality (Track 1).** For `y ≠ 0`, the sum of
`χ(y)` over all multiplicative characters of order dividing `d` counts the `d`-th
roots of `y`. -/
alias sum_mulChar_pow_eq_card := APN.CharSumBounds.sum_mulChar_pow_eq_card

/-- **2D → 1D Rojas–León reduction (Track 2).** A two-variable phase that completes
the square in the second variable to `c·(y + s x)² + P x` (`c ≠ 0`) satisfies the
two-variable Rojas–León bound `(d−1)·q` as soon as the residual `P` satisfies the
one-variable Weil bound — reducing the two-dimensional algebraic-geometry input to
a one-dimensional one. -/
alias rojasLeonBoundTwo_of_factor := APN.CharSumBounds.rojasLeonBoundTwo_of_factor

/-- **Unconditional monomial-residual Rojas–León bound (Track 2).** When the
residual is a pure monomial `x^d`, the two-variable bound is unconditional, via
the Track 1 monomial Weil bound. -/
alias rojasLeonBoundTwo_of_factor_monomial :=
  APN.CharSumBounds.rojasLeonBoundTwo_of_factor_monomial

end CharSumGates.Headlines

namespace HartmannTzeng.Headlines

/-- **The two-dimensional Hartmann–Tzeng bound (Track 3).** For a primitive
`n`-th root of unity `α` and steps `c₁, c₂` both coprime to `n`, a nonzero word
with vanishing syndromes on the grid `{b + i₁·c₁ + i₂·c₂ : 0 ≤ i₁ < m, 0 ≤ i₂ ≤ s}`
(`m ≥ 1`) has Hamming weight at least `(m+1) + s`. This is the genuine
two-dimensional defining-set bound, beyond the single arithmetic-progression
case. -/
alias ht_bound := CodingTheory.BCH.ht_bound

/-- **Hartmann–Tzeng minimum-distance bound (Track 3).** The designed distance
`(m+1) + s` lower-bounds the minimum distance of the two-dimensional
Hartmann–Tzeng cyclic code. -/
alias htCode_minDist_ge := CodingTheory.BCH.htCode_minDist_ge

end HartmannTzeng.Headlines

/-! ## Walsh moments and the `(u | u+v)` construction (round 10)

Three further headline results extend the Flystel/Walsh moment layer (Tracks 1, 2)
and the coding-theory layer (Track 3). Each is `sorry`-free and depends only on the
standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace WalshMoments.Headlines

/-- **Fourth moment of the field-level Walsh transform (Track 1).** For a
nontrivial additive character `ψ` of a finite field `K` (`q = #K`) and any
`F : K × K → K × K`, the fourth-moment of the Walsh spectrum equals `q⁴` times the
number of second-order collision quadruples
`{(x₁,x₂,x₃,x₄) : x₁−x₂+x₃−x₄ = 0 ∧ F x₁−F x₂+F x₃−F x₄ = 0}`. Unconditional, via
additive-character orthogonality only (the sequel to the Parseval second moment). -/
alias walsh_fourth_moment := APN.FlystelWalsh.walsh_fourth_moment

/-- **SCV-style spectral lower bound (Track 2).** Combining the Parseval second
moment `∑‖W‖² = q⁶` with the fourth moment, some nonzero mask `(a,b)` satisfies
`(q⁶ − q⁴)·‖W_F(ψ,a,b)‖² ≥ q⁴·N − q⁸` (`N` the collision count): an
unconditional lower bound on the largest nonzero-mask Walsh coefficient. -/
alias exists_walsh_sq_ge_of_collisions := APN.FlystelWalsh.exists_walsh_sq_ge_of_collisions

/-- **Minimum distance of the `(u | u+v)` construction (Track 3).** For nonzero
linear codes `C₁, C₂ ⊆ Fⁿ`, the `(u | u+v)` code in `F²ⁿ` has minimum weight
`min (2·d(C₁), d(C₂))` — the classical Plotkin construction behind the Reed–Muller
recursion. -/
alias minWeight_uuvCode := CodingTheory.Plotkin.minWeight_uuvCode

end WalshMoments.Headlines

/-! ## Moment inequalities and the `(u | u+v)` dimension (round 11)

Three further headline results extend the Flystel/Walsh moment layer (Tracks 1, 2)
and the coding-theory layer (Track 3). Each is `sorry`-free and depends only on the
standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace WalshMoments.Headlines

/-- **Lower bound on second-order collisions (Track 1).** Cauchy–Schwarz applied
to the Parseval second moment `∑ ‖W‖² = q⁶` and the fourth moment
`∑ ‖W‖⁴ = q⁴·N` gives, for every `F : K × K → K × K` over a finite field `K`
(`q = #K`) and nontrivial `ψ`, the unconditional bound `q⁴ ≤ N`, where
`N = #(secondOrderCollisions F)`. -/
alias secondOrderCollisions_card_ge := APN.FlystelWalsh.secondOrderCollisions_card_ge

/-- **Flat spectrum bounds collisions (Track 2).** The converse to the SCV
lower bound: if every nonzero-mask Walsh square is `≤ M`, then
`q⁴·N ≤ q⁸ + M·(q⁶ − q⁴)` — a flat (low-linearity) Walsh spectrum forces few
second-order collisions. -/
alias secondOrderCollisions_card_le_of_walsh_sq_le :=
  APN.FlystelWalsh.secondOrderCollisions_card_le_of_walsh_sq_le

/-- **Dimension of the `(u | u+v)` construction (Track 3).** For linear codes
`C₁, C₂ ⊆ Fⁿ`, the injective encoding `(u,v) ↦ (u | u+v)` gives
`dim (uuvCode C₁ C₂) = dim C₁ + dim C₂`; with `minWeight_uuvCode` this yields the
full `[2n, k₁+k₂, min(2d₁, d₂)]` Plotkin parameter set. -/
alias finrank_uuvCode := CodingTheory.Plotkin.finrank_uuvCode

end WalshMoments.Headlines

/-! ## Multi-track expansion: topology, direct sums, extensivity, projective
invariance, and the global APN characterization

Five further headline results extend the library along the topology track (new),
the coding-theory track, the statistical-mechanics (physics) track, the
finite-geometry track, and the ZK / symmetric-crypto track.  Each is `sorry`-free
and depends only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`. -/

namespace MultiTrack.Headlines

/-- **Topology track — unique nearest-codeword decoding.** In the Hamming metric
space, if a code has minimum distance `> 2t` then any received word is within
Hamming distance `t` of at most one codeword: two codewords both within distance
`t` coincide.  This is the metric/topological heart of `t`-error correction. -/
alias codeword_unique_decoding :=
  CodingTheory.Topology.codeword_unique_of_hammingDist_le

/-- **Topology track — metric packing.** For a code of minimum distance `> 2t`,
the closed Hamming balls of radius `t` about distinct codewords are disjoint. -/
alias hamming_ball_packing :=
  CodingTheory.Topology.closedBall_disjoint_of_minDist

/-- **Coding track — minimum distance of a direct sum.** `C₁ ⊕ C₂` has minimum
weight `min (d₁, d₂)` (with dimension `k₁ + k₂` via `finrank_directSumCode`). -/
alias minWeight_directSumCode := CodingTheory.minWeight_directSumCode

/-- **Physics track — extensivity of the free energy.** The free energy of a
direct sum of codes (independent spin subsystems) is additive:
`F_{C₁ ⊕ C₂}(β) = F_{C₁}(β) + F_{C₂}(β)`. -/
alias freeEnergy_directSumCode := CodingTheory.freeEnergy_directSumCode

/-- **Geometry track — projective invariance of arcs.** For an invertible matrix
`M`, `M * G` is an arc iff `G` is: arcs (hence MDS codes) are invariant under
invertible projective coordinate changes. -/
alias isArc_projective_invariant := CodingTheory.isArc_mulLeft_iff

/-- **ZK / crypto track — global second-moment characterization of APN.** A
vectorial Boolean function `f` is APN iff its global differential second moment
`∑_{a≠0} ∑_b N_f(a,b)²` attains the minimum `2|F|(|F| − 1)`. -/
alias isAPN_iff_sum_diffCount_sq_global :=
  WalshAB.isAPN_iff_sum_diffCount_sq_global

end MultiTrack.Headlines

/-! ## Steiner Flystel–Walsh-spectrum sub-track (ZK / symmetric crypto)

Headline results of the multivariate transcription of M. J. Steiner, *A note on
the Walsh spectrum of the Flystel* (Designs, Codes and Cryptography 93 (2025)
2245–2262), integrated into the ZK / symmetric-crypto track from the earlier
standalone development.  Each is `sorry`-free and depends only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.  See
`RequestProject/Steiner.lean` for the full layer. -/

namespace Steiner.Headlines

/-- **Power-permutation characterization (Lidl–Niederreiter 7.8).** For `d ≥ 1`,
the power map `x ↦ xᵈ` is a permutation of a finite field `Fq` iff
`gcd(d, #Fq − 1) = 1` — both directions. -/
alias powMap_bijective_iff := Flystel.Foundations.powMap_bijective_iff

/-- **Finite-field character duality (Lidl–Niederreiter 5.7).** Every non-trivial
additive character of `Fq` is `x ↦ ψ₁(b·x)` for a fixed primitive (fundamental)
character `ψ₁` and some `b ≠ 0`: the finite-field instance of `F ≅ F̂`. -/
alias exists_eq_fundamental_smul := Flystel.Foundations.exists_eq_fundamental_smul

/-- **Diagonal Walsh bound.** The multivariate Walsh transform
`W_F(ψ, a, b) = ∑_x ψ(⟨a,x⟩ + ⟨b,F x⟩)` of `F : Fqⁿ → Fqᵐ` has norm at most
`qⁿ`, the trivial bound every Weil/Deligne/Rojas–León estimate improves upon. -/
alias norm_walshTransform_le := Flystel.norm_walshTransform_le

/-- **Linear (`b = 0`) Walsh vanishing.** For a non-trivial character `ψ` and a
nonzero input mask `a`, `W_F(ψ, a, 0) = 0` — case 2 of Steiner's Theorems
3.3/3.5/3.6. -/
alias walshTransform_eq_zero_of_b_eq_zero := Flystel.walshTransform_eq_zero_of_b_eq_zero

/-- **Walsh spectrum under CCZ-equivalence.** If `F` and `G` are CCZ-equivalent
then every Walsh coefficient of `F` equals, in absolute value, some Walsh
coefficient of `G` (Steiner Eq. (6)–(10)). -/
alias walsh_of_CCZEquiv := Flystel.walsh_of_CCZEquiv

/-- **Mask-tracking CCZ-invariance of the Walsh spectrum.** If `F` and `G` are
CCZ-equivalent then every *nonzero*-mask Walsh coefficient of `F` equals, in
absolute value, a *nonzero*-mask Walsh coefficient of `G`.  Because the mask
substitution is invertible, the maximum over nonzero masks (the nonlinearity)
transfers across CCZ-equivalence. -/
alias walsh_of_CCZEquiv_ne := Flystel.walsh_of_CCZEquiv_ne

/-- **Proposition 2.5 (Anemoi, Proposition 1).** For a permutation `E` and any
`Q_γ, Q_δ`, the open and closed Flystel of `(Q_γ, E, Q_δ)` are CCZ-equivalent. -/
alias closed_openFlystel_CCZEquiv := Flystel.closed_openFlystel_CCZEquiv

/-- **Anemoi `x³` deep-entry bound from the classical one-variable Weil bound.**
The two-variable Rojas–León deep-entry input of the Anemoi Walsh sandwich is
*derived* (unconditionally) from the classical one-variable cubic Weil bound over
`F₁₁`, sharpening the open input from the two-variable estimate to the standard
one-variable one. -/
alias anemoi_hdeep_of_oneVarWeil := APN.FlystelWalsh.Anemoi.hdeep_of_oneVarWeil

/-- **Anemoi `x³` Walsh sandwich, conditional only on the one-variable Weil
bound.** -/
alias anemoi_sandwich_of_oneVarWeil := APN.FlystelWalsh.Anemoi.sandwich_of_oneVarWeil

/-- **Poseidon `x⁵` deep-entry bound from the classical one-variable Weil bound**
(quintic Weil bound over `F₁₃`). -/
alias poseidon_hdeep_of_oneVarWeil := APN.FlystelWalsh.Poseidon.hdeep_of_oneVarWeil

/-- **Poseidon `x⁵` Walsh sandwich, conditional only on the one-variable Weil
bound.** -/
alias poseidon_sandwich_of_oneVarWeil := APN.FlystelWalsh.Poseidon.sandwich_of_oneVarWeil

end Steiner.Headlines

/-! ## Dobbertin (1999) — Layers B, C, D on the green Kasami core

Headline results of the next layers of the faithful transcription of Hans
Dobbertin, *Kasami Power Functions, Permutation Polynomials and Cyclic Difference
Sets* (NATO Sci. Ser. C **542**, Kluwer, 1999), added on top of the established
core (Layer 0) and Layer A.  Layer B supplies the paper's Section 2 polynomial
definitions (`q_α`, `P_β`, the linearized `ℓ`) with the `ℓ`-root count coming from
Layer A; Layer C records the permutation-polynomial pillar (the Kasami power map
is a permutation, and its derivative is a two-to-one map, via Layer A); Layer D
adds the cyclic-difference-set pillar (the Singer difference set with Singer
parameters), built on the additive-character Fourier bridge.  Each is `sorry`-free
and depends only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.  See `RequestProject/Dobbertin1999.lean` for the full entry point. -/

namespace Dobbertin1999.NextLayers.Headlines

/-- **Layer C — the Kasami power function is a permutation of `𝔽_{2ⁿ}`.** -/
alias kasamiPow_bijective := Dobbertin1999.Theorem1.kasamiPow_bijective

/-- **Layer C — the Kasami derivative `x ↦ (x+1)^d + x^d` is a two-to-one map.** -/
alias kasamiDeriv_two_to_one := Dobbertin1999.Theorem1.kasamiDeriv_two_to_one

/-- **Layer B — root count of the linearized polynomial `ℓ` of eq. (2), via Layer A.** -/
alias affineLinPoly_root_count := Dobbertin1999.GenKasamiPoly.affineLinPoly_root_count

/-- **Layer D — the Singer set is a cyclic difference set with Singer parameters.** -/
alias singer_isMulDifferenceSet := Dobbertin1999.Singer.singer_isMulDifferenceSet

end Dobbertin1999.NextLayers.Headlines
