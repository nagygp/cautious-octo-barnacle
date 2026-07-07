import RequestProject.Steiner.Foundations
import RequestProject.Steiner.Preliminaries
import RequestProject.Steiner.Walsh
import RequestProject.Steiner.WalshAlgebra
import RequestProject.Steiner.CCZ
import RequestProject.Steiner.Flystel

/-!
# Steiner Flystel–Walsh-spectrum sub-track (ZK / symmetric crypto)

Aggregator for the multivariate transcription of

  M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
  Designs, Codes and Cryptography (2025) 93:2245–2262,

integrated into the project's ZK / symmetric-cryptography track.  Every
declaration collected here is fully proved from Mathlib (`sorry`-free) and
depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

This layer complements the concrete `K × K` Flystel/Walsh development under
`RequestProject/DiffUniformity/` with a general `n, m`-variable treatment over an
arbitrary finite field `Fq`:

* `RequestProject.Steiner.Foundations` — the reusable first-principles layer:
  character duality `F ≅ F̂` (`exists_eq_fundamental_smul`), the power-permutation
  characterisation `powMap_bijective_iff` (`x ↦ xᵈ` permutes `Fq` iff
  `gcd(d, q-1) = 1`, both directions), and the atomic character-sum algebra
  (`norm_charSum_le`, `charSum_add_factor`, `charSum_comp_equiv`,
  `norm_charSum_add_const`, orthogonality and the linear-sum dichotomy).
* `RequestProject.Steiner.Preliminaries` — the paper's Section 2 notation
  (inner product, additive characters, power permutations).
* `RequestProject.Steiner.Walsh` / `WalshAlgebra` — the multivariate Walsh
  transform `walshTransform ψ F a b` and its algebra: the diagonal bound
  `norm_walshTransform_le`, re-indexing invariance `walshTransform_comp_equiv`,
  variable separation `sum_two_var_factor`, and the linear (`b = 0`) vanishing
  `walshTransform_eq_zero_of_b_eq_zero`.
* `RequestProject.Steiner.CCZ` — the graph, affine permutations, CCZ-equivalence,
  and the Walsh-norm relation across CCZ-equivalence (`walsh_of_CCZEquiv`).
* `RequestProject.Steiner.Flystel` — the open/closed Flystel and Proposition 2.5
  (`closed_openFlystel_CCZEquiv`: they are CCZ-equivalent), plus the transcription
  of the Anemoi designers' Conjecture 2.6.
-/
