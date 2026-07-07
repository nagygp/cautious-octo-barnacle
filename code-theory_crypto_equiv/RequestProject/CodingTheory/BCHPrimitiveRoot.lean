import Mathlib
import RequestProject.CodingTheory.BCHMinDist
import RequestProject.CodingTheory.ReedSolomon

/-!
# BCH and Reed–Solomon codes with primitive-root nodes (cyclic instantiation)

This module specialises the abstract BCH bound of
`RequestProject/CodingTheory/BCHBound.lean` and its minimum-distance phrasing in
`RequestProject/CodingTheory/BCHMinDist.lean` to the **genuine cyclic-code
setting**: the nodes are the consecutive powers `α⁰, α¹, …, α^{n−1}` of a
primitive `n`-th root of unity `α` (`orderOf α = n`). These are exactly the
evaluation points of a narrow-sense BCH / Reed–Solomon code, and the syndromes
`S_l(c) = ∑_i c_i · α^{i(b+l)}` are the Mattson–Solomon spectral coefficients of
the codeword.

For such nodes the two structural hypotheses of the abstract bound hold
automatically: the powers `α^i` (`0 ≤ i < n`) are distinct (injectivity, from the
order of `α`) and nonzero (since `α ≠ 0`). Hence the designed distance `δ` is a
genuine lower bound for the minimum distance of the primitive-root BCH code, and
Reed–Solomon codes evaluated at primitive-root points remain MDS.

## Main results

* `primitiveRoot_nodes_injective` — the powers `α^i` (`i < n`) are distinct.
* `primitiveRoot_nodes_ne_zero` — each power `α^i` is nonzero.
* `bchCode_primitiveRoot_minDist_ge` — the BCH bound for primitive-root nodes:
  `δ ≤ minDist (bchCode (α^·) b δ)`.
* `isMDS_reedSolomonCode_primitiveRoot`,
  `minDist_reedSolomonCode_primitiveRoot` — the Reed–Solomon code evaluated at the
  primitive-root nodes is MDS with minimum distance `n − k + 1`.
-/

open Finset BigOperators

namespace CodingTheory
namespace BCH

variable {F : Type*} [Field F]

/-- The **primitive-root nodes** `i ↦ α^i` for `i : Fin n`, the evaluation points
of a cyclic / BCH code with primitive `n`-th root of unity `α`. -/
def primitiveRootNodes (α : F) (n : ℕ) : Fin n → F := fun i => α ^ (i : ℕ)

/-
A primitive `n`-th root of unity is nonzero (its order `n ≥ 1`).
-/
theorem ne_zero_of_orderOf_eq {α : F} {n : ℕ} (hn : 1 ≤ n) (hα : orderOf α = n) :
    α ≠ 0 := by
  contrapose! hn; aesop;

/-
**The primitive-root nodes are distinct.** For `orderOf α = n`, the powers
`α^i` (`0 ≤ i < n`) are pairwise distinct.
-/
theorem primitiveRoot_nodes_injective {α : F} {n : ℕ} (hα : orderOf α = n) :
    Function.Injective (primitiveRootNodes α n) := by
  intro i j hij;
  have h_inj : Set.InjOn (fun k : ℕ => α ^ k) (Set.Iio n) := by
    grind +suggestions;
  exact Fin.ext ( h_inj ( Fin.is_lt i ) ( Fin.is_lt j ) hij )

/-
**The primitive-root nodes are nonzero.**
-/
theorem primitiveRoot_nodes_ne_zero {α : F} {n : ℕ} (hn : 1 ≤ n)
    (hα : orderOf α = n) (i : Fin n) :
    primitiveRootNodes α n i ≠ 0 := by
  exact pow_ne_zero _ ( ne_zero_of_orderOf_eq hn hα )

/-- **The BCH bound for primitive-root nodes.** For a primitive `n`-th root of
unity `α` and a nonzero BCH code of designed distance `δ`, the minimum distance is
at least `δ`. This is the classical BCH bound for cyclic codes. -/
theorem bchCode_primitiveRoot_minDist_ge {α : F} {n : ℕ} (hn : 1 ≤ n)
    (hα : orderOf α = n) (b δ : ℕ)
    (hC : bchCode (primitiveRootNodes α n) b δ ≠ ⊥) :
    δ ≤ minDist (bchCode (primitiveRootNodes α n) b δ) :=
  bchCode_minDist_ge (primitiveRootNodes α n)
    (primitiveRoot_nodes_injective hα) (primitiveRoot_nodes_ne_zero hn hα) b δ hC

/-! ### Reed–Solomon instantiation at primitive-root nodes -/

/-- **Reed–Solomon code at primitive-root nodes is MDS.** Evaluating at the
distinct powers of a primitive `n`-th root of unity yields an MDS `[n, k]` code. -/
theorem isMDS_reedSolomonCode_primitiveRoot {α : F} {n : ℕ} (hα : orderOf α = n)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card (Fin n)) :
    IsMDS (reedSolomonCode (primitiveRootNodes α n) k) :=
  isMDS_reedSolomonCode (primitiveRoot_nodes_injective hα) hk1 hkn

/-- **Minimum distance of the primitive-root Reed–Solomon code.** -/
theorem minDist_reedSolomonCode_primitiveRoot {α : F} {n : ℕ} (hα : orderOf α = n)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card (Fin n)) :
    minDist (reedSolomonCode (primitiveRootNodes α n) k)
      = Fintype.card (Fin n) - k + 1 :=
  minDist_reedSolomonCode (primitiveRoot_nodes_injective hα) hk1 hkn

end BCH
end CodingTheory