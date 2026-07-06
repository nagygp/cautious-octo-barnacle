import Mathlib
import RequestProject.CodingTheory.LinearCode

/-!
# Topology track: the Hamming metric space and unique nearest-codeword decoding

This module opens a **topology track** for the library.  Coding theory is, at
bottom, the geometry of a metric space: the ambient word space `ι → F` carries
the **Hamming metric** `d(x, y) = #{i : xᵢ ≠ yᵢ}`, and the minimum distance of a
code, error correction, and the sphere-packing bound are all *metric* statements
about balls in this space.  Mathlib packages the Hamming metric on the type
synonym `Hamming β` (here `β = fun _ : ι => F`), with `Hamming.dist_eq_hammingDist`
identifying its `dist` with `hammingDist`.  This module transcribes the
topological foundations that are equivalent to — and strengthen — the
coding-theory development:

* the ambient space is a **discrete, compact metric space** (a finite metric
  space), so every subset (in particular every code) is clopen and compact;
* the project's `minDist` is a genuine lower bound on the metric distance between
  distinct codewords (`minDist_le_hammingDist`);
* **unique decoding / the packing radius theorem**: if a code has minimum
  distance `> 2t` then the closed Hamming balls of radius `t` about distinct
  codewords are pairwise disjoint (`closedBall_disjoint_of_minDist`), so every
  received word lies within distance `t` of **at most one** codeword
  (`codeword_unique_of_hammingDist_le`).  This is the topological/metric heart of
  the "a code with `d ≥ 2t+1` corrects `t` errors" theorem, and it is exactly the
  packing that underlies the sphere-packing (Hamming) bound already in the
  library.

## Main results

* `HammingSpace` — notation for the Hamming metric space `Hamming (fun _ : ι => F)`.
* `instance : CompactSpace HammingSpace` and `DiscreteTopology HammingSpace`.
* `mem_closedBall_iff_hammingDist_le` — the metric closed ball is the Hamming ball.
* `minDist_le_hammingDist` — `minDist C ≤ d(x, y)` for distinct codewords.
* `codeword_unique_of_hammingDist_le` — unique decoding within radius `t` when
  `2t < minDist C`.
* `closedBall_disjoint_of_minDist` — the metric packing statement: closed balls of
  radius `t` about distinct codewords are disjoint.
-/

namespace CodingTheory
namespace Topology

open scoped Classical
open Metric

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The **Hamming metric space** on words `ι → F`: the type synonym `Hamming`
carrying `dist = hammingDist`. -/
abbrev HammingSpace (ι : Type*) [Fintype ι] (F : Type*) := Hamming (fun _ : ι => F)

/-
The Hamming metric space is finite, hence **compact**.
-/
instance : CompactSpace (HammingSpace ι F) := by
  infer_instance

/-
The metric closed ball of radius `t` in the Hamming space is exactly the set
of words at Hamming distance `≤ t`.
-/
theorem mem_closedBall_iff_hammingDist_le (x y : HammingSpace ι F) (t : ℕ) :
    y ∈ closedBall x (t : ℝ) ↔
      hammingDist (Hamming.ofHamming x) (Hamming.ofHamming y) ≤ t := by
  rw [ Metric.mem_closedBall, Hamming.dist_eq_hammingDist, hammingDist_comm ] ; norm_cast

variable [DecidableEq F]

/-
The project's `minDist` lower-bounds the Hamming distance between any two
distinct codewords.
-/
theorem minDist_le_hammingDist (C : Submodule F (ι → F)) {x y : ι → F}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    minDist C ≤ hammingDist x y := by
  apply Nat.sInf_le;
  -- Since $x$ and $y$ are distinct codewords in $C$, their Hamming distance is in the distance set of $C$.
  use x, hx, y, hy, hxy;
  convert rfl

/-
**Unique decoding within the packing radius.** If a code has minimum distance
`> 2t`, then any word `y` is within Hamming distance `t` of at most one codeword:
two codewords both within distance `t` of `y` must coincide.
-/
theorem codeword_unique_of_hammingDist_le (C : Submodule F (ι → F)) {t : ℕ}
    (ht : 2 * t < minDist C) {y c₁ c₂ : ι → F}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (h₁ : hammingDist y c₁ ≤ t) (h₂ : hammingDist y c₂ ≤ t) : c₁ = c₂ := by
  contrapose! ht;
  refine' le_trans ( minDist_le_hammingDist C hc₁ hc₂ ht ) _;
  convert hammingDist_triangle c₁ y c₂ |> le_trans <| add_le_add ( hammingDist_comm y c₁ ▸ h₁ ) h₂ using 1 ; ring

/-
**Metric packing.** If a code has minimum distance `> 2t`, the closed Hamming
balls of radius `t` about two distinct codewords are disjoint.
-/
theorem closedBall_disjoint_of_minDist (C : Submodule F (ι → F)) {t : ℕ}
    (ht : 2 * t < minDist C) {c₁ c₂ : ι → F}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (hne : c₁ ≠ c₂) :
    Disjoint
      (closedBall (Hamming.toHamming c₁) (t : ℝ))
      (closedBall (Hamming.toHamming c₂) (t : ℝ)) := by
  contrapose! hne; simp_all +decide [ Set.disjoint_left ] ;
  exact codeword_unique_of_hammingDist_le C ht hc₁ hc₂ hne.choose_spec.1 hne.choose_spec.2

end Topology
end CodingTheory