import RequestProject.CodingTheory.SpherePacking

/-!
# The Hamming association scheme: relations and valencies

This module begins the **association-scheme** layer flagged in
`FUTURE_DIRECTIONS_FOUNDATIONS.md` as the single most *connective* abstraction:
the Hamming scheme is the common home of the coding-theory Delsarte LP bound, the
geometry of designs, and the difference-set / eigenvalue picture on the crypto
side.

The **Hamming scheme** `H(n, q)` has point set `Fⁿ = (ι → F)` (`n = #ι`,
`q = #F`) and, for `0 ≤ i ≤ n`, the *i-th relation* `R_i = {(x, y) : d(x,y) = i}`
on Hamming distance.  Its first structural invariants are the **valencies**
`v_i = #{y : d(x,y) = i} = C(n,i)(q-1)^i` (independent of `x`), the entries that
later become the Krawtchouk eigenvalues of the Bose–Mesner algebra.

## Main results

* `hammingValency` — the valency function `v_i = C(n,i)(q-1)^i`.
* `card_hammingRelation` — every point has exactly `v_i` points at distance `i`
  (regularity of the scheme); this reuses `card_filter_hammingDist_eq`.
* `hammingRelations_partition` — the relations partition the point set: the
  distance spheres about a fixed `x` cover `Fⁿ` and are pairwise disjoint.
* `sum_hammingValency` — the valencies sum to `q^n` (the order of the scheme):
  `Σ_{i=0}^{n} C(n,i)(q-1)^i = q^n`, a binomial identity.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The **valency** of the `i`-th relation of the Hamming scheme `H(n, q)`:
`v_i = C(n, i)(q-1)^i`, the number of points at Hamming distance `i` from any
fixed point. -/
def hammingValency (n q i : ℕ) : ℕ := n.choose i * (q - 1) ^ i

/-
**Regularity of the Hamming scheme.** Every point `c` has exactly
`v_i = C(n,i)(q-1)^i` points at Hamming distance `i`.
-/
theorem card_hammingRelation (c : ι → F) (i : ℕ) :
    (Finset.univ.filter (fun x : ι → F => hammingDist x c = i)).card
      = hammingValency (Fintype.card ι) (Fintype.card F) i := by
  convert card_filter_hammingDist_eq c i using 1

/-
**The relations partition the point set.** The distance spheres about a fixed
`x` cover all of `Fⁿ` and are pairwise disjoint: every other point lies at a
unique Hamming distance `i ≤ n`.
-/
theorem hammingRelations_partition (x : ι → F) :
    (Finset.range (Fintype.card ι + 1)).biUnion
        (fun i => Finset.univ.filter (fun y : ι → F => hammingDist x y = i)) = Finset.univ
    ∧ ∀ i ∈ Finset.range (Fintype.card ι + 1), ∀ j ∈ Finset.range (Fintype.card ι + 1), i ≠ j →
        Disjoint (Finset.univ.filter (fun y : ι → F => hammingDist x y = i))
          (Finset.univ.filter (fun y : ι → F => hammingDist x y = j)) := by
  refine' ⟨ _, _ ⟩;
  · ext y; simp +decide [ hammingDist ] ;
    exact Finset.card_le_univ _;
  · exact fun i hi j hj hij => Finset.disjoint_filter.mpr fun y _ hyi hyj => hij <| hyi.symm.trans hyj

/-
**The order of the scheme.** The valencies sum to `q^n`:
`Σ_{i=0}^{n} C(n,i)(q-1)^i = q^n`.
-/
theorem sum_hammingValency :
    ∑ i ∈ Finset.range (Fintype.card ι + 1),
        hammingValency (Fintype.card ι) (Fintype.card F) i
      = Fintype.card F ^ Fintype.card ι := by
  unfold hammingValency;
  rw [ eq_comm, show Fintype.card F = ( Fintype.card F - 1 ) + 1 from by rw [ Nat.sub_add_cancel ( Fintype.card_pos ) ] ];
  simp +decide [ add_pow, mul_comm ]

end CodingTheory