import RequestProject.Geometry.Arcs

/-!
# The MDS conjecture and the length bound for plane arcs

This module continues the finite-geometry track of
`RequestProject/Geometry/Arcs.lean` (arcs ⇄ MDS codes).  It records the
**main conjecture of the theory of MDS codes / arcs** and proves the classical
special case `k = 2` (arcs of `PG(1, q)`).

A `k`-dimensional MDS code of length `n` corresponds (via `isMDS_genCode_iff_isArc`)
to an `n`-arc of `PG(k-1, q)`: `n` points in general position.  The
**MDS conjecture** (Segre's conjecture) asserts that for `2 ≤ k ≤ q - 1` every
arc satisfies the length bound

  `n ≤ q + 1`

(with the two classical exceptions `q` even and `k ∈ {3, q-1}`, where `q + 2` is
achievable).  This is a famous open problem in general; it is a theorem in the
boundary cases.

Here we prove the `k = 2` case unconditionally: a **plane arc**, i.e. a generator
matrix `G : Matrix (Fin 2) ι F` whose columns are pairwise linearly independent,
has at most `q + 1 = #F + 1` columns, because its columns are pairwise
non-proportional nonzero vectors of `F²`, i.e. distinct points of the projective
line `PG(1, q)`, which has `q + 1` points.

## Main results

* `arc_two_card_le` — a `2`-row arc has `#ι ≤ #F + 1` columns (the projective-line
  bound, via the slope map `ι ↪ Option F`).
* `isMDS_two_length_le` — an `[n, 2]` MDS code has length `n ≤ q + 1`.
* `MDSConjecture` — the statement of the MDS (Segre) conjecture for arcs.
-/

namespace CodingTheory

open scoped Classical
open Matrix

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The **slope map** sending a column `(a, b)` of a 2-row generator matrix to its
point of the projective line `PG(1, q) ≃ F ∪ {∞}`: `none` ("∞") if `a = 0`, and
`some (b / a)` otherwise.  Two columns have the same slope iff they are
proportional. -/
noncomputable def arcSlope (G : Matrix (Fin 2) ι F) (i : ι) : Option F :=
  if G 0 i = 0 then none else some (G 1 i / G 0 i)

/-
**The projective-line length bound for plane arcs.**  A `2`-row arc has at
most `#F + 1` columns: the slope map `ι → Option F` is injective on an arc, and
`#(Option F) = #F + 1`.
-/
theorem arc_two_card_le [Fintype F] {G : Matrix (Fin 2) ι F} (hG : IsArc G) :
    Fintype.card ι ≤ Fintype.card F + 1 := by
  have h_inj : ∀ i j : ι, i ≠ j → arcSlope G i ≠ arcSlope G j := by
    intro i j hij h_eq
    have h_linear_dep : ∃ (a b : F), (a ≠ 0 ∨ b ≠ 0) ∧ a • arcColumn G i + b • arcColumn G j = 0 := by
      by_cases hi : G 0 i = 0 <;> by_cases hj : G 0 j = 0 <;> simp_all +decide [ arcSlope ];
      · by_cases hi' : G 1 i = 0 <;> by_cases hj' : G 1 j = 0 <;> simp_all +decide [ funext_iff, Fin.forall_fin_two, arcColumn ];
        · exact ⟨ 1, 0, by simp +decide ⟩;
        · exact ⟨ 1, one_ne_zero ⟩;
        · exact ⟨ 1, one_ne_zero ⟩;
        · exact ⟨ -G 1 j, G 1 i, by aesop, by ring ⟩;
      · refine' ⟨ -G 0 j, G 0 i, _, _ ⟩ <;> simp_all +decide [ funext_iff, Fin.forall_fin_two ];
        simp_all +decide [ arcColumn, div_eq_iff ];
        grind;
    obtain ⟨ a, b, hne, h ⟩ := h_linear_dep;
    have := Fintype.linearIndependent_iff.mp ( hG { i, j } ?_ ) ( fun x => if x = ⟨ i, by simp +decide ⟩ then a else b ) ?_ <;> simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
    · grind +qlia;
    · rw [ Finset.sum_eq_single ⟨ j, by simp +decide ⟩ ] <;> aesop;
  simpa using Fintype.card_le_of_injective _ ( show Function.Injective ( arcSlope G ) from fun i j hij => Classical.not_not.1 fun hi => h_inj i j hi hij )

/-- **The `k = 2` MDS conjecture (a theorem).**  An `[n, 2]` MDS code over `F`
has length `n ≤ #F + 1`.  Here `G` is a generator matrix with linearly
independent rows. -/
theorem isMDS_two_length_le [Fintype F] {G : Matrix (Fin 2) ι F}
    (hG : LinearIndependent F G) (hmds : IsMDS (genCode G)) :
    Fintype.card ι ≤ Fintype.card F + 1 :=
  arc_two_card_le ((isMDS_genCode_iff_isArc hG (by norm_num)).1 hmds)

/-- **The MDS (Segre) conjecture for arcs.**  For `2 ≤ k ≤ #F - 1`, every arc
`G : Matrix (Fin k) ι F` (every `k` columns linearly independent) has at most
`#F + 1` columns.  This is the statement of a famous open conjecture; the `k = 2`
boundary case is `arc_two_card_le`. -/
def MDSConjecture (F : Type*) [Field F] [Fintype F] : Prop :=
  ∀ (k : ℕ), 2 ≤ k → k ≤ Fintype.card F - 1 →
    ∀ {ι : Type*} [Fintype ι] (G : Matrix (Fin k) ι F),
      IsArc G → Fintype.card ι ≤ Fintype.card F + 1

end CodingTheory