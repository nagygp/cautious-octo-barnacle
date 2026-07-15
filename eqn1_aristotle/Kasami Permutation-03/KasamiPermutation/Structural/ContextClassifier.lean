import RequestProject.KasamiPermutation.Headlines.InvariantAndClassifier
import RequestProject.KasamiPermutation.Structural.Obstruction

/-!
# The Kasami headline as a general obstruction, and the context classifier

This module distils the "equivalent contexts" bridge into its most reusable
structural core, in two independent halves.

## §1 — The Kasami headline via the general obstruction

The necessary direction of the permutation criterion (Theorem 1) is *literally*
the general `KasamiPerm.Obstruction.apply_ne_zero_of_bijective_fixing_zero`
applied at `x = 1`, fed the two evaluations `q_α(0) = 0` and
`q_α(1) = k' + α·n`.  No finite-field machinery is used.

## §2 — The bridge is an equivalence of categories (the Caramello classifier)

The groupoid `Context` of parameter tuples `(n, k, k', α)` and its parity functor
`parFunctor : Context ⥤ Discrete (ZMod 2)` (both defined in
`Headlines.InvariantAndClassifier`) assemble into a genuine **equivalence of
categories**

  `contextClassifier : Context ≌ Discrete (ZMod 2)`,

by proving `parFunctor` full, faithful (the hom-sets are subsingletons) and
essentially surjective.  So the whole groupoid of Kasami contexts *is* the
two-point classifier `ZMod 2`; its two connected components are the two parity
classes.  Corollaries: `iso_iff_par` (isomorphism ⇔ shared invariant) and
`contextSelfDual : Context ≌ Contextᵒᵖ` (the MacLane self-duality of a groupoid,
inherited from the self-dual discrete classifier).  Finally the criterion is read
straight off the classifier (`qKasami_one_eq_zero_iff_classifier`,
`bijective_imp_classifier_one`).

All declarations are `sorry`-free and rest only on the standard axioms.
-/

open scoped BigOperators
open CategoryTheory

namespace KasamiPerm.Headlines.Bridge

open KasamiPerm.Headlines

/-! ═══════════════════════════════════════════════════════════════════
    §1. THE KASAMI HEADLINE AS THE GENERAL OBSTRUCTION
    ═══════════════════════════════════════════════════════════════════ -/

section Headline

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

omit [Fintype L] [CharP L 2] in
/-- **The obstruction at `x = 1`.**  If the generalized Kasami map is bijective it
cannot vanish at `1`, because it fixes `0`.  This is exactly the general
`apply_ne_zero_of_bijective_fixing_zero`, with no finite-field input. -/
theorem qKasami_one_ne_zero_of_bijective (α : ℕ)
    (h : Function.Bijective (qKasami (L := L) n k k' α)) :
    qKasami (L := L) n k k' α 1 ≠ 0 :=
  KasamiPerm.Obstruction.apply_ne_zero_of_bijective_fixing_zero h
    (qKasami_zero α) one_ne_zero

omit [Fintype L] in
/-- **Necessary direction of Theorem 1, as a one-liner.**  Bijectivity of `q_α`
forces `k' + α·n` odd — obtained purely from the general obstruction plus the two
evaluations `q_α(0) = 0`, `q_α(1) = k' + α·n`. -/
theorem qKasami_bijective_imp_parity_v2 (α : ℕ)
    (h : Function.Bijective (qKasami (L := L) n k k' α)) :
    (k' + α * n) % 2 = 1 := by
  have hne := qKasami_one_ne_zero_of_bijective (L := L) α h
  simp only [qKasami_one, ne_eq, CharP.cast_eq_zero_iff L 2] at hne
  omega

end Headline

/-! ═══════════════════════════════════════════════════════════════════
    §2. THE CONTEXT CLASSIFIER (equivalence of categories)
    ═══════════════════════════════════════════════════════════════════ -/

/-- The hom-sets of `Context` are subsingletons (`Context` is a thin groupoid):
a morphism is a mere proof of equal parity. -/
instance instContextHomSubsingleton {c d : Context} : Subsingleton (c ⟶ d) :=
  Equiv.plift.subsingleton

/-- `parFunctor` is faithful: any two parallel morphisms of contexts are equal. -/
instance : parFunctor.Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- `parFunctor` is full: a morphism `parFunctor.obj c ⟶ parFunctor.obj d` in the
discrete classifier is a proof `c.par = d.par`, which is itself a context
morphism. -/
instance : parFunctor.Full where
  map_surjective {_ _} g := ⟨⟨g.down.down⟩, by apply Subsingleton.elim⟩

/-- `parFunctor` is essentially surjective: every parity class `t : ZMod 2` is hit
by the context `(0, 0, t.val, 0)`. -/
instance : parFunctor.EssSurj where
  mem_essImage d := by
    refine ⟨⟨0, 0, (d.as).val, 0⟩, ⟨?_⟩⟩
    refine Discrete.eqToIso ?_
    show ((((d.as).val : ℕ) + 0 * 0 : ℕ) : ZMod 2) = d.as
    simp [ZMod.natCast_rightInverse d.as]

instance : parFunctor.IsEquivalence where

/-- **The Caramello classifier.**  The whole groupoid of Kasami contexts is
*the same category* as the two-point classifier `ZMod 2`: the parity functor is an
equivalence of categories.  Its two connected components are the two parity
classes. -/
noncomputable def contextClassifier : Context ≌ Discrete (ZMod 2) :=
  parFunctor.asEquivalence

/-- **Isomorphism ⇔ shared invariant.**  Two contexts are isomorphic objects iff
they lie in the same parity class — the connected components of `Context` are
exactly the two parity classes. -/
theorem iso_iff_par (c d : Context) : Nonempty (c ≅ d) ↔ c.par = d.par :=
  ⟨fun ⟨e⟩ => e.hom.down, fun h => ⟨⟨⟨h⟩, ⟨h.symm⟩, rfl, rfl⟩⟩⟩

/-- **Self-duality of the context groupoid.**  Since the discrete classifier
`Discrete (ZMod 2)` is self-dual, so is `Context`: `Context ≌ Contextᵒᵖ` (the
MacLane self-duality of a groupoid). -/
noncomputable def contextSelfDual : Context ≌ Contextᵒᵖ :=
  contextClassifier.trans
    ((Discrete.opposite (ZMod 2)).symm.trans contextClassifier.op.symm)

/-! ### Reading the criterion off the classifier -/

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]

omit [Fintype L] in
/-- The Kasami map vanishes at `1` iff the classifier sends its context to the
`0` (trace/parity-even) point. -/
theorem qKasami_one_eq_zero_iff_classifier (c : Context) :
    qKasami (L := L) c.n c.k c.kk c.α 1 = 0 ↔ parFunctor.obj c = Discrete.mk 0 := by
  rw [qKasami_one_eq_zero_iff_par]
  exact ⟨fun h => congrArg Discrete.mk h, fun h => congrArg Discrete.as h⟩

omit [Fintype L] in
/-- **Bijective ⟹ the context lands in the unique "odd" component.**  A context
that can host a permutation is classified by `1 : ZMod 2` — the only component
compatible with bijectivity. -/
theorem bijective_imp_classifier_one (c : Context)
    (h : Function.Bijective (qKasami (L := L) c.n c.k c.kk c.α)) :
    parFunctor.obj c = Discrete.mk 1 := by
  have hne : c.par ≠ 0 := bridge_transports_bijective_necessary (L := L) (𝟙 c) h
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact congrArg Discrete.mk (key c.par hne)

end KasamiPerm.Headlines.Bridge
