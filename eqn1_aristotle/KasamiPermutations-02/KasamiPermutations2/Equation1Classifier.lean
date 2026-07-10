import KasamiPermutations2.Equation1ProofSpace
/-!
# Equation (1) — structural shortcuts and the classifier bridge
This file continues the "Caramello bridge" exploration begun in
`Equation1ProofSpace.lean`.  Where that file *found* the engine-free shortcut for
the necessary direction of Dobbertin's Theorem 1 and *packaged* the two Kasami
contexts as a groupoid, this file **distils the shortcut to its smallest reusable
core** and **upgrades the context bridge to a genuine equivalence of categories**
(the "classifier"), following the clean-code maxim: one idea, stated once, in the
most general place, then reused everywhere.
## What is new here
* **§1 — the one-invariant obstruction, fully general.**  The whole "engine-free"
  argument is a single, three-line fact about *any* self-map of *any* type:
  a map that collides two distinct points is not injective
  (`not_injective_of_collision`), so a bijection fixing `0` cannot vanish at a
  nonzero point (`apply_ne_zero_of_bijective_fixing_zero`).  This is the "small,
  elegant structural invariant that propagates from Mathlib foundations to the
  headline": it needs no field, no finiteness, no Frobenius.
* **§2 — the Kasami shortcut as a one-liner.**  The necessary direction of
  Theorem 1 (`qKasami_bijective_imp_parity_v2`) is now literally the general
  obstruction of §1 fed the two evaluations `q_α(0) = 0`, `q_α(1) = k' + α·n`
  (from `Equation1ProofSpace`).  The proof is a single application.
* **§3 — the context bridge is an equivalence of categories (the classifier).**
  The parity functor `parFunctor : Context ⥤ Discrete (ZMod 2)` is full, faithful
  and essentially surjective, hence an *equivalence*
  (`contextClassifier : Context ≌ Discrete (ZMod 2)`).  This is the sharpest form
  of the "Morita-equivalent contexts" idea: the entire groupoid of Kasami
  contexts is *the same category* as the two-point classifier `ZMod 2`.  Its
  connected components are exactly the two parity classes
  (`iso_iff_par`), and — being a groupoid — it is canonically isomorphic to its
  own opposite (`contextSelfDual : Context ≌ Contextᵒᵖ`, the MacLane dual).
Everything is self-contained (only `Mathlib` plus the sibling file) and
`sorry`-free.
-/
open scoped BigOperators
open Finset CategoryTheory Kasami
namespace Dobbertin1999.Equation1ProofSpace
/-! ═══════════════════════════════════════════════════════════════════
    §1. THE ONE-INVARIANT OBSTRUCTION (fully general, no algebra)
    ═══════════════════════════════════════════════════════════════════ -/
section Abstract
variable {X : Type*}
/-- **Collision obstruction.** A self-map that sends two *distinct* points to the
same value is not injective.  This is the entire mathematical content of the
"engine-free" shortcut, stripped of every hypothesis that is not used. -/
theorem not_injective_of_collision (f : X → X) {a b : X}
    (hab : a ≠ b) (h : f a = f b) : ¬ Function.Injective f :=
  fun hinj => hab (hinj h)
/-- **Zero-collision obstruction.** A self-map that *fixes* `0` and *vanishes* at
some nonzero `c` is not injective (take `a = c`, `b = 0`). -/
theorem not_injective_of_zero_collision [Zero X] (f : X → X) {c : X}
    (hc : c ≠ 0) (h0 : f 0 = 0) (hc0 : f c = 0) : ¬ Function.Injective f :=
  not_injective_of_collision f hc (by rw [hc0, h0])
/-- **The propagating invariant.** A *bijection* that fixes `0` cannot vanish at
any nonzero point.  This one statement — no field, no finiteness — is what the
Kasami headline's necessary direction instantiates. -/
theorem apply_ne_zero_of_bijective_fixing_zero [Zero X] (f : X → X)
    (h0 : f 0 = 0) (hf : Function.Bijective f) {c : X} (hc : c ≠ 0) : f c ≠ 0 :=
  fun hc0 => not_injective_of_zero_collision f hc h0 hc0 hf.injective
end Abstract
/-! ═══════════════════════════════════════════════════════════════════
    §2. THE KASAMI NECESSARY DIRECTION, AS ONE APPLICATION OF §1
    ═══════════════════════════════════════════════════════════════════ -/
section Kasami
variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}
omit [Fintype L] in
/-- **The shortcut, refactored.**  The necessary direction of Dobbertin's
Theorem 1 — if the generalized Kasami map `q_α` is bijective then `k' + α·n` is
odd — is *exactly* the general obstruction `apply_ne_zero_of_bijective_fixing_zero`
applied at the point `1`, using only `q_α(0) = 0` and the value-at-`1` criterion
`q_α(1) = 0 ↔ k' + α·n ≡ 0`.  No finite-field engine is involved. -/
theorem qKasami_bijective_imp_parity_v2 (α : ℕ)
    (h : Function.Bijective (qKasami (L := L) n k k' α)) :
    (k' + α * n) % 2 = 1 := by
  have hne : qKasami (L := L) n k k' α 1 ≠ 0 :=
    apply_ne_zero_of_bijective_fixing_zero _ (qKasami_zero (L := L) α) h one_ne_zero
  rw [Ne, qKasami_one_eq_zero_iff] at hne
  omega
end Kasami
/-! ═══════════════════════════════════════════════════════════════════
    §3. THE CONTEXT BRIDGE IS AN EQUIVALENCE (the classifier)
    ═══════════════════════════════════════════════════════════════════ -/
section Classifier
/-- Hom-sets of `Context` are subsingletons: at most one arrow between contexts
(the proof that they share the parity invariant).  This makes `Context` a *thin*
groupoid — an equivalence relation viewed as a category. -/
instance ctxHomSubsingleton (c d : Context) : Subsingleton (c ⟶ d) :=
  inferInstanceAs (Subsingleton (PLift _))
/-- `parFunctor` is **faithful** — automatic for a thin source category. -/
instance : parFunctor.Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _
/-- `parFunctor` is **full**: a morphism `parFunctor.obj c ⟶ parFunctor.obj d` in
`Discrete (ZMod 2)` is exactly an equality `c.par = d.par`, which is a morphism
`c ⟶ d`. -/
instance : parFunctor.Full where
  map_surjective f := ⟨⟨by simpa [parFunctor] using f.1.1⟩, Subsingleton.elim _ _⟩
/-- `parFunctor` is **essentially surjective**: every parity value `v : ZMod 2` is
realised by the context `(0, 0, v.val, 0)`. -/
instance : parFunctor.EssSurj where
  mem_essImage d := by
    refine ⟨⟨0, 0, d.as.val, 0⟩, ⟨Discrete.eqToIso ?_⟩⟩
    show Context.par _ = d.as
    simp [Context.par]
/-- Hence `parFunctor` is an **equivalence of categories**. -/
noncomputable instance : parFunctor.IsEquivalence := Functor.IsEquivalence.mk
/-- **The classifier bridge.**  The whole groupoid of Kasami contexts is
*equivalent* to the two-object discrete category on `ZMod 2`: one invariant,
`k' + α·n (mod 2)`, and every context is completely determined up to isomorphism
by it.  This is the strongest form of "Morita-equivalent contexts" — not merely a
transport of one invariant, but an identification of the two categories. -/
noncomputable def contextClassifier : Context ≌ Discrete (ZMod 2) :=
  parFunctor.asEquivalence
/-- **The MacLane dual.**  Being (equivalent to a discrete groupoid, hence) a
groupoid, `Context` is equivalent to its own opposite category. -/
noncomputable def contextSelfDual : Context ≌ Contextᵒᵖ :=
  contextClassifier.trans
    ((Discrete.opposite (ZMod 2)).symm.trans contextClassifier.op.symm)
/-- **Connected components = parity classes.**  Two contexts are isomorphic iff
they share the parity invariant; equivalently, the classifier collapses `Context`
onto exactly two components. -/
theorem iso_iff_par (c d : Context) :
    Nonempty (c ≅ d) ↔ c.par = d.par := by
  constructor
  · rintro ⟨e⟩; exact e.hom.down
  · intro h; exact ⟨⟨⟨h⟩, ⟨h.symm⟩, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
end Classifier
/-! ═══════════════════════════════════════════════════════════════════
    §4. THE CRITERION, TRANSPORTED THROUGH THE CLASSIFIER
    ═══════════════════════════════════════════════════════════════════ -/
section Transport
variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
omit [Fintype L] in
/-- The value-at-`1` vanishing criterion is *precisely* the classifier's object
map: `q` vanishes at `1` in context `c` iff `parFunctor.obj c = ⟨0⟩`. -/
theorem qKasami_one_eq_zero_iff_classifier (c : Context) :
    qKasami (L := L) c.n c.k c.kk c.α 1 = 0 ↔ parFunctor.obj c = Discrete.mk 0 := by
  rw [qKasami_one_eq_zero_iff_par]
  constructor
  · intro h; exact congrArg Discrete.mk h
  · intro h; exact congrArg Discrete.as h
omit [Fintype L] in
/-- **Necessary direction, transported.**  If the Kasami map of context `c` is
bijective, then the classifier value of `c` is the nonzero object `⟨1⟩` of
`ZMod 2` — so `c` lies in the "odd" component, the only one that *can* host a
permutation.  This is the §2 shortcut read off from the classifier of §3. -/
theorem bijective_imp_classifier_one {c : Context}
    (h : Function.Bijective (qKasami (L := L) c.n c.k c.kk c.α)) :
    parFunctor.obj c = Discrete.mk 1 := by
  have hpar : (c.kk + c.α * c.n) % 2 = 1 := qKasami_bijective_imp_parity_v2 c.α h
  apply congrArg Discrete.mk
  show Context.par c = 1
  unfold Context.par
  have : ((c.kk + c.α * c.n : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq; omega
  simpa using this
end Transport
/-! ═══════════════════════════════════════════════════════════════════
    §5. THE PARITY GRAPH — COMPOSED PROOF ARROWS AS REACHABILITY
    ═══════════════════════════════════════════════════════════════════ -/
section Graph
/-- **The parity graph.**  Two contexts are joined by an edge exactly when they
are *distinct* and share the parity invariant.  This is the underlying simple
graph of the thin groupoid `Context`: an edge is a single arrow, and a *walk* is
a composite of arrows. -/
def parGraph : SimpleGraph Context where
  Adj c d := c ≠ d ∧ c.par = d.par
  symm := by rintro c d ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- **Reachability = the invariant.**  A walk (a *composite of proof arrows*) from
`c` to `d` exists iff `c` and `d` have equal parity.  Thus the parity graph has
exactly two connected components — the two parity classes — recovering the
classifier's picture (`iso_iff_par`) at the level of `SimpleGraph`. -/
theorem parGraph_reachable_iff (c d : Context) :
    parGraph.Reachable c d ↔ c.par = d.par := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans hstep.2
  · intro h
    by_cases hcd : c = d
    · subst hcd; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hcd, h⟩
/-- **Graph reachability = categorical isomorphism.**  The two "composed-arrow"
notions agree: a walk in `parGraph` and an isomorphism in `Context` both witness
equal parity.  The proof space, the groupoid and the classifier are three views
of the *same* two-class partition. -/
theorem parGraph_reachable_iff_iso (c d : Context) :
    parGraph.Reachable c d ↔ Nonempty (c ≅ d) := by
  rw [parGraph_reachable_iff, iso_iff_par]
end Graph
end Dobbertin1999.Equation1ProofSpace
