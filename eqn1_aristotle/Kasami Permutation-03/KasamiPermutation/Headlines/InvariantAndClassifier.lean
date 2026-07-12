import RequestProject.KasamiPermutation.Headlines.PermutationCriterionAndAPN

/-!
# A Caramello-style bridge for the Dobbertin (1999) paper skeleton

This file sits directly on top of the paper skeleton
`RequestProject.KasamiPermutation.Headlines.PermutationCriterionAndAPN` and explores, in a
machine-checked way, the "equivalent contexts / bridge" shortcuts requested for
the headline results.  Everything here refers to the **true** paper objects
(`KasamiPerm.Headlines.qKasami`, `qKasami_bijective_iff`, `kasami_isAPN`, ...) so that the
categorical picture always maps back to the actual Dobbertin headlines.

The three ingredients:

* **§1 — the structural invariant.**  The value of `q_α` at `1` is the single
  number `k' + α·n (mod 2)`.  Reformulated as `qKasami_one_eq_zero_iff`, this is
  the elementary shortcut that already decides the *necessary* half of Theorem 1
  (proved engine-free in `PermutationCriterionAndAPN` as `qKasami_bijective_imp_parity`).

* **§2 — the proof space as a `SimpleGraph`.**  The dependency structure of the
  headline results (`qKasami_bijective_iff`, `routine_computation`, `frob_shift_two_to_one`,
  `kasamiDeriv_two_to_one`, `kasami_isAPN`) is transcribed as an honest
  `SimpleGraph` and proved **connected** — every headline is linked, through its
  dependencies, down to the common Mathlib/engine base.

* **§3 — the equivalent contexts as a groupoid (Morita/Caramello bridge).**  The
  parameter tuples `(n,k,k',α)` become the objects of a `CategoryTheory`
  groupoid whose morphisms are proofs of equal parity invariant; the invariant is
  realised as a `Functor` to the (self-dual) discrete category on `ZMod 2`; two
  contexts are **isomorphic** iff they share the invariant (the categorical form
  of "Morita-equivalent contexts"); and the headline criterion **transports**
  along the bridge.  `headline_in_context` restates Theorem 1 itself in this
  language, closing the loop back to the paper.

Everything is `sorry`-free and rests only on the standard axioms.
-/

open scoped BigOperators
open Finset CategoryTheory

namespace KasamiPerm.Headlines.Bridge

open KasamiPerm.Headlines

/-! ═══════════════════════════════════════════════════════════════════
    §1. THE STRUCTURAL INVARIANT (value of `q_α` at `1`)
    ═══════════════════════════════════════════════════════════════════ -/

section Invariant

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

omit [Fintype L] in
/-- The value-at-`1` criterion: `q_α(1) = 0 ↔ k' + α·n ≡ 0 (mod 2)`.  This is the
small invariant that, via `qKasami_bijective_imp_parity`, powers the engine-free
necessary direction of Theorem 1. -/
theorem qKasami_one_eq_zero_iff (α : ℕ) :
    qKasami (L := L) n k k' α 1 = 0 ↔ (k' + α * n) % 2 = 0 := by
  rw [qKasami_one, CharP.cast_eq_zero_iff L 2]; omega

end Invariant

/-! ═══════════════════════════════════════════════════════════════════
    §2. THE PROOF SPACE OF THE HEADLINES (`SimpleGraph`)
    ═══════════════════════════════════════════════════════════════════ -/

section ProofSpace

/-- Nodes of the headline dependency graph of `PermutationCriterionAndAPN`.  `base` collects
the Mathlib foundation together with the finite-field "engine"
(`TraceFreeCriterion`/`TraceVersionInfra`/`TraceVersionBase`); the remaining nodes are the paper's own
headline declarations. -/
inductive Node
  | nBase | nThm1 | nRoutine | nFrob | nDeriv | nCor
  deriving DecidableEq, Fintype

open Node

/-- The directed dependency relation `dep a b = "a depends on b"`, transcribed
from the actual proofs in `PermutationCriterionAndAPN`:

* `nThm1` (`qKasami_bijective_iff`)  ⟶ engine `nBase`;
* `nRoutine` (`routine_computation`), `nFrob` (`frob_shift_two_to_one`) ⟶ `nBase`;
* `nDeriv` (`kasamiDeriv_two_to_one`) ⟶ `nThm1`, `nRoutine`;
* `nCor` (`kasami_isAPN`) ⟶ `nDeriv`, `nFrob`. -/
def dep : Node → Node → Prop
  | nThm1, nBase => True
  | nRoutine, nBase => True
  | nFrob, nBase => True
  | nDeriv, nThm1 => True
  | nDeriv, nRoutine => True
  | nCor, nDeriv => True
  | nCor, nFrob => True
  | _, _ => False

instance : DecidableRel dep := by
  intro a b; cases a <;> cases b <;> unfold dep <;> infer_instance

/-- The undirected **proof-space graph** underlying the dependency DAG. -/
def depGraph : SimpleGraph Node := SimpleGraph.fromRel dep

private lemma hadj {a b : Node} (h : dep a b) : depGraph.Adj a b := by
  refine ⟨?_, Or.inl h⟩
  rintro rfl; cases a <;> simp_all [dep]

/-- Every headline node is reachable from the common `nBase`. -/
theorem reach_base (v : Node) : depGraph.Reachable nBase v := by
  cases v
  · exact SimpleGraph.Reachable.refl _
  · exact (hadj (a := nThm1) (b := nBase) trivial).symm.reachable
  · exact (hadj (a := nRoutine) (b := nBase) trivial).symm.reachable
  · exact (hadj (a := nFrob) (b := nBase) trivial).symm.reachable
  · exact ((hadj (a := nThm1) (b := nBase) trivial).symm.reachable).trans
      (hadj (a := nDeriv) (b := nThm1) trivial).symm.reachable
  · refine (((hadj (a := nThm1) (b := nBase) trivial).symm.reachable).trans
      (hadj (a := nDeriv) (b := nThm1) trivial).symm.reachable).trans ?_
    exact (hadj (a := nCor) (b := nDeriv) trivial).symm.reachable

/-- **The headline proof space is connected**: every headline result is linked,
through its dependency chain, to the common base. -/
theorem depGraph_connected : depGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨nBase, reach_base⟩

end ProofSpace

/-! ═══════════════════════════════════════════════════════════════════
    §3. THE EQUIVALENT CONTEXTS AS A GROUPOID (Morita/Caramello bridge)
    ═══════════════════════════════════════════════════════════════════ -/

section Bridge

/-- A **Kasami context**: the parameters `(n, k, k', α)` of a generalized Kasami
map.  The two headline contexts are the trace-free one (`α = 0`) and the trace
one (`α = 1`). -/
structure Context where
  n : ℕ
  k : ℕ
  kk : ℕ
  α : ℕ

/-- The **bridge invariant**: the parity `k' + α·n (mod 2)`, the single number
that decides both the vanishing of `q_α` at `1` and (by Theorem 1) bijectivity. -/
def Context.par (c : Context) : ZMod 2 := ((c.kk + c.α * c.n : ℕ) : ZMod 2)

/-- Morphisms of contexts are proofs of equal parity invariant, turning `Context`
into the groupoid whose connected components are exactly the parity classes — the
categorical shape of "Morita-equivalent contexts": one may travel freely between
any two contexts sharing the invariant. -/
instance : Category Context where
  Hom c d := PLift (c.par = d.par)
  id c := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

instance : Groupoid Context where
  inv f := ⟨f.down.symm⟩

/-- **The bridge correspondence.** Two contexts are linked by a morphism iff they
share the parity invariant. -/
theorem hom_nonempty_iff (c d : Context) :
    Nonempty (c ⟶ d) ↔ c.par = d.par :=
  ⟨fun ⟨f⟩ => f.down, fun h => ⟨⟨h⟩⟩⟩

/-- **Contexts sharing the invariant are isomorphic objects** — the Morita
equivalence of the two contexts as an honest `Iso` in the groupoid. -/
def contextIso {c d : Context} (h : c.par = d.par) : c ≅ d where
  hom := ⟨h⟩
  inv := ⟨h.symm⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The parity invariant as a genuine **functor** to the discrete (hence
self-dual, "MacLane dual") category on `ZMod 2`: one invariant, many contexts. -/
def parFunctor : Context ⥤ Discrete (ZMod 2) where
  obj c := Discrete.mk c.par
  map f := Discrete.eqToHom f.down
  map_id _ := rfl
  map_comp _ _ := by apply Subsingleton.elim

/-- The categorical invariant `Context.par` is literally the value-at-`1`
criterion of §1. -/
theorem par_eq_zero_iff (c : Context) :
    c.par = 0 ↔ (c.kk + c.α * c.n) % 2 = 0 := by
  unfold Context.par
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]

omit [Fintype L] in
/-- The bridge invariant computes the vanishing of the Kasami map at `1`. -/
theorem qKasami_one_eq_zero_iff_par (c : Context) :
    qKasami (L := L) c.n c.k c.kk c.α 1 = 0 ↔ c.par = 0 := by
  rw [qKasami_one_eq_zero_iff, par_eq_zero_iff]

omit [Fintype L] in
/-- **Transport along the bridge (I).** The value-at-`1` non-vanishing criterion
is constant on a connected component: a proof that `q` does not vanish at `1` in
context `c` transports to any context `d` linked to `c`. -/
theorem bridge_transports_nonvanishing {c d : Context} (f : c ⟶ d)
    (h : qKasami (L := L) c.n c.k c.kk c.α 1 ≠ 0) :
    qKasami (L := L) d.n d.k d.kk d.α 1 ≠ 0 := by
  rw [ne_eq, qKasami_one_eq_zero_iff_par] at h ⊢
  rw [← f.down]; exact h

omit [Fintype L] in
/-- **Transport along the bridge (II).** The headline necessary condition of
Theorem 1 transports across the bridge: if the Kasami map of context `c` is
bijective, then every context `d` linked to `c` has odd parity invariant.
Composed with the engine-free `qKasami_bijective_imp_parity`, this is a purely
elementary arrow between the `α = 0` and `α = 1` contexts. -/
theorem bridge_transports_bijective_necessary {c d : Context} (f : c ⟶ d)
    (h : Function.Bijective (qKasami (L := L) c.n c.k c.kk c.α)) :
    d.par ≠ 0 := by
  have hc : (c.kk + c.α * c.n) % 2 = 1 := qKasami_bijective_imp_parity c.α h
  rw [← f.down, ne_eq, par_eq_zero_iff]
  omega

/-! ### Closing the loop: the headline in bridge language -/

/-- **Theorem 1, restated in the bridge language.**  For admissible parameters the
generalized Kasami map of a context is a permutation *iff* the context's bridge
invariant is nonzero.  This maps the categorical invariant back onto the true
Dobbertin headline `qKasami_bijective_iff`. -/
theorem headline_in_context (c : Context)
    (hn : Fintype.card L = 2 ^ c.n) (hk : c.k < c.n) (hcop : Nat.Coprime c.k c.n)
    (hk' : c.k * c.kk % c.n = 1 % c.n) (hk0 : 0 < c.k)
    (hexp : 2 ^ c.k + 1 < 2 ^ c.n - 1) (hα : c.α = 0 ∨ c.α = 1) :
    Function.Bijective (qKasami (L := L) c.n c.k c.kk c.α) ↔ c.par ≠ 0 := by
  rw [qKasami_bijective_iff hn hk hcop hk' hk0 hexp c.α hα, ne_eq, par_eq_zero_iff]
  omega

end Bridge

end KasamiPerm.Headlines.Bridge
