import Mathlib
import KasamiPermutations.KasamiMap
import KasamiPermutations.SpecialValues

/-!
# Equation (1) — the "proof space" and the Caramello bridge

This module packages the *combinatorial skeleton* of Dobbertin's Theorem 1 so
that the rest of the development can reason about it structurally, independently
of the finite-field engine.

Two ideas are set up here and then exploited (and sharpened) in
`Equation1Classifier`:

* **The Kasami context.**  A `Context` bundles the four discrete parameters
  `(n, k, k', α)` that specify a generalized Kasami map `q_α` on some field.  The
  only invariant of a context that the *necessary* direction of Theorem 1 sees is
  its **parity** `Context.par = k' + α·n (mod 2)`.  Two contexts sharing the same
  parity are made isomorphic by declaring `Context` a *thin* category whose arrows
  are exactly the proofs `c.par = d.par`; this is the "groupoid of contexts".

* **The parity functor.**  `parFunctor : Context ⥤ Discrete (ZMod 2)` records the
  single invariant.  `Equation1Classifier` upgrades it to an *equivalence of
  categories* (the "classifier"): the whole groupoid of contexts is the same as
  the two-point discrete category `ZMod 2`.

The bridge lemma `qKasami_one_eq_zero_iff_par` connects the *analytic* fact
`q_α(1) = 0` to the *combinatorial* invariant `Context.par c = 0`.  It is the hinge
that lets the engine-free obstruction of `Equation1Classifier` read off the
necessary direction of the permutation criterion.
-/

open scoped BigOperators
open Finset CategoryTheory Kasami

namespace Dobbertin1999.Equation1ProofSpace

/-! ## The Kasami context and its parity invariant -/

/-- A **Kasami context**: the four discrete parameters `(n, k, k', α)` that pin
down a generalized Kasami map.  (`kk` is the paper's `k'`.) -/
structure Context where
  /-- the field exponent `n` (the field is `𝔽_{2ⁿ}`) -/
  n : ℕ
  /-- the Kasami exponent `k` -/
  k : ℕ
  /-- the paper's `k'` -/
  kk : ℕ
  /-- the trace coefficient `α` -/
  α : ℕ

/-- The **parity invariant** of a context, `k' + α·n (mod 2)`.  This single bit is
the only thing the necessary direction of Theorem 1 depends on. -/
def Context.par (c : Context) : ZMod 2 := ((c.kk + c.α * c.n : ℕ) : ZMod 2)

/-- `Context` as a **thin category**: there is at most one arrow `c ⟶ d`, namely a
proof that `c` and `d` share the parity invariant.  This turns the equivalence
relation "same parity" into a category (a groupoid). -/
instance : Category Context where
  Hom c d := PLift (c.par = d.par)
  id c := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- The **parity functor** `Context ⥤ Discrete (ZMod 2)`, recording the single
invariant `k' + α·n (mod 2)`.  `Equation1Classifier` shows it is an equivalence. -/
def parFunctor : Context ⥤ Discrete (ZMod 2) where
  obj c := Discrete.mk c.par
  map f := Discrete.eqToHom f.down

/-! ## The analytic ↔ combinatorial bridge -/

section Bridge
variable {L : Type*} [Field L] [Fintype L] [CharP L 2]

omit [Fintype L] in
/-- **The bridge.**  For any field `L` of characteristic `2`, the Kasami map of a
context vanishes at `1` iff the context has *even* parity.  This ports the
value-at-`1` criterion (`qKasami_one_eq_zero_iff`) onto the combinatorial
invariant `Context.par`. -/
theorem qKasami_one_eq_zero_iff_par (c : Context) :
    qKasami (L := L) c.n c.k c.kk c.α 1 = 0 ↔ Context.par c = 0 := by
  rw [qKasami_one_eq_zero_iff]
  unfold Context.par
  rw [CharP.cast_eq_zero_iff (ZMod 2) 2]
  omega

end Bridge

end Dobbertin1999.Equation1ProofSpace
