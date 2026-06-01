/-
# Layer 2: Sieve Lattice and Pullback Properties

Sieves are the building blocks of Grothendieck topologies.
This file establishes atomic properties of sieves that ground
Caramello's Chapter 2 in Mathlib.

## DAG Structure (depends on Layer 0 = Mathlib)

```
     sieve_pullback_top     sieve_pullback_bot
             \                    /
         sieve_pullback_inf     sieve_pullback_mono_le
             |                       |
       sieve_pullback_comp    sieve_pullback_id
                    \            /
               covering_stable + covering_transitive
```
-/
import Mathlib

namespace Caramello.SieveBasics

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-! ## Atomic Sieve Facts -/

/-- Pulling back the maximal sieve gives the maximal sieve. -/
lemma sieve_pullback_top {X Y : C} (f : Y ⟶ X) :
    (⊤ : Sieve X).pullback f = ⊤ :=
  Sieve.pullback_top

/-- Pulling back the empty sieve gives the empty sieve. -/
lemma sieve_pullback_bot {X Y : C} (f : Y ⟶ X) :
    (⊥ : Sieve X).pullback f = ⊥ :=
  Sieve.arrows_ext rfl

/-- Pulling back preserves the infimum (intersection) of sieves. -/
lemma sieve_pullback_inf {X Y : C} (f : Y ⟶ X) (S T : Sieve X) :
    (S ⊓ T).pullback f = S.pullback f ⊓ T.pullback f := by
  ext Z g; simp [Sieve.pullback_apply, Sieve.inter_apply]

/-- Pulling back along the identity is the identity. -/
lemma sieve_pullback_id {X : C} (S : Sieve X) :
    S.pullback (𝟙 X) = S := by
  ext Y f; simp

/-- Pulling back along a composition is iterated pullback. -/
lemma sieve_pullback_comp {X Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X) (S : Sieve X) :
    S.pullback (f ≫ g) = (S.pullback g).pullback f := by
  ext W h; simp [Sieve.pullback_apply, Category.assoc]

/-- The pullback of a sieve is monotone w.r.t. the sieve lattice. -/
lemma sieve_pullback_mono_le {X Y : C} (f : Y ⟶ X) {S T : Sieve X}
    (h : S ≤ T) : S.pullback f ≤ T.pullback f :=
  Sieve.pullback_monotone f h

/-! ## Connection to GrothendieckTopology -/

/-- Every covering sieve pulled back is still covering.
    This is the stability axiom. -/
lemma covering_stable {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S : Sieve X) (hS : S ∈ J X) :
    S.pullback f ∈ J Y :=
  J.pullback_stable f hS

/-- The maximal sieve is always covering. -/
lemma top_mem_covering {X : C} (J : GrothendieckTopology C) :
    (⊤ : Sieve X) ∈ J X :=
  J.top_mem X

/-- Transitivity: if S covers X and for every arrow in S the pullback
    of R covers, then R covers X. -/
lemma covering_transitive {X : C} (J : GrothendieckTopology C)
    (S R : Sieve X) (hS : S ∈ J X)
    (hR : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S.arrows f → R.pullback f ∈ J Y) :
    R ∈ J X :=
  J.transitive hS R hR

/-- Superset of a covering sieve is covering. -/
lemma covering_superset {X : C} (J : GrothendieckTopology C)
    {S T : Sieve X} (hS : S ∈ J X) (h : S ≤ T) :
    T ∈ J X :=
  J.superset_covering h hS

end Caramello.SieveBasics
