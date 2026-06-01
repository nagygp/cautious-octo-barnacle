/-
# Layer 27: Simplicial Foundations — Bridging Toposes and Higher Categories

This layer connects the existing topos-theoretic framework (Layers 1–26)
to simplicial methods, establishing the groundwork for higher categorical
patterns. The key insight: just as `Prop` is the subobject classifier Ω
of the 1-topos `Type`, simplicial sets (presheaves on Δ) provide the
combinatorial foundation for higher toposes.

## Mathematical Content

1. **Simplicial objects in Type**: Using Mathlib's `SimplicialObject` and `SSet`.
2. **Nerve of a category**: The nerve functor `Cat → SSet`.
3. **Constant simplicial objects**: Every type gives a "discrete" simplicial set.
4. **Coskeletal conditions**: Simplicial sets determined by low-dimensional data.
5. **Kan conditions**: Kan complexes and quasicategories from Mathlib.
6. **SSet topos structure**: SSet has all limits and colimits.
7. **Truncation levels**: Connecting Prop to the (-1)-truncation level.
8. **Simplicial identity helpers**: Face-degeneracy cancellation.

## DAG Structure (depends on Layers 1, 7, 26)

```
  SSet limits/colimits ←── presheaf topos
       |
  vertexConnected ←── face-degeneracy identities
       |
  constSSet_coskeletal ←── IsCoskeletal
       |
  constSSet ←── Functor.const
       |
  nSimplices, vertices, edges, triangles
       |
  SimplicialObject, SSet (Mathlib)
```
-/
import Mathlib
import RequestProject.Foundations.CoherentCompleteness

namespace Caramello.SimplicialFoundations

open CategoryTheory SimplexCategory

/-! ## Section 1: Simplicial Objects — Basic Observations -/

/-- The simplex category Δ has objects [n] and order-preserving maps. -/
example : Type := SimplexCategory

/-- The standard n-simplex is a cosimplicial object in SSet. -/
example : CosimplicialObject SSet := SSet.stdSimplex

/-- A simplicial set is a functor Δᵒᵖ → Type. -/
example : Type 1 := SSet

/-- The nerve functor sends a (small) category to a simplicial set. -/
example : Functor Cat SSet := nerveFunctor

/-! ## Section 2: Constant (Discrete) Simplicial Objects -/

/-- The constant simplicial set on a type X: every level is X,
    every face and degeneracy map is id. -/
noncomputable def constSSet (X : Type) : SSet :=
  (Functor.const _).obj X

/-- The constant simplicial set at level n is just X. -/
theorem constSSet_obj (X : Type) (n : SimplexCategoryᵒᵖ) :
    (constSSet X).obj n = X := rfl

/-- All structure maps of a constant simplicial set are the identity. -/
theorem constSSet_map_id (X : Type) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    (constSSet X).map f = id := rfl

/-! ## Section 3: n-Simplices -/

/-- The set of n-simplices of a simplicial set S. -/
def nSimplices (S : SSet) (n : ℕ) : Type :=
  S.obj (Opposite.op (SimplexCategory.mk n))

/-- The 0-simplices are the "points" or "objects". -/
abbrev vertices (S : SSet) : Type := nSimplices S 0

/-- The 1-simplices are the "edges" or "morphisms". -/
abbrev edges (S : SSet) : Type := nSimplices S 1

/-- The 2-simplices are the "triangles" or "compositions". -/
abbrev triangles (S : SSet) : Type := nSimplices S 2

/-- Vertices of the constant simplicial set are just X. -/
theorem constSSet_vertices (X : Type) : vertices (constSSet X) = X := rfl

/-- Edges of the constant simplicial set are just X. -/
theorem constSSet_edges (X : Type) : edges (constSSet X) = X := rfl

/-! ## Section 4: Coskeletal Conditions -/

/-- An order-preserving injection [n] ↪ [k] when n < k. -/
def injHom (n k : ℕ) (h : n < k) : SimplexCategory.mk n ⟶ SimplexCategory.mk k :=
  SimplexCategory.mkHom ⟨fun i => ⟨i.1, by omega⟩, fun _ _ hab => hab⟩

/-- A simplicial set S is n-coskeletal if it is determined by its
    simplices in dimensions ≤ n. -/
def IsCoskeletal (S : SSet) (n : ℕ) : Prop :=
  ∀ (k : ℕ), n < k →
    ∀ (x y : nSimplices S k),
      (∀ (f : SimplexCategory.mk n ⟶ SimplexCategory.mk k),
        S.map f.op x = S.map f.op y) →
      x = y

/-- A constant simplicial set is n-coskeletal for all n. -/
theorem constSSet_coskeletal (X : Type) (n : ℕ) :
    IsCoskeletal (constSSet X) n := by
  intro k hk x y h
  have := h (injHom n k hk)
  simp [constSSet, Functor.const] at this
  exact this

/-! ## Section 5: The Kan Condition and ∞-Groupoids -/

/-- Mathlib's Kan complex condition. -/
example (S : SSet) : Prop := SSet.KanComplex S

/-- Mathlib's quasicategory condition (inner Kan). -/
example (S : SSet) : Prop := SSet.Quasicategory S

/-! ## Section 6: SSet as a Topos

SSet = [Δᵒᵖ, Set] is a presheaf topos: it has all limits, colimits,
and a subobject classifier. The subobject classifier of SSet is NOT
Prop — it is the simplicial set of "sieves on Δ[n]" at level n.
This is where higher topos theory diverges from "Prop = Ω". -/

/-- SSet has all limits. -/
noncomputable instance : Limits.HasLimits SSet := inferInstance

/-- SSet has all colimits. -/
noncomputable instance : Limits.HasColimits SSet := inferInstance

/-- SSet has an initial object. -/
noncomputable instance : Limits.HasInitial SSet := inferInstance

/-- SSet has a terminal object. -/
noncomputable instance : Limits.HasTerminal SSet := inferInstance

/-- SSet has all finite products. -/
noncomputable instance : Limits.HasFiniteProducts SSet := inferInstance

/-- SSet has all pullbacks. -/
noncomputable instance : Limits.HasPullbacks SSet := inferInstance

/-! ## Section 7: Subobject Classification Analogy -/

/-- In Type, subobjects of X are classified by X → Prop. -/
theorem type_subobj_classify (X : Type) (P : X → Prop) :
    ∃ (S : Subtype P → X), Function.Injective S :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-! ## Section 8: Simplicial Identity Helpers

The simplicial identities δ_i ≫ σ_j relate face and degeneracy maps.
We package the key cancellation results for use in later proofs. -/

/-- Face-degeneracy cancellation: δ_i ∘ σ_0 = id when δ_i ≫ σ_0 = 𝟙.
    Works for both δ_0 (by δ_comp_σ_self) and δ_1 (by δ_comp_σ_succ). -/
theorem sset_face_degen_cancel (T : SSet) (x : T.obj (Opposite.op (mk 0)))
    (i : Fin 2) (h : δ i ≫ σ (0 : Fin 1) = 𝟙 (mk 0)) :
    T.map (δ i).op (T.map (σ (0 : Fin 1)).op x) = x := by
  change (T.map (σ 0).op ≫ T.map (δ i).op) x = x
  rw [← T.map_comp]
  have : (σ (0 : Fin 1)).op ≫ (δ i).op = 𝟙 _ := by
    show (δ i ≫ σ (0 : Fin 1)).op = _
    rw [h]; rfl
  rw [this]; simp

/-- δ₀ ∘ σ₀ = id on 0-simplices. -/
theorem sset_δ0_σ0_cancel (T : SSet) (x : T.obj (Opposite.op (mk 0))) :
    T.map (δ (0 : Fin 2)).op (T.map (σ (0 : Fin 1)).op x) = x :=
  sset_face_degen_cancel T x 0 SimplexCategory.δ_comp_σ_self

/-- δ₁ ∘ σ₀ = id on 0-simplices. -/
theorem sset_δ1_σ0_cancel (T : SSet) (x : T.obj (Opposite.op (mk 0))) :
    T.map (δ (1 : Fin 2)).op (T.map (σ (0 : Fin 1)).op x) = x :=
  sset_face_degen_cancel T x 1 SimplexCategory.δ_comp_σ_succ

/-! ## Section 9: Vertex Connectivity -/

/-- Two morphisms f g : S ⟶ T of simplicial sets are
    vertex-connected if their images at dimension 0 can be
    connected by edges in T. -/
structure VertexConnected {S T : SSet} (f g : S ⟶ T) : Prop where
  connected : ∀ (x : vertices S),
    ∃ (path : edges T),
      T.map (δ (1 : Fin 2)).op path =
        f.app (Opposite.op (mk 0)) x ∧
      T.map (δ (0 : Fin 2)).op path =
        g.app (Opposite.op (mk 0)) x

/-- Equal morphisms are vertex-connected via degenerate edges. -/
theorem vertexConnected_of_eq {S T : SSet} {f g : S ⟶ T}
    (h : f = g) : VertexConnected f g := by
  subst h
  constructor
  intro x
  use T.map (σ (0 : Fin 1)).op (f.app _ x)
  exact ⟨sset_δ1_σ0_cancel T _, sset_δ0_σ0_cancel T _⟩

/-! ## Section 10: Truncation Levels

The key concept bridging 1-toposes and ∞-toposes is truncation level.
- (-2)-truncated: contractible (= PUnit)
- (-1)-truncated: propositions (= Prop in Lean!)
- 0-truncated: sets (all types in Lean, by UIP)
- n-truncated: n-groupoids
-/

/-- Truncation level, following the HoTT convention. -/
inductive TruncLevel where
  | negTwo : TruncLevel
  | succ : TruncLevel → TruncLevel

namespace TruncLevel

def negOne : TruncLevel := succ negTwo
def zero : TruncLevel := succ negOne
def one : TruncLevel := succ zero

/-- Convert ℕ to a truncation level (0 ↦ zero, etc.). -/
def ofNat : ℕ → TruncLevel
  | 0 => zero
  | n + 1 => succ (ofNat n)

/-- Prop is (-1)-truncated: any two proofs are equal. -/
theorem prop_is_negOne_truncated :
    ∀ (P : Prop) (p q : P), p = q :=
  fun _ p q => Subsingleton.elim p q

/-- In Lean (with UIP), all types are 0-truncated:
    equality of elements is always a proposition. -/
theorem type_is_zero_truncated (X : Type) (x y : X) (p q : x = y) :
    p = q := by subst p; rfl

end TruncLevel

/-! ## Section 11: The 1-Topos ↔ ∞-Topos Analogy

| 1-Topos (Type)          | ∞-Topos (SSet model)            |
|--------------------------|----------------------------------|
| `Prop` = Ω              | Ω_SSet (sieve classifier)       |
| Subsets = X → Prop       | Simplicial subsets               |
| Geometric formulas       | Homotopy-coherent diagrams       |
| Geometric morphisms      | ∞-geometric morphisms            |
| Sheaves on a site        | ∞-sheaves (hypersheaves)         |
| Classifying topos        | Classifying ∞-topos              |
| Points = Set → E        | ∞-points = ∞Grpd → E            |
| Bridge technique         | ∞-bridge technique               |

Key insight: Lean's `Prop = Ω` is the (-1)-truncated case. Higher topos
theory explores what happens when we don't truncate to propositions.
-/

end Caramello.SimplicialFoundations
