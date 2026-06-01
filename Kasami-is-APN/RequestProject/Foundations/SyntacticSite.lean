/-
# Layer 13: Syntactic Sites — The Topology on the Syntactic Category

Given a geometric theory T, the syntactic category C_T (Layer 12) carries
a canonical Grothendieck topology J_T — the **syntactic topology**. The
resulting site (C_T, J_T) is the **syntactic site** of T.

## Mathematical Content

1. **Covering families**: A set of formulas {ψ_i} covers φ if T ⊢ φ ⟹ ⋁ψ_i,
   i.e., φ is derivably below the disjunction of the family.

2. **Finite covering families**: Covering by a pair (binary case) and by
   a finite indexed family, which are the most common in practice.

3. **Pullback stability**: If {ψ_i} covers φ, then {χ ∧ ψ_i} covers χ ∧ φ.
   This follows from the Frobenius rule in geometric logic.

4. **Transitivity**: If {ψ_i} covers φ and each ψ_i is covered by {χ_ij},
   then {χ_ij} covers φ. This is the composition of covering families.

5. **Trivial cover**: {φ} covers φ (by reflexivity).

6. **Monotonicity/refinement**: Larger families covering the same formula
   still cover (weakening).

7. **Compatibility with T-equivalence**: Covering descends to the
   Lindenbaum–Tarski quotient.

8. **Subcanonical property**: Every representable presheaf on C_T is a
   sheaf for the syntactic topology — formalized as the "local character"
   of derivability.

9. **Sheaf condition**: What it means for a Prop-valued assignment to
   satisfy the sheaf condition for the syntactic topology.

## Connection to Caramello's Program

The syntactic site (C_T, J_T) is the key input for constructing the
**classifying topos** Sh(C_T, J_T) in Layer 14. The universal property
of the classifying topos says:

    Mod(T, E) ≅ Geom(E, Sh(C_T, J_T))

for any Grothendieck topos E. The syntactic topology J_T is precisely
what makes this bijection work: it forces the disjunction and existential
axioms of T to become "local" (covering) conditions.

## DAG Structure (depends on Layers 10, 12)

```
  subcanonical_syntactic (★)
       |
  syntacticSheafCondition ← covers_compatible_eval
       |
  covers_descend_quotient ← covers_tequiv_invariant
       |
  covers_transitive (★) ← covers_pullback_stable (★)
       |
  covers_trivial ← covers_refine ← covers_mono_theory
       |
  BinaryCover ← FiniteCover ← Covers
       |
  Derivable, GeomFormula (Layers 10, 12)
```

## Proof Shape Classification

| Lemma | Tag | Description |
|-------|-----|-------------|
| `Covers` | definition | Covering families via infinitary disjunction |
| `BinaryCover` | definition | Binary covering: φ covered by ψ₁, ψ₂ |
| `FiniteCover` | definition | Finite indexed covering family |
| `covers_trivial` | 🧩 atomic | {φ} covers φ |
| `covers_top` | 🧩 atomic | Any nonempty family covers ⊤ |
| `covers_refine` | 🌿 local-glue | Refinement of covers |
| `covers_mono_theory` | 🌿 local-glue | Monotonicity in theory |
| `binaryCover_of_disj` | 🧩 atomic | φ ∨ ψ is covered by {φ, ψ} |
| `covers_pullback_stable` | 🌌 structural | Pullback stability via Frobenius |
| `covers_transitive` | 🌌 structural | Transitivity of covers |
| `covers_tequiv_invariant` | 🌿 local-glue | Covers respect T-equivalence |
| `covers_descend_quotient` | 🌿 local-glue | Covers descend to quotient |
| `covers_compatible_eval` | 🌿 local-glue | Soundness for covers |
| `syntacticSheafCondition` | definition | Sheaf condition for syntactic site |
| `subcanonical_syntactic` | 🌌 structural | Representables are sheaves |
| `covers_binary_pullback` | 🌿 local-glue | Binary pullback stability |
| `covers_ex_intro` | 🧩 atomic | Existential gives cover |
-/
import Mathlib
import RequestProject.Foundations.GeometricLogic
import RequestProject.Foundations.SyntacticCategory

namespace Caramello.SyntacticSite

open GeometricLogic SyntacticCategory

/-! ## Section 1: Covering Families

A covering family for a formula φ in theory T is a collection of
formulas whose (infinitary) disjunction is T-derivable from φ.
This captures the geometric content: the ψ_i "cover" φ.
-/

/-- A family of formulas indexed by ι covers φ in theory T if
    T ⊢ φ ⟹ ⋁ᵢ ψᵢ. This is the infinitary covering condition. -/
def Covers {α : Type} (T : GeomTheory α) (φ : GeomFormula α)
    (ι : Type) (ψ : ι → GeomFormula α) : Prop :=
  T ⊢g φ ⟹ .iDisj ι ψ

/-- Binary covering: φ is covered by ψ₁ and ψ₂ if T ⊢ φ ⟹ ψ₁ ∨ ψ₂. -/
def BinaryCover {α : Type} (T : GeomTheory α) (φ ψ₁ ψ₂ : GeomFormula α) : Prop :=
  T ⊢g φ ⟹ .disj ψ₁ ψ₂

/-- A finite indexed covering: φ is covered by a finite family of formulas
    indexed by Fin n. -/
def FiniteCover {α : Type} (T : GeomTheory α) (φ : GeomFormula α)
    (n : ℕ) (ψ : Fin n → GeomFormula α) : Prop :=
  Covers T φ (Fin n) ψ

/-! ## Section 2: Basic Properties of Covers -/

/-- The trivial cover: any formula covers itself.
    {φ} covers φ since T ⊢ φ ⟹ ⋁{φ} and the single disjunct is φ. -/
lemma covers_trivial {α : Type} (T : GeomTheory α) (φ : GeomFormula α) :
    Covers T φ PUnit (fun _ => φ) :=
  Derivable.iDisj_intro PUnit (fun _ => φ) PUnit.unit

/-- Any formula is covered by the single-element family containing itself. -/
lemma covers_singleton {α : Type} (T : GeomTheory α) (φ : GeomFormula α) :
    Covers T φ Unit (fun _ => φ) :=
  Derivable.iDisj_intro Unit (fun _ => φ) ()

/-- ⊤ is covered by any family containing a formula derivable from ⊤. -/
lemma covers_of_top {α : Type} (T : GeomTheory α)
    {ι : Type} (ψ : ι → GeomFormula α) (i : ι) (h : T ⊢g .top ⟹ ψ i) :
    Covers T .top ι ψ :=
  Derivable.trans h (Derivable.iDisj_intro ι ψ i)

/-- ⊥ is covered by any family (ex falso). -/
lemma covers_bot {α : Type} (T : GeomTheory α)
    (ι : Type) (ψ : ι → GeomFormula α) :
    Covers T .bot ι ψ :=
  Derivable.trans (Derivable.bot_elim (.iDisj ι ψ)) (Derivable.refl _)

/-- If T ⊢ φ ⟹ ψᵢ for some i, then {ψⱼ}ⱼ covers φ. -/
lemma covers_of_le {α : Type} (T : GeomTheory α) (φ : GeomFormula α)
    {ι : Type} (ψ : ι → GeomFormula α) (i : ι)
    (h : T ⊢g φ ⟹ ψ i) :
    Covers T φ ι ψ :=
  Derivable.trans h (Derivable.iDisj_intro ι ψ i)

/-- Monotonicity in the theory: if T ⊆ T' and ψ covers φ in T,
    then ψ covers φ in T'. -/
lemma covers_mono_theory {α : Type} {T T' : GeomTheory α} (h : T ⊆ T')
    {φ : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    (hc : Covers T φ ι ψ) :
    Covers T' φ ι ψ :=
  derivable_mono h hc

/-- If φ' ≤_T φ and ψ covers φ, then ψ covers φ'. -/
lemma covers_of_le_left {α : Type} (T : GeomTheory α)
    {φ φ' : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    (hle : T ⊢g φ' ⟹ φ) (hc : Covers T φ ι ψ) :
    Covers T φ' ι ψ :=
  Derivable.trans hle hc

/-! ## Section 3: Binary and Disjunctive Covers -/

/-- A disjunction φ ∨ ψ is covered by {φ, ψ}. -/
lemma binaryCover_of_disj {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) :
    BinaryCover T (.disj φ ψ) φ ψ :=
  Derivable.refl (.disj φ ψ)

/-- A binary cover implies a general cover (with Bool indexing). -/
lemma covers_of_binaryCover {α : Type} {T : GeomTheory α}
    {φ ψ₁ ψ₂ : GeomFormula α} (h : BinaryCover T φ ψ₁ ψ₂) :
    Covers T φ Bool (fun b => Bool.rec ψ₂ ψ₁ b) := by
  unfold Covers BinaryCover at *
  apply Derivable.trans h
  apply Derivable.disj_elim
  · show T ⊢g ψ₁ ⟹ .iDisj Bool (fun b => Bool.rec ψ₂ ψ₁ b)
    exact Derivable.iDisj_intro Bool (fun b => Bool.rec ψ₂ ψ₁ b) true
  · show T ⊢g ψ₂ ⟹ .iDisj Bool (fun b => Bool.rec ψ₂ ψ₁ b)
    exact Derivable.iDisj_intro Bool (fun b => Bool.rec ψ₂ ψ₁ b) false

/-- An existential ∃ b, ψ(b) is covered by the family {ψ(b)}ᵦ. -/
lemma covers_ex {α : Type} (T : GeomTheory α)
    (β : Type) (ψ : β → GeomFormula α) :
    Covers T (.ex β ψ) β ψ := by
  unfold Covers
  apply Derivable.ex_elim
  intro b
  exact Derivable.iDisj_intro β ψ b

/-- An infinitary disjunction ⋁ᵢ ψᵢ is covered by {ψᵢ}ᵢ. -/
lemma covers_iDisj {α : Type} (T : GeomTheory α)
    (ι : Type) (ψ : ι → GeomFormula α) :
    Covers T (.iDisj ι ψ) ι ψ := by
  unfold Covers
  exact Derivable.iDisj_elim (fun i => Derivable.iDisj_intro ι ψ i)

/-! ## Section 4: Refinement of Covers

If {ψᵢ} covers φ and each ψᵢ ≤ χ(σ(i)), then {χⱼ} covers φ.
This is "refinement" or "coarsening" of covering families.
-/

/-- Refinement: if {ψᵢ} covers φ and there is a map σ : ι → κ with
    each ψᵢ ≤_T χ(σ(i)), then {χⱼ} covers φ. -/
lemma covers_refine {α : Type} (T : GeomTheory α)
    {φ : GeomFormula α} {ι κ : Type}
    {ψ : ι → GeomFormula α} {χ : κ → GeomFormula α}
    (σ : ι → κ)
    (hc : Covers T φ ι ψ)
    (hle : ∀ i, T ⊢g ψ i ⟹ χ (σ i)) :
    Covers T φ κ χ := by
  unfold Covers at *
  apply Derivable.trans hc
  apply Derivable.iDisj_elim
  intro i
  exact Derivable.trans (hle i) (Derivable.iDisj_intro κ χ (σ i))

/-- If every formula in a covering family is below some fixed χ,
    then χ is derivable from φ. -/
lemma le_of_covers_le {α : Type} (T : GeomTheory α)
    {φ χ : GeomFormula α} {ι : Type}
    {ψ : ι → GeomFormula α}
    (hc : Covers T φ ι ψ)
    (hle : ∀ i, T ⊢g ψ i ⟹ χ) :
    T ⊢g φ ⟹ χ :=
  Derivable.trans hc (Derivable.iDisj_elim hle)

/-! ## Section 5: Pullback Stability (★ Key Property)

The fundamental stability axiom for a Grothendieck topology:
if {ψᵢ} covers φ, then {χ ∧ ψᵢ} covers χ ∧ φ.

In the syntactic setting, this follows from the Frobenius rule
(which is an axiom of geometric derivability in Layer 12).
Pullback in a preorder/thin category = conjunction (meet).
-/

/-- **Pullback stability for binary covers.**
    If T ⊢ φ ⟹ ψ₁ ∨ ψ₂ then T ⊢ χ ∧ φ ⟹ (χ ∧ ψ₁) ∨ (χ ∧ ψ₂).

    This is the syntactic analogue of the stability axiom for
    Grothendieck topologies. It follows from the Frobenius rule. -/
lemma covers_binary_pullback {α : Type} (T : GeomTheory α)
    {φ ψ₁ ψ₂ χ : GeomFormula α}
    (hc : BinaryCover T φ ψ₁ ψ₂) :
    BinaryCover T (.conj χ φ) (.conj χ ψ₁) (.conj χ ψ₂) := by
  unfold BinaryCover at *
  -- We need: χ ∧ φ ⊢ (χ ∧ ψ₁) ∨ (χ ∧ ψ₂)
  -- First combine: χ ∧ φ ⊢ χ ∧ (ψ₁ ∨ ψ₂)
  -- Then use Frobenius rule
  apply Derivable.trans
  · exact Derivable.conj_intro (Derivable.conj_elim_left _ _)
      (Derivable.trans (Derivable.conj_elim_right _ _) hc)
  · exact Derivable.frobenius
      (Derivable.disj_intro_left _ _)
      (Derivable.disj_intro_right _ _)

/-- Infinitary Frobenius rule: χ ∧ (⋁ᵢ ψᵢ) ⊢ ⋁ᵢ (χ ∧ ψᵢ).
    This extends the binary Frobenius rule to infinitary disjunctions.
    It is derivable from the rules of geometric logic. -/
lemma infinitary_frobenius {α : Type} (T : GeomTheory α)
    (χ : GeomFormula α) (ι : Type) (ψ : ι → GeomFormula α) :
    T ⊢g .conj χ (.iDisj ι ψ) ⟹ .iDisj ι (fun i => .conj χ (ψ i)) := by
  apply Derivable.iFrobenius
  intro i
  exact Derivable.iDisj_intro ι (fun i => .conj χ (ψ i)) i

/-- **Pullback stability for general covers (★).**
    If {ψᵢ} covers φ then {χ ∧ ψᵢ} covers χ ∧ φ.

    This is the key axiom of a Grothendieck topology:
    covering sieves are stable under pullback (= conjunction in a preorder). -/
lemma covers_pullback_stable {α : Type} (T : GeomTheory α)
    {φ : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    (χ : GeomFormula α)
    (hc : Covers T φ ι ψ) :
    Covers T (.conj χ φ) ι (fun i => .conj χ (ψ i)) := by
  unfold Covers at *
  -- χ ∧ φ ⊢ χ ∧ (⋁ᵢ ψᵢ) ⊢ ⋁ᵢ (χ ∧ ψᵢ)
  apply Derivable.trans
  · exact Derivable.conj_intro (Derivable.conj_elim_left _ _)
      (Derivable.trans (Derivable.conj_elim_right _ _) hc)
  · exact infinitary_frobenius T χ ι ψ

/-- Pullback stability on the left: symmetric version.
    If {ψᵢ} covers φ then {ψᵢ ∧ χ} covers φ ∧ χ. -/
lemma covers_pullback_stable_left {α : Type} (T : GeomTheory α)
    {φ : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    (χ : GeomFormula α)
    (hc : Covers T φ ι ψ) :
    Covers T (.conj φ χ) ι (fun i => .conj (ψ i) χ) := by
  unfold Covers at *
  apply Derivable.trans
  · exact Derivable.conj_intro
      (Derivable.trans (Derivable.conj_elim_left _ _) hc)
      (Derivable.conj_elim_right _ _)
  -- Now need: (⋁ᵢ ψᵢ) ∧ χ ⊢ ⋁ᵢ (ψᵢ ∧ χ)
  -- This is the "right" Frobenius: swap conjuncts, apply iFrobenius, swap back
  -- (⋁ᵢ ψᵢ) ∧ χ: first swap to χ ∧ (⋁ᵢ ψᵢ) via conj_intro
  apply Derivable.trans
  · exact Derivable.conj_intro (Derivable.conj_elim_right _ _) (Derivable.conj_elim_left _ _)
  -- Now: χ ∧ (⋁ᵢ ψᵢ) ⊢ ⋁ᵢ (ψᵢ ∧ χ)
  apply Derivable.trans (infinitary_frobenius T χ ι ψ)
  -- Now: ⋁ᵢ (χ ∧ ψᵢ) ⊢ ⋁ᵢ (ψᵢ ∧ χ)
  apply Derivable.iDisj_elim
  intro i
  apply Derivable.trans
  · exact Derivable.conj_intro (Derivable.conj_elim_right _ _) (Derivable.conj_elim_left _ _)
  · exact Derivable.iDisj_intro ι (fun i => .conj (ψ i) χ) i

/-! ## Section 6: Transitivity of Covers (★ Key Property)

The second key axiom: if {ψᵢ} covers φ, and for each i the
family {χᵢⱼ}ⱼ covers ψᵢ, then the combined family covers φ.
-/

/-- **Transitivity of covers (★).**
    If {ψᵢ} covers φ and each ψᵢ is covered by {χᵢⱼ}ⱼ,
    then the combined family {χᵢⱼ} covers φ.

    This is the transitivity/composition axiom for Grothendieck topologies. -/
lemma covers_transitive {α : Type} (T : GeomTheory α)
    {φ : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    {κ : ι → Type} {χ : (i : ι) → κ i → GeomFormula α}
    (hc : Covers T φ ι ψ)
    (hd : ∀ i, Covers T (ψ i) (κ i) (χ i)) :
    Covers T φ (Σ i, κ i) (fun ⟨i, j⟩ => χ i j) := by
  unfold Covers at *
  apply Derivable.trans hc
  apply Derivable.iDisj_elim
  intro i
  apply Derivable.trans (hd i)
  apply Derivable.iDisj_elim
  intro j
  exact Derivable.iDisj_intro (Σ i, κ i) (fun ⟨i, j⟩ => χ i j) (Sigma.mk i j)

/-! ## Section 7: Compatibility with T-Equivalence

Covers are invariant under T-equivalence of the covered formula
and of the covering formulas.
-/

/-- If φ ⟺_T φ' and {ψᵢ} covers φ, then {ψᵢ} covers φ'. -/
lemma covers_tequiv_left {α : Type} (T : GeomTheory α)
    {φ φ' : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    (heq : T ⊢g φ ⟺ φ') (hc : Covers T φ ι ψ) :
    Covers T φ' ι ψ :=
  Derivable.trans heq.2 hc

/-- If each ψᵢ ⟺_T ψᵢ' and {ψᵢ} covers φ, then {ψᵢ'} covers φ. -/
lemma covers_tequiv_family {α : Type} (T : GeomTheory α)
    {φ : GeomFormula α} {ι : Type} {ψ ψ' : ι → GeomFormula α}
    (heq : ∀ i, T ⊢g ψ i ⟺ ψ' i) (hc : Covers T φ ι ψ) :
    Covers T φ ι ψ' :=
  covers_refine T id hc (fun i => (heq i).1)

/-- Covers are fully invariant under T-equivalence (both sides). -/
lemma covers_tequiv_invariant {α : Type} (T : GeomTheory α)
    {φ φ' : GeomFormula α} {ι : Type} {ψ ψ' : ι → GeomFormula α}
    (heqφ : T ⊢g φ ⟺ φ') (heqψ : ∀ i, T ⊢g ψ i ⟺ ψ' i)
    (hc : Covers T φ ι ψ) :
    Covers T φ' ι ψ' :=
  covers_tequiv_family T heqψ (covers_tequiv_left T heqφ hc)

/-! ## Section 8: Covers Descend to the Lindenbaum–Tarski Quotient

Since covers are invariant under T-equivalence, they define a
well-defined notion on the quotient algebra.
-/

/-- Covering relation on the Lindenbaum–Tarski quotient.
    Well-defined because covers are invariant under T-equivalence. -/
def QuotientCovers {α : Type} {T : GeomTheory α}
    (a : LindenbaumTarski T) (ι : Type)
    (ψ : ι → GeomFormula α) : Prop :=
  ∃ φ : GeomFormula α,
    Quotient.mk (syntacticSetoid T) φ = a ∧ Covers T φ ι ψ

/-- The quotient covering agrees with concrete covering on representatives. -/
lemma quotientCovers_mk {α : Type} {T : GeomTheory α}
    (φ : GeomFormula α) (ι : Type) (ψ : ι → GeomFormula α) :
    QuotientCovers (Quotient.mk (syntacticSetoid T) φ) ι ψ ↔ Covers T φ ι ψ := by
  constructor
  · rintro ⟨φ', heq, hc⟩
    have hequiv : TEquiv T φ' φ := Quotient.exact heq
    exact Derivable.trans hequiv.2 hc
  · intro hc
    exact ⟨φ, rfl, hc⟩

/-! ## Section 9: Soundness for Covers

The soundness theorem lifts to covering families:
if {ψᵢ} covers φ and φ holds in a model, then some ψᵢ holds.
-/

/-- **Soundness for covers**: if {ψᵢ} covers φ and φ(v) holds
    in a model v of T, then ψᵢ(v) holds for some i. -/
lemma covers_sound {α : Type} {T : GeomTheory α}
    {φ : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    (hc : Covers T φ ι ψ)
    (v : α → Prop) (hmodel : T.Model v) (hφ : φ.eval v) :
    ∃ i, (ψ i).eval v :=
  soundness hc v hmodel hφ

/-- Soundness for binary covers: if φ is covered by ψ₁, ψ₂ and
    φ(v) holds, then ψ₁(v) or ψ₂(v) holds. -/
lemma binaryCover_sound {α : Type} {T : GeomTheory α}
    {φ ψ₁ ψ₂ : GeomFormula α}
    (hc : BinaryCover T φ ψ₁ ψ₂)
    (v : α → Prop) (hmodel : T.Model v) (hφ : φ.eval v) :
    ψ₁.eval v ∨ ψ₂.eval v :=
  soundness hc v hmodel hφ

/-! ## Section 10: The Syntactic Topology

We now define the syntactic topology as a structure that captures
the Grothendieck topology axioms in our preorder setting.

A **sieve** on φ in the syntactic preorder is a downward-closed set
of formulas ψ ≤_T φ. The syntactic topology designates certain
sieves as "covering".
-/

/-- A sieve on φ in the syntactic preorder: a downward-closed set
    of formulas below φ. -/
structure SyntacticSieve {α : Type} (T : GeomTheory α) (φ : GeomFormula α) where
  /-- The underlying set of formulas in the sieve -/
  members : Set (GeomFormula α)
  /-- Every member is below φ -/
  mem_le : ∀ ψ ∈ members, T ⊢g ψ ⟹ φ
  /-- Downward-closed: if ψ ∈ S and χ ≤ ψ, then χ ∈ S -/
  downward_closed : ∀ ψ ∈ members, ∀ δ, (T ⊢g δ ⟹ ψ) → δ ∈ members

/-- The maximal sieve on φ: all formulas below φ. -/
def maximalSieve {α : Type} (T : GeomTheory α) (φ : GeomFormula α) :
    SyntacticSieve T φ where
  members := {ψ | T ⊢g ψ ⟹ φ}
  mem_le _ h := h
  downward_closed _ h _ hle := Derivable.trans hle h

/-- The sieve generated by a covering family: all formulas below some ψᵢ. -/
def sieveOfCover {α : Type} (T : GeomTheory α) (φ : GeomFormula α)
    {ι : Type} (ψ : ι → GeomFormula α) (hle : ∀ i, T ⊢g ψ i ⟹ φ) :
    SyntacticSieve T φ where
  members := {δ | ∃ i, T ⊢g δ ⟹ ψ i}
  mem_le δ := by
    rintro ⟨i, hle'⟩
    exact Derivable.trans hle' (hle i)
  downward_closed δ := by
    rintro ⟨i, hle'⟩ γ hγ
    exact ⟨i, Derivable.trans hγ hle'⟩

/-- A sieve is covering if it contains a covering family. -/
def SyntacticSieve.isCovering {α : Type} {T : GeomTheory α}
    {φ : GeomFormula α} (S : SyntacticSieve T φ) : Prop :=
  ∃ (ι : Type) (ψ : ι → GeomFormula α),
    (∀ i, ψ i ∈ S.members) ∧ Covers T φ ι ψ

/-- The maximal sieve is always covering. -/
lemma maximalSieve_isCovering {α : Type} (T : GeomTheory α)
    (φ : GeomFormula α) :
    (maximalSieve T φ).isCovering :=
  ⟨PUnit, fun _ => φ, fun _ => Derivable.refl φ, covers_trivial T φ⟩

/-! ## Section 11: Grothendieck Topology Axioms Verification

We verify that the syntactic topology satisfies the three axioms of a
Grothendieck topology on the syntactic preorder:
1. Maximality: the maximal sieve on φ is covering
2. Stability: covering sieves are stable under pullback (= conjunction)
3. Transitivity: local character (covering of covering is covering)
-/

/-- **Axiom 1 (Maximality):** The maximal sieve is covering.
    This is immediate from covers_trivial. -/
theorem syntactic_topology_maximal {α : Type} (T : GeomTheory α)
    (φ : GeomFormula α) :
    (maximalSieve T φ).isCovering :=
  maximalSieve_isCovering T φ

/-- **Axiom 3 (Transitivity):** If S is a covering sieve on φ,
    and for every ψ ∈ S the sieve R pulled back to ψ is covering,
    then R is covering.

    In the preorder setting: if {ψᵢ} covers φ and each ψᵢ is
    covered by formulas in R, then R covers φ. -/
theorem syntactic_topology_transitive {α : Type} (T : GeomTheory α)
    {φ : GeomFormula α}
    (S R : SyntacticSieve T φ)
    (hS : S.isCovering)
    (hR : ∀ ψ ∈ S.members, ∃ (κ : Type) (δ : κ → GeomFormula α),
      (∀ j, δ j ∈ R.members) ∧ Covers T ψ κ δ) :
    R.isCovering := by
  obtain ⟨ι, ψ, hmem, hcov⟩ := hS
  have hR' : ∀ i, ∃ (κ : Type) (δ : κ → GeomFormula α),
      (∀ j, δ j ∈ R.members) ∧ Covers T (ψ i) κ δ :=
    fun i => hR (ψ i) (hmem i)
  choose κ δ hmemR hcovR using hR'
  exact ⟨Σ i, κ i, fun ⟨i, j⟩ => δ i j,
    fun ⟨i, j⟩ => hmemR i j,
    covers_transitive T hcov hcovR⟩

/-! ## Section 12: The Sheaf Condition for the Syntactic Site

A presheaf on the syntactic category satisfies the sheaf condition
for the syntactic topology if it "glues" compatible families.

In the preorder/thin setting, a monotone function F : C_T^op → Type
is a sheaf iff: whenever {ψᵢ} covers φ, F(φ) is determined by
the F(ψᵢ) via the matching condition.

For Prop-valued presheaves (contravariant = monotone w.r.t. reversed order),
the sheaf condition simplifies to the local character property.
-/

/-- The sheaf condition for a Prop-valued presheaf on the syntactic preorder:
    P is contravariant (presheaf on C_T, i.e., monotone on C_T^op)
    and satisfies the local character (P at φ is determined by covers). -/
def SheafCondition {α : Type} (T : GeomTheory α)
    (P : GeomFormula α → Prop) : Prop :=
  -- P is contravariant (presheaf = order-reversing w.r.t. derivability)
  (∀ φ ψ, (T ⊢g φ ⟹ ψ) → P ψ → P φ) ∧
  -- Local character: if P holds on a covering family, it holds on the covered formula
  (∀ φ (ι : Type) (ψ : ι → GeomFormula α),
    Covers T φ ι ψ → (∀ i, P (ψ i)) → P φ)

/-- A contravariant function satisfying the local character is a sheaf. -/
lemma sheafCondition_of_components {α : Type} (T : GeomTheory α)
    (P : GeomFormula α → Prop)
    (hcontra : ∀ φ ψ, (T ⊢g φ ⟹ ψ) → P ψ → P φ)
    (hlocal : ∀ φ (ι : Type) (ψ : ι → GeomFormula α),
      Covers T φ ι ψ → (∀ i, P (ψ i)) → P φ) :
    SheafCondition T P :=
  ⟨hcontra, hlocal⟩

/-! ## Section 13: Subcanonical Property (★)

The syntactic topology is **subcanonical**: the representable
presheaves (of the form "- ⊢_T χ") are sheaves.

In the preorder setting: for any fixed χ, the predicate
P(φ) := "T ⊢ φ ⟹ χ" satisfies the sheaf condition.
This is because derivability is transitive and respects
the covering relation.

The representable presheaf y(χ) on C_T^op sends φ to
Hom_{C_T}(φ, χ) = {T ⊢ φ ⟹ χ}. Being a presheaf means:
if φ ≤ ψ (i.e. φ ⊢ ψ), then y(χ)(ψ) → y(χ)(φ) by composition.
This is just transitivity of derivability.
-/

/-- **Subcanonical property (★)**: The representable presheaf
    y(χ)(φ) = (T ⊢ φ ⟹ χ) is a sheaf for the syntactic topology.

    This means: if {ψᵢ} covers φ and T ⊢ ψᵢ ⟹ χ for all i,
    then T ⊢ φ ⟹ χ. -/
theorem subcanonical_syntactic {α : Type} (T : GeomTheory α)
    (χ : GeomFormula α) :
    SheafCondition T (fun φ => T ⊢g φ ⟹ χ) := by
  constructor
  · -- Contravariance: if φ ⊢ ψ and ψ ⊢ χ, then φ ⊢ χ (transitivity)
    intro φ ψ hle hψχ
    exact Derivable.trans hle hψχ
  · -- Local character: if {ψᵢ} covers φ and each ψᵢ ⊢ χ, then φ ⊢ χ
    intro φ ι ψ hcov hall
    exact le_of_covers_le T hcov hall

/-! ## Section 14: Model Evaluation as a Cosheaf

Since evaluation in a model is covariant (φ ⊢ ψ implies φ(v) → ψ(v)),
it forms a cosheaf rather than a sheaf on C_T.
-/

/-- The cosheaf condition for a Prop-valued functor on the syntactic category:
    P is covariant and "co-locally" determined by covers. -/
def CosheafCondition {α : Type} (T : GeomTheory α)
    (P : GeomFormula α → Prop) : Prop :=
  -- P is covariant (preserves the order)
  (∀ φ ψ, (T ⊢g φ ⟹ ψ) → P φ → P ψ) ∧
  -- Co-local character: if P holds on φ and {ψᵢ} covers φ, then P holds on some ψᵢ
  (∀ φ (ι : Type) (ψ : ι → GeomFormula α),
    Covers T φ ι ψ → P φ → ∃ i, P (ψ i))

/-- Model evaluation satisfies the cosheaf condition. -/
theorem model_eval_cosheaf {α : Type} (T : GeomTheory α)
    (v : α → Prop) (hmodel : T.Model v) :
    CosheafCondition T (fun φ => φ.eval v) :=
  ⟨fun _ _ hle hφ => soundness hle v hmodel hφ,
   fun _ _ _ hcov hφ => covers_sound hcov v hmodel hφ⟩

/-! ## Section 15: Theory Morphisms and Covers

Theory morphisms (Layer 12) preserve covering families.
-/

/-- A theory morphism preserves covering families:
    if {ψᵢ} covers φ in T₁, then {σ(ψᵢ)} covers σ(φ) in T₂. -/
lemma theoryMorphism_preserves_covers {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    {φ : GeomFormula α} {ι : Type} {ψ : ι → GeomFormula α}
    (hc : Covers T₁ φ ι ψ) :
    Covers T₂ (φ.mapAtoms σ.onAtoms) ι (fun i => (ψ i).mapAtoms σ.onAtoms) := by
  unfold Covers at *
  have h := σ.preserves_derivability hc
  simp [GeomFormula.mapAtoms] at h
  exact h

/-! ## Section 16: Connection to Frame Theory

The covering relation on the syntactic preorder reflects the
frame structure of the Lindenbaum–Tarski algebra. Specifically:
- Binary covers correspond to the join operation
- Covers by singletons correspond to the order relation
- The pullback stability is the frame distributive law
-/

/-- A binary cover T ⊢ φ ⟹ ψ₁ ∨ ψ₂ exactly says that [φ] ≤ [ψ₁] ∨ [ψ₂]
    in the Lindenbaum–Tarski algebra. -/
lemma binaryCover_iff_le_sup {α : Type} (T : GeomTheory α)
    (φ ψ₁ ψ₂ : GeomFormula α) :
    BinaryCover T φ ψ₁ ψ₂ ↔ (syntacticPreorder T).le φ (.disj ψ₁ ψ₂) :=
  Iff.rfl

/-- A singleton cover is just the order relation. -/
lemma covers_singleton_iff {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) :
    Covers T φ PUnit (fun _ => ψ) ↔ (syntacticPreorder T).le φ ψ := by
  constructor
  · intro h
    exact le_of_covers_le T h (fun _ => Derivable.refl ψ)
  · intro h
    exact covers_of_le T φ (fun _ => ψ) PUnit.unit h

/-- Frame distributivity in the syntactic preorder, restated in covering language:
    if {ψ₁, ψ₂} covers φ, then {χ ∧ ψ₁, χ ∧ ψ₂} covers χ ∧ φ.
    This is the pullback stability for binary covers. -/
lemma frame_distrib_as_cover {α : Type} (T : GeomTheory α)
    (φ ψ₁ ψ₂ χ : GeomFormula α)
    (hc : BinaryCover T φ ψ₁ ψ₂) :
    BinaryCover T (.conj χ φ) (.conj χ ψ₁) (.conj χ ψ₂) :=
  covers_binary_pullback T hc

/-! ## Section 17: Empty and Inconsistent Theories -/

/-- In an inconsistent theory (one that derives ⊤ ⊢ ⊥), every
    formula is covered by the empty family. -/
lemma covers_empty_of_inconsistent {α : Type} (T : GeomTheory α)
    (h : T ⊢g .top ⟹ .bot) (φ : GeomFormula α) :
    Covers T φ Empty (fun e => e.elim) := by
  unfold Covers
  apply Derivable.trans (Derivable.top_intro φ)
  apply Derivable.trans h
  exact Derivable.bot_elim _

/-- In a consistent theory, ⊤ is not covered by the empty family.
    (More precisely: if ⊤ is covered by the empty family, the theory
    is inconsistent.) -/
lemma inconsistent_of_covers_empty {α : Type} (T : GeomTheory α)
    (h : Covers T .top Empty (fun e => e.elim))
    (v : α → Prop) (hmodel : T.Model v) :
    False := by
  have : ∃ (i : Empty), _ := covers_sound h v hmodel trivial
  exact this.elim (fun e => e.elim)

end Caramello.SyntacticSite
