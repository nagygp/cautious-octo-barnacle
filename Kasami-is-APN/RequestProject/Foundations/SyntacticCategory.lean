/-
# Layer 12: Syntactic Categories of Geometric Theories

Given a geometric theory T, the **syntactic category** C_T is the
category whose objects are geometric formulas and whose morphisms
are T-provable entailments. This is the first step toward
classifying toposes (Layer 14) and the bridge technique (Layer 16).

## Mathematical Content

1. **Geometric derivability**: An inductive relation `Derivable T φ ψ`
   capturing the rules of geometric logic (reflexivity, transitivity,
   conjunction intro/elim, disjunction intro, existential intro, etc.)

2. **Soundness theorem**: Every derivable sequent is valid in every model.
   This connects the syntactic (proof-theoretic) world to the semantic
   (model-theoretic) world.

3. **Syntactic preorder**: Formulas ordered by T-entailment form a preorder.
   This is the thin version of the syntactic category.

4. **Lattice-like structure**: The syntactic preorder has:
   - A greatest element (⊤)
   - Binary meets (∧)
   - Binary joins (∨)
   - A least element (⊥)

5. **Theory morphisms**: Maps between signatures that preserve derivability,
   giving monotone maps between syntactic preorders.

6. **Lindenbaum–Tarski algebra**: The quotient by T-equivalence, forming
   a bounded lattice with evaluation into models as a monotone map.

## DAG Structure (depends on Layer 10)

```
    theoryMorphismComp
           |
    theoryMorphismId ←── TheoryMorphism
           |
    evalQuotient_monotone
           |
    lindenbaumTarskiPartialOrder ←── LindenbaumTarski
           |
    soundness (★) ←── tequiv_sound
           |
    Derivable (inductive) ←── syntacticPreorder
           |
    GeomFormula, GeomTheory (Layer 10)
```

## Proof Shape Classification

| Lemma | Tag | Description |
|-------|-----|-------------|
| `Derivable` | definition | Geometric derivability rules |
| `derivable_refl` | 🧩 atomic | Reflexivity |
| `derivable_trans` | 🧩 atomic | Transitivity |
| `derivable_mono` | 🌿 local-glue | Monotonicity in theory |
| `soundness` | 🌌 structural | Derivable ⟹ valid in all models |
| `syntacticPreorder` | 🌿 local-glue | Preorder on formulas |
| `syntactic_top_terminal` | 🧩 atomic | ⊤ is greatest |
| `syntactic_bot_initial` | 🧩 atomic | ⊥ is least |
| `syntactic_conj_glb` | 🌿 local-glue | ∧ gives greatest lower bound |
| `syntactic_disj_lub` | 🌿 local-glue | ∨ gives least upper bound |
| `tequiv_equivalence` | 🧩 atomic | T-equivalence is an equivalence |
| `conj_congr` | 🌿 local-glue | ∧ respects T-equivalence |
| `disj_congr` | 🌿 local-glue | ∨ respects T-equivalence |
| `lindenbaumTarskiPartialOrder` | 🌿 local-glue | Partial order on quotient |
| `evalQuotient_monotone` | 🌿 local-glue | Evaluation respects order |
| `TheoryMorphism` | definition | Signature maps preserving derivability |
| `theoryMorphismComp` | 🌿 local-glue | Theory morphisms compose |
-/
import Mathlib
import RequestProject.Foundations.GeometricLogic

namespace Caramello.SyntacticCategory

open GeometricLogic

/-! ## Section 1: Geometric Derivability

The deduction rules of geometric logic. A geometric sequent φ ⊢ ψ
is derivable from theory T if it can be obtained by the following rules.

These rules correspond to the fragment of first-order logic that uses
only ⊤, ⊥, ∧, ∨ (including infinitary), and ∃ — exactly the connectives
preserved by inverse image functors of geometric morphisms.
-/

/-- Derivability of geometric sequents from a theory T.
    `Derivable T φ ψ` means "T proves φ ⊢ ψ" in geometric logic.

    The rules are:
    - `axiom_rule`: sequents in T are derivable
    - `refl`: φ ⊢ φ
    - `trans`: if φ ⊢ ψ and ψ ⊢ χ then φ ⊢ χ
    - `top_intro`: φ ⊢ ⊤ (⊤ is a theorem)
    - `bot_elim`: ⊥ ⊢ ψ (ex falso)
    - `conj_intro`: if φ ⊢ ψ₁ and φ ⊢ ψ₂ then φ ⊢ ψ₁ ∧ ψ₂
    - `conj_elim_left`: φ ∧ ψ ⊢ φ
    - `conj_elim_right`: φ ∧ ψ ⊢ ψ
    - `disj_intro_left`: φ ⊢ φ ∨ ψ
    - `disj_intro_right`: ψ ⊢ φ ∨ ψ
    - `disj_elim`: if φ ⊢ χ and ψ ⊢ χ then φ ∨ ψ ⊢ χ
    - `ex_intro`: φ[b] ⊢ ∃x.φ[x] (existential introduction)
    - `iDisj_intro`: φᵢ ⊢ ∨ᵢ φᵢ (infinitary disjunction introduction)
    - `iDisj_elim`: if φᵢ ⊢ χ for all i then ∨ᵢ φᵢ ⊢ χ
    - `weaken_left`: if φ ⊢ χ then φ ∧ ψ ⊢ χ (weakening)
-/
inductive Derivable {α : Type} (T : GeomTheory α) :
    GeomFormula α → GeomFormula α → Prop where
  | axiom_rule (s : GeomSequent α) (hs : s ∈ T) :
      Derivable T s.antecedent s.consequent
  | refl (φ : GeomFormula α) :
      Derivable T φ φ
  | trans {φ ψ χ : GeomFormula α} :
      Derivable T φ ψ → Derivable T ψ χ → Derivable T φ χ
  | top_intro (φ : GeomFormula α) :
      Derivable T φ .top
  | bot_elim (ψ : GeomFormula α) :
      Derivable T .bot ψ
  | conj_intro {φ ψ₁ ψ₂ : GeomFormula α} :
      Derivable T φ ψ₁ → Derivable T φ ψ₂ → Derivable T φ (.conj ψ₁ ψ₂)
  | conj_elim_left (φ ψ : GeomFormula α) :
      Derivable T (.conj φ ψ) φ
  | conj_elim_right (φ ψ : GeomFormula α) :
      Derivable T (.conj φ ψ) ψ
  | disj_intro_left (φ ψ : GeomFormula α) :
      Derivable T φ (.disj φ ψ)
  | disj_intro_right (φ ψ : GeomFormula α) :
      Derivable T ψ (.disj φ ψ)
  | disj_elim {φ ψ χ : GeomFormula α} :
      Derivable T φ χ → Derivable T ψ χ → Derivable T (.disj φ ψ) χ
  | ex_intro (β : Type) (f : β → GeomFormula α) (b : β) :
      Derivable T (f b) (.ex β f)
  | iDisj_intro (ι : Type) (f : ι → GeomFormula α) (i : ι) :
      Derivable T (f i) (.iDisj ι f)
  | iDisj_elim {ι : Type} {f : ι → GeomFormula α} {χ : GeomFormula α} :
      (∀ i, Derivable T (f i) χ) → Derivable T (.iDisj ι f) χ
  | ex_elim {β : Type} {f : β → GeomFormula α} {χ : GeomFormula α} :
      (∀ b, Derivable T (f b) χ) → Derivable T (.ex β f) χ
  | weaken_left {φ χ : GeomFormula α} (ψ : GeomFormula α) :
      Derivable T φ χ → Derivable T (.conj φ ψ) χ
  | weaken_right {ψ χ : GeomFormula α} (φ : GeomFormula α) :
      Derivable T ψ χ → Derivable T (.conj φ ψ) χ
  | frobenius {φ ψ₁ ψ₂ χ : GeomFormula α} :
      Derivable T (.conj φ ψ₁) χ → Derivable T (.conj φ ψ₂) χ →
      Derivable T (.conj φ (.disj ψ₁ ψ₂)) χ
  /-- Infinitary Frobenius: case-split on an infinitary disjunction under conjunction -/
  | iFrobenius {φ χ : GeomFormula α} {ι : Type} {f : ι → GeomFormula α} :
      (∀ i, Derivable T (.conj φ (f i)) χ) →
      Derivable T (.conj φ (.iDisj ι f)) χ
  /-- Existential Frobenius: case-split on an existential under conjunction -/
  | exFrobenius {φ χ : GeomFormula α} {β : Type} {f : β → GeomFormula α} :
      (∀ b, Derivable T (.conj φ (f b)) χ) →
      Derivable T (.conj φ (.ex β f)) χ

/-- Shorthand notation: `T ⊢g φ ⟹ ψ` means φ ⊢ ψ is derivable from T. -/
notation:50 T " ⊢g " φ " ⟹ " ψ => Derivable T φ ψ

/-! ## Section 2: Basic Derivability Facts -/

/-- Derivability is reflexive. -/
lemma derivable_refl {α : Type} (T : GeomTheory α) (φ : GeomFormula α) :
    T ⊢g φ ⟹ φ :=
  Derivable.refl φ

/-- Derivability is transitive. -/
lemma derivable_trans {α : Type} (T : GeomTheory α)
    {φ ψ χ : GeomFormula α}
    (h₁ : T ⊢g φ ⟹ ψ) (h₂ : T ⊢g ψ ⟹ χ) :
    T ⊢g φ ⟹ χ :=
  Derivable.trans h₁ h₂

/-- Top is derivable from anything. -/
lemma derivable_top {α : Type} (T : GeomTheory α) (φ : GeomFormula α) :
    T ⊢g φ ⟹ .top :=
  Derivable.top_intro φ

/-- Anything is derivable from bottom. -/
lemma derivable_bot {α : Type} (T : GeomTheory α) (ψ : GeomFormula α) :
    T ⊢g .bot ⟹ ψ :=
  Derivable.bot_elim ψ

/-- Monotonicity: if T ⊆ T' then derivability in T implies derivability in T'. -/
lemma derivable_mono {α : Type} {T T' : GeomTheory α} (h : T ⊆ T')
    {φ ψ : GeomFormula α} (hd : T ⊢g φ ⟹ ψ) :
    T' ⊢g φ ⟹ ψ := by
  induction hd with
  | axiom_rule s hs => exact Derivable.axiom_rule s (h hs)
  | refl φ => exact Derivable.refl φ
  | trans _ _ ih₁ ih₂ => exact Derivable.trans ih₁ ih₂
  | top_intro φ => exact Derivable.top_intro φ
  | bot_elim ψ => exact Derivable.bot_elim ψ
  | conj_intro _ _ ih₁ ih₂ => exact Derivable.conj_intro ih₁ ih₂
  | conj_elim_left φ ψ => exact Derivable.conj_elim_left φ ψ
  | conj_elim_right φ ψ => exact Derivable.conj_elim_right φ ψ
  | disj_intro_left φ ψ => exact Derivable.disj_intro_left φ ψ
  | disj_intro_right φ ψ => exact Derivable.disj_intro_right φ ψ
  | disj_elim _ _ ih₁ ih₂ => exact Derivable.disj_elim ih₁ ih₂
  | ex_intro β f b => exact Derivable.ex_intro β f b
  | iDisj_intro ι f i => exact Derivable.iDisj_intro ι f i
  | iDisj_elim _ ih => exact Derivable.iDisj_elim ih
  | ex_elim _ ih => exact Derivable.ex_elim ih
  | weaken_left ψ _ ih => exact Derivable.weaken_left ψ ih
  | weaken_right φ _ ih => exact Derivable.weaken_right φ ih
  | frobenius _ _ ih₁ ih₂ => exact Derivable.frobenius ih₁ ih₂
  | iFrobenius _ ih => exact Derivable.iFrobenius (fun i => ih i)
  | exFrobenius _ ih => exact Derivable.exFrobenius (fun b => ih b)

/-! ## Section 3: Soundness Theorem ★

The fundamental connection between syntax and semantics:
every derivable sequent is valid in every model of T.
-/

/-- **Soundness theorem for geometric logic.**
    If φ ⊢ ψ is derivable from T, then for every valuation v
    that models T, φ(v) implies ψ(v).

    ★ This is the syntactic-semantic bridge: proof-theoretic
    derivability implies truth in all models. -/
theorem soundness {α : Type} {T : GeomTheory α}
    {φ ψ : GeomFormula α} (hd : T ⊢g φ ⟹ ψ)
    (v : α → Prop) (hmodel : T.Model v) :
    φ.eval v → ψ.eval v := by
  induction hd with
  | axiom_rule s hs =>
    exact hmodel s hs
  | refl _ => exact id
  | trans _ _ ih₁ ih₂ => exact ih₂ ∘ ih₁
  | top_intro _ => intro _; trivial
  | bot_elim _ => intro h; exact absurd h id
  | conj_intro _ _ ih₁ ih₂ =>
    intro h; exact ⟨ih₁ h, ih₂ h⟩
  | conj_elim_left φ' ψ' => intro ⟨h, _⟩; exact h
  | conj_elim_right φ' ψ' => intro ⟨_, h⟩; exact h
  | disj_intro_left φ' ψ' => exact Or.inl
  | disj_intro_right φ' ψ' => exact Or.inr
  | disj_elim _ _ ih₁ ih₂ =>
    intro h; exact h.elim ih₁ ih₂
  | ex_intro β f b =>
    intro h; exact ⟨b, h⟩
  | iDisj_intro ι f i =>
    intro h; exact ⟨i, h⟩
  | iDisj_elim _ ih =>
    intro ⟨i, hi⟩; exact ih i hi
  | ex_elim _ ih =>
    intro ⟨b, hb⟩; exact ih b hb
  | weaken_left ψ' _ ih =>
    intro ⟨h, _⟩; exact ih h
  | weaken_right φ' _ ih =>
    intro ⟨_, h⟩; exact ih h
  | frobenius _ _ ih₁ ih₂ =>
    intro ⟨hφ, hδ⟩
    exact hδ.elim (fun hψ₁ => ih₁ ⟨hφ, hψ₁⟩) (fun hψ₂ => ih₂ ⟨hφ, hψ₂⟩)
  | iFrobenius _ ih =>
    intro ⟨hφ, ⟨i, hi⟩⟩
    exact ih i ⟨hφ, hi⟩
  | exFrobenius _ ih =>
    intro ⟨hφ, ⟨b, hb⟩⟩
    exact ih b ⟨hφ, hb⟩

/-- Soundness for sequents: if s is derivable from T,
    then s is valid in every model of T. -/
theorem sequent_soundness {α : Type} {T : GeomTheory α}
    {s : GeomSequent α} (hs : s ∈ T)
    (v : α → Prop) (hmodel : T.Model v) :
    s.valid v :=
  soundness (Derivable.axiom_rule s hs) v hmodel

/-! ## Section 4: T-Equivalence and the Syntactic Preorder

The derivability relation gives a preorder on geometric formulas.
Two formulas are T-equivalent if they are mutually derivable.
-/

/-- T-equivalence: two formulas are equivalent in theory T
    if they are mutually derivable. -/
def TEquiv {α : Type} (T : GeomTheory α) (φ ψ : GeomFormula α) : Prop :=
  (T ⊢g φ ⟹ ψ) ∧ (T ⊢g ψ ⟹ φ)

notation:50 T " ⊢g " φ " ⟺ " ψ => TEquiv T φ ψ

/-- T-equivalence is reflexive. -/
lemma tequiv_refl {α : Type} (T : GeomTheory α) (φ : GeomFormula α) :
    T ⊢g φ ⟺ φ :=
  ⟨Derivable.refl φ, Derivable.refl φ⟩

/-- T-equivalence is symmetric. -/
lemma tequiv_symm {α : Type} (T : GeomTheory α) {φ ψ : GeomFormula α}
    (h : T ⊢g φ ⟺ ψ) : T ⊢g ψ ⟺ φ :=
  ⟨h.2, h.1⟩

/-- T-equivalence is transitive. -/
lemma tequiv_trans {α : Type} (T : GeomTheory α) {φ ψ χ : GeomFormula α}
    (h₁ : T ⊢g φ ⟺ ψ) (h₂ : T ⊢g ψ ⟺ χ) : T ⊢g φ ⟺ χ :=
  ⟨Derivable.trans h₁.1 h₂.1, Derivable.trans h₂.2 h₁.2⟩

/-- T-equivalence is an equivalence relation. -/
lemma tequiv_equivalence {α : Type} (T : GeomTheory α) :
    Equivalence (TEquiv T) :=
  ⟨tequiv_refl T, fun h => tequiv_symm T h, fun h₁ h₂ => tequiv_trans T h₁ h₂⟩

/-- The setoid of geometric formulas modulo T-equivalence. -/
def syntacticSetoid {α : Type} (T : GeomTheory α) : Setoid (GeomFormula α) where
  r := TEquiv T
  iseqv := tequiv_equivalence T

/-- The syntactic preorder: formulas ordered by T-entailment. -/
def syntacticPreorder {α : Type} (T : GeomTheory α) : Preorder (GeomFormula α) where
  le φ ψ := T ⊢g φ ⟹ ψ
  le_refl φ := Derivable.refl φ
  le_trans _ _ _ h₁ h₂ := Derivable.trans h₁ h₂

/-! ## Section 5: Lattice-Like Structure of the Syntactic Preorder

The syntactic preorder inherits lattice-like structure from the
logical connectives. We state these as lemmas using `syntacticPreorder`.
-/

/-- In the syntactic preorder, ⊤ is the greatest element. -/
lemma syntactic_top_terminal {α : Type} (T : GeomTheory α)
    (φ : GeomFormula α) :
    (syntacticPreorder T).le φ .top :=
  Derivable.top_intro φ

/-- In the syntactic preorder, ⊥ is the least element. -/
lemma syntactic_bot_initial {α : Type} (T : GeomTheory α)
    (ψ : GeomFormula α) :
    (syntacticPreorder T).le .bot ψ :=
  Derivable.bot_elim ψ

/-- ∧ is a lower bound: φ ∧ ψ ≤ φ. -/
lemma syntactic_conj_le_left {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) :
    (syntacticPreorder T).le (.conj φ ψ) φ :=
  Derivable.conj_elim_left φ ψ

/-- ∧ is a lower bound: φ ∧ ψ ≤ ψ. -/
lemma syntactic_conj_le_right {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) :
    (syntacticPreorder T).le (.conj φ ψ) ψ :=
  Derivable.conj_elim_right φ ψ

/-- ∧ is the greatest lower bound: if χ ≤ φ and χ ≤ ψ then χ ≤ φ ∧ ψ. -/
lemma syntactic_conj_glb {α : Type} (T : GeomTheory α)
    {φ ψ χ : GeomFormula α}
    (h₁ : (syntacticPreorder T).le χ φ)
    (h₂ : (syntacticPreorder T).le χ ψ) :
    (syntacticPreorder T).le χ (.conj φ ψ) :=
  Derivable.conj_intro h₁ h₂

/-- ∨ is an upper bound: φ ≤ φ ∨ ψ. -/
lemma syntactic_disj_le_left {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) :
    (syntacticPreorder T).le φ (.disj φ ψ) :=
  Derivable.disj_intro_left φ ψ

/-- ∨ is an upper bound: ψ ≤ φ ∨ ψ. -/
lemma syntactic_disj_le_right {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) :
    (syntacticPreorder T).le ψ (.disj φ ψ) :=
  Derivable.disj_intro_right φ ψ

/-- ∨ is the least upper bound: if φ ≤ χ and ψ ≤ χ then φ ∨ ψ ≤ χ. -/
lemma syntactic_disj_lub {α : Type} (T : GeomTheory α)
    {φ ψ χ : GeomFormula α}
    (h₁ : (syntacticPreorder T).le φ χ)
    (h₂ : (syntacticPreorder T).le ψ χ) :
    (syntacticPreorder T).le (.disj φ ψ) χ :=
  Derivable.disj_elim h₁ h₂

/-! ## Section 6: Theory Morphisms and Functoriality

A theory morphism σ : T₁ → T₂ (between theories over possibly different
signatures) consists of a map on atoms that translates T₁-derivable
sequents to T₂-derivable sequents. These give monotone maps between
syntactic preorders — essential for Morita equivalence.
-/

/-- A theory morphism from T₁ (over signature α) to T₂ (over signature β)
    consists of an atom translation f : α → β such that every T₁-derivable
    sequent becomes T₂-derivable after translation. -/
structure TheoryMorphism {α β : Type}
    (T₁ : GeomTheory α) (T₂ : GeomTheory β) where
  /-- The underlying map on atoms (signature translation) -/
  onAtoms : α → β
  /-- Derivability is preserved: if T₁ ⊢ φ ⟹ ψ then T₂ ⊢ σ(φ) ⟹ σ(ψ) -/
  preserves_derivability : ∀ {φ ψ : GeomFormula α},
    Derivable T₁ φ ψ → Derivable T₂ (φ.mapAtoms onAtoms) (ψ.mapAtoms onAtoms)

/-- The identity theory morphism. -/
def theoryMorphismId {α : Type} (T : GeomTheory α) : TheoryMorphism T T where
  onAtoms := id
  preserves_derivability := by
    intro φ ψ hd
    rwa [mapAtoms_id, mapAtoms_id]

/-- Composition of theory morphisms. -/
def theoryMorphismComp {α β γ : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β} {T₃ : GeomTheory γ}
    (σ : TheoryMorphism T₁ T₂) (τ : TheoryMorphism T₂ T₃) :
    TheoryMorphism T₁ T₃ where
  onAtoms := τ.onAtoms ∘ σ.onAtoms
  preserves_derivability := by
    intro φ ψ hd
    rw [mapAtoms_comp, mapAtoms_comp]
    exact τ.preserves_derivability (σ.preserves_derivability hd)

/-- A theory morphism is monotone with respect to the syntactic preorders. -/
lemma theoryMorphism_monotone {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    {φ ψ : GeomFormula α}
    (h : (syntacticPreorder T₁).le φ ψ) :
    (syntacticPreorder T₂).le (φ.mapAtoms σ.onAtoms) (ψ.mapAtoms σ.onAtoms) :=
  σ.preserves_derivability h

/-- A theory morphism preserves T-equivalence. -/
lemma theoryMorphism_preserves_tequiv {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    {φ ψ : GeomFormula α}
    (h : T₁ ⊢g φ ⟺ ψ) :
    T₂ ⊢g (φ.mapAtoms σ.onAtoms) ⟺ (ψ.mapAtoms σ.onAtoms) :=
  ⟨σ.preserves_derivability h.1, σ.preserves_derivability h.2⟩

/-! ## Section 7: Soundness Corollaries

Consequences of the soundness theorem connecting derivability to semantics.
-/

/-- If T has a model where φ holds but ψ doesn't, then φ ⊢ ψ is NOT derivable.
    This is the contrapositive of soundness — useful for showing non-derivability. -/
lemma non_derivable_witness {α : Type} {T : GeomTheory α}
    {φ ψ : GeomFormula α}
    (v : α → Prop) (hmodel : T.Model v)
    (hφ : φ.eval v) (hψ : ¬ψ.eval v) :
    ¬(T ⊢g φ ⟹ ψ) := by
  intro hd
  exact hψ (soundness hd v hmodel hφ)

/-- Soundness for T-equivalence: if φ ⟺_T ψ, then they have the
    same truth value in every model. -/
lemma tequiv_sound {α : Type} {T : GeomTheory α}
    {φ ψ : GeomFormula α} (h : T ⊢g φ ⟺ ψ)
    (v : α → Prop) (hmodel : T.Model v) :
    φ.eval v ↔ ψ.eval v :=
  ⟨soundness h.1 v hmodel, soundness h.2 v hmodel⟩

/-- A derivable sequent is valid in every model — alternative phrasing
    using GeomSequent.valid directly. -/
lemma derivable_implies_valid {α : Type} {T : GeomTheory α}
    {φ ψ : GeomFormula α} (hd : T ⊢g φ ⟹ ψ) :
    ∀ v, T.Model v → (GeomSequent.mk φ ψ).valid v :=
  fun v hm => soundness hd v hm

/-! ## Section 8: Lindenbaum–Tarski Algebra

The quotient of the syntactic preorder by T-equivalence gives a
partial order — the **Lindenbaum–Tarski algebra** of the theory.
For geometric theories, this is a bounded distributive lattice.
-/

/-- The Lindenbaum–Tarski quotient: formulas modulo T-equivalence. -/
def LindenbaumTarski {α : Type} (T : GeomTheory α) :=
  Quotient (syntacticSetoid T)

/-- Lift the entailment relation to the quotient. -/
def LindenbaumTarski.le {α : Type} {T : GeomTheory α} :
    LindenbaumTarski T → LindenbaumTarski T → Prop :=
  Quotient.lift₂ (fun φ ψ => T ⊢g φ ⟹ ψ)
    (by
      intro a₁ a₂ b₁ b₂ ha hb
      simp only [eq_iff_iff]
      constructor
      · intro h; exact Derivable.trans ha.2 (Derivable.trans h hb.1)
      · intro h; exact Derivable.trans ha.1 (Derivable.trans h hb.2))

/-- The Lindenbaum–Tarski algebra is a partial order. -/
noncomputable instance lindenbaumTarskiPartialOrder {α : Type} (T : GeomTheory α) :
    PartialOrder (LindenbaumTarski T) where
  le := LindenbaumTarski.le
  le_refl := by
    intro a; exact Quotient.inductionOn a (fun φ => Derivable.refl φ)
  le_trans := by
    intro a b c; exact Quotient.inductionOn₃ a b c
      (fun φ ψ χ h₁ h₂ => Derivable.trans h₁ h₂)
  le_antisymm := by
    intro a b hab hba
    exact Quotient.inductionOn₂ a b (fun φ ψ h₁ h₂ =>
      Quotient.sound ⟨h₁, h₂⟩) hab hba

/-- The equivalence class of ⊤ in the Lindenbaum–Tarski algebra. -/
def LindenbaumTarski.ltTop {α : Type} {T : GeomTheory α} : LindenbaumTarski T :=
  Quotient.mk (syntacticSetoid T) .top

/-- The equivalence class of ⊥ in the Lindenbaum–Tarski algebra. -/
def LindenbaumTarski.ltBot {α : Type} {T : GeomTheory α} : LindenbaumTarski T :=
  Quotient.mk (syntacticSetoid T) .bot

/-- The Lindenbaum–Tarski algebra has a top element. -/
noncomputable instance lindenbaumTarskiOrderTop {α : Type} (T : GeomTheory α) :
    OrderTop (LindenbaumTarski T) where
  top := LindenbaumTarski.ltTop
  le_top := by
    intro a; exact Quotient.inductionOn a (fun φ => Derivable.top_intro φ)

/-- The Lindenbaum–Tarski algebra has a bottom element. -/
noncomputable instance lindenbaumTarskiOrderBot {α : Type} (T : GeomTheory α) :
    OrderBot (LindenbaumTarski T) where
  bot := LindenbaumTarski.ltBot
  bot_le := by
    intro a; exact Quotient.inductionOn a (fun φ => Derivable.bot_elim φ)

/-! ## Section 9: Congruence Properties

Logical connectives respect T-equivalence, so they descend to
well-defined operations on the Lindenbaum–Tarski algebra.
-/

/-- Conjunction is congruent with respect to T-equivalence. -/
lemma conj_congr {α : Type} {T : GeomTheory α}
    {φ₁ φ₂ ψ₁ ψ₂ : GeomFormula α}
    (h₁ : T ⊢g φ₁ ⟺ φ₂) (h₂ : T ⊢g ψ₁ ⟺ ψ₂) :
    T ⊢g (.conj φ₁ ψ₁) ⟺ (.conj φ₂ ψ₂) := by
  constructor
  · exact Derivable.conj_intro
      (Derivable.trans (Derivable.conj_elim_left _ _) h₁.1)
      (Derivable.trans (Derivable.conj_elim_right _ _) h₂.1)
  · exact Derivable.conj_intro
      (Derivable.trans (Derivable.conj_elim_left _ _) h₁.2)
      (Derivable.trans (Derivable.conj_elim_right _ _) h₂.2)

/-- Disjunction is congruent with respect to T-equivalence. -/
lemma disj_congr {α : Type} {T : GeomTheory α}
    {φ₁ φ₂ ψ₁ ψ₂ : GeomFormula α}
    (h₁ : T ⊢g φ₁ ⟺ φ₂) (h₂ : T ⊢g ψ₁ ⟺ ψ₂) :
    T ⊢g (.disj φ₁ ψ₁) ⟺ (.disj φ₂ ψ₂) := by
  constructor
  · exact Derivable.disj_elim
      (Derivable.trans h₁.1 (Derivable.disj_intro_left _ _))
      (Derivable.trans h₂.1 (Derivable.disj_intro_right _ _))
  · exact Derivable.disj_elim
      (Derivable.trans h₁.2 (Derivable.disj_intro_left _ _))
      (Derivable.trans h₂.2 (Derivable.disj_intro_right _ _))

/-- Meet on the Lindenbaum–Tarski algebra (from conjunction). -/
noncomputable def LindenbaumTarski.ltInf {α : Type} {T : GeomTheory α}
    (a b : LindenbaumTarski T) : LindenbaumTarski T :=
  Quotient.lift₂ (fun φ ψ => Quotient.mk (syntacticSetoid T) (.conj φ ψ))
    (by
      intro a₁ a₂ b₁ b₂ ha hb
      exact Quotient.sound (conj_congr ha hb))
    a b

/-- Join on the Lindenbaum–Tarski algebra (from disjunction). -/
noncomputable def LindenbaumTarski.ltSup {α : Type} {T : GeomTheory α}
    (a b : LindenbaumTarski T) : LindenbaumTarski T :=
  Quotient.lift₂ (fun φ ψ => Quotient.mk (syntacticSetoid T) (.disj φ ψ))
    (by
      intro a₁ a₂ b₁ b₂ ha hb
      exact Quotient.sound (disj_congr ha hb))
    a b

/-- Meet is a lower bound on the left. -/
lemma ltInf_le_left {α : Type} {T : GeomTheory α}
    (a b : LindenbaumTarski T) :
    (lindenbaumTarskiPartialOrder T).le (LindenbaumTarski.ltInf a b) a := by
  exact Quotient.inductionOn₂ a b
    (fun φ ψ => Derivable.conj_elim_left φ ψ)

/-- Meet is a lower bound on the right. -/
lemma ltInf_le_right {α : Type} {T : GeomTheory α}
    (a b : LindenbaumTarski T) :
    (lindenbaumTarskiPartialOrder T).le (LindenbaumTarski.ltInf a b) b := by
  exact Quotient.inductionOn₂ a b
    (fun φ ψ => Derivable.conj_elim_right φ ψ)

/-- Meet is the greatest lower bound. -/
lemma le_ltInf {α : Type} {T : GeomTheory α}
    {a b c : LindenbaumTarski T}
    (h₁ : (lindenbaumTarskiPartialOrder T).le c a)
    (h₂ : (lindenbaumTarskiPartialOrder T).le c b) :
    (lindenbaumTarskiPartialOrder T).le c (LindenbaumTarski.ltInf a b) := by
  exact Quotient.inductionOn₃ a b c
    (fun φ ψ χ h₁ h₂ => Derivable.conj_intro h₁ h₂) h₁ h₂

/-- Join is an upper bound on the left. -/
lemma le_ltSup_left {α : Type} {T : GeomTheory α}
    (a b : LindenbaumTarski T) :
    (lindenbaumTarskiPartialOrder T).le a (LindenbaumTarski.ltSup a b) := by
  exact Quotient.inductionOn₂ a b
    (fun φ ψ => Derivable.disj_intro_left φ ψ)

/-- Join is an upper bound on the right. -/
lemma le_ltSup_right {α : Type} {T : GeomTheory α}
    (a b : LindenbaumTarski T) :
    (lindenbaumTarskiPartialOrder T).le b (LindenbaumTarski.ltSup a b) := by
  exact Quotient.inductionOn₂ a b
    (fun φ ψ => Derivable.disj_intro_right φ ψ)

/-- Join is the least upper bound. -/
lemma ltSup_le {α : Type} {T : GeomTheory α}
    {a b c : LindenbaumTarski T}
    (h₁ : (lindenbaumTarskiPartialOrder T).le a c)
    (h₂ : (lindenbaumTarskiPartialOrder T).le b c) :
    (lindenbaumTarskiPartialOrder T).le (LindenbaumTarski.ltSup a b) c := by
  exact Quotient.inductionOn₃ a b c
    (fun φ ψ χ h₁ h₂ => Derivable.disj_elim h₁ h₂) h₁ h₂

/-! ## Section 10: Evaluation as a Monotone Map

The evaluation map `eval v` sends formulas to Prop, and descends
to the Lindenbaum–Tarski quotient as a monotone map (by soundness).
-/

/-- Evaluation at a model descends to the Lindenbaum–Tarski quotient. -/
noncomputable def evalQuotient {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hmodel : T.Model v) :
    LindenbaumTarski T → Prop :=
  Quotient.lift (GeomFormula.eval v)
    (by
      intro φ ψ h
      simp only [eq_iff_iff]
      exact tequiv_sound h v hmodel)

/-- The quotient evaluation is monotone: it respects the order. -/
lemma evalQuotient_monotone {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hmodel : T.Model v) :
    Monotone (evalQuotient v hmodel) := by
  intro a b h
  exact Quotient.inductionOn₂ a b (fun φ ψ hle =>
    soundness hle v hmodel) h

/-! ## Section 11: Distributivity in the Syntactic Preorder

The key property connecting geometric logic to frame theory:
conjunction distributes over disjunction in the syntactic preorder.
-/

/-- Conjunction distributes over disjunction: φ ∧ (ψ₁ ∨ ψ₂) ⟺ (φ ∧ ψ₁) ∨ (φ ∧ ψ₂).
    This is the frame distributivity law in the syntactic setting. -/
lemma syntactic_distrib {α : Type} (T : GeomTheory α)
    (φ ψ₁ ψ₂ : GeomFormula α) :
    T ⊢g (.conj φ (.disj ψ₁ ψ₂)) ⟺ (.disj (.conj φ ψ₁) (.conj φ ψ₂)) := by
  constructor
  · -- Forward: φ ∧ (ψ₁ ∨ ψ₂) ⊢ (φ ∧ ψ₁) ∨ (φ ∧ ψ₂)
    -- By Frobenius: case-split on ψ₁ ∨ ψ₂ while keeping φ
    exact Derivable.frobenius
      (Derivable.disj_intro_left _ _)  -- φ ∧ ψ₁ ⊢ (φ ∧ ψ₁) ∨ (φ ∧ ψ₂)
      (Derivable.disj_intro_right _ _) -- φ ∧ ψ₂ ⊢ (φ ∧ ψ₁) ∨ (φ ∧ ψ₂)
  · -- Backward: (φ ∧ ψ₁) ∨ (φ ∧ ψ₂) ⊢ φ ∧ (ψ₁ ∨ ψ₂)
    apply Derivable.disj_elim
    · -- φ ∧ ψ₁ ⊢ φ ∧ (ψ₁ ∨ ψ₂)
      apply Derivable.conj_intro
      · exact Derivable.conj_elim_left _ _
      · exact Derivable.trans (Derivable.conj_elim_right _ _)
          (Derivable.disj_intro_left _ _)
    · -- φ ∧ ψ₂ ⊢ φ ∧ (ψ₁ ∨ ψ₂)
      apply Derivable.conj_intro
      · exact Derivable.conj_elim_left _ _
      · exact Derivable.trans (Derivable.conj_elim_right _ _)
          (Derivable.disj_intro_right _ _)

end Caramello.SyntacticCategory
