/-
# Layer 1: Prop as Subobject Classifier Ω for Type

Lean's Prop IS the subobject classifier Ω in the topos of types.
This file formalizes this correspondence, grounding Caramello's
abstract topos theory in Lean's own type theory.

## DAG Structure

```
                  typesClassifier (Main Theorem)
                  /          |            \
        truth_mono    char_isPullback   char_unique
            |          /        \            |
        punit_subsingleton  char_comm   char_range_iff
                               |
                          range_mem_iff
```

All leaf nodes are atomic lemmas provable by `simp`, `ext`, or `Subsingleton.elim`.
-/
import Mathlib

namespace Caramello.PropAsOmega

open CategoryTheory CategoryTheory.Limits

/-! ## Atomic Definitions -/

/-- The truth morphism: PUnit → Prop sending everything to True.
    This is the categorical analogue of ⊤ : 1 → Ω in topos theory. -/
def truth : (PUnit : Type) ⟶ (Prop : Type) := fun _ => True

/-- The characteristic map of a monomorphism m : U → X.
    Sends x to the proposition "x is in the range of m".
    This is the categorical χ_m : X → Ω. -/
def charMap {U X : Type} (m : U ⟶ X) : X ⟶ (Prop : Type) :=
  fun x => x ∈ Set.range m

/-- The unique map to PUnit (terminal morphism). -/
def toUnit (U : Type) : U ⟶ (PUnit : Type) := fun _ => PUnit.unit

/-! ## Layer 1a: Atomic Lemmas (Leaf Nodes) -/

/-- truth is mono because PUnit is a subsingleton. -/
lemma truth_injective : Function.Injective truth := by
  intro a b _
  exact Subsingleton.elim a b

/-- truth is mono in the categorical sense. -/
lemma truth_mono : Mono truth := by
  rw [mono_iff_injective]
  exact truth_injective

/-- Every element in the range of m satisfies the characteristic map. -/
lemma charMap_of_mem_range {U X : Type} (m : U ⟶ X) (u : U) :
    charMap m (m u) = True := by
  simp [charMap]

/-- The square commutes: truth ∘ toUnit = charMap m ∘ m -/
lemma char_comm {U X : Type} (m : U ⟶ X) :
    m ≫ charMap m = toUnit U ≫ truth := by
  ext u
  simp [charMap, truth]

/-! ## Layer 1b: Composite Lemmas -/

/-- The commutative square condition packaged as CommSq. -/
lemma char_commSq {U X : Type} (m : U ⟶ X) [Mono m] :
    CommSq m (toUnit U) (charMap m) truth :=
  ⟨char_comm m⟩

/-- Key characterization: x satisfies charMap m iff x is in the range of m. -/
lemma charMap_iff {U X : Type} (m : U ⟶ X) (x : X) :
    charMap m x ↔ x ∈ Set.range m :=
  Iff.rfl

/-- For an injective m, the preimage of x ∈ range m is unique. -/
lemma unique_preimage {U X : Type} (m : U ⟶ X) (hm : Function.Injective m)
    (x : X) (hx : x ∈ Set.range m) : ∃! u : U, m u = x := by
  obtain ⟨u, hu⟩ := hx
  exact ⟨u, hu, fun v hv => hm (hv.trans hu.symm)⟩

/-! ## Layer 1c: The Pullback Construction -/

/-- Given a cone on the cospan (charMap m, truth), construct a lift to U.
    This uses the fact that the cone condition forces elements into range m,
    and injectivity of m gives unique preimages. -/
noncomputable def pullbackLift {U X : Type} (m : U ⟶ X) (hm : Function.Injective m)
    (s : PullbackCone (charMap m) truth) : s.pt ⟶ U := by
  intro p
  have h : charMap m (s.fst p) = truth (s.snd p) := congr_fun s.condition p
  simp [truth] at h
  rw [charMap_iff] at h
  exact (unique_preimage m hm (s.fst p) h).choose

/-- The lift satisfies m ∘ lift = fst. -/
lemma pullbackLift_fst {U X : Type} (m : U ⟶ X) (hm : Function.Injective m)
    (s : PullbackCone (charMap m) truth) :
    pullbackLift m hm s ≫ m = s.fst := by
  ext p
  simp [pullbackLift]
  have h : charMap m (s.fst p) = truth (s.snd p) := congr_fun s.condition p
  simp [truth] at h
  rw [charMap_iff] at h
  exact (unique_preimage m hm (s.fst p) h).choose_spec.1

/-- The lift satisfies toUnit ∘ lift = snd. -/
lemma pullbackLift_snd {U X : Type} (m : U ⟶ X) (hm : Function.Injective m)
    (s : PullbackCone (charMap m) truth) :
    pullbackLift m hm s ≫ toUnit U = s.snd := by
  funext p
  exact Subsingleton.elim _ _

/-- The lift is unique. -/
lemma pullbackLift_uniq {U X : Type} (m : U ⟶ X) (hm : Function.Injective m)
    (s : PullbackCone (charMap m) truth) (l : s.pt ⟶ U)
    (hl_fst : l ≫ m = s.fst) (_hl_snd : l ≫ toUnit U = s.snd) :
    l = pullbackLift m hm s := by
  ext p
  apply hm
  have h1 : m (l p) = s.fst p := congr_fun hl_fst p
  have h2 : m (pullbackLift m hm s p) = s.fst p := congr_fun (pullbackLift_fst m hm s) p
  exact h1.trans h2.symm

/-! ## Layer 1d: The IsPullback proof -/

/-- The square (m, toUnit, charMap m, truth) is a pullback in Type. -/
noncomputable def char_isPullback {U X : Type} (m : U ⟶ X) [hm : Mono m] :
    IsPullback m (toUnit U) (charMap m) truth := by
  have hinj : Function.Injective m := (mono_iff_injective m).mp hm
  exact IsPullback.mk (char_commSq m) ⟨PullbackCone.IsLimit.mk (char_comm m)
    (pullbackLift m hinj)
    (pullbackLift_fst m hinj)
    (pullbackLift_snd m hinj)
    (pullbackLift_uniq m hinj)⟩

/-! ## Layer 1e: Uniqueness of characteristic map -/

/-
The characteristic map is unique: if χ' also makes a pullback,
    then χ' = charMap m. This is the key uniqueness property of Ω.
-/
lemma char_unique {U X : Type} (m : U ⟶ X) [_hm : Mono m]
    {χ₀' : U ⟶ PUnit} {χ' : X ⟶ Prop}
    (hpb : IsPullback m χ₀' χ' truth) :
    χ' = charMap m := by
      -- We need to show χ' = charMap m, i.e., for all x : X, χ' x ↔ x ∈ Set.range m.
      ext x; constructor <;> intro hx;
      · -- Construct a cone with point PUnit, fst = fun _ => x, snd = fun _ => PUnit.unit.
        set c : PullbackCone χ' truth := PullbackCone.mk (fun _ : PUnit => x) (fun _ : PUnit => PUnit.unit) (by
        unfold truth; aesop;);
        -- By the universal property of the pullback, there exists a unique lift l : PUnit → U such that m ∘ l = fst and toUnit ∘ l = snd.
        obtain ⟨l, hl⟩ := hpb.isLimit.existsUnique c;
        exact ⟨ l PUnit.unit, by simpa using congr_fun ( hl.1 WalkingCospan.left ) PUnit.unit ⟩;
      · obtain ⟨ u, rfl ⟩ := hx;
        have := hpb.1;
        convert congr_fun this.w u;
        simp +decide [ truth ]

/-! ## Main Theorem: Type has a subobject classifier, and it's Prop -/

/-- **The fundamental theorem**: `Type` has a subobject classifier,
    and it is `Prop`. This makes precise the claim that
    Lean's `Prop` IS the topos-theoretic `Ω`.

    This is the categorical incarnation of the fact that
    predicates `P : X → Prop` classify subsets of X. -/
noncomputable def typesClassifier : Classifier (Type) where
  Ω₀ := PUnit
  Ω := Prop
  truth := truth
  mono_truth := truth_mono
  χ₀ := toUnit
  χ := fun m => charMap m
  isPullback := fun m => char_isPullback m
  uniq := by intro U X m _ χ₀' χ' hpb; exact char_unique m hpb

end Caramello.PropAsOmega