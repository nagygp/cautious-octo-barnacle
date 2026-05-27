/-
# AB/APN Function Theory — Core Definitions

Core definitions for Almost Perfect Nonlinear (APN) and Almost Bent (AB) functions
over finite fields/groups. Built on simple Mathlib patterns: `Finset.filter`, `Finset.card`,
`Function.Injective`, `Equiv.Perm`.

## Main definitions

* `ABAPN.deltaSet` — solution set of the difference equation f(x+a) - f(x) = b
* `ABAPN.deltaCount` — number of solutions (cardinality of deltaSet)
* `ABAPN.diffUniformity` — maximum deltaCount over all nonzero a and all b
* `ABAPN.IsAPN` — f is APN iff differential uniformity ≤ 2
* `ABAPN.IsPN` — f is PN (perfect nonlinear) iff differential uniformity = 1
* `ABAPN.IsDiffUniform` — f has differential uniformity exactly δ
-/
import Mathlib

open Finset Function

namespace ABAPN

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### The difference / discrete derivative -/

/-- The discrete derivative of `f` in direction `a`. -/
def diffMap (f : F → F) (a : F) (x : F) : F := f (x + a) - f (x)

/-! ### Solution sets and counts -/

/-- The set of solutions to `f(x + a) - f(x) = b`. -/
def deltaSet (f : F → F) (a b : F) : Finset F :=
  Finset.univ.filter (fun x => f (x + a) - f (x) = b)

/-- Number of solutions to `f(x + a) - f(x) = b`. -/
def deltaCount (f : F → F) (a b : F) : ℕ :=
  (deltaSet f a b).card

/-! ### Differential uniformity -/

/-- The differential uniformity of `f`: the maximum of `deltaCount f a b`
    over all nonzero `a` and all `b`. -/
noncomputable def diffUniformity (f : F → F) : ℕ :=
  Finset.sup (Finset.univ.filter (· ≠ (0 : F))) fun a =>
    Finset.sup Finset.univ fun b =>
      deltaCount f a b

/-! ### APN and PN predicates -/

/-- A function is **Almost Perfect Nonlinear (APN)** if every nonzero-input difference equation
    has at most 2 solutions. -/
def IsAPN (f : F → F) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (b : F), deltaCount f a b ≤ 2

/-- A function is **Perfect Nonlinear (PN)** if every nonzero-input difference equation
    has at most 1 solution. (Only possible in odd characteristic.) -/
def IsPN (f : F → F) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (b : F), deltaCount f a b ≤ 1

/-- A function has **differential uniformity** exactly `δ`. -/
def IsDiffUniform (f : F → F) (δ : ℕ) : Prop :=
  (∀ (a : F), a ≠ 0 → ∀ (b : F), deltaCount f a b ≤ δ) ∧
  (∃ (a : F), a ≠ 0 ∧ ∃ (b : F), deltaCount f a b = δ)

/-! ### Basic API lemmas -/

@[simp]
lemma deltaSet_unfold (f : F → F) (a b : F) :
    deltaSet f a b = Finset.univ.filter (fun x => f (x + a) - f (x) = b) := rfl

@[simp]
lemma deltaCount_unfold (f : F → F) (a b : F) :
    deltaCount f a b = (deltaSet f a b).card := rfl

lemma mem_deltaSet_iff (f : F → F) (a b x : F) :
    x ∈ deltaSet f a b ↔ f (x + a) - f (x) = b := by
  simp [deltaSet]

lemma diffMap_eq_iff (f : F → F) (a b x : F) :
    diffMap f a x = b ↔ x ∈ deltaSet f a b := by
  simp only [diffMap, deltaSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- APN is equivalent to `IsDiffUniform` with δ ≤ 2. -/
lemma isAPN_iff_forall_le_two (f : F → F) :
    IsAPN f ↔ ∀ (a : F), a ≠ 0 → ∀ (b : F), deltaCount f a b ≤ 2 := by
  rfl

/-- PN implies APN. -/
lemma IsPN.isAPN {f : F → F} (hf : IsPN f) : IsAPN f := by
  intro a ha b
  exact le_trans (hf a ha b) (by norm_num)

/-
The identity function has deltaCount = |F| for b = a.
-/
lemma deltaCount_id (a : F) :
    deltaCount id a a = Fintype.card F := by
  exact congr_arg Finset.card ( Finset.filter_true_of_mem fun x _ => by simp +decide )

/-
For identity, deltaCount is 0 when b ≠ a.
-/
lemma deltaCount_id_ne (a : F) (b : F) (hab : b ≠ a) :
    deltaCount (id : F → F) a b = 0 := by
  convert Finset.card_eq_zero.mpr ?_;
  exact Finset.filter_eq_empty_iff.mpr fun x _ => by simpa using hab.symm;

/-- deltaSet is a subset of univ. -/
lemma deltaSet_subset_univ (f : F → F) (a b : F) :
    deltaSet f a b ⊆ Finset.univ :=
  Finset.filter_subset _ _

/-- deltaCount is bounded by the cardinality of the field. -/
lemma deltaCount_le_card (f : F → F) (a b : F) :
    deltaCount f a b ≤ Fintype.card F :=
  Finset.card_filter_le _ _

/-
If `diffMap f a` is injective then deltaCount ≤ 1.
-/
lemma deltaCount_le_one_of_injective_diffMap (f : F → F) (a : F)
    (hinj : Function.Injective (diffMap f a)) (b : F) :
    deltaCount f a b ≤ 1 := by
  -- Since `diffMap f a` is injective, each `b` can map to at most one `x`.
  have h_unique : ∀ x y : F, (diffMap f a x = b ∧ diffMap f a y = b) → x = y := by
    exact fun x y h => hinj <| h.1.trans h.2.symm;
  exact Finset.card_le_one.mpr fun x hx y hy => h_unique x y ⟨ by simpa using Finset.mem_filter.mp hx |>.2, by simpa using Finset.mem_filter.mp hy |>.2 ⟩

end ABAPN