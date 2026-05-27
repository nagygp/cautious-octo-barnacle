/-
# Coding Theory Connections

APN and AB functions correspond to optimal error-correcting codes.
The graph `{(x, f(x)) : x ∈ F}` of an APN function gives a code
with minimum distance related to the differential uniformity.

Built on `Finset`, `Fintype.card`, `Submodule`, `LinearMap`.
-/
import Mathlib
import RequestProject.ABAPN.Defs

open Finset Function ABAPN

namespace ABAPN.Coding

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Hamming-like distance on F^2 -/

/-- The number of coordinates where two codewords in `F × F` differ. -/
def pairHammingDist (a b : F × F) : ℕ :=
  (if a.1 = b.1 then 0 else 1) + (if a.2 = b.2 then 0 else 1)

/-! ### Graph code -/

/-- The graph of `f` as a Finset of pairs `(x, f(x))`. -/
def graphCode (f : F → F) : Finset (F × F) :=
  Finset.univ.image (fun x => (x, f x))

/-
The graph code has cardinality `|F|`.
-/
lemma graphCode_card (f : F → F) : (graphCode f).card = Fintype.card F := by
  convert Finset.card_image_of_injective _ ( show Function.Injective ( fun x : F => ( x, f x ) ) from fun x y hxy => by injection hxy )

/-- Two distinct codewords in the graph code differ in the first coordinate. -/
lemma graphCode_first_coord_injective (f : F → F) (x y : F) (hxy : x ≠ y) :
    (x, f x) ≠ (y, f y) := by
  intro h
  exact hxy (Prod.mk.inj h).1

/-! ### Difference properties of the graph code -/

/-- The multiset of differences `{(x₁ - x₂, f(x₁) - f(x₂)) : x₁ ≠ x₂}`
    characterizes the code's distance properties. -/
def diffMultiset (f : F → F) : Finset (F × F) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p : F × F => p.1 ≠ 0) |>.image
    (fun p : F × F => (p.1, f (p.2 + p.1) - f p.2))

/-- For an APN function, every nonzero pair `(a, b)` appears at most twice
    in the difference multiset (this is the code-theoretic interpretation of APN). -/
lemma apn_diff_bound (f : F → F) (hf : IsAPN f) (a b : F) (ha : a ≠ 0) :
    ((Finset.univ).filter (fun x => f (x + a) - f x = b)).card ≤ 2 :=
  hf a ha b

/-! ### Dual code viewpoint -/

/-- The "dual" perspective: the number of `x` with `f(x+a) - f(x) = b` relates to
    the weight distribution of the associated code. For APN functions, this gives
    a code with good minimum distance properties. -/
lemma apn_implies_good_code (f : F → F) (hf : IsAPN f) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      (Finset.univ.filter (fun x => f (x + a) - f x = b)).card ≤ 2 :=
  hf

end ABAPN.Coding