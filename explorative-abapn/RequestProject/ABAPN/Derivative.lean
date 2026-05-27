/-
# Discrete Derivative / Difference Operator

Algebraic properties of the discrete derivative `Δ_a f(x) = f(x+a) - f(x)`.
Built on `AddMonoidHom`, `Function.Injective`, `Finset` arithmetic.

Key identities:
- Δ_0 f = 0
- Δ_a (f + g) = Δ_a f + Δ_a g  (linearity)
- Δ_a (c • f) = c • Δ_a f
- Δ_a (Δ_b f)(x) = f(x+a+b) - f(x+a) - f(x+b) + f(x)  (second derivative)
- Δ_a id = const a
-/
import Mathlib
import RequestProject.ABAPN.Defs

open Finset Function ABAPN

namespace ABAPN.Derivative

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Zero direction -/

/-- The derivative in direction 0 is the zero function. -/
@[simp]
lemma diffMap_zero (f : F → F) (x : F) : diffMap f 0 x = 0 := by
  simp [diffMap]

/-
deltaCount with a = 0 and b = 0 equals the cardinality of F.
-/
lemma deltaCount_zero_zero (f : F → F) : deltaCount f 0 0 = Fintype.card F := by
  simp +decide [ sub_self ]

/-
deltaCount with a = 0 and b ≠ 0 equals 0.
-/
lemma deltaCount_zero_ne (f : F → F) (b : F) (hb : b ≠ 0) : deltaCount f 0 b = 0 := by
  simp_all +decide [ deltaCount ];
  exact fun h => False.elim ( hb h.symm )

/-! ### Linearity of the difference operator -/

/-
The difference operator is additive in the function argument.
-/
lemma diffMap_add (f g : F → F) (a x : F) :
    diffMap (f + g) a x = diffMap f a x + diffMap g a x := by
  unfold diffMap; ring;
  simp +decide only [Pi.add_apply, add_sub_add_comm]

/-
The difference operator commutes with scalar multiplication.
-/
lemma diffMap_smul (c : F) (f : F → F) (a x : F) :
    diffMap (c • f) a x = c * diffMap f a x := by
  unfold diffMap; simp +decide [ mul_sub ] ;

/-- Difference of a constant function is zero. -/
@[simp]
lemma diffMap_const (c : F) (a x : F) : diffMap (fun _ => c) a x = 0 := by
  simp [diffMap]

/-- Difference of the identity function is the constant `a`. -/
@[simp]
lemma diffMap_id (a x : F) : diffMap id a x = a := by
  simp [diffMap]

/-! ### Second-order difference -/

/-- The second-order discrete derivative. -/
def diffMap₂ (f : F → F) (a b : F) (x : F) : F :=
  diffMap (diffMap f a) b x

/-
Expansion of the second-order derivative.
-/
lemma diffMap₂_eq (f : F → F) (a b x : F) :
    diffMap₂ f a b x = f (x + b + a) - f (x + b) - f (x + a) + f (x) := by
  convert sub_sub _ _ _ using 1;
  unfold diffMap; ring;

/-
The second-order derivative is symmetric in `a` and `b`.
-/
lemma diffMap₂_comm (f : F → F) (a b x : F) :
    diffMap₂ f a b x = diffMap₂ f b a x := by
  rw [ diffMap₂_eq, diffMap₂_eq ] ; ring

/-! ### Additivity of the derivative in the direction -/

/-
Key identity: `Δ_{a+b} f(x) = Δ_a f(x+b) + Δ_b f(x)`
-/
lemma diffMap_add_dir (f : F → F) (a b x : F) :
    diffMap f (a + b) x = diffMap f a (x + b) + diffMap f b x := by
  unfold diffMap; ring;

/-! ### Derivative and composition -/

/-
If `σ` is an additive automorphism, then `Δ_a (σ ∘ f) = σ ∘ (Δ_a f)`.
-/
lemma diffMap_comp_addHom (σ : F →+ F) (f : F → F) (a x : F) :
    diffMap (σ ∘ f) a x = σ (diffMap f a x) := by
  unfold diffMap; simp +decide [ sub_eq_add_neg, map_add, map_neg ] ;

/-! ### Counting: sum of deltaCount over b -/

/-
The sum of `deltaCount f a b` over all `b` equals `|F|` (each `x` contributes to exactly one `b`).
-/
lemma sum_deltaCount_eq_card (f : F → F) (a : F) :
    ∑ b : F, deltaCount f a b = Fintype.card F := by
  simp +decide only [deltaCount, deltaSet];
  simp +decide only [card_filter];
  rw [ Finset.sum_comm ] ; aesop

/- Note: The statement "f bijective implies diffMap f a surjective for a ≠ 0" is FALSE.
   Counterexample: f = id is bijective but diffMap id a = const a, which is not surjective.
   The correct relationship involves APN/PN properties, not just bijectivity. -/

end ABAPN.Derivative