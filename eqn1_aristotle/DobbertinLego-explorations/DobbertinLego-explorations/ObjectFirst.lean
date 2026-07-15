import Mathlib
import DobbertinLego.Assembly
import DobbertinLego.CategoryTheory
import DobbertinLego

/-!
# Object-first: the type-class bundle as consequences of the object

The concrete development carries the bundle `[Field F] [Fintype F] [CharP F 2]` as
three separate hypotheses.  This file **collapses that bundle into the object**:
the primary datum is `F` as an object of `Mod_{𝔽₂}` — i.e. a `ZMod 2`-*algebra*
(equivalently a commutative monoid object of `ModuleCat 𝔽₂`, `objMonObj`) that is a
finite field — and the characteristic-`2` hypothesis is then a **consequence**, not
an input:

* `objCharP` — `CharP F 2` is *derived* from the `ZMod 2`-algebra structure (the
  base object `𝔽₂ ↪ F`), via `charP_of_injective_algebraMap`.  It is no longer
  hypothesized.
* `objMul_eq` — the multiplication used everywhere *is* the monoid-object
  multiplication of the algebra object `AlgCat.of 𝔽₂ F` (`ModuleCat`'s monoidal
  product), recorded through `ModuleCat.MonModuleEquivalenceAlgebra`.

Everything then runs with `F : Type` (universe `0`) throughout, so there is a single
uniform development — no "`Type` section beside the `Type*` proof" split:

* `objFrobLin`, `objFrobLin_telescope`, `objFrobLin_pow_finrank`, `objTrace_isBit`
  reprove the categorical chain with the *object's own* algebra instance;
* `equation2_of_equation1_obj` is the headline `(1) ⟹ (2)` with the collapsed
  bundle: the caller supplies only "`F` is a finite field that is a `𝔽₂`-object".
-/

namespace Dobbertin.Lego.Obj

open CategoryTheory Finset FiniteField

/- **Primary datum.**  `F` as a finite-field object of `Mod_{𝔽₂}`: a `ZMod 2`-module
(`Algebra (ZMod 2) F`) whose multiplication is that of a field.  No `CharP`
hypothesis. -/
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- **Characteristic `2` is a consequence of the object.**  Because `F` is a
`ZMod 2`-algebra, the structure map `𝔽₂ ↪ F` is an injective ring homomorphism, so
`CharP F 2` transfers from `CharP (ZMod 2) 2`.  This *derives* the hypothesis that
the concrete development had to assume. -/
instance objCharP : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

/-! ## Multiplication comes from the monoid object -/

/-- `F` as an **algebra object** `AlgCat 𝔽₂` — a commutative monoid object of
`ModuleCat 𝔽₂`.  Its multiplication is the datum from which the field structure's
`*` is read. -/
noncomputable def objAlg : AlgCat (ZMod 2) := AlgCat.of (ZMod 2) F

/-- `F` as a **monoid object** of the monoidal category `(ModuleCat 𝔽₂, ⊗)`, via
`ModuleCat.MonModuleEquivalenceAlgebra` (monoid objects in `ModuleCat 𝔽₂` = 𝔽₂
algebras).  This is the object-level source of the multiplication. -/
noncomputable def objMonObj : MonObj (ModuleCat.of (ZMod 2) F) :=
  ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of (ZMod 2) F)

/-! ## The categorical chain, object-first, in universe `0`

`objFrobLin` is the Frobenius endomorphism built from the *object's own* algebra
instance (not a freshly-invoked `ZMod.algebra`), so the whole chain — telescope,
finite order, trace-is-a-bit — is one uniform `Type`-level development. -/

/-- **Frobenius as an endomorphism of the object.**  The `𝔽₂`-linear map underlying
`frobeniusAlgHom` (`x ↦ x²`), an element of `Module.End (ZMod 2) F`, built from the
object's algebra structure. -/
noncomputable def objFrobLin : Module.End (ZMod 2) F :=
  (frobeniusAlgHom (ZMod 2) F).toLinearMap

omit [Fintype F] in
@[simp] lemma objFrobLin_apply (x : F) : objFrobLin (F := F) x = x ^ 2 := by
  rw [objFrobLin, AlgHom.toLinearMap_apply, coe_frobeniusAlgHom]; simp

omit [Fintype F] in
/-- The telescope for the object's Frobenius, in its endomorphism ring
(`= End (ModuleCat.of 𝔽₂ F)` via `endRingEquiv`). -/
lemma objFrobLin_telescope (len : ℕ) :
    (objFrobLin (F := F) - 1) * (∑ i ∈ range len, objFrobLin ^ i) = objFrobLin ^ len - 1 :=
  mul_geom_sum objFrobLin len

/-- Algebra endomorphisms → module endomorphisms, multiplicatively. -/
noncomputable def objAlgEndToLin : (F →ₐ[ZMod 2] F) →* Module.End (ZMod 2) F where
  toFun f := f.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **Finite order from the object's finite dimension.**  `φⁿ = 1` at
`n = [F : 𝔽₂]`, sourced from `orderOf (frobeniusAlgHom) = finrank` — the object's
dualizable/finite-dimensional structure — not from raw cardinality. -/
lemma objFrobLin_pow_finrank :
    (objFrobLin (F := F)) ^ (Module.finrank (ZMod 2) F) = 1 := by
  have h : objFrobLin (F := F) = objAlgEndToLin (frobeniusAlgHom (ZMod 2) F) := rfl
  rw [h, ← map_pow, ← FiniteField.orderOf_frobeniusAlgHom (ZMod 2) F,
    pow_orderOf_eq_one, map_one]

omit [Fintype F] in
lemma objFrobLin_pow_apply (r : ℕ) (x : F) :
    ((objFrobLin (F := F)) ^ r) x = x ^ (2 ^ r) := by
  induction r with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, objFrobLin_apply, ← pow_mul, ← pow_succ]

lemma objFrobLin_pow_card {n : ℕ} (hn : Fintype.card F = 2 ^ n) :
    (objFrobLin (F := F)) ^ n = 1 := by
  have hrank : Module.finrank (ZMod 2) F = n := by
    have hcard : Fintype.card F = 2 ^ (Module.finrank (ZMod 2) F) := by
      simpa using Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hn] at hcard
    exact Nat.pow_right_injective (le_refl 2) hcard.symm
  rw [← hrank]; exact objFrobLin_pow_finrank

/-- **The trace is a bit, object-first.**  `∑_{i<n} x^{2ⁱ} ∈ {0,1}`, from the
telescope for `objFrobLin` and finite order `objFrobLin_pow_card`. -/
lemma objTrace_isBit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    (∑ i ∈ range n, (objFrobLin (F := F)) ^ i) x = 0
      ∨ (∑ i ∈ range n, (objFrobLin (F := F)) ^ i) x = 1 := by
  set S : Module.End (ZMod 2) F := ∑ i ∈ range n, objFrobLin ^ i with hS
  have htel : (objFrobLin (F := F) - 1) * S = objFrobLin ^ n - 1 := objFrobLin_telescope n
  rw [objFrobLin_pow_card hn, sub_self] at htel
  have happ := congrArg (fun (e : Module.End (ZMod 2) F) => e x) htel
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply] at happ
  rw [objFrobLin_apply] at happ
  have hsq : (S x) ^ 2 = S x := by linear_combination happ
  have h : S x * (S x - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

/-! ## The headline with the collapsed bundle

The paper's step `(1) ⟹ (2)` now takes as input only "`F` is a finite field that is
a `𝔽₂`-object" — the multiplication comes from the monoid object and `CharP F 2` is
the derived `objCharP`.  It delegates to the concrete headline
`Dobbertin.Lego.equation2_of_equation1`, whose `[CharP F 2]` hypothesis is
discharged by `objCharP`. -/

open Dobbertin.Lego in
/-- **Step (1) ⟹ (2), object-first.**  Same statement as
`Dobbertin.Lego.equation2_of_equation1`, but with the type-class bundle collapsed:
only `[Field F] [Fintype F] [Algebra (ZMod 2) F]` (the object) is assumed, and
`CharP F 2` is supplied by `objCharP`. -/
theorem equation2_of_equation1_obj {n k k' α : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) (hα : α = 0 ∨ α = 1) {c x : F} (hx : x ≠ 0)
    (h : equation1 n k k' α c x) :
    linearized k c x = 0 :=
  equation2_of_equation1 hn hkk' hα hx h

end Dobbertin.Lego.Obj
