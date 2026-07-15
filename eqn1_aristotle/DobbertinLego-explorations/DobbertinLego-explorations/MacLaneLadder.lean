import Mathlib

/-!
# A MacLane-style build of the enrichment ladder

Instead of *assuming* `[Field F] [Fintype F]`, we start from the bare definition of
a category and add one axiom per rung, until the telescope and `φⁿ = 1` fall out of
the *object's* structure:

```
   Category → Ab-enriched (Preadditive) → ModuleCat 𝔽₂ → monoid object → FGModuleCat 𝔽₂
```

* **Rung 1 — Ab.**  In a `Preadditive` category, `End X` is a ring, and the
  telescope `(φ − 1)·Σφⁱ = φⁿ − 1` is the geometric series (`telescope`).  No field,
  no characteristic, no finiteness.
* **Rung 2 — `ModuleCat 𝔽₂`.**  The Frobenius is an actual arrow
  `frob ∈ Module.End (ZMod 2) R`; additivity is `map_add` (the freshman's dream),
  and the telescope is Rung 1 read in this endomorphism ring (`frobArrow_telescope`).
* **Rung 3 — commutative monoid object.**  A monoid object of `(ModuleCat 𝔽₂, ⊗)` is
  an `𝔽₂`-algebra, which is *why* `x ↦ x²` is a morphism at all (`monObj`).
* **Rung 4 — dualizable / finite (`FGModuleCat 𝔽₂`).**  A finite-dimensional object
  has a dual; `Fintype F` and `CharP F 2` are *derived* from
  `[Module.Finite (ZMod 2) F]`, and `orderOf φ = finrank` gives `φⁿ = 1`
  (`frob_pow_finrank`), whence the norm element is a bit (`norm_isBit`).
-/

namespace Dobbertin.Lego.MacLane

open CategoryTheory Finset FiniteField

/-! ## Rung 1 — a category, Ab-enriched -/

theorem telescope {C : Type*} [Category C] [Preadditive C] {X : C}
    (φ : End X) (n : ℕ) :
    (φ - 1) * ∑ i ∈ range n, φ ^ i = φ ^ n - 1 :=
  mul_geom_sum φ n

/-! ## Rung 2 — `ModuleCat 𝔽₂` -/

section Mod
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R] [CharP R 2]

noncomputable def frob : Module.End (ZMod 2) R where
  toFun x := x ^ 2
  map_add' x y := by simpa using add_pow_char (R := R) (p := 2) x y
  map_smul' r x := by
    simp only [RingHom.id_apply, Algebra.smul_def, mul_pow, ← map_pow]
    rw [ZMod.pow_card r]

@[simp] lemma frob_apply (x : R) : frob x = x ^ 2 := rfl

lemma frob_add (x y : R) : frob (R := R) (x + y) = frob x + frob y := map_add _ _ _

lemma frob_pow_apply (r : ℕ) (x : R) : (frob (R := R) ^ r) x = x ^ (2 ^ r) := by
  induction r with
  | zero => simp
  | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, frob_apply, ← pow_mul, ← pow_succ]

lemma frob_telescope (n : ℕ) :
    (frob (R := R) - 1) * ∑ i ∈ range n, frob ^ i = frob ^ n - 1 :=
  mul_geom_sum _ n

noncomputable def frobArrow : End (ModuleCat.of (ZMod 2) R) :=
  (ModuleCat.endRingEquiv _).symm (frob (R := R))

@[simp] lemma endRingEquiv_frobArrow :
    ModuleCat.endRingEquiv _ (frobArrow (R := R)) = frob (R := R) := by
  simp [frobArrow]

lemma frobArrow_telescope (n : ℕ) :
    (frobArrow (R := R) - 1) * ∑ i ∈ range n, frobArrow ^ i = frobArrow ^ n - 1 :=
  telescope frobArrow n

end Mod

/-! ## Rung 3 — commutative monoid object of `(ModuleCat 𝔽₂, ⊗)` -/

section Mon
variable {R : Type} [CommRing R] [Algebra (ZMod 2) R]

noncomputable def monObj : MonObj (ModuleCat.of (ZMod 2) R) :=
  ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of (ZMod 2) R)

end Mon

/-! ## Rung 4 — dualizable / finite: `FGModuleCat 𝔽₂` -/

section FG
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [Module.Finite (ZMod 2) F]

instance : Finite F := Module.finite_of_finite (ZMod 2)
noncomputable instance : Fintype F := Fintype.ofFinite F
instance : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

noncomputable def fgObj : FGModuleCat (ZMod 2) := FGModuleCat.of (ZMod 2) F

noncomputable def fgObj_hasRightDual : HasRightDual (fgObj (F := F)) :=
  inferInstanceAs (HasRightDual (FGModuleCat.of (ZMod 2) F))

noncomputable def algEndToLin : (F →ₐ[ZMod 2] F) →* Module.End (ZMod 2) F where
  toFun f := f.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Module.Finite (ZMod 2) F] in
lemma frob_eq_frobenius : frob (R := F) = algEndToLin (frobeniusAlgHom (ZMod 2) F) := by
  ext x; show x ^ 2 = _; rw [algEndToLin]; simp

lemma frob_orderOf :
    orderOf (frobeniusAlgHom (ZMod 2) F) = Module.finrank (ZMod 2) F :=
  FiniteField.orderOf_frobeniusAlgHom (ZMod 2) F

lemma frob_pow_finrank : (frob (R := F)) ^ (Module.finrank (ZMod 2) F) = 1 := by
  rw [frob_eq_frobenius, ← map_pow, ← frob_orderOf, pow_orderOf_eq_one, map_one]

lemma norm_isBit (x : F) :
    (∑ i ∈ range (Module.finrank (ZMod 2) F), frob (R := F) ^ i) x = 0
      ∨ (∑ i ∈ range (Module.finrank (ZMod 2) F), frob (R := F) ^ i) x = 1 := by
  set S : Module.End (ZMod 2) F := ∑ i ∈ range (Module.finrank (ZMod 2) F), frob ^ i with hS
  have htel : (frob (R := F) - 1) * S = frob ^ (Module.finrank (ZMod 2) F) - 1 :=
    mul_geom_sum _ _
  rw [frob_pow_finrank, sub_self] at htel
  have happ := congrArg (fun (e : Module.End (ZMod 2) F) => e x) htel
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply] at happ
  rw [frob_apply] at happ
  have hsq : (S x) ^ 2 = S x := by linear_combination happ
  have h : S x * (S x - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

end FG

end Dobbertin.Lego.MacLane
