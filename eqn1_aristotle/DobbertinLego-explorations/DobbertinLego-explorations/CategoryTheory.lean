import Mathlib
import DobbertinLego.Endo
import DobbertinLego.Frobenius
import DobbertinLego.Loop
import DobbertinLego.Assembly

/-!
# Building the step `(1) ⟹ (2)` from categorical patterns

This file *rebuilds* the load-bearing algebra of the first step of Dobbertin's
Theorem 1 using Mathlib's `CategoryTheory` / monoidal-category vocabulary, along
the enrichment ladder identified in the discussion:

```
      Ab  ⟶  Mod_{𝔽₂}  ⟶  commutative monoid object  ⟶  dualizable / finite
```

Each rung *removes* an input by promoting it to structure of the ambient object:

* **Ab (preadditive).**  The telescope `(φ−1)·∑φⁱ = φⁿ−1` is a fact about the
  endomorphism **ring** `End X` of an object of any preadditive (Ab-enriched)
  category.  Additivity of an endomorphism is free there; char 2 is *not* needed.
  → `preadditive_telescope`.
* **Mod_{𝔽₂}.**  Working over the base object `𝔽₂ = ZMod 2` makes Frobenius a
  **morphism of 𝔽₂-modules**: `frobLin = (frobeniusAlgHom (ZMod 2) F).toLinearMap`
  is an element of the endomorphism ring `Module.End (ZMod 2) F`, and its
  additivity is `map_add` — the char-2 freshman's dream, now *free* from the
  algebra structure rather than an input.  → `frobLin`, `frobLin_add`.
* **Commutative monoid object.**  A commutative monoid object in
  `(ModuleCat 𝔽₂, ⊗)` is exactly a commutative 𝔽₂-algebra
  (`ModuleCat.monModuleEquivalenceAlgebra`); `F` is one, which is *why* squaring
  `x ↦ x²` is a ring/algebra map at all.  → `FasMonObj`, `frobLin_eq_frobeniusAlgHom`.
* **Dualizable / finite.**  A finite field is a finite-dimensional, hence
  **dualizable** object of the right-rigid category `FGModuleCat 𝔽₂`; finiteness
  is what forces `φⁿ = 1` (Fermat) and provides the evaluation/coevaluation trace.
  → `FasFGModule`, `frobLin_hasRightDual`, `frobLin_pow_card`, `frobLin_orderOf`.

The two arithmetic inputs (`trace_isBit_cat`, `partialTrace_telescope_cat`) and the
headline (`equation2_of_equation1_cat`) are then reassembled purely from the
preadditive telescope applied to `frobLin` (and `frobLin ^ k`), with Fermat coming
from finiteness — recovering the same statements proved concretely in
`DobbertinLego.lean`.
-/

namespace Dobbertin.Lego.Cat

open CategoryTheory Finset FiniteField

/-! ## Rung 1 — Ab: the telescope lives in the endomorphism ring of a preadditive object

In any preadditive (Ab-enriched) category the endomorphisms `End X` of an object
form a **ring** (composition = multiplication, `𝟙 X = 1`).  The whole
Artin–Schreier telescope is the geometric-series identity in that ring; it needs
nothing about fields, characteristic, or finiteness. -/

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] (X : C)

/-- **The telescope is Ab-level.**  In the endomorphism ring `End X` of an object
of a preadditive category, `(φ − 1) · (∑_{i<len} φⁱ) = φ^len − 1` — the geometric
series / additive Hilbert 90.  Multiplication is composition, `1` is `𝟙 X`.  This
is the abstract shape of every telescoping step below. -/
theorem preadditive_telescope (φ : End X) (len : ℕ) :
    (φ - 1) * (∑ i ∈ range len, φ ^ i) = φ ^ len - 1 :=
  mul_geom_sum φ len

end Preadditive

/-! ## Rungs 2–4 specialized to `F = 𝔽_{2ⁿ}`

We fix a finite field `F` of characteristic `2` and make it a `ZMod 2`-algebra,
i.e. a module over the base object `𝔽₂ = ZMod 2`. -/

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The base object `𝔽₂ = ZMod 2`: `F` is a `ZMod 2`-algebra (a `𝔽₂`-module with a
compatible multiplication).  This is the "work over `Mod_{𝔽₂}`" step. -/
noncomputable local instance zmod2Alg : Algebra (ZMod 2) F := ZMod.algebra F 2

/-! ### Rung 2 — Mod_{𝔽₂}: Frobenius is a morphism of 𝔽₂-modules

Over the base `𝔽₂` the Frobenius is not a bare map with a hand-proved additivity:
it is Mathlib's `frobeniusAlgHom (ZMod 2) F : F →ₐ[ZMod 2] F` (an *algebra* map,
`x ↦ x^{#𝔽₂} = x²`), whose underlying `𝔽₂`-linear map is an element of the
endomorphism ring `Module.End (ZMod 2) F`.  Its additivity is `map_add` — the
char-2 freshman's dream, now *free* from the algebra/monoid-object structure. -/

/-- **Frobenius as an endomorphism of the 𝔽₂-module `F`.**  The `𝔽₂`-linear map
underlying `frobeniusAlgHom`, `x ↦ x²`, as an element of the ring
`Module.End (ZMod 2) F`. -/
noncomputable def frobLin : Module.End (ZMod 2) F :=
  (frobeniusAlgHom (ZMod 2) F).toLinearMap

omit [Fintype F] in
/-- `frobLin` is the squaring map `x ↦ x²`. -/
@[simp] lemma frobLin_apply (x : F) : frobLin (F := F) x = x ^ 2 := by
  rw [frobLin, AlgHom.toLinearMap_apply, coe_frobeniusAlgHom]; simp

omit [Fintype F] in
/-- **Additivity is free.**  `frobLin` is a module morphism, so
`frobLin (x + y) = frobLin x + frobLin y` is `map_add` — the freshman's dream is
supplied by the `Mod_{𝔽₂}` structure, not proved by hand. -/
lemma frobLin_add (x y : F) : frobLin (F := F) (x + y) = frobLin x + frobLin y :=
  map_add _ _ _

omit [Fintype F] in
/-- **The endomorphism ring is the module object's `End`.**  The ring
`Module.End 𝔽₂ F` in which `frobLin` and the telescope live is, via
`ModuleCat.endRingEquiv`, the very endomorphism ring `End (ModuleCat.of 𝔽₂ F)` of
the `Mod_{𝔽₂}` object.  So the identities below are `preadditive_telescope`
read through this ring isomorphism. -/
noncomputable def endRing_iso :
    CategoryTheory.End (ModuleCat.of (ZMod 2) F) ≃+* Module.End (ZMod 2) F :=
  ModuleCat.endRingEquiv _

omit [Fintype F] in
/-- **The telescope for `frobLin`** — `preadditive_telescope` realized in the
endomorphism ring `Module.End 𝔽₂ F` (see `endRing_iso`):
`(frobLin − 1)·(∑ frobLinⁱ) = frobLin^len − 1`. -/
lemma frobLin_telescope (len : ℕ) :
    (frobLin (F := F) - 1) * (∑ i ∈ range len, frobLin ^ i) = frobLin ^ len - 1 :=
  mul_geom_sum frobLin len

/-! ### Frobenius as internal arrow data

Rather than a bare `Module.End`, the Frobenius is genuinely an **arrow** of the
category `ModuleCat 𝔽₂`: the morphism `frobMor : ModuleCat.of 𝔽₂ F ⟶ ModuleCat.of 𝔽₂ F`,
i.e. an element of `End (ModuleCat.of 𝔽₂ F)`.  It is the preimage of `frobLin` under
the ring isomorphism `endRingEquiv` (`endRing_iso`), so the telescope can be run
*inside* the categorical endomorphism ring `End X` and then transported. -/

omit [Fintype F] in
/-- **Frobenius as an arrow.**  The categorical morphism
`frobMor : ModuleCat.of 𝔽₂ F ⟶ ModuleCat.of 𝔽₂ F` underlying `frobLin`, i.e. the
preimage of `frobLin` under `ModuleCat.endRingEquiv`.  This is `frobLin` as literal
arrow data of the `Mod_{𝔽₂}` object. -/
noncomputable def frobMor : CategoryTheory.End (ModuleCat.of (ZMod 2) F) :=
  (endRing_iso (F := F)).symm frobLin

omit [Fintype F] in
/-- `endRingEquiv` (`endRing_iso`) carries the arrow `frobMor` back to `frobLin`. -/
@[simp] lemma endRing_iso_frobMor :
    endRing_iso (F := F) (frobMor (F := F)) = frobLin := by
  simp [frobMor, endRing_iso]

omit [Fintype F] in
/-- **The telescope as arrow data.**  Run entirely inside the categorical
endomorphism ring `End (ModuleCat.of 𝔽₂ F)`:
`(frobMor − 𝟙) ∘ (∑ frobMorⁱ) = frobMor^len − 𝟙`.  This is `preadditive_telescope`
for the object `ModuleCat.of 𝔽₂ F`; `endRing_iso` transports it to
`frobLin_telescope`. -/
lemma frobMor_telescope (len : ℕ) :
    (frobMor (F := F) - 1) * (∑ i ∈ range len, frobMor ^ i) = frobMor ^ len - 1 :=
  preadditive_telescope (ModuleCat.of (ZMod 2) F) frobMor len

omit [Fintype F] in
/-- Iterated Frobenius: `frobLinʳ x = x^{2ʳ}` — the `r`-fold "doubling on the
exponent", read as a power in the endomorphism ring. -/
lemma frobLin_pow_apply (r : ℕ) (x : F) : ((frobLin (F := F)) ^ r) x = x ^ (2 ^ r) := by
  induction r with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, frobLin_apply, ← pow_mul, ← pow_succ]

omit [Fintype F] in
/-- `frobLinʳ` agrees with the concrete Frobenius brick `frob r` of
`DobbertinLego/Frobenius`. -/
lemma frobLin_pow_eq_frob (r : ℕ) (x : F) : ((frobLin (F := F)) ^ r) x = frob r x := by
  rw [frobLin_pow_apply, frob]

/-! ### Rung 4 — finite / dualizable: `φⁿ = 1` is finite order, not raw cardinality

A finite field is a finite-*dimensional* 𝔽₂-vector space, i.e. a **dualizable**
object of `FGModuleCat 𝔽₂`.  It is that finite dimension — the rank of the dual —
that forces the Frobenius to have finite order `φⁿ = 1`, with `n = [F : 𝔽₂]` the
dimension of the object.

The identity `φⁿ = 1` is therefore obtained here from the **order** of the
Frobenius (`frobLin_orderOf`: `orderOf φ = [F:𝔽₂]`, via
`FiniteField.orderOf_frobeniusAlgHom`) rather than from raw Fermat
(`FiniteField.pow_card`).  Concretely, `φ` is the image of the algebra
automorphism `frobeniusAlgHom` under the multiplicative map `algEndToLin`, so
`φ^{orderOf} = 1` transports to `φⁿ = 1`; the annihilating polynomial `Xⁿ − 1`
(`frobLin_pow_finrank`) is thus read off the object's dimension. -/

omit [Fintype F] in
/-- **Algebra endomorphisms → module endomorphisms, multiplicatively.**  The map
sending an algebra automorphism `f : F →ₐ[𝔽₂] F` to its underlying 𝔽₂-linear
endomorphism is a *monoid* homomorphism `(F →ₐ[𝔽₂] F) →* Module.End 𝔽₂ F`
(composition ↦ composition, `id ↦ 1`).  It carries `frobeniusAlgHom` to `frobLin`,
so order and powers of the two agree. -/
noncomputable def algEndToLin : (F →ₐ[ZMod 2] F) →* Module.End (ZMod 2) F where
  toFun f := f.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Fintype F] in
@[simp] lemma algEndToLin_frobeniusAlgHom :
    algEndToLin (frobeniusAlgHom (ZMod 2) F) = frobLin (F := F) := rfl

/-- **Finite order = dimension.**  The Frobenius algebra endomorphism has order
`[F : 𝔽₂]` — the categorical "finite order from dualizability/finiteness" fact
(`FiniteField.orderOf_frobeniusAlgHom`).  This, not cardinality, is the source of
`φⁿ = 1`. -/
lemma frobLin_orderOf :
    orderOf (frobeniusAlgHom (ZMod 2) F) = Module.finrank (ZMod 2) F :=
  FiniteField.orderOf_frobeniusAlgHom (ZMod 2) F

/-- The dimension `[F : 𝔽₂]` is the exponent `n` (`#F = 2ⁿ`). -/
lemma finrank_eq {n : ℕ} (hn : Fintype.card F = 2 ^ n) : Module.finrank (ZMod 2) F = n := by
  have hcard : Fintype.card F = 2 ^ (Module.finrank (ZMod 2) F) := by
    simpa using Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [hn] at hcard
  exact Nat.pow_right_injective (le_refl 2) hcard.symm

/-- **`Xⁿ − 1` from the dimension.**  At the object's own dimension
`n = [F : 𝔽₂]`, the Frobenius satisfies `φⁿ = 1`, i.e. it is annihilated by
`Xⁿ − 1`.  Proof: `φ = algEndToLin (frobeniusAlgHom)`, whose order is exactly the
dimension (`frobLin_orderOf`), so `pow_orderOf_eq_one` transports across the monoid
map — no appeal to `FiniteField.pow_card`. -/
lemma frobLin_pow_finrank : (frobLin (F := F)) ^ (Module.finrank (ZMod 2) F) = 1 := by
  rw [← algEndToLin_frobeniusAlgHom, ← map_pow, ← frobLin_orderOf, pow_orderOf_eq_one,
    map_one]

/-- **`φⁿ = 1`.**  On `𝔽_{2ⁿ}` the `n`-fold Frobenius is the identity of the
endomorphism ring.  Now sourced from finite dimension (`frobLin_pow_finrank`,
`finrank_eq`), i.e. from the object being a dualizable / finite-dimensional
`FGModuleCat 𝔽₂`, rather than from raw cardinality Fermat. -/
lemma frobLin_pow_card {n : ℕ} (hn : Fintype.card F = 2 ^ n) : (frobLin (F := F)) ^ n = 1 := by
  rw [← finrank_eq hn]; exact frobLin_pow_finrank

/-! ## Rung 3 — commutative monoid object, and the dualizable/rigid picture

These statements are honest realizations of the two structural rungs as
`CategoryTheory` objects.  They need the base object and `F` in the same universe,
so this section fixes `F : Type`. -/

section Objects

open MonoidalCategory

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

noncomputable local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- **Rung 3.**  `F` as a **commutative monoid object** in the monoidal category
`(ModuleCat 𝔽₂, ⊗)`.  Via `ModuleCat.monModuleEquivalenceAlgebra`, monoid objects
in `ModuleCat 𝔽₂` are exactly 𝔽₂-algebras; this is the object structure that makes
`x ↦ x²` an algebra map (hence `frobLin` well-defined). -/
noncomputable def FasMonObj : MonObj (ModuleCat.of (ZMod 2) F) :=
  ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of (ZMod 2) F)

/-- `F` as an object of `FGModuleCat 𝔽₂`, the category of finite-dimensional
𝔽₂-vector spaces. -/
noncomputable def FasFGModule : FGModuleCat (ZMod 2) := FGModuleCat.of (ZMod 2) F

/-- **Rung 4.**  `FGModuleCat 𝔽₂` is right-rigid, so `F` is a **dualizable** object:
it has a right dual, with the evaluation/coevaluation maps that produce the
categorical trace.  (The paper's absolute trace `Tr` is, via
`DobbertinLego.Categorical.trace_eq_algebraMap_trace`, exactly Mathlib's
`Algebra.trace 𝔽₂ F`.) -/
noncomputable def FasFGModule_hasRightDual : HasRightDual (FasFGModule (F := F)) :=
  inferInstanceAs (HasRightDual (FGModuleCat.of (ZMod 2) F))

end Objects

/-! ## Assembly — the arithmetic inputs and headline, rebuilt from the telescope

`trace n x = ∑_{i<n} frobLinⁱ x` and `partialTrace k k' x = ∑_{j<k'} (frobLinᵏ)ʲ x`
are the norm elements of `frobLin` and `frobLin ^ k`; applying
`preadditive_telescope` (i.e. `mul_geom_sum`) recovers the two facts the paper
uses. -/

open Dobbertin.Lego

omit [Fintype F] in
/-- `trace n x` is the norm element of `frobLin`, evaluated at `x`. -/
lemma trace_eq (n : ℕ) (x : F) :
    trace n x = (∑ i ∈ range n, (frobLin (F := F)) ^ i) x := by
  rw [trace, loop, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [frobLin_pow_eq_frob, mul_one])

omit [Fintype F] in
/-- `partialTrace k k' x` is the norm element of `frobLin ^ k`, evaluated at `x`. -/
lemma partialTrace_eq (k k' : ℕ) (x : F) :
    partialTrace k k' x = (∑ j ∈ range k', ((frobLin (F := F)) ^ k) ^ j) x := by
  rw [partialTrace, loop, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← pow_mul, frobLin_pow_eq_frob, Nat.mul_comm]

/-- **The trace is a bit — categorical proof.**  `Tr(x) ∈ {0,1}`, obtained from the
preadditive telescope: `(frobLin − 1)·(∑ frobLinⁱ) = frobLinⁿ − 1 = 0` by Fermat,
so `Tr(x)² = Tr(x)`. -/
lemma trace_isBit_cat {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    trace n x = 0 ∨ trace n x = 1 := by
  rw [trace_eq]
  set S : Module.End (ZMod 2) F := ∑ i ∈ range n, frobLin ^ i with hS
  have htel : (frobLin (F := F) - 1) * S = frobLin ^ n - 1 := frobLin_telescope n
  rw [frobLin_pow_card hn, sub_self] at htel
  have happ := congrArg (fun (e : Module.End (ZMod 2) F) => e x) htel
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply] at happ
  rw [frobLin_apply] at happ
  have hsq : (S x) ^ 2 = S x := by linear_combination happ
  have h : S x * (S x - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

/-- **Artin–Schreier telescope — categorical proof.**  `S(x) + P(x) = x² + x`, from
the preadditive telescope for `φ = frobLin ^ k`: `(φ − 1)·(∑ φʲ) = φ^{k'} − 1`,
with `φ(P) = S` (`= P^{2ᵏ}`) and `φ^{k'} x = x²` by periodicity `k·k' ≡ 1 (mod n)`. -/
lemma partialTrace_telescope_cat {n k k' : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) (x : F) :
    numeratorSum k k' x + partialTrace k k' x = x ^ 2 + x := by
  set ψ : Module.End (ZMod 2) F := frobLin ^ k with hψ
  have htel : (ψ - 1) * (∑ j ∈ range k', ψ ^ j) = ψ ^ k' - 1 := mul_geom_sum ψ k'
  have happ := congrArg (fun (e : Module.End (ZMod 2) F) => e x) htel
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at happ
  rw [← partialTrace_eq] at happ
  have hψP : ψ (partialTrace k k' x) = numeratorSum k k' x := by
    rw [hψ, frobLin_pow_apply, numeratorSum_eq_frob_partialTrace]
  have hψk' : (ψ ^ k') x = x ^ 2 := by
    rw [hψ, ← pow_mul, frobLin_pow_apply, ← frob, frob_periodic hn, hkk']; simp [frob]
  rw [hψP, hψk'] at happ
  have h : numeratorSum k k' x - partialTrace k k' x = x ^ 2 - x := happ
  rw [sub_eq_add_neg, sub_eq_add_neg, CharTwo.neg_eq, CharTwo.neg_eq] at h
  exact h

/-- **The linearization step — categorical route.**  Same statement as
`DobbertinLego.linearized_eq_zero_of_solution`, but sourcing the telescope from
`partialTrace_telescope_cat`. -/
lemma linearized_eq_zero_of_solution_cat {n k k' : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) {ε : F} (hε : ε = 0 ∨ ε = 1) {c x : F} (hx : x ≠ 0)
    (hsol : numeratorSum k k' x + ε = c * x ^ (2 ^ k + 1)) :
    linearized k c x = 0 := by
  unfold linearized
  set P := partialTrace k k' x with hPdef
  set S := numeratorSum k k' x with hSdef
  have hS : S = P ^ (2 ^ k) := numeratorSum_eq_frob_partialTrace k k' x
  have hP : S + P = x ^ 2 + x := partialTrace_telescope_cat hn hkk' x
  have hεpow : ε ^ (2 ^ k) = ε := by
    rcases hε with rfl | rfl <;> simp [zero_pow (show (2 : ℕ) ^ k ≠ 0 by positivity)]
  have hP_sub : P = (x ^ 2 + x) + c * x ^ (2 ^ k + 1) + ε := by
    rw [hS] at hP; grind +ring
  have hS_pow : S = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k)
      + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) + ε := by
    rw [hS, hP_sub, add_pow_char_pow, add_pow_char_pow, add_pow_char_pow, hεpow]
  have h_core : c * x ^ (2 ^ k + 1)
      = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k) + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) := by
    grind +ring
  apply mul_left_cancel₀ (pow_ne_zero (2 ^ k) hx)
  rw [mul_zero]
  have e1 : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ k) * x ^ (2 ^ k) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  have hexp : (2 ^ k + 1) * 2 ^ k = 2 ^ (2 * k) + 2 ^ k := by
    rw [add_mul, one_mul, ← pow_add, two_mul]
  have e2 : (c * x ^ (2 ^ k + 1)) ^ (2 ^ k)
      = c ^ (2 ^ k) * (x ^ (2 ^ (2 * k)) * x ^ (2 ^ k)) := by
    rw [mul_pow, ← pow_mul, hexp, pow_add]
  rw [e1, e2] at h_core
  linear_combination (norm := ring_nf) h_core
  simp [CharTwo.two_eq_zero]

/-- **Step (1) ⟹ (2) of Dobbertin's Theorem 1 — rebuilt from categorical patterns.**
Identical statement to `DobbertinLego.equation2_of_equation1`, but every structural
ingredient (the telescope, the trace-is-a-bit fact) is supplied by the enrichment
ladder above: the preadditive telescope applied to the 𝔽₂-module endomorphism
`frobLin`, with Fermat coming from finiteness. -/
theorem equation2_of_equation1_cat {n k k' α : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) (hα : α = 0 ∨ α = 1) {c x : F} (hx : x ≠ 0)
    (h : equation1 n k k' α c x) :
    linearized k c x = 0 := by
  have hbit : (α : F) * trace n x = 0 ∨ (α : F) * trace n x = 1 := by
    have hαcast : (α : F) = 0 ∨ (α : F) = 1 := by rcases hα with rfl | rfl <;> simp
    rcases hαcast with h0 | h1
    · exact Or.inl (by rw [h0, zero_mul])
    · rw [h1, one_mul]; exact trace_isBit_cat hn x
  exact linearized_eq_zero_of_solution_cat hn hkk' hbit hx h.symm

end Dobbertin.Lego.Cat
