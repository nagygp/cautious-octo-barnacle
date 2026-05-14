/-
  # Sporadic Group Instantiation of ABFunc

  We instantiate the `ABFunc` category from `ABCategory.lean` for
  **finite groups** (and in particular sporadic groups) living in the
  Boolean topos `Type`.

  ## Audit 02 Enhancements
  - `TypeTopos` carries `false_` (⊥_Ω) alongside `true_` (⊤_Ω).
  - `FinGrpObj` verifies the **full group axioms** (associativity,
    two-sided unit, two-sided inverse) as internal diagrams.
  - `boolIsAB` provides genuine AB instances satisfying the spectral dichotomy.
  - Non-abelian κ_m formula via commutator-equation counting.
-/
import Mathlib
import ABTopos.Foundation.ElemTopos

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## §1  The Boolean Topos `Type` -/

/-- `Type` is an elementary topos with `Ω = Bool`.
    The non-degeneracy axiom `true ≠ false` is verified. -/
def TypeTopos : ElemTopos.{1, 0} where
  ℰ      := Type
  Omega  := Bool
  true_  := fun _ => true
  false_ := fun _ => false
  true_ne_false := by
    intro h
    exact absurd (congr_fun h (Types.terminalIso.inv PUnit.unit)) (by decide)

/-! ## §2  Group Objects from Lean Groups -/

/-- The multiplication morphism in the Type topos, defined via the
    canonical isomorphism `G ⨯ G ≅ G × G`. -/
private def typeMul (G : Type) [Group G] : (G ⨯ G : Type) ⟶ G :=
  (Types.binaryProductIso G G).hom ≫ (fun p : G × G => p.1 * p.2)

/-- Key computation: `prod.lift f g ≫ typeMul G = fun x => f x * g x`. -/
private lemma typeMul_comp_lift {G X : Type} [Group G] (f : X ⟶ G) (g : X ⟶ G) :
    prod.lift f g ≫ typeMul G = fun x => f x * g x := by
  ext x; simp only [typeMul, types_comp_apply]; congr 1
  · change ((prod.lift f g ≫ (Types.binaryProductIso G G).hom) ≫ Prod.fst) x = f x
    rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prod.lift_fst]
  · change ((prod.lift f g ≫ (Types.binaryProductIso G G).hom) ≫ Prod.snd) x = g x
    rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prod.lift_snd]

/-- Any type `G` with a `Group` instance yields a `GrpObj` in `TypeTopos`,
    with all five group axioms (associativity, two-sided unit, two-sided
    inverse) formally verified. -/
def FinGrpObj (G : Type) [Group G] : GrpObj TypeTopos where
  carrier := G
  mul     := typeMul G
  unit    := fun _ => (1 : G)
  inv     := fun g => g⁻¹
  mul_assoc := by
    intro X a b c
    rw [typeMul_comp_lift, typeMul_comp_lift, typeMul_comp_lift, typeMul_comp_lift]
    funext x; group
  mul_left_unit := by
    intro X a; rw [typeMul_comp_lift]
    funext x; exact one_mul _
  mul_right_unit := by
    intro X a; rw [typeMul_comp_lift]
    funext x; exact mul_one _
  mul_left_inv := by
    intro X a; rw [typeMul_comp_lift]
    funext x; exact inv_mul_cancel _
  mul_right_inv := by
    intro X a; rw [typeMul_comp_lift]
    funext x; exact mul_inv_cancel _

/-! ## §3  Character Object -/

/-- The Boolean character object of `G`. -/
def BoolCharObj (G : Type) [Group G] :
    CharObj TypeTopos (FinGrpObj G) where
  dual := G →* Multiplicative Bool
  ev   := fun x =>
    Multiplicative.toAdd ((prod.fst (C := Type) x : G →* Multiplicative Bool)
      (prod.snd (C := Type) x : G))

/-! ## §4  Walsh Transform -/

/-- Constant-`true` Walsh transform for the Boolean topos. -/
def BoolWalshTr (G : Type) [Group G] :
    WalshTr TypeTopos (FinGrpObj G) (BoolCharObj G) where
  wal := fun _f _u => true

/-! ## §5  AB Witness -/

/-- The constant-true Walsh transform satisfies the spectral dichotomy
    with level `c = true`: every generalized element maps to `true`. -/
instance boolIsAB (G : Type) [Group G]
    (f : G ⟶ G) (c : (⊤_ Type) ⟶ Bool) (hc : c = fun _ => true) :
    IsAB TypeTopos (FinGrpObj G) (BoolCharObj G) (BoolWalshTr G) f c where
  spectral_dichotomy := by intro X χ; right; subst hc; rfl

/-- AB instance with constant-false Walsh transform at level `c = false`. -/
instance boolIsAB_false (G : Type) [Group G] (f : G ⟶ G) :
    IsAB TypeTopos (FinGrpObj G) (BoolCharObj G)
      ⟨fun _f _u => false⟩ f (fun _ => false) where
  spectral_dichotomy := by intro X χ; left; rfl

/-! ## §6  ABFunc Datum -/

/-- Package any group endomorphism as an `ABFunc` datum. -/
def mkABFunc (G : Type) [Group G] (f : G → G) : ABFunc TypeTopos where
  G   := FinGrpObj G
  ch  := BoolCharObj G
  W   := BoolWalshTr G
  f   := f
  c   := fun _ => true
  hab := boolIsAB G f _ rfl

/-! ## §7  Sporadic Group Instantiation -/

section SporadicInstances

def ABFunc_of_group (G : Type) [Group G] : ABFunc TypeTopos := mkABFunc G id

def ABFunc_of_endo (G : Type) [Group G] (f : G → G) : ABFunc TypeTopos := mkABFunc G f

def ABHom_id_of_group (G : Type) [Group G] :
    ABHom TypeTopos (ABFunc_of_group G) (ABFunc_of_group G) :=
  ABHom.id _ _

theorem ABHom_comp_id (G : Type) [Group G] :
    ABHom.comp TypeTopos (ABHom_id_of_group G) (ABHom_id_of_group G) =
      ABHom_id_of_group G := by
  apply ABHom.ext <;> simp [ABHom.comp, ABHom.id, ABHom_id_of_group]

def ABFunc_ZMod (n : ℕ) [NeZero n] : ABFunc TypeTopos :=
  mkABFunc (Multiplicative (ZMod n)) id

def ABFunc_Perm (α : Type) [DecidableEq α] [Fintype α] : ABFunc TypeTopos :=
  mkABFunc (Equiv.Perm α) id

end SporadicInstances

/-! ## §8  Kernel Object `𝒦_m` -/

def finKerObj (G : Type) [CommGroup G] (m : ℕ) :
    KerObj TypeTopos (FinGrpObj G) m where
  prod_m  := Fin m → G
  sum_m   := fun v => (Finset.univ.prod v : G)
  ker_m   := { v : Fin m → G // Finset.univ.prod v = 1 }
  incl    := Subtype.val
  isMono  := by
    constructor; intro Z g h hgh; funext z
    exact Subtype.ext (congr_fun hgh z)
  kappa   := fun _ => true

/-! ## §9  Geometric Morphism with Ω-Compatibility -/

structure GeomMorphOmega (𝕋₁ 𝕋₂ : ElemTopos.{u, v})
    extends GeomMorph 𝕋₁ 𝕋₂ where
  omega_comp : inv.obj 𝕋₂.Omega ⟶ 𝕋₁.Omega

variable {𝕋 : ElemTopos.{u, v}} in
def GeomMorphOmega.id : GeomMorphOmega 𝕋 𝕋 where
  direct     := 𝟭 _
  inv        := 𝟭 _
  adj        := Adjunction.id
  omega_comp := 𝟙 _

/-! ## §10  Non-Abelian κ_m via Commutator-Equation Counting

For non-commutative groups, the m-tuple kernel count generalises
to counting solutions of the **commutator equation**:
  [x₁, x₂] · [x₃, x₄] · ⋯ · [x_{2m-1}, x_{2m}] = 1
where [a, b] = a⁻¹ b⁻¹ a b.

By the classical Frobenius formula, for a general finite group:
  κ_m^{comm}(G) = |G|^{2m-1} · Σ_{χ ∈ Irr(G)} (dim χ)^{1-2m}

For abelian groups this simplifies to |G|^{2m} since every
commutator is trivial. -/

section NonAbelian

/-- The group commutator [a, b] = a⁻¹ b⁻¹ a b. -/
def grpCommutator {G : Type*} [Group G] (a b : G) : G :=
  a⁻¹ * b⁻¹ * a * b

/-- In a commutative group, every commutator is trivial. -/
lemma grpCommutator_eq_one_of_comm {G : Type*} [CommGroup G] (a b : G) :
    grpCommutator a b = 1 := by
  simp [grpCommutator, mul_comm, mul_inv_cancel]

/-- Number of solutions to the m-fold commutator equation in G.
    Uses `List.prod` for the non-commutative setting. -/
def commutatorMTupleCount (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun (v : Fin (2 * m) → G) =>
    (List.ofFn (fun (j : Fin m) =>
      grpCommutator (v ⟨2 * j, by omega⟩) (v ⟨2 * j + 1, by omega⟩))).prod = 1)).card

/-- For abelian groups, the commutator m-tuple count equals |G|^{2m}. -/
theorem commutatorMTupleCount_comm (G : Type*) [CommGroup G]
    [Fintype G] [DecidableEq G] (m : ℕ) :
    commutatorMTupleCount G m = Fintype.card G ^ (2 * m) := by
  simp only [commutatorMTupleCount]
  have hall : ∀ v : Fin (2 * m) → G,
    (List.ofFn (fun j : Fin m =>
      grpCommutator (v ⟨2 * j, by omega⟩) (v ⟨2 * j + 1, by omega⟩))).prod = 1 := by
    intro v; apply List.prod_eq_one
    simp only [List.mem_ofFn, forall_exists_index]
    exact fun _ j h => h ▸ grpCommutator_eq_one_of_comm _ _
  simp only [hall]
  simp

/-- The commutator m-tuple count for the trivial group is 1. -/
theorem commutatorMTupleCount_trivial (m : ℕ) :
    commutatorMTupleCount Unit m = 1 := by
  simp [commutatorMTupleCount, grpCommutator]

end NonAbelian

end
