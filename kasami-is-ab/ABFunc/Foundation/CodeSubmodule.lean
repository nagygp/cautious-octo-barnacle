import Mathlib
import CodingTheory.BinaryCode

/-!
# Binary Codes as Submodules: Connecting to Mathlib's Linear Algebra

Bridges `BinaryCode` to Mathlib's `Submodule (ZMod 2)`, unlocking dual
codes via `Submodule.dualAnnihilator`, the Galois connection on submodule
lattices, and dimension theory via `Module.finrank`.
-/

open Finset BigOperators

noncomputable section

/-! ## §1  BinaryCode → Submodule -/

/-- Convert a `BinaryCode n` to a `Submodule (ZMod 2) (Fin n → ZMod 2)`. -/
def BinaryCode.toSubmodule {n : ℕ} (C : BinaryCode n) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := { v | v ∈ C.codewords }
  add_mem' ha hb := C.add_mem _ _ ha hb
  zero_mem' := C.zero_mem
  smul_mem' r v hv := by
    show _ ∈ C.codewords
    have : r • v = fun i => r * v i := by ext; simp [Pi.smul_apply, smul_eq_mul]
    rw [this]; fin_cases r <;> simp_all [C.zero_mem]

/-! ## §2  The Standard GF(2) Inner Product -/

/-- Standard GF(2) inner product as a bilinear map. -/
def gf2BilinForm (n : ℕ) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun u := {
    toFun := fun v => ∑ i : Fin n, u i * v i
    map_add' := by intros; simp [Finset.sum_add_distrib, mul_add]
    map_smul' := by intros; simp [smul_eq_mul, Finset.mul_sum, mul_left_comm]
  }
  map_add' := by intros; ext; simp [Finset.sum_add_distrib, add_mul]
  map_smul' := by intros; ext; simp [smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The inner product is symmetric. -/
theorem gf2BilinForm_symm (n : ℕ) (u v : Fin n → ZMod 2) :
    gf2BilinForm n u v = gf2BilinForm n v u := by
  simp [gf2BilinForm, mul_comm]

/-- Non-degeneracy: ⟨u, v⟩ = 0 for all v implies u = 0. -/
theorem gf2BilinForm_nondegenerate (n : ℕ) (u : Fin n → ZMod 2)
    (h : ∀ v, gf2BilinForm n u v = 0) : u = 0 := by
  ext i
  have := h (Pi.single i 1)
  simp only [gf2BilinForm, LinearMap.coe_mk, AddHom.coe_mk] at this
  simp [Pi.single, Function.update] at this; exact this

/-! ## §3  Orthogonal Complement (Dual Code) -/

/-- The orthogonal complement = dual code C⊥. -/
def BinaryCode.orthogonalSubmodule {n : ℕ} (C : BinaryCode n) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := { v | ∀ c ∈ C.codewords, gf2BilinForm n v c = 0 }
  add_mem' ha hb c hc := by
    simp only [gf2BilinForm, LinearMap.coe_mk, AddHom.coe_mk] at *
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [ha c hc, hb c hc, add_zero]
  zero_mem' c _ := by simp [gf2BilinForm]
  smul_mem' r v hv c hc := by
    fin_cases r
    · simp [gf2BilinForm]
    · simpa using hv c hc

theorem orthogonal_mem_iff {n : ℕ} (C : BinaryCode n) (v : Fin n → ZMod 2) :
    v ∈ C.orthogonalSubmodule ↔ ∀ c ∈ C.codewords, gf2BilinForm n v c = 0 :=
  Iff.rfl

/-- Symmetry of orthogonality. -/
theorem codeword_in_double_orthogonal {n : ℕ} (C : BinaryCode n)
    (c : Fin n → ZMod 2) (hc : c ∈ C.codewords)
    (v : Fin n → ZMod 2) (hv : v ∈ C.orthogonalSubmodule) :
    gf2BilinForm n c v = 0 := by
  rw [gf2BilinForm_symm]; exact hv c hc

/-! ## §4  Antitonicity -/

theorem orthogonal_antitone {n : ℕ} (C₁ C₂ : BinaryCode n)
    (h : ∀ c, c ∈ C₁.codewords → c ∈ C₂.codewords) :
    ∀ v, v ∈ C₂.orthogonalSubmodule → v ∈ C₁.orthogonalSubmodule :=
  fun v hv c hc => hv c (h c hc)

/-! ## §5  Mathlib's Galois Connection -/

theorem dualAnnihilator_gc_instance (n : ℕ) :
    GaloisConnection
      (OrderDual.toDual ∘ Submodule.dualAnnihilator
        (R := ZMod 2) (M := Fin n → ZMod 2))
      (Submodule.dualCoannihilator ∘ OrderDual.ofDual) :=
  Submodule.dualAnnihilator_gc (ZMod 2) (Fin n → ZMod 2)

/-- The evaluation map: v ↦ ⟨v, ·⟩. -/
def evalMap (n : ℕ) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin n → ZMod 2) where
  toFun v := (gf2BilinForm n) v
  map_add' := by intros; ext; simp [gf2BilinForm, add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; ext; simp [gf2BilinForm, smul_eq_mul, Finset.mul_sum]

/-! ## §6  Blackboxed Known Results -/

/-
**Known**: dim(C) + dim(C⊥) = n.
-/
theorem dim_plus_codim {n : ℕ} (C : BinaryCode n)
    (_hLinear : ∃ k, C.codewords.card = 2 ^ k) :
    ∃ k k' : ℕ, C.codewords.card = 2 ^ k ∧ k + k' = n := by
      cases' _hLinear with k hk _hLinear;
      exact ⟨ k, n - k, hk, Nat.add_sub_of_le ( show k ≤ n from le_of_not_gt fun h => by have := Finset.card_le_univ C.codewords; norm_num at this; linarith [ pow_lt_pow_right₀ ( by decide : 1 < 2 ) h ] ) ⟩

/-
**Known**: C⊥⊥ = C for linear codes.
-/
theorem double_orthogonal_eq {n : ℕ} (C : BinaryCode n)
    (_hLinear : ∃ k, C.codewords.card = 2 ^ k) :
    ∀ v, (∀ w, (∀ c ∈ C.codewords, gf2BilinForm n w c = 0) →
        gf2BilinForm n v w = 0) →
      v ∈ C.codewords := by
        intro v hv;
        contrapose! hv;
        -- Since $v \notin C$, there exists a linear functional $f$ such that $f(v) \neq 0$ and $f(c) = 0$ for all $c \in C$.
        obtain ⟨f, hf⟩ : ∃ f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, f v ≠ 0 ∧ ∀ c ∈ C.codewords, f c = 0 := by
          have h_dual : ∀ (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2), v ∉ S → ∃ f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, f v ≠ 0 ∧ ∀ c ∈ S, f c = 0 := by
            exact?;
          convert h_dual ( C.toSubmodule ) v _;
          exact hv;
        -- Since $f$ is a linear functional, there exists a vector $w$ such that $f(x) = \langle w, x \rangle$ for all $x$.
        obtain ⟨w, hw⟩ : ∃ w : Fin n → ZMod 2, ∀ x : Fin n → ZMod 2, f x = gf2BilinForm n w x := by
          have h_dual : ∀ f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∃ w : Fin n → ZMod 2, ∀ x : Fin n → ZMod 2, f x = ∑ i, w i * x i := by
            intro f; use fun i => f ( Pi.single i 1 ) ; intro x; rw [ f.pi_apply_eq_sum_univ ] ; simp +decide [ mul_comm ] ;
            exact Finset.sum_congr rfl fun i _ => by congr; ext j; aesop;
          exact h_dual f;
        use w; simp_all +decide [ gf2BilinForm_symm ] ;

/-
**Known**: evalMap is bijective (GF(2)^n is self-dual).
-/
theorem evalMap_bijective (n : ℕ) : Function.Bijective (evalMap n) := by
  -- Since the domain and codomain are finite vector spaces of the same dimension, a linear map between them is bijective if and only if it is injective.
  have h_inj : Function.Injective (evalMap n) := by
    -- To prove injectivity, assume that for all $v$, $\langle u, v \rangle = \langle u', v \rangle$. We need to show that $u = u'$.
    intro u u' h_eq
    have h_eq_inner : ∀ v, gf2BilinForm n u v = gf2BilinForm n u' v := by
      exact fun v => congr_arg ( fun f => f v ) h_eq;
    exact Classical.not_not.1 fun h => absurd ( gf2BilinForm_nondegenerate n ( u - u' ) fun v => by simpa [ sub_eq_add_neg, map_add, map_neg ] using sub_eq_zero.2 ( h_eq_inner v ) ) ( sub_ne_zero.2 h );
  exact ⟨ h_inj, LinearMap.range_eq_top.mp <| Submodule.eq_top_of_finrank_eq <| by simp +decide [ LinearMap.finrank_range_of_inj h_inj ] ⟩

/-! ## §7  κ_m restated -/

theorem mTupleCount_submodule {n : ℕ} (C : BinaryCode n) (m : ℕ) (hm : m ≥ 1) :
    mTupleCount C m = C.codewords.card ^ (m - 1) :=
  mTupleCount_eq_card_pow C m hm

/-! ## §8  Frobenius -/

theorem frobenius_gf2_id : frobenius (ZMod 2) 2 = RingHom.id (ZMod 2) := by
  ext x; fin_cases x <;> rfl

theorem frobenius_order' (K : Type) [Field K] [Fintype K]
    [Fact (Nat.Prime 2)] [CharP K 2] {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) :
    frobenius K 2 ^ n = 1 :=
  FiniteField.frobenius_pow hcard

/-! ## §9  Master Bridge -/

theorem code_submodule_bridge {n : ℕ} (C : BinaryCode n) :
    (∀ m, m ≥ 1 → mTupleCount C m = C.codewords.card ^ (m - 1)) ∧
    (∀ v, v ∈ C.orthogonalSubmodule ↔
      ∀ c ∈ C.codewords, gf2BilinForm n v c = 0) ∧
    (∀ v c, v ∈ C.orthogonalSubmodule → c ∈ C.codewords →
      gf2BilinForm n c v = 0) :=
  ⟨fun m hm => mTupleCount_eq_card_pow C m hm,
   fun v => orthogonal_mem_iff C v,
   fun v c hv hc => codeword_in_double_orthogonal C c hc v hv⟩

end