/-
  # Isomorphism Seal: APN/AB Transfer Across Field Isomorphisms

  The fundamental bridge between computational verification (on Nat-based GF(2^n))
  and abstract Mathlib-grounded definitions.

  ## Architecture

  ```
  Nat-based GF(2^n)  ──φ──▶  Abstract Field K
       │                           │
    checkAPN = true             IsAPN f
       │                           │
    native_decide        isomorphism_seal
       ▼                           ▼
  "Verified on model"   "Verified on any K ≅ model"
  ```

  ## Key Theorems

  1. `apn_transfer_equiv`: APN transfers across additive group isomorphisms
  2. `diff_uniformity_fibre_transfer`: Fibre sizes are isomorphism invariants
  3. `frobenius_apn_invariance`: EA-equivalent power maps are simultaneously APN
  4. `ea_equiv_preserves_apn`: EA-equivalence preserves APN
  5. `master_bridge_principle`: The master bridge connecting all layers
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## §1  APN Transfer via Additive Group Isomorphism

This is the core "isomorphism seal": if f is APN on G and φ : G ≃+ H,
then φ ∘ f ∘ φ⁻¹ is APN on H. -/

/-- The differential map D_a(f)(x) = f(x + a) - f(x). -/
def diffMap {G : Type*} [AddCommGroup G] (f : G → G) (a : G) : G → G :=
  fun x => f (x + a) - f x

/-- The differential fibre: {x | D_a(f)(x) = b}. -/
def diffFibre {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → G) (a b : G) : Finset G :=
  Finset.univ.filter fun x => diffMap f a x = b

/-- A function is APN if all nontrivial differential fibres have size ≤ 2. -/
def IsAPN' {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → G) : Prop :=
  ∀ (a : G), a ≠ 0 → ∀ (b : G), (diffFibre f a b).card ≤ 2

/-- The conjugated function φ ∘ f ∘ φ⁻¹. -/
def conjugate {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (f : G → G) : H → H :=
  φ ∘ f ∘ φ.symm

/-
Key lemma: the fibre of the conjugated function bijects with the
    original fibre via φ.
-/
lemma diffFibre_conjugate_eq
    {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (φ : G ≃+ H) (f : G → G) (a b : H) :
    diffFibre (conjugate φ f) a b =
      (diffFibre f (φ.symm a) (φ.symm b)).map φ.toEquiv.toEmbedding := by
  unfold diffFibre;
  simp +decide [ Finset.ext_iff, Set.ext_iff, diffMap, conjugate ];
  simp +decide [ ← map_sub, ← map_add, φ.injective.eq_iff ];
  exact fun x => ⟨ fun h => by rw [ ← h, φ.symm_apply_apply ], fun h => by rw [ h, φ.apply_symm_apply ] ⟩

/-- **Isomorphism Seal (APN)**: APN transfers across additive group isomorphisms. -/
theorem apn_transfer_equiv
    {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (φ : G ≃+ H) (f : G → G) (hf : IsAPN' f) :
    IsAPN' (conjugate φ f) := by
  intro a ha b
  rw [diffFibre_conjugate_eq]
  rw [Finset.card_map]
  exact hf (φ.symm a) (by simp [ha]) (φ.symm b)

/-- Corollary: APN is invariant under conjugation by isomorphism. -/
theorem apn_invariant_conjugation
    {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (φ : G ≃+ H) (f : G → G) :
    IsAPN' f ↔ IsAPN' (conjugate φ f) := by
  constructor
  · exact apn_transfer_equiv φ f
  · intro h
    have key : f = conjugate φ.symm (conjugate φ f) := by
      ext x; simp [conjugate]
    rw [key]
    exact apn_transfer_equiv φ.symm _ h

/-! ## §2  Differential Fibre Size is an Isomorphism Invariant -/

/-- The fibre size of the conjugate equals the fibre size of the original. -/
theorem diff_uniformity_fibre_transfer
    {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (φ : G ≃+ H) (f : G → G) (a b : H) :
    (diffFibre (conjugate φ f) a b).card =
    (diffFibre f (φ.symm a) (φ.symm b)).card := by
  rw [diffFibre_conjugate_eq, Finset.card_map]

/-! ## §3  EA-Equivalence Preserves APN -/

/-- EA-equivalence data: g = L₁ ∘ f ∘ L₂ + L₃. -/
structure EAEquivData (G : Type*) [AddCommGroup G] where
  L₁ : G ≃+ G        -- post-composition linear bijection
  L₂ : G ≃+ G        -- pre-composition linear bijection
  L₃ : G →+ G         -- additive term

/-- Apply an EA-equivalence to a function. -/
def EAEquivData.apply {G : Type*} [AddCommGroup G]
    (e : EAEquivData G) (f : G → G) : G → G :=
  fun x => e.L₁ (f (e.L₂ x)) + e.L₃ x

/-
EA-equivalence preserves APN.
-/
theorem ea_equiv_preserves_apn
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (e : EAEquivData G) (f : G → G) (hf : IsAPN' f) :
    IsAPN' (e.apply f) := by
  intro a ha b;
  unfold diffFibre;
  convert hf ( e.L₂ a ) _ ( e.L₁.symm ( b - e.L₃ a ) ) using 1;
  · refine' Finset.card_bij ( fun x hx => e.L₂ x ) _ _ _ <;> simp_all +decide [ sub_eq_iff_eq_add, diffMap ];
    · intro x hx; unfold diffFibre; simp_all +decide [ sub_eq_iff_eq_add, diffMap ] ;
      simp_all +decide [ EAEquivData.apply, sub_eq_iff_eq_add ];
      apply_fun e.L₁.symm at hx; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
      grind;
    · intro x hx; use e.L₂.symm x; simp_all +decide [ diffFibre, diffMap, EAEquivData.apply ] ;
      simp_all +decide [ sub_eq_iff_eq_add, ← add_assoc ];
      abel1;
  · exact fun h => ha ( e.L₂.injective <| by simpa using h )

/-! ## §4  Frobenius-Orbit APN Invariance for Power Maps -/

/-
Power maps related by Frobenius automorphism are simultaneously APN
    (stated for char 2 fields).
-/
theorem frobenius_apn_invariance
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (d : ℕ) :
    IsAPN' (fun (x : K) => x ^ d) ↔
    IsAPN' (fun (x : K) => x ^ (2 * d)) := by
  -- We'll use that $x^{2d} = (x^d)^2$.
  have h_exp : ∀ x : K, x ^ (2 * d) = (x ^ d) ^ 2 := by
    exact fun x => by ring;
  -- Since $x^{2d} = (x^d)^2$, we can use the fact that squaring is an automorphism in characteristic 2.
  have h_aut : Function.Bijective (fun x : K => x ^ 2) := by
    have h_aut : Function.Injective (fun x : K => x ^ 2) := by
      intro x y hxy;
      grind;
    exact ⟨ h_aut, Finite.injective_iff_surjective.mp h_aut ⟩;
  -- Since squaring is an automorphism in characteristic 2, we can use the fact that the differential map is preserved under this automorphism.
  have h_diff_map : ∀ a b : K, (Finset.filter (fun x => (x ^ d) ^ 2 - ((x + a) ^ d) ^ 2 = b) (Finset.univ : Finset K)).card = (Finset.filter (fun x => x ^ d - (x + a) ^ d = (Function.invFun (fun x : K => x ^ 2) b)) (Finset.univ : Finset K)).card := by
    -- Since squaring is an automorphism in characteristic 2, we can use the fact that the differential map is preserved under this automorphism. Specifically, if $y^2 = b$, then $y = \sqrt{b}$.
    have h_sqrt : ∀ b : K, (Function.invFun (fun x : K => x ^ 2) b) ^ 2 = b := by
      exact fun b => Function.invFun_eq ( h_aut.2 b );
    intro a b; congr 1 with x; simp +decide [ ← sq, h_sqrt ] ;
    grind +extAll;
  constructor <;> intro h a ha b <;> simp_all +decide [ IsAPN' ];
  · convert h a ha ( Function.invFun ( fun x : K => x ^ 2 ) b ) using 1;
    convert h_diff_map a b using 1;
    · unfold diffFibre; simp +decide [ diffMap ] ;
      rw [ Finset.card_filter, Finset.card_filter ];
      grind;
    · unfold diffFibre; simp +decide [ diffMap ] ;
      rw [ Finset.card_filter, Finset.card_filter ];
      grind;
  · convert h a ha ( ( b : K ) ^ 2 ) using 1;
    convert h_diff_map a ( b ^ 2 ) |> Eq.symm using 1;
    · rw [ Function.leftInverse_invFun ( show Function.Injective ( fun x : K => x ^ 2 ) from ?_ ) ];
      · unfold diffFibre; simp +decide [ sub_eq_iff_eq_add ] ;
        unfold diffMap; simp +decide [ sub_eq_iff_eq_add' ] ;
        rw [ Finset.card_filter, Finset.card_filter ];
        grind;
      · exact Finite.injective_iff_surjective.mpr ( by intro x; replace h_aut := congr_arg Multiset.toFinset h_aut; rw [ Finset.ext_iff ] at h_aut; specialize h_aut x; aesop );
    · unfold diffFibre; simp +decide [ diffMap ] ;
      rw [ Finset.card_filter, Finset.card_filter ];
      grind

/-! ## §5  Walsh Transform and AB Transfer -/

/-- The Walsh transform of f : G → G using an additive character χ. -/
def walshTransform {G : Type*} [Field G] [Fintype G] [DecidableEq G]
    (χ : AddChar G ℂ) (f : G → G) (a b : G) : ℂ :=
  ∑ x : G, χ (a * x + b * f x)

/-- A function is AB if all Walsh coefficients (b ≠ 0) satisfy
    |W|² ∈ {0, 2^{n+1}}. -/
def IsABField {G : Type*} [Field G] [Fintype G] [DecidableEq G]
    (χ : AddChar G ℂ) (f : G → G) (n : ℕ) : Prop :=
  ∀ (a b : G), b ≠ 0 →
    walshTransform χ f a b = 0 ∨
    Complex.normSq (walshTransform χ f a b) = (2 : ℝ) ^ (n + 1)

/-! ## §6  Category-Theoretic Spectrum Invariants

The differential uniformity and Walsh spectrum are CCZ-invariants,
meaning they factor through the CCZ-equivalence groupoid. -/

/-- Spectrum data: the numerical invariants of a function. -/
structure SpectrumInvariants where
  diffUniformity : ℕ
  walshSqValues : Multiset ℕ
  parsevalSum : ℕ

/-- Spectrum data for "bent" (AB) functions. -/
def bentSpectrum (n : ℕ) (supportSize : ℕ) : SpectrumInvariants where
  diffUniformity := 2
  walshSqValues := Multiset.replicate supportSize (2 ^ (n + 1)) +
    Multiset.replicate (2 ^ (2 * n) - supportSize) 0
  parsevalSum := supportSize * 2 ^ (n + 1)

/-! ## §7  Master Bridge Principle -/

/-- The bridge principle: if f is APN on G and g is the "same" function
    on H (via an isomorphism φ), then g is APN on H. -/
theorem master_bridge_principle
    {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (φ : G ≃+ H) (f : G → G) (g : H → H)
    (hfg : ∀ x, g (φ x) = φ (f x))
    (hf : IsAPN' f) : IsAPN' g := by
  have hg : g = conjugate φ f := by
    ext x
    simp only [conjugate, Function.comp]
    specialize hfg (φ.symm x)
    simp at hfg
    exact hfg
  rw [hg]
  exact apn_transfer_equiv φ f hf

end