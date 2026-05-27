import Mathlib

/-!
# Lemma 3.1 — Dempwolff & Müller

Formalization of Lemma 3.1 from "Permutation polynomials and
translation planes of even order" by U. Dempwolff and P. Müller (Adv. Geom. 2013).

**Setting.** Let `F/K` be a finite field extension, `T : F →ₗ[K] K` a nondegenerate
trace form, `L : F →ₗ[K] F` a `K`-linear map with trace-adjoint `L*` (satisfying
`T(L(w)·z) = T(w·L*(z))`), and `M : F → F` a multiplicative bijection with
inverse `M⁻¹`.

**Lemma 3.1.** The map `x ↦ L(x)·M(x)` is injective on `F` if and only if
`x ↦ L*(x)·M⁻¹(x)` is injective.

**Proof outline.** Associated to `L`, `M` and `y ∈ F` we define the `K`-linear
map `Δ_{L,M,y}(x) = L(x·y)·M(y)`. From the identity
`P(x·y₁) − P(x·y₂) = (Δ_{y₁}(x) − Δ_{y₂}(x))·M(x)`,
one deduces that `P` is injective iff the differences `Δ_{y₁} − Δ_{y₂}` are
invertible for all distinct `y₁, y₂`. The key trace identity
`T(Δ_{L,M,y}(u)·v) = T(u·Δ_{L*,M⁻¹,M(y)}(v))` shows that the adjoint
of each difference map is the corresponding difference for `(L*, M⁻¹)`.
Since a `K`-linear map is bijective iff its trace-adjoint is, and `M` is
bijective, the two injectivity conditions are equivalent.
-/

namespace DempwolffMueller

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [Finite F]

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- `PMap31 L M x = L(x) · M(x)`, the product map from Lemma 3.1. -/
def PMap31 (L : F →ₗ[K] F) (M : F → F) (x : F) : F := L x * M x

/-- `Delta L M y` is the `K`-linear map `x ↦ L(x·y) · M(y)`,
    associated to `L`, `M` and `y ∈ F` in the proof of Lemma 3.1. -/
noncomputable def Delta (L : F →ₗ[K] F) (M : F → F) (y : F) : F →ₗ[K] F where
  toFun x := L (x * y) * M y
  map_add' x₁ x₂ := by simp [add_mul, map_add, add_mul]
  map_smul' r x := by
    show L ((r • x) * y) * M y = r • (L (x * y) * M y)
    rw [smul_mul_assoc, map_smul, smul_mul_assoc]

-- ═══════════════════════════════════════════
-- Layer 1 : Multiplicative-map properties
-- ═══════════════════════════════════════════

section MultMap
variable {F' : Type*} [Field F']

/-
A multiplicative injective map on a nontrivial field sends `0` to `0`.
-/
lemma mul_map_zero {M : F' → F'} (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinj : Function.Injective M) :
    M 0 = 0 := by
      by_cases h : M 0 = 0 <;> simp_all +decide;
      have := hM 0;
      simp_all +decide [ mul_comm ];
      simpa [ this ] using @hMinj 0 1

/-- If `M` is injective and `M(0) = 0`, then `M(x) ≠ 0` for `x ≠ 0`. -/
lemma mul_map_ne_zero {M : F' → F'} (hMinj : Function.Injective M) (hM0 : M 0 = 0)
    {x : F'} (hx : x ≠ 0) :
    M x ≠ 0 :=
  fun h => hx (hMinj (h.trans hM0.symm))

/-
The inverse of a multiplicative bijection is multiplicative.
-/
lemma inv_mul_of_mul_bij {M Minv : F' → F'} (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinvL : ∀ x, Minv (M x) = x) (hMinvR : ∀ x, M (Minv x) = x) :
    ∀ a b, Minv (a * b) = Minv a * Minv b := by
      intro a b;
      rw [ ← hMinvL ( Minv a * Minv b ), hM, hMinvR, hMinvR ]

/-
The inverse of a multiplicative bijection sends `0` to `0`.
-/
lemma inv_map_zero {M Minv : F' → F'} (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinj : Function.Injective M) (hMinvL : ∀ x, Minv (M x) = x) :
    Minv 0 = 0 := by
      conv_lhs => rw [show (0 : F') = M 0 from (mul_map_zero hM hMinj).symm]
      exact hMinvL 0

end MultMap

-- ═══════════════════════════════════════════
-- Layer 2 : Fundamental algebraic identity
-- ═══════════════════════════════════════════

lemma Delta_apply (L : F →ₗ[K] F) (M : F → F) (y x : F) :
    Delta L M y x = L (x * y) * M y := rfl

/-
`P(x·y) = Δ_{L,M,y}(x) · M(x)` when `M` is multiplicative.
-/
lemma PMap31_mul_eq (L : F →ₗ[K] F) {M : F → F} (hM : ∀ a b, M (a * b) = M a * M b)
    (x y : F) :
    PMap31 L M (x * y) = Delta L M y x * M x := by
      unfold PMap31 Delta; simp +decide [ *, mul_comm, mul_assoc, mul_left_comm ] ;

/-
`P(x·y₁) − P(x·y₂) = (Δ_{y₁}(x) − Δ_{y₂}(x)) · M(x)`.
-/
lemma PMap31_mul_sub (L : F →ₗ[K] F) {M : F → F} (hM : ∀ a b, M (a * b) = M a * M b)
    (x y₁ y₂ : F) :
    PMap31 L M (x * y₁) - PMap31 L M (x * y₂) =
    (Delta L M y₁ x - Delta L M y₂ x) * M x := by
      convert PMap31_mul_eq L hM x y₁ |> fun h1 => PMap31_mul_eq L hM x y₂ |> fun h2 => h1 |> fun h3 => h2 |> fun h4 => ?_ using 1
      simp_all +decide [ sub_mul, mul_sub ]

/-
═══════════════════════════════════════════
Layer 3 : P injective ↔ Δ-differences injective
═══════════════════════════════════════════

If `(Δ_{y₁} − Δ_{y₂})(x) = 0` and `P` is injective, then `x = 0`.
    From the identity, `P(x·y₁) = P(x·y₂)`, so `x·y₁ = x·y₂`, giving `x = 0`.
-/
lemma Delta_sub_ker_trivial_of_PMap31_injective (L : F →ₗ[K] F) {M : F → F}
    (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinj : Function.Injective M)
    (hP : Function.Injective (PMap31 L M))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂) {x : F}
    (hx : (Delta L M y₁ - Delta L M y₂) x = 0) :
    x = 0 := by
      -- By PMap31_mul_sub, we have P(x·y₁) - P(x·y₂) = 0.
      have hP_sub : PMap31 L M (x * y₁) - PMap31 L M (x * y₂) = 0 := by
        convert PMap31_mul_sub L hM x y₁ y₂ using 1 ; aesop ( simp_config := { singlePass := true } ) ;
      simp_all +decide [ sub_eq_zero, hP.eq_iff ]

/-
Forward direction: `P` injective ⟹ `Δ_{y₁} − Δ_{y₂}` injective for `y₁ ≠ y₂`.
-/
lemma Delta_sub_injective_of_PMap31_injective (L : F →ₗ[K] F) {M : F → F}
    (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinj : Function.Injective M)
    (hP : Function.Injective (PMap31 L M))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂) :
    Function.Injective (Delta L M y₁ - Delta L M y₂) := by
      refine' LinearMap.ker_eq_bot.mp _;
      exact eq_bot_iff.mpr fun x hx => Delta_sub_ker_trivial_of_PMap31_injective L hM hMinj hP hy hx

/-
Backward direction: if all `Δ_{y₁} − Δ_{y₂}` are injective for `y₁ ≠ y₂`,
    then `P` is injective.

    Proof: if `P(a) = P(b)`, set `x = 1` in the identity to get
    `(Δ_a − Δ_b)(1) · M(1) = 0`; since `M(1) ≠ 0`, `(Δ_a − Δ_b)(1) = 0`;
    injectivity of `Δ_a − Δ_b` forces `1 = 0`, contradicting nontriviality.
-/
lemma PMap31_injective_of_Delta_sub_injective (L : F →ₗ[K] F) {M : F → F}
    (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinj : Function.Injective M)
    (hDelta : ∀ y₁ y₂ : F, y₁ ≠ y₂ →
      Function.Injective (Delta L M y₁ - Delta L M y₂)) :
    Function.Injective (PMap31 L M) := by
      intro a b hab;
      by_cases h : a = b <;> simp_all +decide [ sub_eq_iff_eq_add ];
      -- From PMap31_mul_sub with x = 1: P(1·a) - P(1·b) = (Δ_a(1) - Δ_b(1)) · M(1).
      have h_sub : (Delta L M a - Delta L M b) 1 * M 1 = 0 := by
        have h_sub : PMap31 L M (1 * a) - PMap31 L M (1 * b) = (Delta L M a - Delta L M b) 1 * M 1 := by
          convert PMap31_mul_sub L hM 1 a b using 1;
        aesop;
      -- Since $M(1) \neq 0$, we have $(Δ_a - Δ_b)(1) = 0$.
      have h_zero : (Delta L M a - Delta L M b) 1 = 0 := by
        have := mul_map_ne_zero hMinj ( mul_map_zero hM hMinj ) one_ne_zero; aesop;
      exact absurd ( hDelta a b h ( show ( Delta L M a - Delta L M b ) 1 = ( Delta L M a - Delta L M b ) 0 from by aesop ) ) ( by aesop )

/-
`PMap31 L M` injective ↔ `Δ_{y₁} − Δ_{y₂}` bijective for all distinct `y₁, y₂`.
    (Injectivity = bijectivity in finite dimension.)
-/
lemma PMap31_injective_iff_Delta_sub_bijective (L : F →ₗ[K] F) {M : F → F}
    (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinj : Function.Injective M) :
    Function.Injective (PMap31 L M) ↔
    ∀ y₁ y₂ : F, y₁ ≠ y₂ → Function.Bijective (Delta L M y₁ - Delta L M y₂) := by
      refine' ⟨ fun h y₁ y₂ hy => _, fun h => PMap31_injective_of_Delta_sub_injective L hM hMinj fun y₁ y₂ hy => _ ⟩;
      · exact ⟨ Delta_sub_injective_of_PMap31_injective L hM hMinj h hy, Finite.injective_iff_surjective.mp ( Delta_sub_injective_of_PMap31_injective L hM hMinj h hy ) ⟩;
      · exact h y₁ y₂ hy |>.1

/-
═══════════════════════════════════════════
Layer 4 : Adjoint and bijectivity
═══════════════════════════════════════════

If `A` is surjective, then its trace-adjoint `A*` is injective.

    If `A*(v) = 0` then `T(A(u) · v) = T(u · 0) = 0` for all `u`.
    Surjectivity gives `T(w · v) = 0` for all `w`, whence `v = 0`.
-/
lemma adjoint_injective_of_surjective (T : F →ₗ[K] K)
    (hT : ∀ x : F, (∀ y : F, T (x * y) = 0) → x = 0)
    (A Aadj : F →ₗ[K] F) (hAdj : ∀ u v, T (A u * v) = T (u * Aadj v))
    (hAsurj : Function.Surjective A) :
    Function.Injective Aadj := by
      intro v w hvw;
      contrapose! hT;
      refine' ⟨ v - w, _, _ ⟩ <;> simp_all +decide [ sub_eq_zero ];
      intro y; obtain ⟨ u, rfl ⟩ := hAsurj y; simp +decide [ *, mul_sub, sub_mul ] ;
      have := hAdj u v; have := hAdj u w; simp_all +decide [ mul_comm ] ;

/-
If `A*` is surjective then `A` is injective (symmetric argument).
-/
lemma injective_of_adjoint_surjective (T : F →ₗ[K] K)
    (hT : ∀ x : F, (∀ y : F, T (x * y) = 0) → x = 0)
    (A Aadj : F →ₗ[K] F) (hAdj : ∀ u v, T (A u * v) = T (u * Aadj v))
    (hAadjsurj : Function.Surjective Aadj) :
    Function.Injective A := by
      -- Suppose A u = 0. Then for all v, T(A u * v) = T(0 * v) = 0.
      by_contra hA_not_inj
      obtain ⟨u, hu⟩ : ∃ u, u ≠ 0 ∧ A u = 0 := by
        contrapose! hA_not_inj;
        exact LinearMap.ker_eq_bot.mp ( LinearMap.ker_eq_bot'.mpr fun u hu => Classical.not_not.1 fun hu' => hA_not_inj u hu' hu );
      -- So T(u * Aadj v) = 0 for all v (by hAdj).
      have hTuAadj : ∀ v : F, T (u * Aadj v) = 0 := by
        exact fun v => hAdj u v ▸ by simp +decide [ hu.2 ] ;
      exact hu.1 ( hT u fun v => by obtain ⟨ w, rfl ⟩ := hAadjsurj v; exact hTuAadj w )

/-
A `K`-linear endomorphism on a finite field is bijective iff its
    trace-adjoint is bijective.
-/
lemma bijective_iff_adjoint_bijective (T : F →ₗ[K] K)
    (hT : ∀ x : F, (∀ y : F, T (x * y) = 0) → x = 0)
    (A Aadj : F →ₗ[K] F) (hAdj : ∀ u v, T (A u * v) = T (u * Aadj v)) :
    Function.Bijective A ↔ Function.Bijective Aadj := by
      constructor <;> intro h;
      · refine' ⟨ adjoint_injective_of_surjective T hT A Aadj hAdj h.2, _ ⟩;
        exact LinearMap.surjective_of_injective ( adjoint_injective_of_surjective T hT A Aadj hAdj h.2 );
      · -- If `Aadj` is bijective, then `A` is injective.
        have h_inj : Function.Injective A := by
          apply injective_of_adjoint_surjective T hT A Aadj hAdj h.2;
        exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

/-
═══════════════════════════════════════════
Layer 5 : The key adjoint identity for Δ
═══════════════════════════════════════════

Core trace substitution: `T(L(u·y) · c) = T(u·y · L*(c))`.
    Instantiation of the adjoint property with `w = u·y`, `z = c`.
-/
lemma trace_adj_subst (T : F →ₗ[K] K) (L Ladj : F →ₗ[K] F)
    (hAdj : ∀ w z, T (L w * z) = T (w * Ladj z))
    (u y c : F) :
    T (L (u * y) * c) = T (u * y * Ladj c) := by
      exact hAdj _ _

/-- Rearrangement `u · y · w = u · (w · y)` in a commutative ring. -/
lemma mul_right_comm_assoc (u y w : F) :
    u * y * w = u * (w * y) := by ring

/-
**Key adjoint identity.** `Δ_{L*,M⁻¹,M(y)}` is the trace-adjoint of `Δ_{L,M,y}`:

    `T(Δ_{L,M,y}(u) · v) = T(u · Δ_{L*,M⁻¹,M(y)}(v))`.

    Expanding both sides reduces to `T(L(u·y) · M(y)·v) = T(u · L*(v·M(y)) · y)`,
    which follows from the adjoint property `T(L(w)·z) = T(w · L*(z))`
    with `w = u·y`, `z = M(y)·v`, and commutativity.
-/
lemma Delta_adjoint_spec (T : F →ₗ[K] K) (L Ladj : F →ₗ[K] F)
    (hAdj : ∀ w z, T (L w * z) = T (w * Ladj z))
    {M Minv : F → F} (hMinv : ∀ x, Minv (M x) = x)
    (u v y : F) :
    T (Delta L M y u * v) = T (u * Delta Ladj Minv (M y) v) := by
      -- Using the adjoint property and the fact that multiplication is commutative, we can rewrite the right-hand side.
      have h_rw : T (u * Ladj (v * M y) * y) = T (u * Ladj (M y * v) * y) := by
        rw [ mul_comm ( M y ) v ];
      convert h_rw using 1;
      · convert hAdj ( u * y ) ( v * M y ) using 1 <;> ring!;
        simp +decide only [Delta_apply, mul_comm, mul_left_comm];
      · simp +decide [ Delta, mul_assoc ];
        simp +decide [ mul_comm, hMinv ]

/-
The adjoint of `Δ_{y₁} − Δ_{y₂}` is `Δ^*_{M(y₁)} − Δ^*_{M(y₂)}`:

    `T((Δ_{L,M,y₁} − Δ_{L,M,y₂})(u) · v) = T(u · (Δ_{L*,M⁻¹,M(y₁)} − Δ_{L*,M⁻¹,M(y₂)})(v))`.
-/
lemma Delta_sub_adjoint_spec (T : F →ₗ[K] K) (L Ladj : F →ₗ[K] F)
    (hAdj : ∀ w z, T (L w * z) = T (w * Ladj z))
    {M Minv : F → F} (hMinv : ∀ x, Minv (M x) = x)
    (u v y₁ y₂ : F) :
    T ((Delta L M y₁ - Delta L M y₂) u * v) =
    T (u * (Delta Ladj Minv (M y₁) - Delta Ladj Minv (M y₂)) v) := by
      convert congr_arg₂ ( · - · ) ( Delta_adjoint_spec T L Ladj hAdj hMinv u v y₁ ) ( Delta_adjoint_spec T L Ladj hAdj hMinv u v y₂ ) using 1 <;> simp +decide [ sub_mul, mul_sub ]

/-
═══════════════════════════════════════════
Layer 6 : Δ-difference bijective ↔ adjoint Δ-difference bijective
═══════════════════════════════════════════

`Δ_{L,M,y₁} − Δ_{L,M,y₂}` is bijective iff its adjoint
    `Δ_{L*,M⁻¹,M(y₁)} − Δ_{L*,M⁻¹,M(y₂)}` is bijective.
    Combines the adjoint identity (Layer 5) with `bijective_iff_adjoint_bijective`.
-/
lemma Delta_sub_bijective_iff_adj (T : F →ₗ[K] K)
    (hT : ∀ x : F, (∀ y : F, T (x * y) = 0) → x = 0)
    (L Ladj : F →ₗ[K] F) (hAdj : ∀ w z, T (L w * z) = T (w * Ladj z))
    {M Minv : F → F} (hMinv : ∀ x, Minv (M x) = x)
    (y₁ y₂ : F) :
    Function.Bijective (Delta L M y₁ - Delta L M y₂) ↔
    Function.Bijective (Delta Ladj Minv (M y₁) - Delta Ladj Minv (M y₂)) := by
      convert bijective_iff_adjoint_bijective T hT _ _ _ using 1
      exact fun u v => Delta_sub_adjoint_spec T L Ladj hAdj hMinv u v y₁ y₂

/-
═══════════════════════════════════════════
Layer 7 : Relabelling via M bijective
═══════════════════════════════════════════

Quantifying over distinct pairs is invariant under a bijection.
-/
lemma forall_ne_bij {α : Type*} {M : α → α} (hMbij : Function.Bijective M)
    {Q : α → α → Prop} :
    (∀ y₁ y₂, y₁ ≠ y₂ → Q (M y₁) (M y₂)) ↔ (∀ z₁ z₂, z₁ ≠ z₂ → Q z₁ z₂) := by
      constructor <;> intro h z₁ z₂ hz;
      · obtain ⟨ y₁, rfl ⟩ := hMbij.2 z₁; obtain ⟨ y₂, rfl ⟩ := hMbij.2 z₂; specialize h y₁ y₂; aesop;
      · exact h _ _ ( hMbij.injective.ne hz )

/-
═══════════════════════════════════════════
Layer 8 : Main theorem — Lemma 3.1
═══════════════════════════════════════════

**Lemma 3.1.** Let `L : F → F` be `K`-linear with trace-adjoint `L*`,
    and let `M : F → F` be a multiplicative bijection with inverse `M⁻¹`.
    Then `x ↦ L(x)·M(x)` is injective iff `x ↦ L*(x)·M⁻¹(x)` is injective.

    The chain of equivalences is:

    `PMap31 L M` injective
    ↔ `∀ y₁ ≠ y₂, Δ_{L,M,y₁} − Δ_{L,M,y₂}` bijective            (Layer 3)
    ↔ `∀ y₁ ≠ y₂, Δ_{L*,M⁻¹,M(y₁)} − Δ_{L*,M⁻¹,M(y₂)}` bijective  (Layer 6)
    ↔ `∀ z₁ ≠ z₂, Δ_{L*,M⁻¹,z₁} − Δ_{L*,M⁻¹,z₂}` bijective      (Layer 7)
    ↔ `PMap31 L* M⁻¹` injective                                    (Layer 3)
-/
theorem lemma_3_1 (T : F →ₗ[K] K)
    (hT : ∀ x : F, (∀ y : F, T (x * y) = 0) → x = 0)
    (L Ladj : F →ₗ[K] F) (hAdj : ∀ w z, T (L w * z) = T (w * Ladj z))
    (M Minv : F → F)
    (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_bij : Function.Bijective M)
    (hMinv_mul : ∀ a b, Minv (a * b) = Minv a * Minv b)
    (hMinv_inj : Function.Injective Minv)
    (hMinvL : ∀ x, Minv (M x) = x)
    (_hMinvR : ∀ x, M (Minv x) = x) :
    Function.Injective (PMap31 L M) ↔ Function.Injective (PMap31 Ladj Minv) := by
  convert ( PMap31_injective_iff_Delta_sub_bijective L hM_mul hM_bij.injective ) using 1;
  convert ( PMap31_injective_iff_Delta_sub_bijective Ladj hMinv_mul hMinv_inj ).symm using 1;
  · convert PMap31_injective_iff_Delta_sub_bijective Ladj hMinv_mul hMinv_inj using 1;
  · convert ( PMap31_injective_iff_Delta_sub_bijective Ladj hMinv_mul hMinv_inj ).symm using 1;
    convert ( forall_ne_bij hM_bij ) using 1;
    exact forall_congr' fun x => forall_congr' fun y => forall_congr' fun hxy => Delta_sub_bijective_iff_adj T hT L Ladj hAdj hMinvL x y

end DempwolffMueller