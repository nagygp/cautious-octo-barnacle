import Mathlib

/-!
# Lemma 3.1 — Dempwolff & Müller

The map x ↦ L(x)·M(x) is injective on F iff x ↦ L*(x)·M⁻¹(x) is injective,
where L* is the trace-adjoint and M is a multiplicative bijection.
-/

namespace DempwolffMueller

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [Finite F]

def PMap31 (L : F →ₗ[K] F) (M : F → F) (x : F) : F := L x * M x

noncomputable def Delta (L : F →ₗ[K] F) (M : F → F) (y : F) : F →ₗ[K] F where
  toFun x := L (x * y) * M y
  map_add' x₁ x₂ := by simp [add_mul, map_add, add_mul]
  map_smul' r x := by
    show L ((r • x) * y) * M y = r • (L (x * y) * M y)
    rw [smul_mul_assoc, map_smul, smul_mul_assoc]

@[simp] lemma Delta_apply (L : F →ₗ[K] F) (M : F → F) (y x : F) :
    Delta L M y x = L (x * y) * M y := rfl

section MultMap
variable {F' : Type*} [Field F']

lemma mul_map_zero {M : F' → F'} (hM : ∀ a b, M (a * b) = M a * M b)
    (hMinj : Function.Injective M) : M 0 = 0 := by
  by_contra h;
  have hM0 : ∀ x : F', M x = 1 := by
    intro x; specialize hM 0 x; aesop;
  simpa [ hM0 ] using @hMinj 0 1

lemma mul_map_ne_zero {M : F' → F'} (hMinj : Function.Injective M)
    (hM0 : M 0 = 0) {x : F'} (hx : x ≠ 0) : M x ≠ 0 :=
  fun h => hx (hMinj (h.trans hM0.symm))

end MultMap

lemma PMap31_mul_eq (L : F →ₗ[K] F) {M : F → F}
    (hM : ∀ a b, M (a * b) = M a * M b) (x y : F) :
    PMap31 L M (x * y) = Delta L M y x * M x := by
  simp [PMap31, hM]; ring

lemma PMap31_inj_iff_Delta_sub_bij (L : F →ₗ[K] F) {M : F → F}
    (hM : ∀ a b, M (a * b) = M a * M b) (hMinj : Function.Injective M) :
    Function.Injective (PMap31 L M) ↔
    ∀ y₁ y₂ : F, y₁ ≠ y₂ → Function.Bijective (Delta L M y₁ - Delta L M y₂) := by
  constructor;
  · intro hP y₁ y₂ hy₁₂
    have h_ker : ∀ x, (Delta L M y₁ - Delta L M y₂) x = 0 → x = 0 := by
      intro x hx
      have h_eq : PMap31 L M (x * y₁) = PMap31 L M (x * y₂) := by
        simp_all +decide [ sub_eq_iff_eq_add, PMap31_mul_eq ];
      have := hP h_eq; aesop;
    exact ⟨ LinearMap.ker_eq_bot.mp ( LinearMap.ker_eq_bot'.mpr h_ker ), LinearMap.surjective_of_injective ( LinearMap.ker_eq_bot.mp ( LinearMap.ker_eq_bot'.mpr h_ker ) ) ⟩;
  · intro h x y hxy
    by_contra hneq
    have h_eq : (Delta L M y - Delta L M x) 1 = 0 := by
      simp_all +decide [ PMap31, Delta ]
    have h_bijective : Function.Bijective (Delta L M y - Delta L M x) := by
      exact h y x ( Ne.symm hneq )
    exact hneq (h_bijective.injective (by
    have := h_bijective.injective; have := @this 0 1; aesop;))

lemma bijective_iff_adjoint_bijective (T : F →ₗ[K] K)
    (hT : ∀ x : F, (∀ y : F, T (x * y) = 0) → x = 0)
    (A Aadj : F →ₗ[K] F)
    (hAdj : ∀ u v, T (A u * v) = T (u * Aadj v)) :
    Function.Bijective A ↔ Function.Bijective Aadj := by
  constructor;
  · intro h;
    have h_nondeg : ∀ v w : F, (∀ u : F, T (A u * v) = T (A u * w)) → v = w := by
      intro v w hvw
      have h_eq : ∀ u : F, T (A u * (v - w)) = 0 := by
        simp +decide [ mul_sub, hvw ];
      exact sub_eq_zero.mp ( hT _ fun x => by obtain ⟨ u, rfl ⟩ := h.2 x; simpa [ mul_comm ] using h_eq u );
    have h_adj_inj : Function.Injective Aadj := by
      exact fun v w hvw => h_nondeg v w fun u => by rw [ hAdj, hAdj, hvw ] ;
    exact ⟨h_adj_inj, by
      exact LinearMap.surjective_of_injective h_adj_inj⟩;
  · intro hAadj_bijective
    have hA_inj : Function.Injective A := by
      intros u v huv
      have h_eq : ∀ w : F, T (u * Aadj w) = T (v * Aadj w) := by
        exact fun w => by rw [ ← hAdj, ← hAdj, huv ] ;
      exact sub_eq_zero.mp ( hT ( u - v ) fun w => by obtain ⟨ w, rfl ⟩ := hAadj_bijective.2 w; simpa [ sub_mul ] using sub_eq_zero.mpr ( h_eq w ) )
    exact ⟨hA_inj, Finite.injective_iff_surjective.1 hA_inj⟩

lemma Delta_adjoint_spec (T : F →ₗ[K] K) (L Ladj : F →ₗ[K] F)
    (hAdj : ∀ w z, T (L w * z) = T (w * Ladj z))
    {M Minv : F → F} (hMinv : ∀ x, Minv (M x) = x)
    (u v y : F) :
    T (Delta L M y u * v) = T (u * Delta Ladj Minv (M y) v) := by
  have := hAdj ( u * y ) ( v * M y ) ; simp_all +decide [ mul_assoc, mul_left_comm ] ;
  convert this using 1 <;> ring

lemma forall_ne_bij {α : Type*} {M : α → α} (hMbij : Function.Bijective M)
    {Q : α → α → Prop} :
    (∀ y₁ y₂, y₁ ≠ y₂ → Q (M y₁) (M y₂)) ↔ (∀ z₁ z₂, z₁ ≠ z₂ → Q z₁ z₂) := by
  constructor <;> intro h z₁ z₂ hz
  · obtain ⟨y₁, rfl⟩ := hMbij.2 z₁
    obtain ⟨y₂, rfl⟩ := hMbij.2 z₂
    exact h y₁ y₂ (fun heq => hz (congr_arg M heq))
  · exact h _ _ (fun heq => hz (hMbij.1 heq))

theorem lemma_3_1 (T : F →ₗ[K] K)
    (hT : ∀ x : F, (∀ y : F, T (x * y) = 0) → x = 0)
    (L Ladj : F →ₗ[K] F)
    (hAdj : ∀ w z, T (L w * z) = T (w * Ladj z))
    (M Minv : F → F)
    (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_bij : Function.Bijective M)
    (hMinv_mul : ∀ a b, Minv (a * b) = Minv a * Minv b)
    (hMinv_inj : Function.Injective Minv)
    (hMinvL : ∀ x, Minv (M x) = x)
    (hMinvR : ∀ x, M (Minv x) = x) :
    Function.Injective (PMap31 L M) ↔ Function.Injective (PMap31 Ladj Minv) := by
  rw [ DempwolffMueller.PMap31_inj_iff_Delta_sub_bij L hM_mul hM_bij.injective ];
  rw [ DempwolffMueller.PMap31_inj_iff_Delta_sub_bij Ladj hMinv_mul hMinv_inj ];
  have h_bijective_iff_adjoint_bijective : ∀ y₁ y₂ : F, Function.Bijective (Delta L M y₁ - Delta L M y₂) ↔ Function.Bijective (Delta Ladj Minv (M y₁) - Delta Ladj Minv (M y₂)) := by
    intro y₁ y₂
    apply bijective_iff_adjoint_bijective T hT (Delta L M y₁ - Delta L M y₂) (Delta Ladj Minv (M y₁) - Delta Ladj Minv (M y₂));
    intro u v; simp +decide [ Delta, hAdj ] ; ring;
    simp +decide [ mul_assoc, hAdj, hMinvL ];
    simp +decide only [mul_comm];
  convert forall_ne_bij hM_bij using 1;
  simp +decide only [h_bijective_iff_adjoint_bijective]

end DempwolffMueller
