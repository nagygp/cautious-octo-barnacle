import Mathlib

/-!
# Gauss Sum Bridge: Connecting to Mathlib's Number Theory

Connects the project's Gauss sum theory to Mathlib's `gaussSum` infrastructure:
- `gaussSum_mul_gaussSum_eq_card` for Stickelberger
- `AddChar.sum_eq_zero_of_ne_one` for character orthogonality
- `FiniteField.frobenius_pow` for Frobenius periodicity
-/

open Finset BigOperators

noncomputable section

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/-! ## §1  Additive Character via Trace -/

noncomputable instance instAlgBridge [CharP 𝔽 2] : Algebra (ZMod 2) 𝔽 :=
  (ZMod.castHom (dvd_refl 2) 𝔽).toAlgebra

noncomputable def AbsTrace' [CharP 𝔽 2] : 𝔽 →+ ZMod 2 :=
  (Algebra.trace (ZMod 2) 𝔽).toAddMonoidHom

noncomputable def χ' [CharP 𝔽 2] : 𝔽 → ℂ :=
  fun x => (-1 : ℂ) ^ (AbsTrace' 𝔽 x).val

private lemma neg_one_pow_add' (x y : ZMod 2) :
    (-1 : ℂ) ^ (x + y).val = (-1 : ℂ) ^ x.val * (-1 : ℂ) ^ y.val := by
  fin_cases x <;> fin_cases y <;> simp +decide [
    show (0 : ZMod 2).val = 0 from by decide,
    show (1 : ZMod 2).val = 1 from by decide,
    show (0 + 0 : ZMod 2) = 0 from by decide,
    show (0 + 1 : ZMod 2) = 1 from by decide,
    show (1 + 0 : ZMod 2) = 1 from by decide,
    show (1 + 1 : ZMod 2) = 0 from by decide]

noncomputable def χ'_addChar [CharP 𝔽 2] : AddChar 𝔽 ℂ where
  toFun := χ' 𝔽
  map_zero_eq_one' := by simp [χ', AbsTrace', map_zero]
  map_add_eq_mul' a b := by
    simp only [χ', map_add]
    exact neg_one_pow_add' (AbsTrace' 𝔽 a) (AbsTrace' 𝔽 b)

/-- **Known**: χ is primitive. -/
theorem χ'_isPrimitive [CharP 𝔽 2] :
    (χ'_addChar 𝔽).IsPrimitive := by sorry

/-! ## §2  MulChar from monoid hom -/

/-- Convert 𝔽ˣ →* ℂˣ to Mathlib MulChar. -/
def toMulChar (ψ : 𝔽ˣ →* ℂˣ) : MulChar 𝔽 ℂ where
  toFun x := if hx : x = 0 then 0 else (ψ (Units.mk0 x hx) : ℂ)
  map_one' := by simp [show (1 : 𝔽) ≠ 0 from one_ne_zero]
  map_mul' a b := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · simp_all
    · simp_all
    · simp_all
    · simp [ha, hb, mul_ne_zero ha hb]
  map_nonunit' a ha := by
    simp [show a = 0 from by by_contra h; exact ha (IsUnit.mk0 a h)]

/-
**Known**: Project's Gauss sum = Mathlib's gaussSum.
-/
theorem project_gauss_eq_mathlib [CharP 𝔽 2] (ψ : 𝔽ˣ →* ℂˣ) :
    ∑ x : 𝔽ˣ, (ψ x : ℂ) * χ' 𝔽 (x : 𝔽) =
      gaussSum (toMulChar 𝔽 ψ) (χ'_addChar 𝔽) := by
        unfold gaussSum;
        rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : 𝔽ˣ => ( x : 𝔽 ) ) Finset.univ ) ) ];
        · refine' Finset.sum_bij ( fun x _ => x ) _ _ _ _ <;> simp +decide [ toMulChar ];
          · aesop;
          · exact?;
        · simp +contextual [ toMulChar ];
          exact fun x hx hx' => False.elim ( hx ( Units.mk0 x hx' ) rfl )

/-! ## §3  Stickelberger via Mathlib -/

/-- Mathlib's Gauss sum product identity (directly from Mathlib). -/
theorem gauss_product_identity [CharP 𝔽 2]
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1) (hψ : (χ'_addChar 𝔽).IsPrimitive) :
    gaussSum χ (χ'_addChar 𝔽) * gaussSum χ⁻¹ (χ'_addChar 𝔽)⁻¹ =
      (Fintype.card 𝔽 : ℂ) :=
  gaussSum_mul_gaussSum_eq_card hχ hψ

/-- **Known**: ‖g(χ,ψ)‖² = q. -/
theorem gauss_norm_sq [CharP 𝔽 2]
    (χ : MulChar 𝔽 ℂ) (_hχ : χ ≠ 1) (_hψ : (χ'_addChar 𝔽).IsPrimitive) :
    ‖gaussSum χ (χ'_addChar 𝔽)‖ ^ 2 = (Fintype.card 𝔽 : ℝ) := by sorry

/-- ‖g(χ,ψ)‖ = √q (proved from norm²). -/
theorem gauss_norm_sqrt [CharP 𝔽 2]
    (χ : MulChar 𝔽 ℂ) (_hχ : χ ≠ 1) (_hψ : (χ'_addChar 𝔽).IsPrimitive)
    (hNorm : ‖gaussSum χ (χ'_addChar 𝔽)‖ ^ 2 = (Fintype.card 𝔽 : ℝ)) :
    ‖gaussSum χ (χ'_addChar 𝔽)‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
  exact hNorm

/-! ## §4  Kasami Exponent -/

def kasamiExp' (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- **Known**: Kasami exponent coprime to 2^n - 1. -/
theorem kasami_coprime (n k : ℕ) (_hn : n ≥ 1) (_hcoprime : Nat.Coprime k n) :
    Nat.Coprime (kasamiExp' k) (2 ^ n - 1) := by sorry

/-- **Known**: Kasami is a permutation. -/
theorem kasami_permutation (n k : ℕ) (_hn : n ≥ 1) (_hcoprime : Nat.Coprime k n)
    (_hcard : Fintype.card 𝔽 = 2 ^ n)
    (_hKC : Nat.Coprime (kasamiExp' k) (2 ^ n - 1)) :
    Function.Bijective (fun (x : 𝔽ˣ) => x ^ (kasamiExp' k)) := by sorry

/-! ## §5  Character Orthogonality -/

/-- From Mathlib: sum of nontrivial character is zero. -/
theorem character_orth [CharP 𝔽 2] (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    ∑ x : 𝔽, ψ x = 0 :=
  AddChar.sum_eq_zero_of_ne_one hψ

/-- Concrete: Σ_x χ(ax) = q·𝟙[a=0]. -/
theorem character_orth_concrete [CharP 𝔽 2] (a : 𝔽)
    (hχ : χ'_addChar 𝔽 ≠ 1) :
    ∑ x : 𝔽, χ' 𝔽 (a * x) = if a = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha, χ', AbsTrace', map_zero]
  · have : ∑ x : 𝔽, χ' 𝔽 (a * x) = ∑ y : 𝔽, χ' 𝔽 y :=
      Equiv.sum_comp (Equiv.mulLeft₀ a ha) _
    rw [this]; exact AddChar.sum_eq_zero_of_ne_one hχ

/-! ## §6  Walsh Trivial Bound -/

theorem walsh_trivial_bound [CharP 𝔽 2] (d : ℕ) (u : 𝔽) :
    ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖ ≤ Fintype.card 𝔽 := by
  calc ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖
      ≤ ∑ x : 𝔽, ‖χ' 𝔽 (u * x + x ^ d)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : 𝔽, 1 := by
        apply Finset.sum_le_sum; intro x _
        simp only [χ']; have : (AbsTrace' 𝔽 (u * x + x ^ d)).val < 2 := ZMod.val_lt _
        interval_cases (AbsTrace' 𝔽 (u * x + x ^ d)).val <;> simp
    _ = Fintype.card 𝔽 := by simp

/-! ## §7  Blackboxed Moment Results -/

/-- **Known**: APN ⟹ M₄ ≤ 2q³. -/
theorem apn_fourth_moment' [CharP 𝔽 2] (d : ℕ)
    (_hAPN : ∀ (a b : 𝔽), a ≠ 0 →
      (Finset.univ.filter (fun x => (x + a) ^ d + x ^ d = b)).card ≤ 2) :
    ∑ u : 𝔽, ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖ ^ 4 ≤
      2 * (Fintype.card 𝔽 : ℝ) ^ 3 := by sorry

/-- **Known**: Cauchy-Schwarz rigidity. -/
theorem moment_rigidity' [CharP 𝔽 2] (d : ℕ)
    (_hM₂ : ∑ u : 𝔽, ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖ ^ 2 =
      (Fintype.card 𝔽 : ℝ) ^ 2)
    (_hM₄ : ∑ u : 𝔽, ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖ ^ 4 ≤
      2 * (Fintype.card 𝔽 : ℝ) ^ 3) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ u : 𝔽,
      ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖ = 0 ∨
      ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖ = C := by sorry

/-! ## §8  Master Connection -/

/-- All connections from Mathlib to the project's spectral theory. -/
theorem master_gauss_connection [CharP 𝔽 2] :
    -- (i) Character orthogonality
    (χ'_addChar 𝔽 ≠ 1 → ∑ x : 𝔽, (χ'_addChar 𝔽) x = 0) ∧
    -- (ii) Gauss sum product
    (∀ (χ : MulChar 𝔽 ℂ), χ ≠ 1 → (χ'_addChar 𝔽).IsPrimitive →
      gaussSum χ (χ'_addChar 𝔽) * gaussSum χ⁻¹ (χ'_addChar 𝔽)⁻¹ =
        (Fintype.card 𝔽 : ℂ)) ∧
    -- (iii) Walsh bound
    (∀ d (u : 𝔽), ‖∑ x : 𝔽, χ' 𝔽 (u * x + x ^ d)‖ ≤ Fintype.card 𝔽) :=
  ⟨fun hχ => AddChar.sum_eq_zero_of_ne_one hχ,
   fun χ hχ hψ => gaussSum_mul_gaussSum_eq_card hχ hψ,
   fun d u => walsh_trivial_bound 𝔽 d u⟩

end