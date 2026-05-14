import Mathlib

/-!
# AB Spectral Collapse — Top-Down Decomposition

## Goal
Decompose `combined_identity`:
  `|𝔽| · |𝒯(v₁,v₂)| = |Δ|³`
for Kasami power functions over GF(2ⁿ) with n odd, into a chain of
lemmas reaching down to Mathlib infrastructure.

## Proof Architecture (top → bottom)

```
  combined_identity                             -- Level 0 ✅
  ├── fourier_triple_inversion                  -- Level 1 ✅
  └── spectral_sum_eq_delta_cubed               -- Level 1 ✅ (composition)
      ├── kasami_is_AB                          -- Level 2 ✅ (composition)
      │   ├── gauss_sum_abs_sqrt_q              -- Level 3 ✅
      │   │   └── gauss_norm_sq_eq_card         -- Level 3 ✅
      │   │       └── gauss_mul_conj            -- Level 4 ✅ (Mathlib)
      │   └── gauss_abs_to_AB                   -- Level 3 [sorry]
      │       └── (Stickelberger + Frobenius)   -- not in Mathlib
      └── AB_implies_spectral_cube              -- Level 2 [sorry]
          └── (direct spectral analysis)        -- deep combinatorics
```

## Proved from Mathlib (✅)
- char2_add_self_zero, char2_neg_eq_id
- addchar_sum_zero, addchar_orthogonality
- gauss_mul_conj (gaussSum_mul_gaussSum_eq_card)
- gauss_norm_sq_eq_card, gauss_sum_abs_sqrt_q
- parseval_for_delta
- deltahat_at_zero
- fourier_triple_inversion
- All composition/wiring theorems

## Remaining sorry's (2 deep results)
1. `gauss_abs_to_AB` — Gauss sum magnitudes ⟹ AB property.
   Requires: Stickelberger relation + Frobenius decomposition of
   d = 4ᵏ − 2ᵏ + 1 into three Galois orbits, controlling Walsh phases.
2. `AB_implies_spectral_cube` — AB property ⟹ T(v₁,v₂) = |Δ|³.
   Requires: Detailed spectral analysis of the crosscorrelation function
   under the AB constraint. The naïve decomposition via two-valued |δ̂|²
   is FALSE (δ̂(0) = |Δ| ≠ 0 and |Δ|² ≠ 2q in general). The correct
   proof uses the full convolution structure of Δ and moment calculations.
-/

open Finset BigOperators Complex

noncomputable section

set_option maxHeartbeats 800000

-- ════════════════════════════════════════════════════════════
-- SECTION 1 : DEFINITIONS
-- ════════════════════════════════════════════════════════════

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

/-- Kasami exponent d(k) = 4ᵏ − 2ᵏ + 1 -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- Power map x ↦ x^d on 𝔽 -/
def kasamiF (k : ℕ) (x : 𝔽) : 𝔽 := x ^ kasamiExp k

/-- Differential set Δ = { f(b) + f(b+1) + 1 | b ∈ 𝔽 } -/
def Δ (k : ℕ) : Finset 𝔽 :=
  Finset.univ.image (fun b : 𝔽 => kasamiF 𝔽 k b + kasamiF 𝔽 k (b + 1) + 1)

/-- Walsh transform  Ŵ_g(u) = Σ_{x ∈ 𝔽} ψ(g(x) + u·x) -/
def walshTransform (ψ : AddChar 𝔽 ℂ) (g : 𝔽 → 𝔽) (u : 𝔽) : ℂ :=
  ∑ x : 𝔽, ψ (g x + u * x)

/-- AB (Almost Bent) predicate:
    ∀ u, ‖Ŵ(u)‖² ∈ {0, 2·q}  where q = |𝔽| -/
def IsAB (ψ : AddChar 𝔽 ℂ) (g : 𝔽 → 𝔽) : Prop :=
  ∀ u : 𝔽, ‖walshTransform 𝔽 ψ g u‖ ^ 2 = 0 ∨
            ‖walshTransform 𝔽 ψ g u‖ ^ 2 = (2 : ℝ) * (Fintype.card 𝔽 : ℝ)

/-- Fourier coefficient of 1_Δ: δ̂(a) = Σ_{x ∈ Δ} ψ(a·x) -/
def deltaHat (ψ : AddChar 𝔽 ℂ) (k : ℕ) (a : 𝔽) : ℂ :=
  ∑ x ∈ Δ 𝔽 k, ψ (a * x)

/-- Triple set 𝒯(v₁,v₂) = { (x,y,z) ∈ Δ³ | v₁x + v₂y + (v₁+v₂)z = 0 } -/
def 𝒯 (k : ℕ) (v₁ v₂ : 𝔽) : Finset (𝔽 × 𝔽 × 𝔽) :=
  ((Δ 𝔽 k) ×ˢ (Δ 𝔽 k) ×ˢ (Δ 𝔽 k)).filter
    (fun t => v₁ * t.1 + v₂ * t.2.1 + (v₁ + v₂) * t.2.2 = 0)

/-- Spectral triple sum T(v₁,v₂) = Σ_{a ∈ 𝔽} δ̂(v₁a)·δ̂(v₂a)·δ̂((v₁+v₂)a) -/
def spectralTripleSum (ψ : AddChar 𝔽 ℂ) (k : ℕ) (v₁ v₂ : 𝔽) : ℂ :=
  ∑ a : 𝔽, deltaHat 𝔽 ψ k (v₁ * a) *
           deltaHat 𝔽 ψ k (v₂ * a) *
           deltaHat 𝔽 ψ k ((v₁ + v₂) * a)

-- ════════════════════════════════════════════════════════════
-- SECTION 2 : LEVEL 5 — MATHLIB FOUNDATIONS (all ✅)
-- ════════════════════════════════════════════════════════════

/-- In characteristic 2, x + x = 0. ✅ -/
theorem char2_add_self_zero (x : 𝔽) : x + x = 0 := by
  have h : (2 : 𝔽) = 0 := CharP.cast_eq_zero 𝔽 2
  calc x + x = 2 * x := by ring
    _ = 0 * x := by rw [h]
    _ = 0 := zero_mul x

/-- In characteristic 2, −x = x. ✅ -/
theorem char2_neg_eq_id (x : 𝔽) : -x = x := by
  have h : x + x = 0 := char2_add_self_zero 𝔽 x
  have : -x = -(x + x) + x := by ring
  rw [h] at this; simpa using this

/-- d(k) = 4ᵏ − 2ᵏ + 1 by definition. ✅ -/
theorem kasami_exp_structure (k : ℕ) : kasamiExp k = 4 ^ k - 2 ^ k + 1 := rfl

-- ════════════════════════════════════════════════════════════
-- SECTION 3 : LEVEL 4 — CHARACTER THEORY (all ✅)
-- ════════════════════════════════════════════════════════════

/-- For primitive ψ, Σ_x ψ(x) = 0. ✅ -/
theorem addchar_sum_zero
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) :
    ∑ x : 𝔽, ψ x = 0 := by
  have h_ne : ψ ≠ 1 := by
    intro h; simp_all [AddChar.IsPrimitive]
    exact hψ (show (1 : 𝔽) ≠ 0 by simp) (by ext; simp +decide [AddChar.mulShift])
  exact AddChar.sum_eq_zero_of_ne_one h_ne

/-- G(χ,ψ)·G(χ⁻¹,ψ⁻¹) = q. ✅ (Mathlib: gaussSum_mul_gaussSum_eq_card) -/
theorem gauss_mul_conj
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = ↑(Fintype.card 𝔽) :=
  gaussSum_mul_gaussSum_eq_card hχ hψ

/-
Primitive additive characters exist. ✅
-/
theorem trace_defines_primitive_char
    (n : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card 𝔽 = 2 ^ n) :
    ∃ (ψ : AddChar 𝔽 ℂ), ψ.IsPrimitive := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar 𝔽 ℂ, ψ ≠ 1 := by
    by_contra! h;
    have h_contra : Fintype.card (AddChar 𝔽 ℂ) = 1 := by
      exact Fintype.card_eq_one_iff.mpr ⟨ 1, h ⟩;
    exact absurd h_contra ( by rw [ Fintype.card_eq_nat_card ] ; simp +decide [ hcard, Nat.pow_le_pow_right ] ; linarith );
  contrapose! hψ;
  apply AddChar.ext;
  intro x; specialize hψ ψ; simp_all +decide [ AddChar.IsPrimitive ] ;
  obtain ⟨ y, hy, hy' ⟩ := hψ; replace hy' := congr_arg ( fun f => f ( x / y ) ) hy'; simp_all +decide [ div_eq_inv_mul, AddChar.mulShift_apply ] ;

-- ════════════════════════════════════════════════════════════
-- SECTION 4 : LEVEL 3 — GAUSS SUMS, PARSEVAL (mostly ✅)
-- ════════════════════════════════════════════════════════════

/-- Additive character orthogonality: Σ_x ψ(ax) = q·[a=0]. ✅ -/
theorem addchar_orthogonality
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) (a : 𝔽) :
    ∑ x : 𝔽, ψ (a * x) =
      if a = 0 then ↑(Fintype.card 𝔽) else 0 := by
  split_ifs with ha
  · subst ha; simp
  · calc ∑ x : 𝔽, ψ (a * x)
        = ∑ x : 𝔽, ψ x := Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun x => ψ x)
      _ = 0 := addchar_sum_zero 𝔽 ψ hψ

/-
|G(χ,ψ)|² = q for nontrivial χ. ✅
-/
theorem gauss_norm_sq_eq_card
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card 𝔽 : ℝ) := by
  have h_gauss_mul : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card 𝔽 : ℂ) := by
    exact?;
  have h_gauss_conj : gaussSum χ⁻¹ ψ⁻¹ = starRingEnd ℂ (gaussSum χ ψ) := by
    have h_gauss_conj : ∀ x : 𝔽, χ⁻¹ x = starRingEnd ℂ (χ x) := by
      intro x; by_cases hx : x = 0 <;> simp +decide [ hx, MulChar.inv_apply ] ;
      · simp +decide [ MulChar.map_zero ];
      · have h_gauss_conj : ∀ x : 𝔽ˣ, χ x⁻¹ = starRingEnd ℂ (χ x) := by
          have h_gauss_conj : ∀ x : 𝔽ˣ, χ x * starRingEnd ℂ (χ x) = 1 := by
            intro x; rw [ Complex.mul_conj ] ; simp +decide [ Complex.normSq_eq_norm_sq ] ;
            have h_gauss_conj : ∀ x : 𝔽ˣ, χ x ^ (Fintype.card 𝔽ˣ) = 1 := by
              simp +decide [ ← map_pow, pow_card_eq_one ];
              simp +decide [ ← Units.val_pow_eq_pow_val, pow_card_eq_one ];
            exact Or.inl ( by have := h_gauss_conj x; replace := congr_arg Norm.norm this; norm_num at this; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop );
          intro x; specialize h_gauss_conj x; simp_all +decide [ mul_comm ] ;
          have := χ.map_mul x⁻¹ x; simp_all +decide [ mul_comm ] ;
          grind;
        simpa using h_gauss_conj ( Units.mk0 x hx );
    simp +decide [ gaussSum, h_gauss_conj ];
    refine' Finset.sum_congr rfl fun x _ => _;
    exact congr_arg _ ( by rw [ show ψ ( -x ) = ( starRingEnd ℂ ) ( ψ x ) from by simp +decide [ AddChar.map_neg_eq_conj ] ] );
  simp_all +decide [ Complex.ext_iff, sq ];
  simp_all +decide [ Complex.normSq, Complex.norm_def ]

/-- |G(χ,ψ)| = √q. ✅ (from gauss_norm_sq_eq_card) -/
theorem gauss_sum_abs_sqrt_q
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
  rw [← gauss_norm_sq_eq_card 𝔽 ψ hψ χ hχ, Real.sqrt_sq (norm_nonneg _)]

/-- **gauss_abs_to_AB**: Gauss sum magnitudes ⟹ AB property for Kasami.

    This is the deepest sorry in the chain. The proof requires:
    1. Expressing Ŵ_{x^d}(u) as a product of three Frobenius-shifted
       Gauss sums G(χ^{2^0}, ψ) · G(χ^{2^k}, ψ) · G(χ^{2^{2k}}, ψ)
       (using the Kasami exponent d = 1 + 2^k(2^k − 1))
    2. Showing that with gcd(k,n) = 1 and n odd, the three Frobenius
       orbits are distinct, so the product has magnitude q^{3/2}
    3. Dividing by q to get |Ŵ(u)| = √(2q) when nonzero
    4. This uses the Stickelberger relation to control phases -/
theorem gauss_abs_to_AB
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (hgauss : ∀ (χ : MulChar 𝔽 ℂ), χ ≠ 1 →
      ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ)) :
    IsAB 𝔽 ψ (kasamiF 𝔽 k) := by
  sorry

/-- δ̂(0) = |Δ|. ✅ -/
theorem deltahat_at_zero
    (ψ : AddChar 𝔽 ℂ) (k : ℕ) :
    deltaHat 𝔽 ψ k 0 = ↑(Δ 𝔽 k).card := by
  simp [deltaHat]

/-
Parseval: Σ_a |δ̂(a)|² = q·|Δ|. ✅
-/
theorem parseval_for_delta
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) (k : ℕ) :
    ∑ a : 𝔽, ‖deltaHat 𝔽 ψ k a‖ ^ 2 =
      (Fintype.card 𝔽 : ℝ) * (Δ 𝔽 k).card := by
  -- By definition of $deltaHat$, we have:
  have h_deltaHat_def : ∀ a : 𝔽, ‖deltaHat 𝔽 ψ k a‖ ^ 2 = ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, ψ (a * (x - y)) := by
    intro a
    have h_expand : ‖deltaHat 𝔽 ψ k a‖ ^ 2 = (∑ x ∈ Δ 𝔽 k, ψ (a * x)) * (∑ y ∈ Δ 𝔽 k, starRingEnd ℂ (ψ (a * y))) := by
      have h_expand : ‖deltaHat 𝔽 ψ k a‖ ^ 2 = (∑ x ∈ Δ 𝔽 k, ψ (a * x)) * starRingEnd ℂ (∑ x ∈ Δ 𝔽 k, ψ (a * x)) := by
        rw [ Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow ];
        rfl;
      rw [ h_expand, map_sum ];
    rw [ h_expand, Finset.sum_mul ];
    simp +decide [ mul_sub, Finset.mul_sum _ _ _, Finset.sum_mul ];
    refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
    rw [ show ψ ( a * x - a * y ) = ψ ( a * x ) * ψ ( - ( a * y ) ) by rw [ ← AddChar.map_add_eq_mul ] ; ring, AddChar.map_neg_eq_inv ];
    have h_char : ∀ x : 𝔽, ψ x * starRingEnd ℂ (ψ x) = 1 := by
      simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    exact congr_arg _ ( eq_inv_of_mul_eq_one_right ( h_char _ ) );
  -- By character orthogonality, $\sum_{a \in \mathbb{F}} \psi(a(x-y)) = q$ if $x=y$ and $0$ otherwise.
  have h_char_ortho : ∀ x y : 𝔽, (∑ a : 𝔽, ψ (a * (x - y))) = if x = y then (Fintype.card 𝔽 : ℂ) else 0 := by
    intro x y; split_ifs with hxy; simp +decide [ hxy ] ; have := addchar_orthogonality 𝔽 ψ hψ ( x - y ) ; simp_all +decide [ mul_comm ] ;
    exact sub_ne_zero_of_ne hxy;
  have h_sum_char_ortho : ∑ a : 𝔽, ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, ψ (a * (x - y)) = ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, (if x = y then (Fintype.card 𝔽 : ℂ) else 0) := by
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun y hy => h_char_ortho x y;
  convert congr_arg Complex.re h_sum_char_ortho using 1 <;> norm_num [ ← h_deltaHat_def, mul_comm ];
  norm_cast

-- ════════════════════════════════════════════════════════════
-- SECTION 5 : LEVEL 2 — AB + SPECTRAL CUBE
-- ════════════════════════════════════════════════════════════

/-- Kasami is AB. ✅ (from gauss_sum_abs_sqrt_q + gauss_abs_to_AB) -/
theorem kasami_is_AB
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) :
    IsAB 𝔽 ψ (kasamiF 𝔽 k) :=
  gauss_abs_to_AB 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ
    (fun χ hχ => gauss_sum_abs_sqrt_q 𝔽 ψ hψ χ hχ)

/-- **AB_implies_spectral_cube**: AB property ⟹ T(v₁,v₂) = |Δ|³.

    This is the second deep sorry. The proof requires computing
    the triple spectral sum Σ_a δ̂(v₁a)·δ̂(v₂a)·δ̂((v₁+v₂)a) using:

    1. The crosscorrelation structure of an AB function
    2. The multiplicative Fourier expansion of the derivative indicator
    3. Moment calculations showing the a≠0 terms cancel

    NOTE: A naïve decomposition via ‖δ̂(a)‖² ∈ {0, 2q} is FALSE
    (counterexample: δ̂(0) = |Δ| = 2^{n-1}, and |Δ|² = 2^{2n-2} ≠ 2q
    unless n = 3). The correct proof requires the full convolution
    structure and is closely tied to the specific Kasami function. -/
theorem AB_implies_spectral_cube
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (hAB : IsAB 𝔽 ψ (kasamiF 𝔽 k))
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3) := by
  sorry

/-
════════════════════════════════════════════════════════════
SECTION 6 : LEVEL 1 — FOURIER INVERSION + SPECTRAL COLLAPSE
════════════════════════════════════════════════════════════

Fourier inversion: |𝔽|·|𝒯| = T. ✅
-/
theorem fourier_triple_inversion
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive) (k : ℕ) (v₁ v₂ : 𝔽) :
    (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card =
      spectralTripleSum 𝔽 ψ k v₁ v₂ := by
  -- Expand the spectral triple sum and use character orthogonality.
  have h_expand : spectralTripleSum 𝔽 ψ k v₁ v₂ = ∑ x ∈ Δ 𝔽 k, ∑ y ∈ Δ 𝔽 k, ∑ z ∈ Δ 𝔽 k, ∑ a : 𝔽, ψ (a * (v₁ * x + v₂ * y + (v₁ + v₂) * z)) := by
    simp +decide only [spectralTripleSum, deltaHat];
    simp +decide only [sum_mul _ _ _, mul_sum, sum_sigma'];
    refine' Finset.sum_bij ( fun x _ => ⟨ x.snd.fst.fst, x.snd.fst.snd, x.snd.snd, x.fst ⟩ ) _ _ _ _ <;> simp +decide;
    · tauto;
    · bound;
    · exact fun b hb₁ hb₂ hb₃ => ⟨ b.2.2.2, b.1, b.2.1, b.2.2.1, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃ ⟩, rfl ⟩;
    · simp +decide [ mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, AddChar.map_add_eq_mul ];
  -- By character orthogonality, $\sum_{a \in \mathbb{F}} \psi(a \cdot c) = q \cdot [c = 0]$.
  have h_ortho : ∀ c : 𝔽, ∑ a : 𝔽, ψ (a * c) = if c = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
    convert addchar_orthogonality 𝔽 ψ hψ using 1;
    simp +decide only [mul_comm];
  simp_all +decide [ mul_comm, mul_assoc, mul_left_comm, Finset.sum_ite ];
  unfold 𝒯; simp +decide [ mul_comm, Finset.sum_filter ] ;
  simp +decide only [card_filter, sum_product];
  simp +decide only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum _ _ _,
      mul_comm]

/-- T = |Δ|³. ✅ (from kasami_is_AB + AB_implies_spectral_cube) -/
theorem spectral_sum_eq_delta_cubed
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3) :=
  AB_implies_spectral_cube 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ
    (kasami_is_AB 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ)
    v₁ v₂ hv₁ hv₂ hne

-- ════════════════════════════════════════════════════════════
-- SECTION 7 : LEVEL 0 — THE MAIN THEOREM
-- ════════════════════════════════════════════════════════════

/-- **combined_identity** : |𝔽| · |𝒯(v₁,v₂)| = |Δ|³.
    ✅ (from fourier_triple_inversion + spectral_sum_eq_delta_cubed) -/
theorem combined_identity
    (n k : ℕ)
    (hn : 3 ≤ n) (hn_odd : n % 2 = 1) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) (hk : 1 ≤ k)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ.IsPrimitive)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    Fintype.card 𝔽 * (𝒯 𝔽 k v₁ v₂).card = (Δ 𝔽 k).card ^ 3 := by
  have h1 := fourier_triple_inversion 𝔽 ψ hψ k v₁ v₂
  have h2 := spectral_sum_eq_delta_cubed 𝔽 n k hn hn_odd hcard hcoprime hk ψ hψ v₁ v₂ hv₁ hv₂ hne
  have h3 : (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card = ↑((Δ 𝔽 k).card ^ 3) := by
    rw [h1, h2]
  exact_mod_cast h3

-- ════════════════════════════════════════════════════════════
-- SECTION 8 : COMPOSITION WITNESSES (all ✅)
-- ════════════════════════════════════════════════════════════

set_option linter.unusedSectionVars false in
/-- L1 → L0 composition witness -/
theorem combined_identity_from_L1
    (k : ℕ) (ψ : AddChar 𝔽 ℂ) (v₁ v₂ : 𝔽)
    (h_fourier : (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card =
      spectralTripleSum 𝔽 ψ k v₁ v₂)
    (h_spectral : spectralTripleSum 𝔽 ψ k v₁ v₂ = ↑((Δ 𝔽 k).card ^ 3)) :
    (Fintype.card 𝔽 : ℂ) * ↑(𝒯 𝔽 k v₁ v₂).card = ↑((Δ 𝔽 k).card ^ 3) := by
  rw [h_fourier, h_spectral]

set_option linter.unusedSectionVars false in
/-- L4 → L3 composition witness -/
theorem gauss_sum_abs_from_norm_sq
    (ψ : AddChar 𝔽 ℂ) (χ : MulChar 𝔽 ℂ)
    (h_sq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card 𝔽 : ℝ)) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
  rw [← h_sq, Real.sqrt_sq (norm_nonneg _)]

end