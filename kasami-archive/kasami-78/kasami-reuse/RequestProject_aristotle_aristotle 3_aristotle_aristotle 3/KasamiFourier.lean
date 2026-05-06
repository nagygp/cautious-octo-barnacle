/-
  KasamiFourier.lean

  Step 2 of the Kasami Triple-Count proof pathway:
  Fourier analysis of the Kasami differential set Δ.

  Building on `KasamiCharacters.lean` (Step 1), this file establishes:
  1. The indicator (characteristic) function of Δ = kasamiDelta.
  2. Its Fourier transform: `deltaFourier(a) = ∑_{x ∈ Δ} χ(a·x)`.
  3. The orthogonality identity for the primitive character χ:
       ∑_a χ(a·t) = |F| if t = 0, else 0.
  4. The **Fourier identity for triple counting**:
       |F| · |{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}|
         = ∑_a δ̂(v₁·a) · δ̂(v₂·a) · δ̂((v₁+v₂)·a)

  This does NOT prove the constant 2^{2n-3}; it only establishes
  the bridge between the combinatorial triple count and the spectral side.

  Reference: Standard Fourier-analytic counting over finite abelian groups.
-/
import Mathlib
import KasamiConjecture
import KasamiCharacters

noncomputable section

open Finset BigOperators Complex

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Section 1: Indicator Function of kasamiDelta -/

/-- The indicator (characteristic) function of the Kasami differential set Δ,
    as a ℂ-valued function: `1_Δ(x) = 1` if `x ∈ Δ`, else `0`. -/
def deltaIndicator (k : ℕ) (x : F) : ℂ :=
  if x ∈ kasamiDelta F k then 1 else 0

omit [CharP F 2] in
theorem deltaIndicator_mem {k : ℕ} {x : F} (hx : x ∈ kasamiDelta F k) :
    deltaIndicator F k x = 1 := by
  simp [deltaIndicator, hx]

omit [CharP F 2] in
theorem deltaIndicator_nmem {k : ℕ} {x : F} (hx : x ∉ kasamiDelta F k) :
    deltaIndicator F k x = 0 := by
  simp [deltaIndicator, hx]

omit [CharP F 2] in
theorem deltaIndicator_cases (k : ℕ) (x : F) :
    deltaIndicator F k x = 0 ∨ deltaIndicator F k x = 1 := by
  unfold deltaIndicator; split_ifs <;> simp

/-! ## Section 2: Fourier Transform of the Indicator Function -/

/-- The Fourier transform of the indicator function of Δ:
    `δ̂(a) = ∑_{x ∈ F} 1_Δ(x) · χ(a·x) = ∑_{x ∈ Δ} χ(a·x)`. -/
def deltaFourier (k : ℕ) (a : F) : ℂ :=
  ∑ x : F, deltaIndicator F k x * (kasamiChar F) (a * x)

/-
The Fourier transform equals the sum restricted to Δ.
-/
omit [CharP F 2] in
theorem deltaFourier_eq_sum_over_delta (k : ℕ) (a : F) :
    deltaFourier F k a = ∑ x ∈ kasamiDelta F k, (kasamiChar F) (a * x) := by
  unfold deltaFourier deltaIndicator;
  simp +decide

/-
At a = 0, the Fourier transform equals |Δ|.
-/
omit [CharP F 2] in
theorem deltaFourier_zero (k : ℕ) :
    deltaFourier F k (0 : F) = ↑(kasamiDelta F k).card := by
  have := deltaFourier_eq_sum_over_delta F k; simp_all +decide ;

/-! ## Section 3: Full Orthogonality Identity -/

/-- **Full orthogonality for the primitive character χ.**
    `∑_{a ∈ F} χ(a · t) = |F|` when `t = 0`, and `= 0` when `t ≠ 0`. -/
theorem charSum_ite (t : F) :
    ∑ a : F, (kasamiChar F) (a * t) =
      if t = 0 then ↑(Fintype.card F) else 0 := by
  split_ifs with h
  · simp [h, AddChar.map_zero_eq_one]
  · exact sum_char_mul_eq_zero F t h

/-- Same as `charSum_ite` but with multiplication on the left. -/
theorem charSum_ite' (t : F) :
    ∑ a : F, (kasamiChar F) (t * a) =
      if t = 0 then ↑(Fintype.card F) else 0 := by
  simp only [show ∀ a : F, t * a = a * t from fun a => mul_comm t a]
  exact charSum_ite F t

/-! ## Section 4: The Fourier Identity for Triple Counting -/

/-- The "triple sum" — the spectral side of the Fourier identity.
    `T_spec(v₁, v₂) = ∑_a δ̂(v₁·a) · δ̂(v₂·a) · δ̂((v₁+v₂)·a)`. -/
def tripleSpectral (k : ℕ) (v₁ v₂ : F) : ℂ :=
  ∑ a : F, deltaFourier F k (v₁ * a) *
           deltaFourier F k (v₂ * a) *
           deltaFourier F k ((v₁ + v₂) * a)

/-- The "triple count" expressed as a ℂ-valued sum over Δ³ with the
    orthogonality filter. This is the combinatorial side:
    `T_comb(v₁, v₂) = ∑_{x ∈ Δ} ∑_{y ∈ Δ} ∑_{z ∈ Δ} [v₁x + v₂y + (v₁+v₂)z = 0]`. -/
def tripleCombinatorial (k : ℕ) (v₁ v₂ : F) : ℂ :=
  ∑ x ∈ kasamiDelta F k, ∑ y ∈ kasamiDelta F k, ∑ z ∈ kasamiDelta F k,
    if v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 then (1 : ℂ) else 0

/-
The combinatorial triple count equals the cardinality of `tripleSet`.
-/
omit [CharP F 2] in
theorem tripleCombinatorial_eq_card (k : ℕ) (v₁ v₂ : F) :
    tripleCombinatorial F k v₁ v₂ = ↑(tripleSet F k v₁ v₂).card := by
  unfold tripleCombinatorial tripleSet;
  simp +decide only [card_filter];
  erw [ Finset.sum_product ] ; norm_cast;
  exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_product ] ;

/-
**Key helper**: The Fourier expansion identity.
    Expanding the three Fourier transforms and swapping sums yields:
    `∑_a δ̂(v₁a) · δ̂(v₂a) · δ̂((v₁+v₂)a)`
    `= ∑_{x ∈ Δ} ∑_{y ∈ Δ} ∑_{z ∈ Δ} ∑_a χ(a·(v₁x + v₂y + (v₁+v₂)z))`.
-/
omit [CharP F 2] in
theorem tripleSpectral_expand (k : ℕ) (v₁ v₂ : F) :
    tripleSpectral F k v₁ v₂ =
      ∑ x ∈ kasamiDelta F k, ∑ y ∈ kasamiDelta F k,
        ∑ z ∈ kasamiDelta F k, ∑ a : F,
          (kasamiChar F) (a * (v₁ * x + v₂ * y + (v₁ + v₂) * z)) := by
  unfold tripleSpectral;
  simp +decide only [deltaFourier_eq_sum_over_delta];
  simp +decide only [mul_assoc, sum_mul _ _ _];
  simp +decide only [Finset.mul_sum _ _ _];
  simp +decide only [← mul_assoc, ← AddChar.map_add_eq_mul];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ) )

/-
**Key helper**: Applying orthogonality to the inner sum.
    The inner sum ∑_a χ(a·t) acts as `|F| · δ_{t,0}`, so:
    `∑_{x,y,z ∈ Δ} ∑_a χ(a·(v₁x+v₂y+(v₁+v₂)z))`
    `= |F| · ∑_{x,y,z ∈ Δ} [v₁x + v₂y + (v₁+v₂)z = 0]`
    `= |F| · T_comb(v₁, v₂)`.
-/
theorem tripleSpectral_via_orthogonality (k : ℕ) (v₁ v₂ : F) :
    tripleSpectral F k v₁ v₂ =
      ↑(Fintype.card F) * tripleCombinatorial F k v₁ v₂ := by
  convert tripleSpectral_expand F k v₁ v₂ using 1;
  rw [ tripleCombinatorial ];
  simp +decide only [Finset.mul_sum _ _ _];
  exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun z hz => by rw [ charSum_ite ] ; aesop;

/-- **THE FOURIER IDENTITY FOR TRIPLE COUNTING.**

    This is the central bridge between the combinatorial world and the spectral world:

    `|F| · |{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}|`
    `= ∑_a δ̂(v₁·a) · δ̂(v₂·a) · δ̂((v₁+v₂)·a)`

    Equivalently:
    `↑(tripleSet F k v₁ v₂).card = (↑|F|)⁻¹ · tripleSpectral(v₁, v₂)`

    This identity holds for ALL v₁, v₂ (not just distinct nonzero ones).
    The constant `2^{2n-3}` is NOT proved here; that requires analyzing the
    spectral values of `deltaFourier` using the AB property of the Kasami function. -/
theorem fourier_triple_identity (k : ℕ) (v₁ v₂ : F) :
    ↑(Fintype.card F) * ↑(tripleSet F k v₁ v₂).card = tripleSpectral F k v₁ v₂ := by
  rw [tripleSpectral_via_orthogonality, tripleCombinatorial_eq_card]

end