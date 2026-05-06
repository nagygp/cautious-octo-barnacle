/-
  KasamiFourier.lean

  Fourier analysis of the Kasami differential set Δ.

  Establishes the central Fourier identity:
    |F| · |{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}|
      = ∑_a δ̂(v₁·a) · δ̂(v₂·a) · δ̂((v₁+v₂)·a)

  This bridges the combinatorial count with the spectral side.

  Reference: Standard Fourier-analytic counting over finite abelian groups.
-/
import Mathlib
import KasamiTripleCount.KasamiDefs
import KasamiTripleCount.KasamiCharacters

noncomputable section

open Finset BigOperators Complex

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Indicator and Fourier Transform of Δ -/

/-- Indicator function of Δ: `1_Δ(x) = 1` if `x ∈ Δ`, else `0`. -/
def deltaIndicator (k : ℕ) (x : F) : ℂ :=
  if x ∈ kasamiDelta F k then 1 else 0

/-- Fourier transform of the indicator:
    `δ̂(a) = ∑_{x ∈ Δ} χ(a·x)`. -/
def deltaFourier (k : ℕ) (a : F) : ℂ :=
  ∑ x : F, deltaIndicator F k x * (kasamiChar F) (a * x)

omit [CharP F 2] in
theorem deltaFourier_eq_sum_over_delta (k : ℕ) (a : F) :
    deltaFourier F k a = ∑ x ∈ kasamiDelta F k, (kasamiChar F) (a * x) := by
  unfold deltaFourier deltaIndicator
  simp +decide

omit [CharP F 2] in
theorem deltaFourier_zero (k : ℕ) :
    deltaFourier F k (0 : F) = ↑(kasamiDelta F k).card := by
  have := deltaFourier_eq_sum_over_delta F k; simp_all +decide

/-! ## Orthogonality -/

theorem charSum_ite (t : F) :
    ∑ a : F, (kasamiChar F) (a * t) =
      if t = 0 then ↑(Fintype.card F) else 0 := by
  split_ifs with h
  · simp [h, AddChar.map_zero_eq_one]
  · exact sum_char_mul_eq_zero F t h

/-! ## Triple Spectral Sum -/

/-- `T_spec(v₁, v₂) = ∑_a δ̂(v₁·a) · δ̂(v₂·a) · δ̂((v₁+v₂)·a)`. -/
def tripleSpectral (k : ℕ) (v₁ v₂ : F) : ℂ :=
  ∑ a : F, deltaFourier F k (v₁ * a) *
           deltaFourier F k (v₂ * a) *
           deltaFourier F k ((v₁ + v₂) * a)

/-- Combinatorial side:
    `T_comb = ∑_{x,y,z ∈ Δ} [v₁x + v₂y + (v₁+v₂)z = 0]`. -/
def tripleCombinatorial (k : ℕ) (v₁ v₂ : F) : ℂ :=
  ∑ x ∈ kasamiDelta F k, ∑ y ∈ kasamiDelta F k, ∑ z ∈ kasamiDelta F k,
    if v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 then (1 : ℂ) else 0

omit [CharP F 2] in
theorem tripleCombinatorial_eq_card (k : ℕ) (v₁ v₂ : F) :
    tripleCombinatorial F k v₁ v₂ = ↑(tripleSet F k v₁ v₂).card := by
  unfold tripleCombinatorial tripleSet
  simp +decide only [card_filter]
  erw [Finset.sum_product]; norm_cast
  exact Finset.sum_congr rfl fun _ _ => by rw [Finset.sum_product]

/-! ## Fourier Expansion -/

omit [CharP F 2] in
theorem tripleSpectral_expand (k : ℕ) (v₁ v₂ : F) :
    tripleSpectral F k v₁ v₂ =
      ∑ x ∈ kasamiDelta F k, ∑ y ∈ kasamiDelta F k,
        ∑ z ∈ kasamiDelta F k, ∑ a : F,
          (kasamiChar F) (a * (v₁ * x + v₂ * y + (v₁ + v₂) * z)) := by
  unfold tripleSpectral
  simp +decide only [deltaFourier_eq_sum_over_delta]
  simp +decide only [mul_assoc, sum_mul _ _ _]
  simp +decide only [Finset.mul_sum _ _ _]
  simp +decide only [← mul_assoc, ← AddChar.map_add_eq_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
    Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring)))

theorem tripleSpectral_via_orthogonality (k : ℕ) (v₁ v₂ : F) :
    tripleSpectral F k v₁ v₂ =
      ↑(Fintype.card F) * tripleCombinatorial F k v₁ v₂ := by
  convert tripleSpectral_expand F k v₁ v₂ using 1
  rw [tripleCombinatorial]
  simp +decide only [Finset.mul_sum _ _ _]
  exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy =>
    Finset.sum_congr rfl fun z hz => by rw [charSum_ite]; aesop

/-- **THE FOURIER IDENTITY FOR TRIPLE COUNTING.**

    `|F| · |tripleSet| = tripleSpectral`

    This holds for ALL v₁, v₂. -/
theorem fourier_triple_identity (k : ℕ) (v₁ v₂ : F) :
    ↑(Fintype.card F) * ↑(tripleSet F k v₁ v₂).card = tripleSpectral F k v₁ v₂ := by
  rw [tripleSpectral_via_orthogonality, tripleCombinatorial_eq_card]

end
