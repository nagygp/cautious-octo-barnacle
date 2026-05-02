/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cross-Correlation of m-Sequences

This module formalizes the cross-correlation theory of maximal-length linear
recurring sequences (m-sequences) over `GF(2^n)`, connecting sequence-level
cross-correlation to the Walsh–Hadamard transform and the Almost Bent property.

## Overview

An **m-sequence** of period `2^n - 1` over `GF(2)` is the sequence
`{Tr(α^t) : t = 0, 1, ..., 2^n - 2}` where `α` is a primitive element
of `GF(2^n)` and `Tr` is the absolute trace to `GF(2)`.

Given a decimation `d`, the **cross-correlation** of two m-sequences at
element `b ∈ GF(2^n)` is:
  `C_d(b) = ∑_{x ∈ GF(2^n)^*} χ(x + b·x^d)`
where `χ(x) = (-1)^{Tr(x)}` is the canonical additive character.

The key results are:
1. `C_d(b) + 1 = ∑_{x ∈ F} χ(x + b·x^d)` (inclusion of x=0 term)
2. For bijective power maps (`gcd(d, 2^n-1) = 1`):
   `C_d(b) + 1 = W_{x^e}(b)` where `e ≡ d⁻¹ (mod 2^n - 1)`
3. Three-valued cross-correlation ↔ Almost Bent property

## Main definitions

- `crossCorrFull f b` — the "full" cross-correlation `∑_x χ(x + b·f(x))`
- `crossCorr f b` — the cross-correlation `∑_{x ≠ 0} χ(x + b·f(x))`
- `IsThreeValuedCrossCorr f` — three-valued cross-correlation property

## Main results

- `crossCorr_eq_full_sub_one` — `C_f(b) = Ĉ_f(b) - 1`
- `crossCorrFull_bij_eq_wht_inv` — `Ĉ_f(b) = W_{f⁻¹}(b)` for bijections
- `threeValuedCrossCorr_iff_ab_inv` — three-valued ↔ AB of inverse
- `crossCorrFull_parseval` — Parseval identity for cross-correlation
- `kasami_three_valued_crossCorr` — Kasami three-valued theorem

## References

- [Gold (1968)][gold1968], IEEE Trans. IT 14(1)
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Canteaut, Charpin, Dobbertin (2000)][canteaut2000], SIAM J. Discrete Math.
- [Carlet (2021)][carlet2021], *Boolean Functions for Cryptography and Coding Theory*, Ch. 6
- [Lidl, Niederreiter (1997)][lidl1997], *Finite Fields*, Ch. 5
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ## Cross-Correlation Definitions -/

/-- The "full" cross-correlation of a function `f : F_{2^n} → F_{2^n}` at element `b`,
    summing over ALL elements of `F_{2^n}` (including 0):
    `Ĉ_f(b) = ∑_{x ∈ F_{2^n}} χ(x + b · f(x))`

    This differs from the standard cross-correlation by the `x = 0` term
    (which contributes `χ(0) = 1`). -/
def crossCorrFull {n : ℕ} (f : F2n n → F2n n) (b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (x + b * f x)

/-- The cross-correlation of a function `f : F_{2^n} → F_{2^n}` at element `b`,
    summing over nonzero elements:
    `C_f(b) = ∑_{x ∈ F_{2^n}^*} χ(x + b · f(x))`

    This is the standard cross-correlation of the m-sequence with its
    `f`-decimated version. When `f(x) = x^d`, this gives the classical
    cross-correlation function `C_d(b)`. -/
def crossCorr {n : ℕ} (f : F2n n → F2n n) (b : F2n n) : ℤ :=
  ∑ x ∈ Finset.univ.filter (· ≠ (0 : F2n n)), chi n (x + b * f x)

/-! ## Basic Properties -/

/-- The cross-correlation equals the full cross-correlation minus 1
    (the `x = 0` term contributes `χ(0) = 1`). -/
theorem crossCorr_eq_full_sub_one {n : ℕ} (f : F2n n → F2n n) (hf : f 0 = 0)
    (b : F2n n) :
    crossCorr f b = crossCorrFull f b - 1 := by
  unfold crossCorr crossCorrFull
  have h0 : chi n ((0 : F2n n) + b * f 0) = 1 := by simp [hf, chi_zero]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2n n)), h0]
  have : ∑ x ∈ Finset.univ.erase 0, chi n (x + b * f x) =
      ∑ x ∈ Finset.univ.filter (· ≠ (0 : F2n n)), chi n (x + b * f x) := by
    apply Finset.sum_congr
    · ext x; simp [Finset.mem_erase, Finset.mem_filter]
    · intros; rfl
  linarith

/-- Equivalent formulation: `C_f(b) + 1 = Ĉ_f(b)`. -/
theorem crossCorr_add_one {n : ℕ} (f : F2n n → F2n n) (hf : f 0 = 0)
    (b : F2n n) :
    crossCorr f b + 1 = crossCorrFull f b := by
  linarith [crossCorr_eq_full_sub_one f hf b]

/-- The full cross-correlation at `b = 0` equals the character sum `∑_x χ(x)`. -/
theorem crossCorrFull_zero {n : ℕ} (f : F2n n → F2n n) :
    crossCorrFull f 0 = ∑ x : F2n n, chi n x := by
  simp [crossCorrFull]

/-- The cross-correlation at `b = 0` equals `-1` (for `n ≥ 1`). -/
theorem crossCorr_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : f 0 = 0) :
    crossCorr f 0 = -1 := by
  rw [crossCorr_eq_full_sub_one f hf]
  simp only [crossCorrFull_zero]
  rw [chi_sum_all_zero hn]
  ring

/-! ## Connection to Walsh–Hadamard Transform -/

/-- The full cross-correlation equals the WHT of the scaled function `b · f`
    evaluated at `a = 1`:
    `Ĉ_f(b) = W_{b·f}(1) = ∑_x χ(1·x + (b·f)(x))` -/
theorem crossCorrFull_eq_wht_scaled {n : ℕ} (f : F2n n → F2n n) (b : F2n n) :
    crossCorrFull f b = wht (fun x => b * f x) 1 := by
  unfold crossCorrFull wht
  congr 1; ext x; congr 1; ring

/-
**Key theorem**: For bijective `f`, the full cross-correlation equals the WHT
    of the compositional inverse `f⁻¹`:
    `Ĉ_f(b) = W_{f⁻¹}(b)`

    Proof: Substituting `y = f(x)` (which is a bijection), we get
    `∑_x χ(x + b·f(x)) = ∑_y χ(f⁻¹(y) + b·y) = W_{f⁻¹}(b)`.

    This is the fundamental connection between cross-correlation and Walsh
    spectrum that underlies the Kasami three-valued theorem.
-/
theorem crossCorrFull_bij_eq_wht_inv {n : ℕ} (f : F2n n → F2n n)
    (hf : Function.Bijective f) (b : F2n n) :
    crossCorrFull f b = wht (Function.invFun f) b := by
  unfold crossCorrFull wht;
  conv_rhs => rw [ ← Equiv.sum_comp ( Equiv.ofBijective f hf ) ] ;
  simp +decide [ Function.invFun_eq ( hf.2 _ ), add_comm ];
  exact Finset.sum_congr rfl fun x hx => by rw [ Function.leftInverse_invFun hf.injective ] ;

/-- Corollary: For power maps `x ↦ x^d` with `gcd(d, 2^n - 1) = 1`,
    the cross-correlation is determined by the WHT of the inverse power map. -/
theorem crossCorr_powMap_eq_wht_inv {n : ℕ} (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d)) (b : F2n n) :
    crossCorr (F2n.powMap n d) b =
    wht (Function.invFun (F2n.powMap n d)) b - 1 := by
  rw [crossCorr_eq_full_sub_one _ (F2n.powMap_zero n d hd),
      crossCorrFull_bij_eq_wht_inv _ hbij]

/-! ## Extended Walsh–Hadamard Transform -/

/-- The extended (two-argument) Walsh–Hadamard transform:
    `Ŵ_f(a, b) = ∑_{x ∈ F} χ(a·x + b·f(x))`

    This generalizes both the standard WHT (`b = 1`) and the
    cross-correlation (`a = 1`). -/
def extWht {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (a * x + b * f x)

/-- The extended WHT at `b = 1` equals the standard WHT. -/
theorem extWht_b_one {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    extWht f a 1 = wht f a := by
  simp [extWht, wht]

/-- The extended WHT at `a = 1` equals the full cross-correlation. -/
theorem extWht_a_one {n : ℕ} (f : F2n n → F2n n) (b : F2n n) :
    extWht f 1 b = crossCorrFull f b := by
  simp [extWht, crossCorrFull]

/-- The extended WHT at `a = 0` gives the character sum over the range. -/
theorem extWht_a_zero {n : ℕ} (f : F2n n → F2n n) (b : F2n n) :
    extWht f 0 b = ∑ x : F2n n, chi n (b * f x) := by
  simp [extWht]

/-- The extended WHT at `b = 0` gives the standard character sum. -/
theorem extWht_b_zero {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    extWht f a 0 = ∑ x : F2n n, chi n (a * x) := by
  simp [extWht]

/-- The extended WHT at `(0, 0)` equals `|F_{2^n}| = 2^n`. -/
theorem extWht_zero_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    extWht f 0 0 = (2 ^ n : ℤ) := by
  simp [extWht, chi_zero, Finset.card_univ, F2n.card n hn]

/-! ## Parseval Identity for Cross-Correlation -/

/-- **Parseval identity for the full cross-correlation**:
    `∑_b Ĉ_f(b)^2 = (2^n)^2`

    This follows from the Parseval identity for the WHT of the inverse function
    when `f` is bijective. -/
theorem crossCorrFull_parseval {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hbij : Function.Bijective f) :
    ∑ b : F2n n, crossCorrFull f b ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  have h : ∀ b : F2n n, crossCorrFull f b = wht (Function.invFun f) b :=
    fun b => crossCorrFull_bij_eq_wht_inv f hbij b
  simp_rw [h]
  exact wht_parseval hn _

/-! ## Three-Valued Cross-Correlation -/

/-- A function `f : F_{2^n} → F_{2^n}` has **three-valued cross-correlation** if
    for all `b`, the squared full cross-correlation `Ĉ_f(b)^2` is
    either `0` or `2^{n+1}`.

    When `n` is odd, this is equivalent to the cross-correlation values being
    in `{-1, -1 + 2^{(n+1)/2}, -1 - 2^{(n+1)/2}}` for nonzero `b`,
    which is the classical three-valued cross-correlation property of
    Gold (1968) and Kasami (1971). -/
def IsThreeValuedCrossCorr {n : ℕ} (f : F2n n → F2n n) : Prop :=
  ∀ b : F2n n, crossCorrFull f b ^ 2 = 0 ∨ crossCorrFull f b ^ 2 = (2 ^ (n + 1) : ℤ)

/-- For bijections, three-valued cross-correlation is equivalent to the
    compositional inverse being Almost Bent:
    `IsThreeValuedCrossCorr f ↔ IsAlmostBent f⁻¹`

    This is the core connection between m-sequence cross-correlation theory
    and the spectral theory of Boolean/vectorial functions. -/
theorem threeValuedCrossCorr_iff_ab_inv {n : ℕ} (f : F2n n → F2n n)
    (hbij : Function.Bijective f) :
    IsThreeValuedCrossCorr f ↔ IsAlmostBent (Function.invFun f) := by
  unfold IsThreeValuedCrossCorr IsAlmostBent
  constructor
  · intro h a
    have := h a
    rwa [crossCorrFull_bij_eq_wht_inv f hbij] at this
  · intro h b
    have := h b
    rwa [← crossCorrFull_bij_eq_wht_inv f hbij] at this

/-! ## Almost Bent Implies Three-Valued Cross-Correlation -/

/-- **AB inverse ⟹ three-valued**: If `f⁻¹` is Almost Bent, then `f` has
    three-valued cross-correlation. Direct from the equivalence. -/
theorem ab_inv_implies_threeValued {n : ℕ} (f : F2n n → F2n n)
    (hbij : Function.Bijective f)
    (hab : IsAlmostBent (Function.invFun f)) :
    IsThreeValuedCrossCorr f :=
  (threeValuedCrossCorr_iff_ab_inv f hbij).mpr hab

/-! ## AB Preservation Under Inversion for Power Maps -/

/-
**WHT symmetry for power maps**: For a bijective power map `x^d`,
    `W_f(a) = W_{f⁻¹}(a^{-d})` for nonzero `a`.

    Proof: In `W_f(a) = ∑_x χ(ax + x^d)`, substitute `x → a⁻¹·x`:
    `W_f(a) = ∑_x χ(x + a^{-d}·x^d) = W_{f⁻¹}(a^{-d})`.
-/
theorem wht_powMap_eq_wht_inv_shift {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d))
    (a : F2n n) (ha : a ≠ 0) :
    wht (F2n.powMap n d) a =
    wht (Function.invFun (F2n.powMap n d)) (a⁻¹ ^ d) := by
  rw [ ← crossCorrFull_bij_eq_wht_inv ];
  · apply Finset.sum_bij (fun x _ => a * x);
    · simp;
    · aesop;
    · exact fun b _ => ⟨ a⁻¹ * b, Finset.mem_univ _, by simp +decide [ ha ] ⟩;
    · unfold F2n.powMap; simp +decide [ ha, mul_pow, mul_assoc, mul_left_comm ] ;
  · assumption

/-
The WHT of a bijective power map at 0 is 0.
-/
theorem wht_powMap_zero {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d)) :
    wht (F2n.powMap n d) 0 = 0 := by
  convert chi_sum_all_zero hn;
  convert Equiv.sum_comp ( Equiv.ofBijective _ hbij ) _ using 1;
  unfold wht; aesop;

/-
The map `a ↦ a⁻¹^d` is a bijection on `F_{2^n}^*` when `d` is coprime to `2^n - 1`.
    (Since both inversion and x^d are bijections on F*.)
-/
theorem inv_pow_bijective {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d)) :
    Function.Bijective (fun (a : F2n n) => a⁻¹ ^ d) := by
  have := hbij;
  convert this.comp ( show Function.Bijective ( fun a : F2n n => a⁻¹ ) from ?_ ) using 1;
  exact ⟨ inv_injective, inv_surjective ⟩

/-
For power maps on finite fields, the AB property is preserved under
    compositional inversion.

    If `x ↦ x^d` is a bijection on `F_{2^n}` (i.e., `gcd(d, 2^n - 1) = 1`),
    then `x^d` is Almost Bent if and only if the inverse map `x^e`
    (where `de ≡ 1 mod 2^n - 1`) is Almost Bent.

    Proof: By `wht_powMap_eq_wht_inv_shift`, `W_f(a) = W_{f⁻¹}(a⁻¹^d)` for `a ≠ 0`.
    Since `a ↦ a⁻¹^d` is a bijection on `F^*` and both `W_f(0)` and `W_{f⁻¹}(0)`
    are 0, the multisets `{W_f(a)²}` and `{W_{f⁻¹}(b)²}` coincide.
-/
theorem ab_iff_ab_inv_powMap {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d)) :
    IsAlmostBent (F2n.powMap n d) ↔
    IsAlmostBent (Function.invFun (F2n.powMap n d)) := by
  -- By `wht_powMap_eq_wht_inv_shift`, `W_f(a) = W_{f⁻¹}(a⁻¹^d)` for `a ≠ 0`.
  have h_wht_eq : ∀ a : F2n n, a ≠ 0 → wht (F2n.powMap n d) a = wht (Function.invFun (F2n.powMap n d)) (a⁻¹ ^ d) :=
    fun a ha => wht_powMap_eq_wht_inv_shift hn d hd hbij a ha
  constructor <;> intro h a <;> by_cases ha : a = 0 <;> simp_all +decide [ IsAlmostBent ];
  · have h_wht_inv_zero : ∑ x : F2n n, chi n x = 0 := by
      exact?;
    have h_wht_inv_zero : ∑ x : F2n n, chi n (Function.invFun (F2n.powMap n d) x) = ∑ x : F2n n, chi n x := by
      apply Finset.sum_bij (fun x _ => Function.invFun (F2n.powMap n d) x);
      · simp;
      · intro x₁ hx₁ x₂ hx₂ h; have := Function.invFun_eq ( show ∃ y, F2n.powMap n d y = x₁ from by replace hbij := congr_arg Multiset.toFinset hbij; rw [ Finset.ext_iff ] at hbij; specialize hbij x₁; aesop ) ; have := Function.invFun_eq ( show ∃ y, F2n.powMap n d y = x₂ from by replace hbij := congr_arg Multiset.toFinset hbij; rw [ Finset.ext_iff ] at hbij; specialize hbij x₂; aesop ) ; aesop;
      · exact fun x _ => ⟨ F2n.powMap n d x, Finset.mem_univ _, Function.leftInverse_invFun ( show Function.Injective ( F2n.powMap n d ) from Finite.injective_iff_surjective.mpr <| by simpa [ Finset.ext_iff ] using congr_arg Multiset.toFinset hbij ) x ⟩;
      · exact fun _ _ => rfl;
    unfold wht; aesop;
  · -- Since `a ↦ a⁻¹^d` is a bijection on `F^*`, there exists `b ≠ 0` such that `b⁻¹^d = a`.
    obtain ⟨b, hb⟩ : ∃ b : F2n n, b ≠ 0 ∧ b⁻¹ ^ d = a := by
      have := inv_pow_bijective hn d hd ( by simpa [ Function.bijective_iff_existsUnique ] using hbij );
      exact Exists.elim ( this.2 a ) fun x hx => ⟨ x, by aesop_cat, hx ⟩;
    specialize h b; aesop;
  · exact Or.inl ( wht_powMap_zero hn d hd <| by exact? )

/-- Corollary: For bijective power maps, three-valued cross-correlation
    is equivalent to the power map itself being Almost Bent. -/
theorem threeValuedCrossCorr_iff_ab_powMap {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d)) :
    IsThreeValuedCrossCorr (F2n.powMap n d) ↔ IsAlmostBent (F2n.powMap n d) := by
  rw [threeValuedCrossCorr_iff_ab_inv _ hbij, ← ab_iff_ab_inv_powMap hn d hd hbij]

/-! ## Cross-Correlation Values -/

/-- For three-valued cross-correlation, the actual cross-correlation values satisfy:
    either `C_f(b) = -1` (when `Ĉ_f(b) = 0`) or `(C_f(b) + 1)^2 = 2^{n+1}`.
    When `n` is odd, the latter means `C_f(b) = -1 ± 2^{(n+1)/2}`. -/
theorem crossCorr_values_of_threeValued {n : ℕ} (f : F2n n → F2n n)
    (hf : f 0 = 0) (htv : IsThreeValuedCrossCorr f) (b : F2n n) :
    crossCorr f b = -1 ∨
    (crossCorr f b + 1) ^ 2 = (2 ^ (n + 1) : ℤ) := by
  rcases htv b with h | h
  · left
    have : crossCorrFull f b = 0 := sq_eq_zero_iff.mp h
    rw [crossCorr_eq_full_sub_one f hf, this]
    ring
  · right
    rw [crossCorr_eq_full_sub_one f hf]
    ring_nf
    exact h

/-! ## Counting Nonzero Cross-Correlation Values -/

/-- For three-valued cross-correlation with a bijection, the number of nonzero
    full cross-correlation values equals `2^{n-1}`.
    (From the AB nonzero count for the inverse.) -/
theorem threeValued_nonzero_count {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hbij : Function.Bijective f) (htv : IsThreeValuedCrossCorr f) :
    (Finset.univ.filter fun b : F2n n => crossCorrFull f b ≠ 0).card = 2 ^ (n - 1) := by
  have hab := (threeValuedCrossCorr_iff_ab_inv f hbij).mp htv
  convert ab_nonzero_count hn _ hab using 1
  congr 1; ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [crossCorrFull_bij_eq_wht_inv f hbij]

/-! ## Kasami Three-Valued Cross-Correlation Theorem -/

/-- **Kasami's Three-Valued Cross-Correlation Theorem** (Kasami 1971):
    For the Kasami power function `f(x) = x^d` where `d = 4^k - 2^k + 1`,
    when `gcd(k, n) = 1` and `n` is odd, the cross-correlation is three-valued:
    `C_d(b) ∈ {-1, -1 + 2^{(n+1)/2}, -1 - 2^{(n+1)/2}}` for all `b ∈ F_{2^n}^*`.

    This is equivalent to the Kasami function being Almost Bent, which is
    the deep algebraic result from Kasami (1971) / Canteaut-Charpin-Dobbertin (2000). -/
theorem kasami_three_valued_crossCorr (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    IsThreeValuedCrossCorr (kasamiF n k) := by
  rw [show kasamiF n k = F2n.powMap n (kasamiExp k) from rfl]
  rw [threeValuedCrossCorr_iff_ab_powMap hn _ (Nat.pos_iff_ne_zero.mp (kasamiExp_pos k))
      (kasamiExp_permutation k n hk hn hn_odd hgcd)]
  exact kasami_is_ab n k hk hn hn_odd hgcd

/-- **Gold's Three-Valued Theorem** (Gold 1968): The special case `k = 1`
    gives the Gold function `f(x) = x^3` with three-valued cross-correlation. -/
theorem gold_three_valued_crossCorr (n : ℕ) (hn : n ≠ 0) (hn_odd : Odd n) :
    IsThreeValuedCrossCorr (kasamiF n 1) :=
  kasami_three_valued_crossCorr n 1 one_ne_zero hn hn_odd (Nat.coprime_one_left n)

/-! ## Cross-Correlation of m-Sequences (Sequence-Level Definition) -/

/-- An m-sequence is defined by a primitive element `α` of `F_{2^n}`:
    `s(t) = Tr(α^t)` for `t = 0, 1, ..., 2^n - 2`.

    We represent it as a function from `F_{2^n}` via the substitution `x = α^t`,
    giving the bipolar form `(-1)^{s(t)} = χ(x)`. -/
def mSeqBipolar (n : ℕ) (x : F2n n) : ℤ := chi n x

/-- The sequence-level cross-correlation of two m-sequences with decimation `d`:
    `C_d^{seq}(b) = ∑_{x ∈ F^*} χ(x) · χ(b · x^d)`

    This equals our function-level cross-correlation since
    `χ(x) · χ(b·x^d) = χ(x + b·x^d)` (by the multiplicative property of χ). -/
def mSeqCrossCorr {n : ℕ} (d : ℕ) (b : F2n n) : ℤ :=
  ∑ x ∈ Finset.univ.filter (· ≠ (0 : F2n n)),
    mSeqBipolar n x * mSeqBipolar n (b * x ^ d)

/-- The sequence-level cross-correlation equals the function-level one. -/
theorem mSeqCrossCorr_eq_crossCorr {n : ℕ} (d : ℕ) (b : F2n n) :
    mSeqCrossCorr d b = crossCorr (F2n.powMap n d) b := by
  unfold mSeqCrossCorr crossCorr mSeqBipolar F2n.powMap
  congr 1; ext x
  rw [← chi_add]

/-! ## Additional Cross-Correlation Identities -/

/-- **Full cross-correlation at b = 0** (for any function `f`):
    `Ĉ_f(0) = ∑_x χ(x) = 0` when `n ≥ 1`. -/
theorem crossCorrFull_at_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    crossCorrFull f 0 = 0 := by
  simp [crossCorrFull, chi_sum_all_zero hn]

/-- **WHT at 0 of inverse**: For bijective `f`,
    `W_{f⁻¹}(0) = 0` when `n ≥ 1`. -/
theorem wht_inv_at_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hbij : Function.Bijective f) :
    wht (Function.invFun f) 0 = 0 := by
  rw [← crossCorrFull_bij_eq_wht_inv f hbij]
  exact crossCorrFull_at_zero hn f

/-- **Autocorrelation**: The full cross-correlation of the identity function at `b`
    equals `∑_x χ((1+b)·x)`. -/
theorem crossCorrFull_identity {n : ℕ} (b : F2n n) :
    crossCorrFull (fun x : F2n n => x) b =
    ∑ x : F2n n, chi n ((1 + b) * x) := by
  unfold crossCorrFull
  congr 1; ext x; congr 1; ring

/-- For the identity decimation, the full cross-correlation equals `2^n` when `b = 1`
    (i.e., `1 + b = 0` in char 2), and `0` otherwise. -/
theorem crossCorrFull_identity_value {n : ℕ} (hn : n ≠ 0) (b : F2n n) :
    crossCorrFull (fun x : F2n n => x) b =
    if b = 1 then (2 ^ n : ℤ) else 0 := by
  rw [crossCorrFull_identity]
  have h1b : (1 : F2n n) + b = 0 ↔ b = 1 := by
    constructor
    · intro h
      have : b = -(1 : F2n n) + ((1 : F2n n) + b) := by ring
      rw [this, h, add_zero, F2n.neg_eq]
    · intro h; rw [h]; exact F2n.add_self 1
  rw [chi_sum hn (1 + b)]
  simp only [h1b]

end
end Kasami