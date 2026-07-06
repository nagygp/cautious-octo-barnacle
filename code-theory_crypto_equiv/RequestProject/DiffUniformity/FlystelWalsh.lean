import Mathlib
import RequestProject.DiffUniformity.Flystel

/-!
# Walsh spectrum of the Flystel — elementary layer

This module begins the formalisation of

> M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
> Designs, Codes and Cryptography **93** (2025) 2245–2262.

The paper estimates the absolute value of the Walsh transform of the Anemoi
*closed Flystel* `V` and, via CCZ-equivalence (`APN.cczEquiv_flystelField_symm`),
of the *open Flystel* `H`.  Its main result (Theorem 3.3) is a six-way case
split; the deep entries rest on algebraic-geometry character-sum bounds
(Weil/Deligne/Rojas-León), which are the foundational *gates* tracked in
`FLYSTEL_WALSH_ROADMAP.md`.  This file formalises the **elementary, gate-free**
content:

* the field-level **Walsh transform** of Definition 2.1 for a function
  `F : K × K → K × K` against a `ℂ`-valued additive character `ψ : AddChar K ℂ`
  (`FlystelWalsh.walsh`);
* the **trivial value** `W_F(ψ, 0, 0) = q²` (Theorem 3.3, first case);
* the **orthogonality / permutation-polynomial vanishing** mechanism: a balanced
  linear-approximation function forces `W = 0` (`walsh_eq_zero_of_balanced`),
  together with the two ways the closed Flystel realises balance —
  bijectivity of the linear approximation in either coordinate
  (`balanced_of_bijective_fst`, `balanced_of_bijective_snd`);
* the **closed Flystel** `V` in its direct functional form (Eq. 11),
  `closedFlystelMap`, and the resulting **zero entries** of Theorem 3.3
  (cases `a ≠ 0, b = 0` and `b ≠ 0` with `a₁ = b₁ = 0` or `a₂ = b₂ = 0`).

## Main results

* `FlystelWalsh.walsh` — the Walsh transform of `F : K × K → K × K`.
* `walsh_zero_zero` — `W_F(ψ, 0, 0) = (card K)²`.
* `walsh_eq_zero_of_balanced` — balance ⇒ the Walsh coefficient vanishes.
* `balanced_of_bijective_fst`, `balanced_of_bijective_snd` — coordinate-wise
  bijectivity criteria for balance.
* `closedFlystelMap` — the closed Flystel `V` (Eq. 11).
* `walsh_eq_zero_of_b_zero` — Theorem 3.3 case `a ≠ 0, b = 0`.
* `walsh_closedFlystel_eq_zero_of_fst_zero`,
  `walsh_closedFlystel_eq_zero_of_snd_zero` — Theorem 3.3 zero entries
  (`a₂ = b₂ = 0` resp. `a₁ = b₁ = 0`).
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The standard inner product on `K × K`, `⟨a, x⟩ = a₁·x₁ + a₂·x₂`. -/
def dotProd (a x : K × K) : K := a.1 * x.1 + a.2 * x.2

/-- The **Walsh transform** (Definition 2.1) of a function `F : K × K → K × K`
for the additive character `ψ` at the linear approximation `(a, b)`:
`W_F(ψ, a, b) = ∑_{x ∈ K²} ψ(⟨a, x⟩ + ⟨b, F x⟩)`. -/
noncomputable def walsh (ψ : AddChar K ℂ) (F : K × K → K × K) (a b : K × K) : ℂ :=
  ∑ x : K × K, ψ (dotProd a x + dotProd b (F x))

/-
**Theorem 3.3, first case.**  The trivial Walsh coefficient is `q²`.
-/
omit [DecidableEq K] in
theorem walsh_zero_zero (ψ : AddChar K ℂ) (F : K × K → K × K) :
    walsh ψ F 0 0 = (Fintype.card K : ℂ) ^ 2 := by
  -- The sum of 1 over all elements in K × K is just the cardinality of K × K, which is (Fintype.card K)^2.
  simp [walsh, dotProd];
  ring

/-- A linear-approximation function `g : K × K → K` is **balanced** when every
value has exactly `q` preimages. -/
def Balanced (g : K × K → K) : Prop :=
  ∀ y : K, (univ.filter (fun x : K × K => g x = y)).card = Fintype.card K

/-
If the linear-approximation function `x ↦ ⟨a, x⟩ + ⟨b, F x⟩` is balanced and
`ψ` is non-trivial, then the Walsh coefficient vanishes (additive-character
orthogonality / permutation-polynomial argument).
-/
theorem walsh_eq_zero_of_balanced (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : K × K → K × K) (a b : K × K)
    (hbal : Balanced (fun x => dotProd a x + dotProd b (F x))) :
    walsh ψ F a b = 0 := by
  -- By definition of walsh, we have:
  unfold walsh;
  -- By definition of balanced, each fiber has cardinality $|K|$.
  have h_fiber_card : ∀ y : K, (Finset.filter (fun x => dotProd a x + dotProd b (F x) = y) Finset.univ).card = Fintype.card K := by
    exact hbal;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ x : K × K, ψ (dotProd a x + dotProd b (F x)) = ∑ y : K, ∑ x ∈ Finset.filter (fun x => dotProd a x + dotProd b (F x) = y) Finset.univ, ψ y := by
    simp +decide only [sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  simp_all +decide [ Finset.sum_const, nsmul_eq_mul ];
  rw [ ← Finset.mul_sum _ _ _, AddChar.sum_eq_zero_of_ne_one hψ, MulZeroClass.mul_zero ]

/-
If, for every fixed second coordinate `v`, the map `y ↦ g (y, v)` is a
bijection of `K`, then `g` is balanced.
-/
omit [Field K] in
theorem balanced_of_bijective_fst (g : K × K → K)
    (hg : ∀ v : K, Function.Bijective (fun y : K => g (y, v))) :
    Balanced g := by
  intro y
  have h_card : (Finset.univ.filter (fun x : K × K => g x = y)).card = Finset.card (Finset.univ : Finset K) := by
    refine' Finset.card_bij ( fun v _ => v.2 ) _ _ _ <;> simp +decide;
    · intro a b hab a' b' hab' h; have := hg b; have := this.1; aesop;
    · exact fun v => hg v |>.2 y
  exact h_card

/-
If, for every fixed first coordinate `y`, the map `v ↦ g (y, v)` is a
bijection of `K`, then `g` is balanced.
-/
omit [Field K] in
theorem balanced_of_bijective_snd (g : K × K → K)
    (hg : ∀ y : K, Function.Bijective (fun v : K => g (y, v))) :
    Balanced g := by
  intro y
  have h_card : (Finset.univ.filter (fun x : K × K => g x = y)).card = Finset.card (Finset.univ : Finset K) := by
    refine' Finset.card_bij ( fun x hx => x.1 ) _ _ _ <;> simp_all +decide [ Function.Bijective ];
    · intro a b hab a' b' hab' h; have := hg a; have := this.1; have := this ( by aesop : g ( a, b ) = g ( a, b' ) ) ; aesop;
    · exact fun b => hg b |>.2 y
  exact h_card

/-
**Theorem 3.3, case `a ≠ 0, b = 0`.**  With a non-trivial input mask and the
trivial output mask, the linear form `⟨a, x⟩` is balanced, so the Walsh
coefficient vanishes.
-/
theorem walsh_eq_zero_of_b_zero (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : K × K → K × K) (a : K × K) (ha : a ≠ 0) :
    walsh ψ F a 0 = 0 := by
  by_cases ha1 : a.1 = 0;
  · by_cases ha2 : a.2 = 0 <;> simp_all +decide [ Prod.ext_iff ];
    apply walsh_eq_zero_of_balanced ψ hψ F a 0;
    apply balanced_of_bijective_snd; intro y; simp [dotProd, ha1];
    exact Multiset.map_univ_val_equiv ( Equiv.mulLeft₀ a.2 ha2 );
  · apply walsh_eq_zero_of_balanced ψ hψ F a 0;
    apply balanced_of_bijective_fst; intro v; simp only [dotProd, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero];
    exact ⟨ fun x y hxy => by simp_all +decide [ mul_right_cancel₀ ha1 ],
      fun z => ⟨ ( z - a.2 * v ) / a.1, by field_simp [ ha1 ]; ring ⟩ ⟩

/-- The **closed Flystel** `V` of `(Q_γ, E, Q_δ)` in its direct functional form
(Eq. 11): `V(y, v) = (E(y - v) + Q_γ(y), E(y - v) + Q_δ(v))`. -/
def closedFlystelMap (E Qγ Qδ : K → K) : K × K → K × K :=
  fun p => (E (p.1 - p.2) + Qγ p.1, E (p.1 - p.2) + Qδ p.2)

/-
**Theorem 3.3 zero entry, `a₂ = b₂ = 0`, `b₁ ≠ 0`.**  Solving the linear
approximation for the second coordinate `v` (where `E(y - v)` is a bijection in
`v`) shows it is balanced, so the closed-Flystel Walsh coefficient vanishes.
-/
theorem walsh_closedFlystel_eq_zero_of_snd_zero (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (E Qγ Qδ : K → K) (hE : Function.Bijective E) (a b : K × K)
    (ha2 : a.2 = 0) (hb2 : b.2 = 0) (hb1 : b.1 ≠ 0) :
    walsh ψ (closedFlystelMap E Qγ Qδ) a b = 0 := by
  -- Since $a.2 = 0$ and $b.2 = 0$, the coefficient of $E(y - v)$ in $g$ is $b.1$, which is nonzero.
  have h_coeff : ∀ y : K, Function.Bijective (fun v : K => a.1 * y + b.1 * (E (y - v) + Qγ y)) := by
    intro y
    have h_inj : Function.Injective (fun v : K => a.1 * y + b.1 * (E (y - v) + Qγ y)) := by
      intro v w hvw; have := hE.1; simp_all +decide [ Function.Injective.eq_iff this ] ;
    exact ⟨h_inj, Finite.injective_iff_surjective.mp h_inj⟩;
  convert walsh_eq_zero_of_balanced ψ hψ ( closedFlystelMap E Qγ Qδ ) a b ( balanced_of_bijective_snd _ _ ) using 1;
  simp_all +decide [ dotProd, closedFlystelMap ]

/-
**Theorem 3.3 zero entry, `a₁ = b₁ = 0`, `b₂ ≠ 0`.**  Solving the linear
approximation for the first coordinate `y` (where `E(y - v)` is a bijection in
`y`) shows it is balanced, so the closed-Flystel Walsh coefficient vanishes.
-/
theorem walsh_closedFlystel_eq_zero_of_fst_zero (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (E Qγ Qδ : K → K) (hE : Function.Bijective E) (a b : K × K)
    (ha1 : a.1 = 0) (hb1 : b.1 = 0) (hb2 : b.2 ≠ 0) :
    walsh ψ (closedFlystelMap E Qγ Qδ) a b = 0 := by
  convert walsh_eq_zero_of_balanced ψ hψ ( closedFlystelMap E Qγ Qδ ) a b ( balanced_of_bijective_fst _ _ ) using 1;
  intro v
  unfold dotProd closedFlystelMap
  simp [ha1, hb1];
  -- Since $E$ is bijective, the function $y \mapsto E(y - v)$ is also bijective.
  have h_bij : Function.Bijective (fun y => E (y - v)) := by
    exact hE.comp ( Function.bijective_iff_has_inverse.mpr ⟨ fun y => y + v, fun y => by simp +decide, fun y => by simp +decide ⟩ );
  have h_bij : Function.Bijective (fun y => a.2 * v + b.2 * (y + Qδ v)) := by
    exact ⟨ fun x y hxy => by simpa [ hb2 ] using hxy, fun x => ⟨ ( x - a.2 * v ) / b.2 - Qδ v, by simp +decide [ hb2, mul_div_cancel₀ ] ⟩ ⟩;
  exact Multiset.map_univ_val_equiv ( Equiv.ofBijective _ h_bij |> Equiv.trans ( Equiv.ofBijective _ ‹_› ) )

end FlystelWalsh
end APN