import RequestProject.Walsh.Transform

/-!
# Dobbertin (1999) / Dillon–Dobbertin (2004) — cyclic difference sets with Singer parameters (Layer D)

This module is **Layer D** of the full-paper roadmap
([`DOBBERTIN1999_FULL_ROADMAP.md`](../../DOBBERTIN1999_FULL_ROADMAP.md)) for
Dobbertin (1999), *"Kasami Power Functions, Permutation Polynomials and Cyclic
Difference Sets"*.  It supplies the **Singer difference-set foundation** that the
paper's third pillar (P3) rests on, built directly on the additive-character /
Fourier bridge already established in `RequestProject/DifferenceSets/Basic.lean`
and `RequestProject/Walsh/Transform.lean`.

## Cyclic difference sets with Singer parameters (Dillon–Dobbertin, Definition 1)

Let `L = 𝔽_{2ⁿ}` and let `L* = Lˣ` be its (cyclic) multiplicative group of order
`2ⁿ − 1`.  A `k`-subset `D ⊆ L*` is a **(cyclic) difference set with Singer
parameters**
```
   (v, k, λ) = (2ⁿ − 1, 2^{n-1} − 1, 2^{n-2} − 1)
```
if, for every `g ∈ L*` with `g ≠ 1`, the equation `g = x · y⁻¹` has exactly `λ`
solutions `(x, y)` with `x, y ∈ D`; equivalently `#(D ∩ gD) = λ`.

## The classical Singer set

The archetypal example (Dillon–Dobbertin, Section 2) is the **trace hyperplane**
```
   D = { x ∈ L* : Tr(x) = 0 },
```
the nonzero points of the hyperplane `Tr = 0`.  We prove, purely through the
additive sign character `WalshAB.χ` and its orthogonality relation
`WalshAB.χ_sum_eq` (the "Fourier bridge"), that:

* `singerSet_card` — `#D = 2^{n-1} − 1`;
* `singer_isMulDifferenceSet` — for every `g ≠ 0, 1` the multiplicative
  representation count `mulRepCount D g = 2^{n-2} − 1`, i.e. `D` is a cyclic
  difference set with Singer parameters `(2ⁿ − 1, 2^{n-1} − 1, 2^{n-2} − 1)`.

The whole argument is finite-field harmonic analysis: the map
`x ↦ (Tr x, Tr (g·x))` is `𝔽₂`-linear and (for `g ≠ 0, 1`) surjective onto
`𝔽₂²`, so each of its four fibres has `2^{n-2}` points — a fact we read off from
`∑_x (1 + χ x)(1 + χ (g·x)) = q` via `WalshAB.χ_sum_eq`.

Everything is `sorry`-free on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/

set_option maxHeartbeats 1600000

namespace Dobbertin1999.Singer

open Finset Fintype BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The **classical Singer difference set**: the nonzero field elements of
absolute trace `0` (the nonzero points of the hyperplane `Tr = 0`). -/
noncomputable def singerSet : Finset F := univ.filter (fun x => x ≠ 0 ∧ Tr x = 0)

/-- The **multiplicative representation count** of `D` at `g`: the number of
`y ∈ D` with `g · y ∈ D`.  For `g ∈ L*, g ≠ 1` this is the Singer
difference-set parameter `λ = #(D ∩ gD)` (the number of ways to write
`g = x · y⁻¹` with `x, y ∈ D`). -/
noncomputable def mulRepCount (D : Finset F) (g : F) : ℕ :=
  (univ.filter (fun y => y ∈ D ∧ g * y ∈ D)).card

/-- **A subset `D ⊆ L*` is a (cyclic) difference set with parameter `λ`** if
every `g ∈ L*` with `g ≠ 1` has exactly `λ` multiplicative representations
(Dillon–Dobbertin, Definition 1). -/
def IsMulDifferenceSet (D : Finset F) (lam : ℕ) : Prop :=
  ∀ g : F, g ≠ 0 → g ≠ 1 → mulRepCount D g = lam

/-! ## Character-sum counting of trace fibres -/

/-
**Trace-hyperplane count.**  Over `𝔽_{2ⁿ}` the hyperplane `Tr = 0` has
`2^{n-1}` points: `2 · #{x : Tr x = 0} = q`.
-/
theorem card_trace_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) :
    2 * (univ.filter (fun x : F => Tr x = 0)).card = 2 ^ n := by
  convert WalshAB.χ_sum_eq ( 1 : F ) using 1;
  simp +decide [ Finset.sum_ite, WalshAB.χ ];
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num;
  grind

/-
**Two-trace count.**  For `g ≠ 0, 1` the map `x ↦ (Tr x, Tr (g·x))` is
surjective onto `𝔽₂²`, so the joint fibre `Tr x = 0 ∧ Tr (g·x) = 0` has
`2^{n-2}` points: `4 · #{x : Tr x = 0 ∧ Tr (g·x) = 0} = q`.
-/
theorem card_two_trace_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (g : F) (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    4 * (univ.filter (fun x : F => Tr x = 0 ∧ Tr (g * x) = 0)).card = 2 ^ n := by
  have h_sum : ∑ x : F, (1 + WalshAB.χ x) * (1 + WalshAB.χ (g * x)) = 2 ^ n := by
    simp +decide only [mul_add, mul_one, add_mul, one_mul, sum_add_distrib, sum_const, nsmul_eq_mul];
    simp +decide [ ← WalshAB.χ_mul, hn ];
    have h_sum_zero : ∑ x : F, χ x = 0 ∧ ∑ x : F, χ (g * x) = 0 ∧ ∑ x : F, χ ((1 + g) * x) = 0 := by
      have h_sum_zero : ∀ c : F, c ≠ 0 → ∑ x : F, χ (c * x) = 0 := by
        intro c hc; have := χ_sum_eq c; aesop;
      refine' ⟨ _, h_sum_zero g hg0, h_sum_zero ( 1 + g ) _ ⟩;
      · simpa using h_sum_zero 1 one_ne_zero;
      · grobner;
    simp_all +decide [ add_mul ];
  convert h_sum using 1;
  rw [ Finset.sum_congr rfl fun x hx => show ( 1 + χ x ) * ( 1 + χ ( g * x ) ) = if Tr x = 0 ∧ Tr ( g * x ) = 0 then 4 else 0 from ?_ ];
  · simp +decide [ Finset.sum_ite, mul_comm ];
    grind;
  · unfold χ; split_ifs <;> simp_all +decide ;

/-! ## The Singer set is a difference set with Singer parameters -/

/-
**Size of the Singer set.**  `#{x ∈ L* : Tr x = 0} = 2^{n-1} − 1`.
-/
theorem singerSet_card {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn1 : 1 ≤ n) :
    (singerSet (F := F)).card = 2 ^ (n - 1) - 1 := by
  simp +decide [ singerSet, Finset.filter_ne', Finset.filter_and ];
  have := card_trace_zero hn; rw [ show 2 ^ n = 2 * 2 ^ ( n - 1 ) by rw [ ← pow_succ', Nat.sub_add_cancel hn1 ] ] at this; omega;

/-
**The Singer set is a difference set with Singer parameters.**  For every
`g ∈ L*` with `g ≠ 1`, the multiplicative representation count of the Singer set
is `2^{n-2} − 1`.  Together with `singerSet_card` this exhibits
`{x ∈ L* : Tr x = 0}` as a cyclic difference set with Singer parameters
`(2ⁿ − 1, 2^{n-1} − 1, 2^{n-2} − 1)`.
-/
theorem singer_isMulDifferenceSet {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn2 : 2 ≤ n) :
    IsMulDifferenceSet (singerSet (F := F)) (2 ^ (n - 2) - 1) := by
  intro g hg0 hg1
  have h_filter : (univ.filter (fun y : F => y ∈ singerSet ∧ g * y ∈ singerSet)) = (univ.filter (fun y : F => Tr y = 0 ∧ Tr (g * y) = 0)).erase 0 := by
    ext y; simp [singerSet];
    tauto;
  have h_card : (univ.filter (fun y : F => Tr y = 0 ∧ Tr (g * y) = 0)).card = 2 ^ (n - 2) := by
    have := card_two_trace_zero hn g hg0 hg1; rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ] ; omega;
  unfold mulRepCount; aesop;

end Dobbertin1999.Singer