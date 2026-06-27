import ConjecturesMTupleTripleCount.Foundations.SpectralSum
import ConjecturesMTupleTripleCount.MTuple
import ConjecturesMTupleTripleCount.Support.AutocorrQuadratic

/-!
# Foundations, Layer 7 — the Kasami cross-correlation distribution

This module realizes **Layer 7** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`): it specializes the Layer-6 machinery to the
**explicit Kasami cross-correlation (derivative autocorrelation)** in order to
*discharge the `Vanish` hypothesis* on a concrete, satisfiable class of
coefficient tuples.

## The autocorrelation of the cube map (= Kasami map at `k = 1`)

The Kasami exponent at `k = 1` is `d 1 = 3` (the cube/Gold map).  Its derivative
`Δ(x³)_a(x) = a·x² + a²·x + a³` is **`F₂`-affine** (the autocorrelation
infrastructure already collected for this case lives in
`ConjecturesMTupleTripleCount/Support/AutocorrQuadratic.lean`).  An affine derivative makes the
scaled autocorrelation a *single* additive-character sum, so the
cross-correlation is supported on a two-element subgroup:

* `cube_autocorr_eq_zero` — for `a ≠ 0`, `R(s) = ∑_x χ(s·Δ(x³)_a x) = 0` unless
  `s = 0` or `s·a³ = 1`;
* `cube_autocorr_zero` — `R(0) = q` (the trivial-frequency value).

So the support of the cube cross-correlation is exactly `{0, a^{-3}}` — a clean,
fully computed instance of "the Kasami cross-correlation distribution".

## Discharging `Vanish`

Because the support is `{0, a^{-3}}`, a product `∏_i R(t·cᵢ)` over `t ≠ 0` can be
nonzero only when `t·cᵢ = a^{-3}` for *every* `i`, which forces all the `cᵢ`
equal.  Hence:

* `cube_vanish_of_not_all_eq` — for nonzero coefficients that are **not all
  equal**, `Vanish 3 (·³) a c` holds (unconditionally — the `Vanish` hypothesis
  is discharged);
* `kasami_one_vanish_triple` — the same for the Kasami map at `k = 1`
  (`x ↦ x^{d 1}`);
* `kasami_one_triple_count` — its payoff via `MTuple.triple_count_of_vanish`:
  the image triple count is `2^{2n-3}`.

The order-3 obstruction (`MTuple/Disproof.lean`, re-exposed in Layer 6 as
`cube_equal_not_vanish`) shows the "not all equal" side-condition is *necessary*:
the equal-coefficient cube triple count is `0`.  Together this gives the **exact**
admissibility characterization for the cube map:

* `cube_admissible_iff` — for `n ≥ 2` odd and nonzero coefficients,
  `AdmissibleTriple n (·³) a c ↔ ¬ (c₀ = c₁ ∧ c₁ = c₂)`.

## The general honest target

For general `k`, evaluating the Kasami cross-correlation in closed form is the
classical Kasami weight-distribution computation; what is *unconditional* from
Layers 5–6 is the equivalence `AdmissibleTriple ↔ Vanish`, so the honest target
theorem is the conditional discharge:

* `kasami_is_vanish_triple` — for an admissible triple, `Vanish 3 (·^{d k}) a c`
  holds (hence `MTuple.triple_count_of_vanish` applies).

## Sources

Kasami (1971); Dobbertin (1999); Canteaut–Charpin–Dobbertin (SIAM 2000);
Chabaud–Vaudenay §3.

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): the genuinely new mathematics
here is the single affine-derivative character-sum evaluation
(`cube_autocorr_eq_zero`); everything else *assembles* it with the already-built
Layer-6 admissibility iff and the `MTuple` count, each lemma with a single
responsibility and an intention-revealing name (DRY).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## A square root in characteristic two -/

omit [DecidableEq F] in
/-- In a finite field of characteristic two the Frobenius `x ↦ x²` is bijective,
so every element is a square. -/
theorem exists_sq (z : F) : ∃ r : F, r ^ 2 = z := by
  have hinj : Function.Injective (fun x : F => x ^ 2) := by
    intro x y hxy
    simpa [sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq] using hxy
  exact (Finite.injective_iff_surjective.mp hinj) z

/-! ## The cube cross-correlation distribution -/

omit [DecidableEq F] in
/-- **The trivial-frequency value.** `R(0) = ∑_x χ(0·Δ(x³)_a x) = q`. -/
theorem cube_autocorr_zero (a : F) :
    autocorrScaled (fun x : F => x ^ 3) 0 a = (Fintype.card F : ℤ) :=
  MTuple.autocorrScaled_zero _ a

/-
**The cube cross-correlation is supported on `{0, a^{-3}}`.**  For `a ≠ 0`,
the scaled autocorrelation `R(s) = ∑_x χ(s·Δ(x³)_a x)` vanishes whenever `s ≠ 0`
and `s·a³ ≠ 1`.  This is the affine-derivative evaluation: the cube derivative
`Δ(x³)_a(x) = a·x² + a²·x + a³` is `F₂`-affine, so after the Frobenius
substitution `χ(s·a·x²) = χ(r·x)` (with `r² = s·a`) the sum collapses to the
additive-character orthogonality `∑_x χ((r + s·a²)·x)`, which is `0` unless
`r + s·a² = 0`, i.e. `s = 0 ∨ s·a³ = 1`.
-/
theorem cube_autocorr_eq_zero (a : F) (ha : a ≠ 0) (s : F)
    (hs0 : s ≠ 0) (hs1 : s * a ^ 3 ≠ 1) :
    autocorrScaled (fun x : F => x ^ 3) s a = 0 := by
  obtain ⟨ r, hr ⟩ := exists_sq ( s * a );
  have h_inner_sum : ∑ x : F, χ (s * a * x ^ 2 + s * a ^ 2 * x) = ∑ x : F, χ ((r + s * a ^ 2) * x) := by
    refine' Finset.sum_congr rfl fun x _ => _;
    rw [ show s * a * x ^ 2 + s * a ^ 2 * x = ( r * x ) ^ 2 + s * a ^ 2 * x by linear_combination' hr.symm * x ^ 2 ];
    rw [ add_mul, WalshAB.χ_mul ];
    rw [ WalshAB.χ_sq_eq, WalshAB.χ_mul ];
  have h_inner_sum_zero : ∑ x : F, χ ((r + s * a ^ 2) * x) = 0 := by
    convert WalshAB.χ_sum_eq ( r + s * a ^ 2 ) using 1;
    grind +suggestions;
  convert congr_arg ( fun x : ℤ => x * χ ( s * a ^ 3 ) ) h_inner_sum using 1;
  · rw [ MTuple.autocorrScaled_eq, Finset.sum_mul ];
    refine' Finset.sum_congr rfl fun x _ => _;
    rw [ ← WalshAB.χ_mul ] ; rw [ MTuple.cube_deriv ] ; ring;
  · rw [ h_inner_sum_zero, MulZeroClass.zero_mul ]

/-! ## Discharging `Vanish` for the cube map -/

/-
**`Vanish` discharged for the cube map.**  For nonzero coefficients that are
**not all equal**, the nonzero-frequency spectral sum vanishes.  (For any `t ≠ 0`
the product `∏_i R(t·cᵢ)` is nonzero only if every `t·cᵢ = a^{-3}`, forcing the
`cᵢ` all equal; the not-all-equal hypothesis kills every term.)
-/
theorem cube_vanish_of_not_all_eq (a : F) (ha : a ≠ 0) (c : Fin 3 → F)
    (hc : ∀ i, c i ≠ 0) (hne : ¬ (c 0 = c 1 ∧ c 1 = c 2)) :
    Vanish 3 (fun x : F => x ^ 3) a c := by
  refine' Finset.sum_eq_zero _;
  intro t ht; by_contra h; simp_all +decide [ Fin.prod_univ_three ] ;
  -- By `cube_autocorr_eq_zero a ha s`, each factor `autocorrScaled (·^3) (t * c i) a ≠ 0` implies `(t * c i) * a^3 = 1`.
  have h_eq : ∀ i, (t * c i) * a^3 = 1 := by
    intro i
    have h_eq : autocorrScaled (fun x => x ^ 3) (t * c i) a ≠ 0 := by
      fin_cases i <;> tauto;
    exact Classical.not_not.1 fun h => h_eq <| cube_autocorr_eq_zero a ha ( t * c i ) ( mul_ne_zero ht ( hc i ) ) h;
  grind

/-! ## The Kasami `k = 1` specialization -/

/-- **`Vanish` discharged for the Kasami map at `k = 1`.**  Since `d 1 = 3`, the
Kasami map at `k = 1` is the cube map, so for nonzero, not-all-equal coefficients
the spectral sum vanishes. -/
theorem kasami_one_vanish_triple (a : F) (ha : a ≠ 0) (c : Fin 3 → F)
    (hc : ∀ i, c i ≠ 0) (hne : ¬ (c 0 = c 1 ∧ c 1 = c 2)) :
    Vanish 3 (fun x : F => x ^ d 1) a c := by
  have hd : d 1 = 3 := by decide
  simpa [hd] using cube_vanish_of_not_all_eq a ha c hc hne

/-- **The Kasami `k = 1` triple count.**  Combining the discharged `Vanish` with
`MTuple.triple_count_of_vanish`: for nonzero, not-all-equal coefficients the
image triple count of the Kasami map at `k = 1` is `2^{2n-3}`. -/
theorem kasami_one_triple_count (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F) (hc : ∀ i, c i ≠ 0)
    (hne : ¬ (c 0 = c 1 ∧ c 1 = c 2)) :
    imgCount 3 (fun x : F => x ^ d 1) a c = 2 ^ (2 * n - 3) := by
  have hd : d 1 = 3 := by decide
  have hv : Vanish 3 (fun x : F => x ^ 3) a c := cube_vanish_of_not_all_eq a ha c hc hne
  have := triple_count_of_vanish n hn hcard (fun x : F => x ^ 3) MTuple.cube_isAPN a ha c hv
  simpa [hd] using this

/-! ## The exact admissibility characterization for the cube map -/

/-- **Exact admissibility for the cube map.**  For `n ≥ 2` odd and nonzero
coefficients, a triple is admissible (its image triple count is `2^{2n-3}`) iff
the coefficients are **not all equal**.  The forward direction is the order-3
obstruction (`cube_equal_not_vanish`); the reverse is `cube_vanish_of_not_all_eq`
through the Layer-6 equivalence `admissibleTriple_iff_vanish`. -/
theorem cube_admissible_iff (n : ℕ) (hodd : Odd n) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (a : F) (ha : a ≠ 0) (c : Fin 3 → F)
    (hc : ∀ i, c i ≠ 0) :
    AdmissibleTriple n (fun x : F => x ^ 3) a c ↔ ¬ (c 0 = c 1 ∧ c 1 = c 2) := by
  rw [admissibleTriple_iff_vanish n hn hcard _ MTuple.cube_isAPN a ha c]
  constructor
  · intro hv hall
    have hcfun : c = (fun _ => c 0) := by
      funext i; fin_cases i <;> simp_all
    rw [hcfun] at hv
    exact cube_equal_not_vanish n hodd hn hcard a ha (c 0) (hc 0) hv
  · exact fun hne => cube_vanish_of_not_all_eq a ha c hc hne

/-! ## The general honest target -/

variable {n k : ℕ}

/-- **The honest "Kasami is Vanish" target (general `k`).**  For an *admissible*
coefficient triple, the nonzero-frequency spectral sum of the Kasami map
`x ↦ x^{d k}` vanishes.  This is the `.mp` direction of the Layer-6 equivalence
`kasami_admissibleTriple_iff_vanish`; some admissibility hypothesis is
unavoidable (the equal-coefficient cube map already violates `Vanish`).  Feeding
the conclusion to `MTuple.triple_count_of_vanish` yields the exact triple count
`2^{2n-3}`. -/
theorem kasami_is_vanish_triple (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F)
    (hadm : AdmissibleTriple n (fun x : F => x ^ d k) a c) :
    Vanish 3 (fun x : F => x ^ d k) a c :=
  (kasami_admissibleTriple_iff_vanish hcard hk hkn hcop hnodd hn a ha c).mp hadm

end Vanish.Foundations