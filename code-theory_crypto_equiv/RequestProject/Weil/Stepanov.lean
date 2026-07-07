import RequestProject.Weil.AuxPoly

/-!
# Stepanov's method: the auxiliary-polynomial engine

This module contains the elementary heart of the *recommended* route to the Weil bound,
following Stepanov.  The strategy avoids zeta functions entirely.  It rests on one soft engine
and one deep, problem-specific construction:

1. **Counting engine** (`card_le_of_rootMultiplicity`).  If a nonzero polynomial `g` vanishes to
   order at least `m` at every point of a finite set `S`, then `m · |S| ≤ deg g`.  This is just
   "the number of roots-with-multiplicity is at most the degree".

2. **Auxiliary-polynomial existence** (`exists_aux_poly`).  This is the genuinely hard, creative
   step.  For suitable parameters `m, ℓ` one constructs an explicit nonzero polynomial of
   controlled degree that vanishes to order `≥ m` at every `𝔽_q`-point of the Artin–Schreier
   curve.  The construction uses the Frobenius identity `x^q = x` on `𝔽_q` together with a clever
   choice of `𝔽_q`-linear combination of `p`-th powers, and Hasse derivatives to certify the
   high-order vanishing.

Feeding (2) into (1) and optimising `m, ℓ` yields the **point-count bounds**
`curvePointCount_le` / `curvePointCount_ge`, i.e.
$$ \bigl| \#C_f(\mathbb F_q) - q \bigr| \;\le\; (d-1)(p-1)\sqrt q \;=\; 2g\,\sqrt q, $$
where `g = (d-1)(p-1)/2` is the genus of the Artin–Schreier curve.

## Main statements (skeletons)
* `Weil.Stepanov.card_le_of_rootMultiplicity` — the counting engine (soft; fillable first).
* `Weil.Stepanov.exists_aux_poly` — the auxiliary-polynomial existence (deep core).
* `Weil.Stepanov.curvePointCount_le` / `curvePointCount_ge` — the one-sided point-count bounds.
-/

open scoped BigOperators
open Polynomial
open Classical

namespace Weil
namespace Stepanov

variable {F : Type*} [Field F] [Fintype F]

/-
**Counting engine.**  If `g ≠ 0` and every element of a finite set `S` is a root of `g` of
multiplicity at least `m`, then `m · |S| ≤ deg g`.

This is the elementary engine behind Stepanov's method: a high-order-vanishing auxiliary
polynomial of bounded degree can only have few special roots.  It follows from
`∑_{a ∈ S} rootMultiplicity a g ≤ g.natDegree`.
-/
omit [Fintype F] in
lemma card_le_of_rootMultiplicity (g : F[X]) (hg : g ≠ 0) (S : Finset F) (m : ℕ)
    (hS : ∀ a ∈ S, m ≤ g.rootMultiplicity a) :
    m * S.card ≤ g.natDegree := by
  have h_prod : (∏ a ∈ S, (Polynomial.X - Polynomial.C a) ^ m) ∣ g := by
    refine' Finset.prod_dvd_of_coprime _ _;
    · intro a ha b hb hab; exact IsCoprime.pow ( Polynomial.irreducible_X_sub_C _ |> fun h => h.coprime_iff_not_dvd.mpr fun h' => hab <| by simpa [ sub_eq_iff_eq_add ] using Polynomial.dvd_iff_isRoot.mp h' ) ;
    · exact fun a ha => dvd_trans ( pow_dvd_pow _ ( hS a ha ) ) ( Polynomial.pow_rootMultiplicity_dvd _ _ );
  have := Polynomial.natDegree_le_of_dvd h_prod hg; simp_all +decide [ Polynomial.natDegree_prod', Finset.prod_pow ] ;

/-
**Curve point count via curve-point predicate.**  Each `x` with `IsCurvePoint f x` contributes
exactly `p` solutions `y` (a full `℘`-fibre), and every other `x` contributes none, so
`#C_f(𝔽_q) = p · #{x : IsCurvePoint f x}`.  This converts the two-dimensional point count into a
one-dimensional count to which Stepanov's bound applies.
-/
lemma asPointCount_eq_card_mul (f : F[X]) :
    asPointCount f = ringChar F * (Finset.univ.filter (IsCurvePoint f)).card := by
  rw [ Finset.card_filter, Weil.asPointCount_eq_sum ];
  rw [ Finset.mul_sum _ _ _ ];
  refine' Finset.sum_congr rfl fun x _ => _;
  split_ifs <;> simp_all +decide [ IsCurvePoint ];
  have := Weil.asOp_fiber_card ( eval x f ) ; aesop;

/-- **Upper bound on curve points (Stepanov core output).**  The number of `x ∈ 𝔽_q` that lift to a
point of the curve is at most `q/p + (d-1)(p-1)/(2)·√q`-shaped; packaged here as the bound feeding
`curvePointCount_le` after multiplying by `p`.  Obtained from `exists_aux_poly` and
`card_le_of_rootMultiplicity`. -/
lemma card_curvePoints_le (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) :
    (ringChar F : ℝ) * ((Finset.univ.filter (IsCurvePoint f)).card : ℝ)
      ≤ Fintype.card F
        + (f.natDegree - 1) * (ringChar F - 1) * Real.sqrt (Fintype.card F) := by
  sorry

/-
**Auxiliary-polynomial existence (deep core of Stepanov's method).**

*CORRECTION (commented out — false as originally stated).*  The skeleton stated this as

```
lemma exists_aux_poly (f : F[X]) (m ℓ : ℕ) :
    ∃ g : F[X], g ≠ 0 ∧
      g.natDegree ≤ ℓ * Fintype.card F + m * f.natDegree * ℓ ∧
      ∀ x : F, IsCurvePoint f x → m ≤ g.rootMultiplicity x
```

with **no constraint relating `m`, `ℓ` and the number of curve points**.  This is *false*: take
`F = 𝔽₂`, `f = X`, `m = 2`, `ℓ = 0`.  The degree bound becomes `g.natDegree ≤ 0`, forcing `g` to be a
nonzero constant; but `x = 0` is a curve point of `y² - y = x` (since `0² - 0 = 0 = X.eval 0`), and a
nonzero constant has `rootMultiplicity = 0 < 2`.  Contradiction, so the stated `∃` is unsatisfiable.

The genuine Stepanov construction is *not* this unconstrained statement.  Existence of a nonzero
low-degree polynomial vanishing to order `m` at all curve points only holds in the admissible
parameter regime (the number of linear vanishing conditions, `m · #points`, must be strictly below the
dimension of the chosen polynomial space), and the *sharp* `(d-1)(p-1)` constant requires the
delicate degree/parameter optimisation that uses the `x^q = x` reduction and Hasse-derivative
linearisation.  That genuine deep content is recorded directly by the true (still-`sorry`) one-sided
bounds `curvePointCount_le` / `curvePointCount_ge` below, rather than by a mis-stated intermediate.
The `AuxPoly` module assembles the linear-algebra engine and the linearised vanishing conditions
that a correct construction would combine.
-/

/-- **Upper point-count bound (Stepanov output).**  The number of affine `𝔽_q`-points of the
Artin–Schreier curve is at most `q + (d-1)(p-1)√q`, where `d = deg f` and `p` is the
characteristic.  Obtained by feeding `exists_aux_poly` into `card_le_of_rootMultiplicity` and
optimising the parameters. -/
lemma curvePointCount_le (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) :
    (asPointCount f : ℝ) ≤ Fintype.card F
      + (f.natDegree - 1) * (ringChar F - 1) * Real.sqrt (Fintype.card F) := by
  sorry

/-- **Lower point-count bound (Stepanov output).**  The complementary one-sided bound, obtained by
applying the upper bound to the "non-points" (the same argument with the trace condition negated),
gives `q - (d-1)(p-1)√q ≤ #C_f(𝔽_q)`. -/
lemma curvePointCount_ge (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) :
    (Fintype.card F : ℝ) - (f.natDegree - 1) * (ringChar F - 1) * Real.sqrt (Fintype.card F)
      ≤ asPointCount f := by
  sorry

end Stepanov
end Weil