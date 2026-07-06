# Roadmap: the general one-variable Weil bound (skeleton sub-library)

**Goal.** The general (non-monomial) one-variable Weil bound for additive
character sums: for a finite field `F = 𝔽_q` of characteristic `p`, a nontrivial
additive character `ψ : F → ℂ`, and a polynomial `f ∈ F[X]` of degree `d` with
`p ∤ d`,

```
‖ ∑_{x ∈ 𝔽_q} ψ(f(x)) ‖ ≤ (d − 1) · √q.
```

**Lean statement.** `Weil.weil_bound` in `RequestProject/Weil/WeilBound.lean`.

This file is the mathematical map for the skeleton library under
`RequestProject/Weil/`. Every lemma in those modules is currently `sorry`; the
modules are written *unfolded* — each node is a single concrete Lean declaration
with a real, Mathlib-rooted statement (no deep `sorry`'d placeholder nodes and no
placeholder hypotheses), so that filling the small lemmas mechanically derives the
general bound. A clean `lake build` of the whole library currently succeeds (only
`sorry` warnings).

The whole sub-library is built by the existing `RequestProject` lake target (the
`RequestProject.+` glob); it is deliberately **not** imported by
`RequestProject/Headlines.lean`, so the verified headline entry stays `sorry`-free
while this skeleton is filled in over multiple sessions.

## File / declaration inventory

| File | Declarations (all `sorry`) |
|------|----------------------------|
| `CharSum.lean` | `charSum`; `charSum_one`, `charSum_const`, `norm_charSum_le`, `charSum_linear_eq_zero`, `charSum_mulShift` |
| `ArtinSchreier.lean` | `asOp`, `primeField`, `IsCurvePoint`, `asPointCount`; `asOp_add`, `asOp_fiber_card`, `asPointCount_eq_sum` |
| `Stepanov.lean` | `auxDegBound`; `card_le_of_rootMultiplicity`, `exists_aux_poly`, `curvePointCount_le`, `curvePointCount_ge` |
| `PointCountBound.lean` | `genus`; `two_mul_genus_eq`, `abs_curvePointCount_sub_card_le` |
| `Zeta.lean` | `zetaCoeff`, `SatisfiesRH`; `abs_sub_le_of_satisfiesRH` |
| `WeilBound.lean` | `primeFinset`; `norm_le_of_powerSum_bound`, `norm_sum_le_of_powerSum_bound`, `exists_bridge`, `weil_bound` |

## Two routes

There are two classical routes to this bound. The skeleton implements both at the
level of statements, but only the **Stepanov route** (Route B) is set up as a
realistic end-to-end fill target.

### Route A — Zeta function + RH for curves (Weil I) — deep, not recommended

1. **Sum-as-point-count.** Identify `∑_x ψ(f(x))` with point counts of the
   Artin–Schreier curve `y^p − y = f(x)`, reducing the Weil bound to bounding
   `|#C(𝔽_q) − q|`.
2. **Zeta function & rationality.** `Z(C/𝔽_q, T) = exp(∑_{k≥1} N_k T^k / k)` is
   rational with numerator a polynomial of degree `2g`.
3. **Functional equation + RH for curves.** The reciprocal roots have absolute
   value `√q`. This is the hard core (Weil I); the genus here is
   `g = (d−1)(p−1)/2`.
4. **Assembly.** `|N_k − q| ≤ 2g√q ⇒ ‖∑ ψ(f x)‖ ≤ (d−1)√q`.

**Status.** Step 3 (RH for curves / Weil I) is genuinely deep and is not in
Mathlib. In the skeleton, Route A appears only in `Zeta.lean`, over an abstract
point-count sequence `N : ℕ → ℕ`:

* `Weil.Zeta.SatisfiesRH q g N` — RH packaged on point counts
  (`N k = q^k + 1 − ∑ α_iᵏ` with `|α_i| = √q`);
* `Weil.Zeta.abs_sub_le_of_satisfiesRH` — the elementary consequence
  `|N k − (q^k+1)| ≤ 2g√(q^k)` (a triangle-inequality argument; a good fillable
  target).

Proving `SatisfiesRH` for an actual curve is left open — that is Weil I.

### Route B — Stepanov's elementary method — recommended fill target

Stepanov's auxiliary-polynomial method avoids zeta functions and is far more
self-contained. It is the skeleton's main path:

```
CharSum → ArtinSchreier → Stepanov → PointCountBound → WeilBound.
```

## Module-by-module DAG (Route B)

Bottom-up; each bullet names the Lean declaration and what it needs.

### `CharSum.lean` — foundations (fill first; elementary)

* `charSum ψ f := ∑ x, ψ (f.eval x)` — the object of study.
* `charSum_one`, `charSum_const`, `norm_charSum_le` — elementary; Mathlib only
  (`AddChar.norm_apply`, finite sums).
* `charSum_linear_eq_zero` — nontrivial `ψ` vs a linear `f` sums to `0`
  (`AddChar.sum_eq_zero_of_ne_one` after the affine change of variable). The
  `d = 1` base case.
* `charSum_mulShift` — `charSum (ψ.mulShift c) f = charSum ψ (C c * f)`; reduces
  the bound to a single fixed nontrivial character.

### `ArtinSchreier.lean` — the dictionary (elementary–medium)

* `asOp y := y^p − y` (`℘`); `primeField F` (= roots of `Xᵖ − X` = `𝔽_p`);
  `IsCurvePoint f x y`; `asPointCount f` (= `#C_f(𝔽_q)`).
* `asOp_add` — `℘` is additive (`add_pow_char`/frobenius plus ring algebra).
* `asOp_fiber_card` — every fibre of `℘` has size `0` or `p` (a coset of
  `ker ℘ = 𝔽_p`).
* `asPointCount_eq_sum` — Fubini: `#C_f = ∑_x #{y : ℘ y = f(x)}`.

### `Stepanov.lean` — the engine (soft engine + deep core)

* `card_le_of_rootMultiplicity` — counting engine: if `g ≠ 0` vanishes to order
  `≥ m` on a finite set `S`, then `m·|S| ≤ deg g`. Soft; follows from
  `∑_{a∈S} rootMultiplicity a g ≤ g.natDegree`. **Fill this early.**
* `auxDegBound f` — the tuned degree bound
  `(q + (d−1)(p−1)√q) / p` on the `x`-coordinates.
* `exists_aux_poly` — **deep core**: a nonzero auxiliary polynomial of degree
  `≤ m·auxDegBound f` vanishing to order `≥ m` at every `x`-coordinate of a
  rational point. The creative Stepanov construction (an `𝔽_q`-linear combination
  of `p`-th powers, using `x^q = x` on `𝔽_q`, with high-order vanishing certified
  by Hasse derivatives). The constant is tuned so that, after
  `card_le_of_rootMultiplicity` and the fibre count `asOp_fiber_card` (each
  non-empty fibre has size `p`, so `#C_f = p · #{x : ∃ y, ℘ y = f(x)}`), the sharp
  slack `(d−1)(p−1)√q` appears.
* `curvePointCount_le`, `curvePointCount_ge` — the one-sided bounds
  `|#C_f − q| ≤ (d−1)(p−1)√q`, from the two lemmas above by optimising `m ≈ √q`.

### `PointCountBound.lean` — packaging (soft)

* `genus f := (d−1)(p−1)/2`.
* `two_mul_genus_eq` — `2g = (d−1)(p−1)` (the product is even because `p ∤ d`).
* `abs_curvePointCount_sub_card_le` — two-sided `|#C_f − q| ≤ 2g√q` from the two
  one-sided bounds (`abs_le`). Fillable once the one-sided bounds exist.

### `WeilBound.lean` — assembly (medium → headline)

* `norm_le_of_powerSum_bound` / `norm_sum_le_of_powerSum_bound` — the analytic
  root-extraction (tensor-power trick): a uniform `‖∑_i α_iᵏ‖ ≤ C·rᵏ` for all
  `k ≥ 1` caps each `|α_i| ≤ r`, hence `‖∑ α_i‖ ≤ n·r`.
* `primeFinset F` — the prime field `𝔽_p ⊆ F` as a `Finset`.
* `exists_bridge` — additive-orthogonality dictionary: for the standard character
  `ψ₀ = e∘Tr`, `#C_f(𝔽_q) = ∑_{t ∈ 𝔽_p} charSum (ψ₀.mulShift t) f` (the `t = 0`
  term being `q`). So `#C_f − q = ∑_{t ≠ 0} charSum (ψ₀.mulShift t) f`.
* `weil_bound` — the headline. Steps: (i) reduce to a fixed nontrivial character
  via `charSum_mulShift`; (ii) use `exists_bridge` +
  `abs_curvePointCount_sub_card_le` to bound the sum of the `p−1` nontrivial sums;
  (iii) descend to a single character with the sharp constant by the
  extension-field amplification (`norm_sum_le_of_powerSum_bound`): apply the
  point-count bound over every `𝔽_{q^k}`, take `2k`-th roots of `‖S‖^{2k}`, and
  let `k → ∞`. Equivalently, the Artin–Schreier `L`-function's reciprocal roots
  have absolute value `√q`.

## Suggested filling order

1. `card_le_of_rootMultiplicity` (Stepanov engine) and the `CharSum` elementary
   lemmas.
2. `asOp_add`, `asOp_fiber_card`, `asPointCount_eq_sum` (the dictionary).
3. `abs_sub_le_of_satisfiesRH` (Zeta — self-contained warm-up).
4. `two_mul_genus_eq`, then `norm_le_of_powerSum_bound` /
   `norm_sum_le_of_powerSum_bound` (analytic root extraction).
5. `exists_aux_poly` (the hard core) ⟹ `curvePointCount_le`/`curvePointCount_ge`
   ⟹ `abs_curvePointCount_sub_card_le`.
6. `exists_bridge`, then assemble `weil_bound`.

## Honest caveats (load-bearing content)

* The deepest single obligation in Route B is `exists_aux_poly` (the Stepanov
  construction) together with the parameter optimisation feeding
  `curvePointCount_le`/`curvePointCount_ge`. This is the whole theorem: the
  Hasse-derivative vanishing and degree bookkeeping, with the constant tuned to
  feed `(d−1)√q`.
* The sharp `(d−1)` constant for an *individual* character (as opposed to the
  average of the `p−1` nontrivial sums) needs the extension-field amplification
  step inside `weil_bound`. For this to have anything to stand on,
  `curvePointCount_le`/`curvePointCount_ge` are stated for a *generic* finite
  field `F`, so they apply verbatim over every extension `𝔽_{q^k}` with a constant
  independent of `k` — exactly what the `k → ∞` limit requires. When filling, keep
  the bounds field-generic; do **not** specialise them to the base field.
* Route A's `SatisfiesRH` (Weil I) is intentionally left open; it is recorded only
  to complete the map.

## Does this suffice for the general Weil bound?

Yes, in principle: if every listed `sorry` is filled with its stated statement,
`weil_bound` follows mechanically along the DAG above. The non-mechanical,
load-bearing content is concentrated in `exists_aux_poly` (+ its parameter
optimisation), the uniform-over-extensions point-count bounds, and the
amplification limit `norm_le_of_powerSum_bound`.
