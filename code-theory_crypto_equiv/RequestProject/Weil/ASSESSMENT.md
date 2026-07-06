# Assessment: are the `weil-bound.zip` files sufficient to finish the proof?

This note answers the question "are these files sufficient to derive what is remaining?" for the
expanded `RequestProject/Weil/` skeleton shipped in `weil-bound.zip`, and records exactly what was
filled, what was corrected, and what genuinely remains.

**Short answer.** *Partially.* The supporting modules the zip added (`Frobenius`, `Hasse`, `Trace`,
`AuxPoly`, `Amplification`, `Extensions`) are enough to discharge **all** the *soft / analytic /
packaging / field-theoretic* obligations — these are now proved sorry-free, and the headline
`Weil.weil_bound` is proved as a genuine reduction. They are **not** enough to discharge the three
genuinely deep, not-in-Mathlib cores (Stepanov's auxiliary-polynomial bound, the curve Riemann
Hypothesis / Artin–Schreier L-function rationality, and the extension trace-transitivity bridge);
those remain as honest, *true* `sorry`s. In addition, several statements in the skeleton were
**false as written** and had to be corrected (see below).

The whole project builds (`lake build` succeeds); `RequestProject/Headlines.lean` is unaffected.

## Newly proved, sorry-free

Verified with `#print axioms` to use only `propext / Classical.choice / Quot.sound`:

* `Amplification.norm_le_of_powerSum_bound`, `norm_sum_le_of_powerSum_bound`,
  `charSum_single_le_of_extension_bound` — the analytic power-sum / dominant-root engine.
* `Hasse.hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity` — converse vanishing criterion.
* `AuxPoly.auxAnsatz_natDegree_le` (corrected bound), `hasseDeriv_auxAnsatz_linear`.
* `Stepanov.asPointCount_eq_card_mul`.
* `Weil.exists_bridge` — **additive Hilbert 90 fully discharged** (`#C_f = ∑_{t∈𝔽_p} charSum …`),
  using the already-proved `Trace.bridge_pointwise`.
* `Extensions.liftChar_ne_one`, `natDegree_baseChange`, `ringChar_baseField`,
  `abs_extPointCount_sub_le` (uniform-over-extensions point-count bound, a genuine reduction onto the
  Stepanov bounds), `towerField` (+ instances), `towerField_card`, `towerField_one_equiv`,
  `exists_extension_tower` — the full extension-tower construction (splitting fields of `X^{q^k}-X`),
  **sorry-free**.
* `Weil.weil_bound` — the **headline** `‖∑ₓ ψ(f x)‖ ≤ (d-1)√q`, proved by assembling the tower, the
  power-sum descent and the `E₁ ≃ₐ[F] F` trace transport. It depends (via `#print axioms`,
  `sorryAx`) only on the one remaining deep input `exists_charSum_eigenvalues_le`.

## Statements that were FALSE in the skeleton (corrected / commented out, with explanation)

These were `sorry`-stubs whose *statements* cannot hold; leaving them as `sorry` would have been
misleading and (worse) let downstream proofs "cheat" by deriving `False`:

1. `Stepanov.exists_aux_poly` — unconstrained in `(m, ℓ)`; false e.g. for `F=𝔽₂, f=X, m=2, ℓ=0`
   (forces a nonzero degree-0 polynomial to vanish to order 2 at a curve point). Commented out; the
   genuine content lives in the true bounds `curvePointCount_le/ge`.
2. `Amplification.exists_powerSum_repn` — claims *any* sequence with `Sk 0 = 0` is a finite power
   sum; false (e.g. `Sk = id`, `d = 1`). Commented out; the real, correctly-hypothesised statement
   is `Extensions.exists_charSum_eigenvalues_le`.
3. `AuxPoly.auxAnsatz_ne_zero_of_coeff` — false for the naive ansatz (`f = X` makes the building
   blocks `X^i f^j` collide). Commented out.
4. `AuxPoly.auxAnsatz_natDegree_le` — the recorded degree bound `ℓq + mdℓ` is false (the ansatz has
   degree `~ ℓ + md²`); restated with the correct bound and proved.
5. `Extensions.exists_extension_tower` (and the matching `hcard` hypotheses of
   `exists_combined_eigenvalues` / `exists_charSum_eigenvalues_le`) — required `card (E k) = q^k`
   for **all** `k`, impossible at `k = 0` (a field cannot have 1 element); also forced `E` into
   universe 0 while `F : Type*`. Corrected to `1 ≤ k → …` and `E : ℕ → Type u` in `F`'s universe;
   then proved.

## Genuinely deep, still-`sorry` (true statements; not derivable from these files alone)

These are the research-level heart of Weil's theorem for the Artin–Schreier curve; they are not in
Mathlib and each needs substantial new theory:

* `Stepanov.card_curvePoints_le`, `Stepanov.curvePointCount_le`, `Stepanov.curvePointCount_ge`
  — Stepanov's auxiliary-polynomial bound with the sharp `(d-1)(p-1)` constant (the real
  construction + parameter optimisation; `curvePointCount_ge` needs an independent second
  construction).
* `Extensions.exists_combined_eigenvalues`, `Extensions.exists_charSum_eigenvalues_le`
  — the curve Riemann Hypothesis / rationality of the Artin–Schreier L-function (the reciprocal
  roots have absolute value `≤ √q`).
* `Extensions.extBridge` — the bridge identity over an extension; needs the trace-transitivity
  identity `absTrace_E = absTrace_F ∘ Tr_{E/F}` as its own lemma.

`weil_bound` is wired to follow from `exists_charSum_eigenvalues_le` (+ the now-proved tower and
power-sum descent), so completing that single deep input (curve RH for the Artin–Schreier curve)
would discharge the headline.
