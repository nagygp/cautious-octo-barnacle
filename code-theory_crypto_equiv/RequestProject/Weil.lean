import RequestProject.Weil.CharSum
import RequestProject.Weil.Frobenius
import RequestProject.Weil.Hasse
import RequestProject.Weil.ArtinSchreier
import RequestProject.Weil.Trace
import RequestProject.Weil.AuxPoly
import RequestProject.Weil.Stepanov
import RequestProject.Weil.PointCountBound
import RequestProject.Weil.Amplification
import RequestProject.Weil.Extensions
import RequestProject.Weil.WeilBound
import RequestProject.Weil.Zeta

/-!
# A skeleton library for the one-variable Weil bound

This is the aggregator module for the `Weil.*` development.  See `ROADMAP.md` at the project root
for the mathematical roadmap and the dependency DAG, and the individual modules for details.

## Foundations
* `RequestProject.Weil.CharSum`        — additive character sums `charSum ψ f` and basic facts.
* `RequestProject.Weil.Frobenius`      — Frobenius identities and the arithmetic of `𝔽_q`.
* `RequestProject.Weil.Hasse`          — Hasse derivatives and the high-order vanishing criterion.

## The Artin–Schreier dictionary
* `RequestProject.Weil.ArtinSchreier`  — the operator `℘`, the curve, point counts, the dictionary.
* `RequestProject.Weil.Trace`          — the absolute trace, additive orthogonality, the bridge.

## Stepanov's method
* `RequestProject.Weil.AuxPoly`        — the auxiliary-polynomial construction (linear-algebra engine,
                                          ansatz, counting inequality).
* `RequestProject.Weil.Stepanov`       — Stepanov's counting engine and the point-count bounds.
* `RequestProject.Weil.PointCountBound` — the two-sided `|N - q| ≤ 2g√q` point-count bound.

## Assembly
* `RequestProject.Weil.Amplification`  — extension-field amplification / power-sum eigenvalue descent.
* `RequestProject.Weil.Extensions`     — uniform-over-extensions point counts and the L-function link.
* `RequestProject.Weil.WeilBound`      — the headline bound `‖∑ₓ ψ(f x)‖ ≤ (d-1)√q`.

## Alternative route
* `RequestProject.Weil.Zeta`           — the zeta-function (Weil I) route, statements only.
-/
