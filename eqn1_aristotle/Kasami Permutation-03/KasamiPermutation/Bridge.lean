import RequestProject.KasamiPermutation.Bridge.UnitsPower
import RequestProject.KasamiPermutation.Bridge.ArtinSchreier
import RequestProject.KasamiPermutation.Bridge.TwoToOne

/-!
# Structural bridges for the Dobbertin (1999) development

This namespace collects **bridge modules**: small, structural re-derivations of the
load-bearing facts behind the headline results, each obtained by moving to whichever
mathematical context ("theory") makes the step cheapest, and letting a general
Mathlib abstraction do the work.  The recurring pattern is:

> isolate a *small invariant*, transport it across a (possibly *non-faithful*)
> functor to a context where Mathlib already proves the result, then bring the
> conclusion back.

## The bridges

* `Bridge/UnitsPower.lean` — **the units functor `F ↦ Fˣ`.**  Bijectivity of a
  power map `x ↦ xᵃ` on a finite field is transported to the cyclic group `Fˣ`,
  where Mathlib's `powCoprime` settles it from the single numerical invariant
  `gcd(a, |F| − 1) = 1`.  Gives an alternative proof of the Gold-permutation
  headline (`gold_permutation_via_units`).

* `Bridge/ArtinSchreier.lean` — **the exponential-characteristic invariant.**  The
  char-2 Artin–Schreier telescoping lemma `L_k(x² + x) = x^{2ᵏ} + x` (which drives
  the MCM → APN chain) is a special case of a characteristic-free telescoping
  invariant `linTrace p k (xᵖ − x) = x^{pᵏ} − x`, re-derived here and specialised
  back to the exact library lemma (`truncTrace_artin_schreier_via_invariant`).

* `Bridge/TwoToOne.lean` — **the forgetful functor `Field ⤳ AddGroup`.**  The
  two-to-one heart of Corollary 2 (that `x ↦ x² + x` has fibres `{x, x+1}`) is
  read off from Mathlib's fiber–kernel coset equivalence once `℘` is seen as an
  `AddMonoidHom`; the only content is the invariant `ker ℘ = {0, 1}`.  The bridge
  proof needs no finiteness of `F` (`artinSchreier_fiber_card`,
  `artinSchreier_two_to_one`).

All declarations here are `sorry`-free and rest only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/
