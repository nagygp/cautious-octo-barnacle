import RequestProject.Foundations.KasamiCrossCorrelation

/-!
# Foundations, Layer 11 — the general-`k`, general-`m` Kasami weight / `m`-tuple count

This module realizes **Layer 11** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`): the *thin assembly* that combines a discharged
`Vanish` hypothesis for the general-`k` Kasami map `x ↦ x^{d k}` with the
already-proved counting engine `MTuple.imgCount_of_vanish` to obtain the
closed-form image `m`-tuple count

  `imgCount m (·^{d k}) a c = 2^{(m-1)n - m}`

for general `k` and general arity `m` — the general-`k` analogue of Layer 8's
`cube_mtuple_count`.

## The argument

As the roadmap stresses, **no new counting machinery is needed here**:

* `MTuple.imgCount_of_vanish` already turns *any* APN map with a discharged
  `Vanish` into the count `imgCount m f a c = 2^{(m-1)n - m}` (and
  `MTuple.triple_count_of_vanish` into `2^{2n-3}` at `m = 3`);
* the Kasami map `x ↦ x^{d k}` is APN — `KasamiAB.kasami_is_apn_pred`.

So the *only* missing input is the general-`k` discharge of `Vanish` itself, which
is the (still open) deliverable of Layer 10.  Accordingly the Layer-11 counts are
stated **conditionally** on that discharge:

* `kasami_mtuple_count` takes the spectral hypothesis `Vanish m (·^{d k}) a c`
  directly (the general-`m` Layer-10 deliverable) and assembles the count via
  `MTuple.imgCount_of_vanish` and `KasamiAB.kasami_is_apn_pred`;
* `kasami_triple_count` is its `m = 3` form, stated against the explicit
  `AdmissibleTriple` packaging and assembled via the already-built conditional
  Layer-7 bridge `kasami_is_vanish_triple` (which turns `AdmissibleTriple` into
  `Vanish` through the Layer-6 equivalence) and `MTuple.triple_count_of_vanish`.

Once Layer 10 supplies an *unconditional* general-`k` `Vanish` discharge on an
explicit admissible class, these results upgrade to unconditional counts by
substituting that discharge for the `Vanish` / `AdmissibleTriple` hypotheses —
exactly as Layer 8 already does unconditionally for `k = 1` via
`cube_vanish_of_not_all_eq_gen`.

## Sources

Kasami (1971); Chabaud–Vaudenay §3 (the higher-moment / m-tuple-count engine);
MacWilliams–Sloane (Pless power moments).

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): the counts are thin assemblies
of the already-built engine with the Kasami APN headline (DRY), each with a
single responsibility and an intention-revealing name; the genuinely deep input
(the general-`k` `Vanish` discharge) is isolated as a hypothesis, not duplicated.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable {n k : ℕ}

/-! ## The general-`k`, general-`m` Kasami `m`-tuple count (conditional on `Vanish`) -/

/-- **The general-`k`, general-`m` Kasami `m`-tuple count.**  For the Kasami map
`x ↦ x^{d k}` (which is APN, `KasamiAB.kasami_is_apn_pred`), once the
nonzero-frequency spectral sum is discharged (`Vanish m (·^{d k}) a c`, the
general-`m` Layer-10 deliverable) the image `m`-tuple count is `2^{(m-1)n - m}`.

This is a thin assembly of `MTuple.imgCount_of_vanish` with the Kasami APN
headline — the general-`k` analogue of Layer 8's `cube_mtuple_count`. -/
theorem kasami_mtuple_count {m : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (hm : 2 ≤ m) (a : F) (ha : a ≠ 0) (c : Fin m → F)
    (hv : Vanish m (fun x : F => x ^ d k) a c) :
    imgCount m (fun x : F => x ^ d k) a c = 2 ^ ((m - 1) * n - m) :=
  imgCount_of_vanish n m (by omega) hm hcard _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd (by omega)) a ha c hv

/-! ## The `m = 3` specialization — the Kasami triple count (conditional on `AdmissibleTriple`) -/

/-- **The general-`k` Kasami triple count.**  The `m = 3` form of
`kasami_mtuple_count`: for an *admissible* coefficient triple the image triple
count of the Kasami map `x ↦ x^{d k}` is `2^{2n-3}`.

Assembled from the conditional Layer-7 bridge `kasami_is_vanish_triple`
(`AdmissibleTriple → Vanish`, via the Layer-6 equivalence) and
`MTuple.triple_count_of_vanish`. -/
theorem kasami_triple_count (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F)
    (hadm : AdmissibleTriple n (fun x : F => x ^ d k) a c) :
    imgCount 3 (fun x : F => x ^ d k) a c = 2 ^ (2 * n - 3) :=
  triple_count_of_vanish n (by omega) hcard _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd (by omega)) a ha c
    (kasami_is_vanish_triple hcard hk hkn hcop hnodd hn a ha c hadm)

end Vanish.Foundations
