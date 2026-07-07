import RequestProject.MTuple.Count
import RequestProject.MTuple.Disproof
import RequestProject.MTuple.VanishCriterion

/-!
# m-Tuple / triple counts for APN derivatives — headline results

This is the entry point for the honest, `FlatSpectrum`-free account of the
m-tuple count of an APN derivative.  See `RequestProject/MTuple/Count.lean` for
the construction and `RequestProject/MTuple/Disproof.lean` for the refutations.

For `f : GF(2ⁿ) → GF(2ⁿ)`, nonzero `a`, and coefficients `c : Fin m → F`, with
`Δf_a(x) = f(x+a)+f(x)`, the **image m-tuple count** is
`imgCount m f a c = #{ y : Fin m → F | (∀ i, yᵢ ∈ Im Δf_a) ∧ Σᵢ cᵢ·yᵢ = 0 }`.

## Summary of what is true

* **Fourier inversion (unconditional):** `q · preCount = Σ_t Πᵢ R(t·cᵢ)`
  (`MTuple.card_mul_preCount`), where `R(s) = Σ_x χ(s·Δf_a x)` is the scaled
  autocorrelation.

* **Exact count under the genuine, satisfiable condition `Vanish`**
  (`MTuple.imgCount_of_vanish`): if the nonzero-frequency spectral sum vanishes,
  then `imgCount m f a c = 2^{(m-1)n - m}`.  The triple case is
  `MTuple.triple_count_of_vanish`.

  `Vanish` is the genuine correlation-balance content; it replaces the old
  `FlatSpectrum` hypothesis, which forced Walsh values `±2^{n/2}` and is
  **unsatisfiable for `n` odd** — the regime the entire Kasami development lives
  in.

* **The unconditional formula is FALSE.**  With only `cᵢ ≠ 0`:
  - at `m = 2`, equal coefficients give `imgCount = 2^{n-1} ≠ 2^{n-2}`
    (`MTuple.m_tuple_count_two_false`), valid for *every* APN `f`;
  - the APN cube map (Gold/Kasami `k = 1`) has equal-coefficient **triple**
    count `0 ≠ 2^{2n-3}` for `n` odd (`MTuple.triple_count_cube_false`).
-/

namespace MTuple

open Fintype WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Triple count under `Vanish`.** `m = 3` specialization of
`imgCount_of_vanish`: APN + the genuine spectral condition `Vanish` gives
`imgCount 3 f a c = 2^{2n-3}`. -/
theorem triple_count_of_vanish (n : ℕ) (hn : 1 ≤ n) (hcard : card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (c : Fin 3 → F) (hv : Vanish 3 f a c) :
    imgCount 3 f a c = 2 ^ (2 * n - 3) := by
  have h := imgCount_of_vanish n 3 hn (by norm_num) hcard f hf a ha c hv
  simpa using h

end MTuple
