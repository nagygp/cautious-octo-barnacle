import Mathlib
import RequestProject.CodingTheory.MacWilliamsDistribution

/-!
# The Delsarte inequalities (the linear-programming constraints)

This module is the next layer toward the **Delsarte linear-programming bound**
(roadmap item 9 of `CODING_THEORY_DIRECTIONS.md`, MacWilliams–Sloane Ch. 17),
building on the Krawtchouk-transform form of the MacWilliams identity
(`CodingTheory.macwilliams_distribution`).

The Delsarte LP bound maximises `Σ_i A_i` over weight distributions `(A_i)`
subject to the **Delsarte inequalities**: the Krawtchouk transform of the weight
distribution is nonnegative.  This module establishes those inequalities — the
linear constraints the LP optimises over — in two equivalent forms.

For a linear code `C` of length `n = #ι` over a field with `q = #F` elements,
with primal weight distribution `A_i = weightDistribution C i` and dual weight
distribution `B_k = weightDistribution Cᗮ k`:

* `delsarte_transform_eq` — the exact identity (over `ℤ`):
  `|C| · B_k = Σ_{i=0}^{n} A_i · K_k(i)`,
  i.e. the Krawtchouk transform of the primal distribution is `|C|` times the
  dual distribution.  (This is `macwilliams_distribution` cleared of the
  denominator and recognised as an integer identity.)
* `delsarte_inequality` — the **Delsarte inequality**:
  `0 ≤ Σ_{i=0}^{n} A_i · K_k(i)`  for every `k ≤ n`,
  because the right-hand side equals `|C| · B_k ≥ 0`.

These nonnegativity constraints, together with `A_0 = 1` and `Σ_i A_i = |C|`,
are precisely the feasible region of the Delsarte/Δ linear program; the remaining
work for the full bound is the optimisation over feasible `(A_i)`.

## Main results

* `delsarte_transform_eq` — `|C| · B_k = Σ_i A_i K_k(i)` over `ℤ`.
* `delsarte_inequality` — `0 ≤ Σ_i A_i K_k(i)` over `ℤ` (and `delsarte_inequality_real`
  over `ℝ`).
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
**The Delsarte transform identity (integer form).**  Clearing the `1/|C|`
denominator in the Krawtchouk-transform MacWilliams identity
(`macwilliams_distribution`) gives the exact integer identity
`|C| · B_k = Σ_{i=0}^{n} A_i · K_k(i)`, where `A_i = weightDistribution C i`,
`B_k = weightDistribution Cᗮ k`, `n = #ι`, `q = #F`.
-/
theorem delsarte_transform_eq (C : Submodule F (ι → F)) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    (Fintype.card C : ℤ) * (weightDistribution (dualCode C) k : ℤ)
      = ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (weightDistribution C i : ℤ)
            * krawtchouk (Fintype.card F) (Fintype.card ι) k i := by
  have := macwilliams_distribution C k hk;
  convert congr_arg ( fun x : ℂ => ( Fintype.card C : ℂ ) * x ) this using 1;
  norm_num [ ← mul_assoc, ← @Int.cast_inj ℂ ]

/-
**The Delsarte inequality (integer form).**  For every `k ≤ n` the Krawtchouk
transform of the weight distribution of a code is nonnegative:
`0 ≤ Σ_{i=0}^{n} A_i · K_k(i)`, because it equals `|C| · B_k` with `B_k ≥ 0`.
These are the linear constraints of the Delsarte LP bound.
-/
theorem delsarte_inequality (C : Submodule F (ι → F)) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    0 ≤ ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (weightDistribution C i : ℤ)
            * krawtchouk (Fintype.card F) (Fintype.card ι) k i := by
  convert delsarte_transform_eq C k hk ▸ mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) using 1

/-
**The Delsarte inequality (real form).**  The real-valued restatement of
`delsarte_inequality`, the form used in the Delsarte/Δ linear program.
-/
theorem delsarte_inequality_real (C : Submodule F (ι → F)) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    0 ≤ ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (weightDistribution C i : ℝ)
            * (krawtchouk (Fintype.card F) (Fintype.card ι) k i : ℝ) := by
  convert delsarte_inequality C k hk using 1;
  norm_cast

end CodingTheory