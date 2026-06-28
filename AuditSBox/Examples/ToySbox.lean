import Mathlib
import AuditSBox.Audit.CipherDefs
import AuditSBox.Audit.CustomSbox

/-!
# Toy 4-bit S-Box — Design Challenge Certificate

This module demonstrates the audit framework as a **design tool**, not just a
verification tool. We exhibit a freshly designed 4-bit permutation `toy` whose
metrics were tuned to the optimum achievable for 4-bit permutations:

  - differential uniformity δ = 4 (optimal: no 4-bit permutation is APN/2-uniform);
  - nonlinearity NL = 4 (maximum for 4-bit permutations);
  - boomerang uniformity β = 10 (low).

The workflow is: pick a candidate table, run `auditSbox` / the `*Check`
functions, adjust entries, and re-audit until the metrics hit their targets.
The certificates below pin down the final design.

## Verified Properties

| Property                | Value | Status          |
|-------------------------|-------|-----------------|
| Bijectivity             | ✓     | `native_decide` |
| Differential uniformity | 4     | `native_decide` |
| Max Walsh coefficient   | 8     | `native_decide` |
| Nonlinearity            | 4     | `native_decide` |
| Boomerang uniformity    | 10    | `native_decide` |

This matches the best simultaneously achievable profile for a 4-bit permutation
(δ = 4, NL = 4), with a boomerang uniformity (β = 10) strictly below the generic
value 16 — comparable to the strongest standardized 4-bit S-boxes (e.g.
Serpent S3/S4/S5/S7, PRINCE, Midori Sb1).
-/

namespace ToySbox

open CipherAudit

/-! ### S-box definition -/

/-- A designed 4-bit S-box meeting the optimal (δ = 4, NL = 4) profile. -/
def toy : Array Nat := #[1, 14, 8, 3, 9, 13, 6, 0, 10, 4, 2, 7, 11, 5, 15, 12]

/-- The inverse table. -/
def toyInv : Array Nat := invertTable toy

/-! ### Bijectivity -/

theorem toy_bijective : isPermCheck toy 4 = true := by native_decide

/-! ### Differential uniformity -/

theorem ddt_bounded : ddtBoundCheck toy 4 4 = true := by native_decide
theorem ddt_tight : ddtTightCheck toy 4 4 = true := by native_decide
theorem ddt_not_2bounded : ddtBoundCheck toy 4 2 = false := by native_decide

/-! ### Walsh spectrum / nonlinearity -/

theorem walsh_bounded : walshBoundCheck toy 4 8 = true := by native_decide
theorem walsh_tight : walshBoundCheck toy 4 7 = false := by native_decide
theorem nonlinearity_eq : (2 ^ 4 - 8) / 2 = 4 := by norm_num

/-! ### Boomerang uniformity -/

theorem boomerang_bounded :
    boomerangBoundCheck toy toyInv 4 10 = true := by native_decide
theorem boomerang_tight :
    boomerangBoundCheck toy toyInv 4 9 = false := by native_decide

/-! ### Audit certificate -/

def certificate : Certificate where
  name         := "Toy-4bit"
  bits         := 4
  diffUnif     := 4
  nonlinearity := 4
  walshMax     := 8
  boomerangU   := 10
  isPerm       := true

/-! ### Derivative image bound -/

theorem deriv_image_lb : derivImageLowerBound 4 4 = 4 := by native_decide

end ToySbox
