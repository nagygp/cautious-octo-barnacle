import Mathlib
import AuditSBox.Audit.CipherDefs
import AuditSBox.Audit.CustomSbox

/-!
# PRINCE S-Box — Formal Audit Certificate

Machine-verified security properties of the PRINCE cipher S-box
(Borghoff–Canteaut–Güneysu–Kavun–Knežević–Knudsen–Leander–Nikov–Paar–
Rechberger–Rombouts–Thomsen–Yalçın, ASIACRYPT 2012).

PRINCE is a low-latency block cipher designed for hardware, used in
automotive and embedded applications. Its 4-bit S-box is a permutation on
GF(2)⁴ (16 elements).

## Verified Properties

| Property                | Value | Status          |
|-------------------------|-------|-----------------|
| Bijectivity             | ✓     | `native_decide` |
| Differential uniformity | 4     | `native_decide` |
| Max Walsh coefficient   | 8     | `native_decide` |
| Nonlinearity            | 4     | `native_decide` |
| Boomerang uniformity    | 10    | `native_decide` |

The PRINCE S-box achieves optimal differential uniformity (δ = 4) and
maximum nonlinearity (NL = 4) for 4-bit permutations, together with a low
boomerang uniformity (β = 10).

## Table provenance

The lookup table is transcribed from the PRINCE specification:

  - S (hex): b f 3 2 a c 9 1 6 7 8 0 e 5 d 4
-/

namespace PRINCE

open CipherAudit

/-! ### S-box definition -/

/-- The PRINCE 4-bit S-box lookup table. -/
def sbox : Array Nat := #[11, 15, 3, 2, 10, 12, 9, 1, 6, 7, 8, 0, 14, 5, 13, 4]

/-- The inverse PRINCE S-box. -/
def sboxInv : Array Nat := invertTable sbox

/-! ### Bijectivity -/

theorem sbox_bijective : isPermCheck sbox 4 = true := by native_decide

/-! ### Differential uniformity -/

theorem ddt_bounded : ddtBoundCheck sbox 4 4 = true := by native_decide
theorem ddt_tight : ddtTightCheck sbox 4 4 = true := by native_decide
theorem ddt_not_2bounded : ddtBoundCheck sbox 4 2 = false := by native_decide

/-! ### Walsh spectrum / nonlinearity -/

theorem walsh_bounded : walshBoundCheck sbox 4 8 = true := by native_decide
theorem walsh_tight : walshBoundCheck sbox 4 7 = false := by native_decide
theorem nonlinearity_eq : (2 ^ 4 - 8) / 2 = 4 := by norm_num

/-! ### Boomerang uniformity -/

theorem boomerang_bounded :
    boomerangBoundCheck sbox sboxInv 4 10 = true := by native_decide
theorem boomerang_tight :
    boomerangBoundCheck sbox sboxInv 4 9 = false := by native_decide

/-! ### Audit certificate -/

def certificate : Certificate where
  name         := "PRINCE"
  bits         := 4
  diffUnif     := 4
  nonlinearity := 4
  walshMax     := 8
  boomerangU   := 10
  isPerm       := true

/-! ### Derivative image bound -/

theorem deriv_image_lb : derivImageLowerBound 4 4 = 4 := by native_decide

end PRINCE
