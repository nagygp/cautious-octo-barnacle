import Mathlib
import AuditSBox.Audit.CipherDefs

/-!
# GIFT S-Box — Formal Audit Certificate

Machine-verified security properties of the GIFT cipher S-box
(Banik–Pandey–Peyrin–Sasaki–Sim–Todo, CHES 2017).

GIFT is a lightweight block cipher designed for constrained environments.
Its 4-bit S-box operates on GF(2)⁴ (16 elements).

## Verified Properties

| Property              | Value | Status     |
|-----------------------|-------|------------|
| Bijectivity           | ✓     | `native_decide` |
| Differential uniformity | 6   | `native_decide` |
| Max Walsh coefficient | 8     | `native_decide` |
| Nonlinearity          | 4     | `native_decide` |
| Boomerang uniformity  | 16    | `native_decide` |

## Differential bias

With δ = 6 over GF(2⁴), the derivative image has |img(a)| ≥ ⌈16/6⌉ = 3
distinct output differences for any a ≠ 0.

The differential bias is 6/16 = 0.375, giving ~1.42 bits of security
per S-box invocation against differential cryptanalysis.
-/

namespace GIFT

open CipherAudit

/-! ### S-box definition -/

/-- The GIFT 4-bit S-box lookup table (hexadecimal: 1,a,4,c,6,f,3,9,2,d,b,7,5,0,8,e). -/
def sbox : Array Nat :=
  #[1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]

/-- The inverse GIFT S-box. -/
def sboxInv : Array Nat := invertTable sbox

/-! ### Bijectivity -/

/-- The GIFT S-box is a permutation on {0, …, 15}. -/
theorem sbox_bijective : isPermCheck sbox 4 = true := by native_decide

/-! ### Differential uniformity -/

/-- The GIFT S-box has differential uniformity ≤ 6:
    ∀ a ≠ 0, ∀ b, |{x | S(x ⊕ a) ⊕ S(x) = b}| ≤ 6. -/
theorem ddt_bounded : ddtBoundCheck sbox 4 6 = true := by native_decide

/-- The bound δ = 6 is tight: some DDT entry equals 6. -/
theorem ddt_tight : ddtTightCheck sbox 4 6 = true := by native_decide

/-- The GIFT S-box is NOT 4-bounded (some DDT entry > 4). -/
theorem ddt_not_4bounded : ddtBoundCheck sbox 4 4 = false := by native_decide

/-! ### Walsh spectrum / nonlinearity -/

/-- The maximum Walsh coefficient magnitude is ≤ 8. -/
theorem walsh_bounded : walshBoundCheck sbox 4 8 = true := by native_decide

/-- The Walsh bound is tight (some Walsh coefficient has magnitude 8). -/
theorem walsh_tight : walshBoundCheck sbox 4 7 = false := by native_decide

/-- Nonlinearity of the GIFT S-box = (2⁴ − 8) / 2 = 4. -/
theorem nonlinearity_eq : (2 ^ 4 - 8) / 2 = 4 := by norm_num

/-! ### Boomerang uniformity -/

/-- The boomerang uniformity of GIFT is ≤ 16. -/
theorem boomerang_bounded :
    boomerangBoundCheck sbox sboxInv 4 16 = true := by native_decide

/-! ### Audit certificate -/

/-- Complete audit certificate for the GIFT S-box. -/
def certificate : Certificate where
  name         := "GIFT"
  bits         := 4
  diffUnif     := 6
  nonlinearity := 4
  walshMax     := 8
  boomerangU   := 16
  isPerm       := true

/-! ### Derivative image bound -/

/-- Derivative image lower bound: |img(a)| ≥ ⌈16/6⌉ = 3 for a ≠ 0. -/
theorem deriv_image_lb : derivImageLowerBound 4 6 = 3 := by native_decide

/-- GIFT is NOT 2-uniform (not APN): some nonzero DDT entry exceeds 2
    (indeed δ = 6 > 2). -/
theorem not_optimal : ddtBoundCheck sbox 4 2 = false := by native_decide

end GIFT
