import Mathlib
import AuditSBox.Audit.CipherDefs
import AuditSBox.Audit.CustomSbox

/-!
# Keccak χ (5-bit) — Formal Audit Certificate

Machine-verified security properties of the Keccak (SHA-3) nonlinear mapping
χ, restricted to a single 5-bit row (Bertoni–Daemen–Peeters–Van Assche; SHA-3,
FIPS 202).

χ is the only nonlinear step of the Keccak-f permutation. It acts independently
on each row of 5 bits via

    yᵢ = xᵢ ⊕ ((¬x₍ᵢ₊₁₎) ∧ x₍ᵢ₊₂₎)        (indices mod 5).

To guarantee the table is *accurate by construction* (rather than transcribed),
the lookup table below is computed directly from this algebraic definition by
`chi5`, and all certificates are proved on that computed table.

## Verified Properties

| Property                | Value | Status          |
|-------------------------|-------|-----------------|
| Bijectivity             | ✓     | `native_decide` |
| Differential uniformity | 8     | `native_decide` |
| Max Walsh coefficient   | 16    | `native_decide` |
| Nonlinearity            | 8     | `native_decide` |
| Boomerang uniformity    | 16    | `native_decide` |

## Note on bijectivity

For an *odd* row length (here 5), χ is a permutation — it is in fact invertible,
which is what makes Keccak-f a permutation. (χ is non-invertible only for even
row lengths.) The certificates below therefore include a permutation proof and
a boomerang-uniformity bound; the generic DDT/Walsh framework applies regardless
of bijectivity.
-/

namespace KeccakChi

open CipherAudit

/-! ### Algebraic definition of χ on a 5-bit row -/

/-- One application of Keccak's χ to a 5-bit value `x`:
    output bit `i` is `xᵢ ⊕ ((¬x₍ᵢ₊₁₎) ∧ x₍ᵢ₊₂₎)`, indices mod 5. -/
def chi5 (x : Nat) : Nat := Id.run do
  let mut out := 0
  for i in [:5] do
    let xi  := (x >>> i) &&& 1
    let xi1 := (x >>> ((i + 1) % 5)) &&& 1
    let xi2 := (x >>> ((i + 2) % 5)) &&& 1
    let bit := xi ^^^ ((1 - xi1) &&& xi2)
    out := out ||| (bit <<< i)
  return out

/-- The χ lookup table on 5-bit rows, computed from `chi5`. -/
def sbox : Array Nat := (Array.range 32).map chi5

/-- The inverse table. -/
def sboxInv : Array Nat := invertTable sbox

/-! ### Bijectivity -/

theorem sbox_bijective : isPermCheck sbox 5 = true := by native_decide

/-! ### Differential uniformity -/

theorem ddt_bounded : ddtBoundCheck sbox 5 8 = true := by native_decide
theorem ddt_tight : ddtTightCheck sbox 5 8 = true := by native_decide
theorem ddt_not_6bounded : ddtBoundCheck sbox 5 6 = false := by native_decide

/-! ### Walsh spectrum / nonlinearity -/

theorem walsh_bounded : walshBoundCheck sbox 5 16 = true := by native_decide
theorem walsh_tight : walshBoundCheck sbox 5 15 = false := by native_decide
theorem nonlinearity_eq : (2 ^ 5 - 16) / 2 = 8 := by norm_num

/-! ### Boomerang uniformity -/

theorem boomerang_bounded :
    boomerangBoundCheck sbox sboxInv 5 16 = true := by native_decide

/-! ### Audit certificate -/

def certificate : Certificate where
  name         := "Keccak-chi5"
  bits         := 5
  diffUnif     := 8
  nonlinearity := 8
  walshMax     := 16
  boomerangU   := 16
  isPerm       := true

/-! ### Derivative image bound -/

theorem deriv_image_lb : derivImageLowerBound 5 8 = 4 := by native_decide

end KeccakChi
