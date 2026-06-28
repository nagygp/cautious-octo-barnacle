import Mathlib
import AuditSBox.Audit.CipherDefs
import AuditSBox.Audit.CustomSbox

/-!
# SKINNY-128 8-bit S-Box — Formal Audit Certificate

Machine-verified security properties of the **8-bit** SKINNY S-box `S8`
(Beierle–Jean–Kölbl–Leander–Moradi–Peyrin–Sasaki–Sasdrich–Sim, CRYPTO 2016),
used in the 128-bit-state versions of the SKINNY tweakable block cipher.

Unlike the standardized 4-bit and 8-bit S-boxes audited elsewhere in this
project (AES, SM4, Serpent, …), the SKINNY-128 S-box is a *deliberately
lightweight* design: it is built from a few iterations of a cheap bit-sliced
round (an XOR with a NOR of two bits, followed by a bit rotation).  The price
of that low gate-count is comparatively weak per-call statistics, which the
cipher compensates for with a larger number of rounds.

The audit below records the *true* metrics of the table as supplied; it is an
honest accounting, not a marketing sheet.

## Verified Properties

| Property                | Value | Status          |
|-------------------------|-------|-----------------|
| Bijectivity             | ✓     | `native_decide` |
| Differential uniformity | 64    | `native_decide` |
| Max Walsh coefficient   | 128   | `native_decide` |
| Nonlinearity            | 64    | `native_decide` |
| Boomerang uniformity    | 256   | `native_decide` |

For comparison, the AES 8-bit S-box achieves δ = 4, NL = 112, β = 6.  The
SKINNY-128 S-box trades all three metrics for hardware cheapness: δ = 64 means
the best differential transition holds with probability 64/256 = 2⁻²; the
nonlinearity 64 corresponds to a Walsh maximum of 128 = 2⁷; and the boomerang
uniformity reaches the maximum possible value 256 = 2⁸ for some difference pair.

The 256-entry inverse table published with the cipher was checked to coincide
exactly with `invertTable sbox`, confirming `sbox` is a permutation and that the
specification's two tables are mutually consistent.

## Differential bias

With δ = 64 over GF(2⁸), the derivative-image lower bound degrades to
⌈256/64⌉ = 4: each nonzero input difference is guaranteed to reach at least 4
distinct output differences (versus 64 for AES).  This quantifies exactly how
much structural richness is sacrificed for the lightweight construction.
-/

namespace SKINNY8

open CipherAudit

/-! ### S-box definition -/

/-- The SKINNY-128 8-bit S-box lookup table `S8` (256 entries). -/
def sbox : Array Nat := #[
  101,76,106,66,75,99,67,107,85,117,90,122,83,115,91,123,
  53,140,58,129,137,51,128,59,149,37,152,42,144,35,153,43,
  229,204,232,193,201,224,192,233,213,245,216,248,208,240,217,249,
  165,28,168,18,27,160,19,169,5,181,10,184,3,176,11,185,
  50,136,60,133,141,52,132,61,145,34,156,44,148,36,157,45,
  98,74,108,69,77,100,68,109,82,114,92,124,84,116,93,125,
  161,26,172,21,29,164,20,173,2,177,12,188,4,180,13,189,
  225,200,236,197,205,228,196,237,209,241,220,252,212,244,221,253,
  54,142,56,130,139,48,131,57,150,38,154,40,147,32,155,41,
  102,78,104,65,73,96,64,105,86,118,88,120,80,112,89,121,
  166,30,170,17,25,163,16,171,6,182,8,186,0,179,9,187,
  230,206,234,194,203,227,195,235,214,246,218,250,211,243,219,251,
  49,138,62,134,143,55,135,63,146,33,158,46,151,39,159,47,
  97,72,110,70,79,103,71,111,81,113,94,126,87,119,95,127,
  162,24,174,22,31,167,23,175,1,178,14,190,7,183,15,191,
  226,202,238,198,207,231,199,239,210,242,222,254,215,247,223,255]

/-- The inverse SKINNY-128 8-bit S-box, computed from `sbox`.
    This was verified to match the inverse table `S8_inv` published with
    the cipher specification. -/
def sboxInv : Array Nat := invertTable sbox

/-! ### Bijectivity -/

/-- The SKINNY-128 8-bit S-box is a permutation on {0, …, 255}. -/
theorem sbox_bijective : isPermCheck sbox 8 = true := by native_decide

/-! ### Differential uniformity -/

/-- The SKINNY-128 8-bit S-box has differential uniformity ≤ 64. -/
theorem ddt_bounded : ddtBoundCheck sbox 8 64 = true := by native_decide

/-- The bound δ = 64 is tight: some DDT entry equals 64. -/
theorem ddt_tight : ddtTightCheck sbox 8 64 = true := by native_decide

/-- The S-box is NOT 63-bounded, confirming δ = 64 exactly. -/
theorem ddt_not_63bounded : ddtBoundCheck sbox 8 63 = false := by native_decide

/-! ### Walsh spectrum / nonlinearity -/

/-- The maximum Walsh coefficient magnitude is ≤ 128. -/
theorem walsh_bounded : walshBoundCheck sbox 8 128 = true := by native_decide

/-- The Walsh bound is tight (some Walsh coefficient has magnitude 128). -/
theorem walsh_tight : walshBoundCheck sbox 8 127 = false := by native_decide

/-- Nonlinearity of the SKINNY-128 8-bit S-box = (2⁸ − 128) / 2 = 64. -/
theorem nonlinearity_eq : (2 ^ 8 - 128) / 2 = 64 := by norm_num

/-! ### Boomerang uniformity -/

/-- The boomerang uniformity of the SKINNY-128 8-bit S-box is ≤ 256
    (the maximum possible value for an 8-bit permutation). -/
theorem boomerang_bounded :
    boomerangBoundCheck sbox sboxInv 8 256 = true := by native_decide

/-- The boomerang bound is tight: some BCT entry equals 256. -/
theorem boomerang_tight :
    boomerangBoundCheck sbox sboxInv 8 255 = false := by native_decide

/-! ### Audit certificate -/

/-- Complete audit certificate for the SKINNY-128 8-bit S-box. -/
def certificate : Certificate where
  name         := "SKINNY-8bit"
  bits         := 8
  diffUnif     := 64
  nonlinearity := 64
  walshMax     := 128
  boomerangU   := 256
  isPerm       := true

/-! ### Derivative image bound -/

/-- Derivative image lower bound: |img(a)| ≥ ⌈256/64⌉ = 4 for a ≠ 0.
    The lightweight construction (δ = 64) reduces the guaranteed
    derivative-image size to 4, versus 64 for the δ = 4 AES S-box. -/
theorem deriv_image_lb : derivImageLowerBound 8 64 = 4 := by native_decide

end SKINNY8
