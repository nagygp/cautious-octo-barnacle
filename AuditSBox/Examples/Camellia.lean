import Mathlib
import AuditSBox.Audit.CipherDefs
import AuditSBox.Audit.CustomSbox

/-!
# Camellia S-Boxes — Formal Audit Certificates

Machine-verified security properties of all four Camellia 8-bit S-boxes
(Aoki–Ichikawa–Kanda–Matsui–Moriai–Nakajima–Tokita, 2000;
ISO/IEC 18033-3, CRYPTREC recommended cipher).

Camellia uses four 8-bit S-boxes (SBOX1–SBOX4), each a permutation on
GF(2)⁸ (256 elements). SBOX1 is the base S-box, and the remaining three
are derived from it via bit rotations:

  - SBOX2(x) = SBOX1(x) ≪ 1   (left rotate output by 1 bit)
  - SBOX3(x) = SBOX1(x) ≪ 7   (left rotate output by 7 bits = right rotate by 1)
  - SBOX4(x) = SBOX1(x ≪ 1)   (left rotate input by 1 bit)

Because bit rotation is a linear operation over GF(2)⁸, all four S-boxes
are affine-equivalent and share identical differential/linear/boomerang
properties.

## Verified Properties (all four S-boxes)

| Property              | Value | Status     |
|-----------------------|-------|------------|
| Bijectivity           | ✓     | `native_decide` |
| Differential uniformity | 4   | `native_decide` |
| Max Walsh coefficient | 32    | `native_decide` |
| Nonlinearity          | 112   | `native_decide` |
| Boomerang uniformity  | 6     | `native_decide` |

These are the same optimal metrics as AES and SM4 — all three ciphers
base their S-boxes on multiplicative inversion in GF(2⁸).
-/

namespace Camellia

open CipherAudit

/-! ### Helper: bit rotations -/

/-- Left rotation by 1 bit (8-bit width). -/
def rotl1 (n : Nat) : Nat := ((n <<< 1) ||| (n >>> 7)) &&& 0xFF

/-- Left rotation by 7 bits (8-bit width), equivalent to right rotation by 1. -/
def rotl7 (n : Nat) : Nat := ((n <<< 7) ||| (n >>> 1)) &&& 0xFF

/-! ### S-box definitions -/

/-- Camellia SBOX1 — the base 8-bit S-box (256 entries). -/
def sbox1 : Array Nat := #[
  112, 130, 44, 236, 179, 39, 192, 229, 228, 133, 87, 53, 234, 12, 174, 65,
  35, 239, 107, 147, 69, 25, 165, 33, 237, 14, 79, 78, 29, 101, 146, 189,
  134, 184, 175, 143, 124, 235, 31, 206, 62, 48, 220, 95, 94, 197, 11, 26,
  166, 225, 57, 202, 213, 71, 93, 61, 217, 1, 90, 214, 81, 86, 108, 77,
  139, 13, 154, 102, 251, 204, 176, 45, 116, 18, 43, 32, 240, 177, 132, 153,
  223, 76, 203, 194, 52, 126, 118, 5, 109, 183, 169, 49, 209, 23, 4, 215,
  20, 88, 58, 97, 222, 27, 17, 28, 50, 15, 156, 22, 83, 24, 242, 34,
  254, 68, 207, 178, 195, 181, 122, 145, 36, 8, 232, 168, 96, 252, 105, 80,
  170, 208, 160, 125, 161, 137, 98, 151, 84, 91, 30, 149, 224, 255, 100, 210,
  16, 196, 0, 72, 163, 247, 117, 219, 138, 3, 230, 218, 9, 63, 221, 148,
  135, 92, 131, 2, 205, 74, 144, 51, 115, 103, 246, 243, 157, 127, 191, 226,
  82, 155, 216, 38, 200, 55, 198, 59, 129, 150, 111, 75, 19, 190, 99, 46,
  233, 121, 167, 140, 159, 110, 188, 142, 41, 245, 249, 182, 47, 253, 180, 89,
  120, 152, 6, 106, 231, 70, 113, 186, 212, 37, 171, 66, 136, 162, 141, 250,
  114, 7, 185, 85, 248, 238, 172, 10, 54, 73, 42, 104, 60, 56, 241, 164,
  64, 40, 211, 123, 187, 201, 67, 193, 21, 227, 173, 244, 119, 199, 128, 158]

/-- Camellia SBOX2 — SBOX1(x) rotated left by 1 bit. -/
def sbox2 : Array Nat := (Array.range 256).map fun x => rotl1 sbox1[x]!

/-- Camellia SBOX3 — SBOX1(x) rotated left by 7 bits (= right by 1). -/
def sbox3 : Array Nat := (Array.range 256).map fun x => rotl7 sbox1[x]!

/-- Camellia SBOX4 — SBOX1 applied to input rotated left by 1 bit. -/
def sbox4 : Array Nat := (Array.range 256).map fun x => sbox1[rotl1 x]!

/-- Inverse tables. -/
def sbox1Inv : Array Nat := invertTable sbox1
def sbox2Inv : Array Nat := invertTable sbox2
def sbox3Inv : Array Nat := invertTable sbox3
def sbox4Inv : Array Nat := invertTable sbox4

/-! ### SBOX1 — Formal certificates -/
namespace S1

theorem perm : isPermCheck sbox1 8 = true := by native_decide
theorem ddt_bounded : ddtBoundCheck sbox1 8 4 = true := by native_decide
theorem ddt_tight : ddtTightCheck sbox1 8 4 = true := by native_decide
theorem ddt_not_2bounded : ddtBoundCheck sbox1 8 2 = false := by native_decide
theorem walsh_bounded : walshBoundCheck sbox1 8 32 = true := by native_decide
theorem walsh_tight : walshBoundCheck sbox1 8 31 = false := by native_decide
theorem nonlinearity_eq : (2 ^ 8 - 32) / 2 = 112 := by norm_num
theorem boomerang_bounded :
    boomerangBoundCheck sbox1 sbox1Inv 8 6 = true := by native_decide
theorem boomerang_tight :
    boomerangBoundCheck sbox1 sbox1Inv 8 5 = false := by native_decide

def certificate : Certificate where
  name         := "Camellia-S1"
  bits         := 8
  diffUnif     := 4
  nonlinearity := 112
  walshMax     := 32
  boomerangU   := 6
  isPerm       := true

theorem deriv_image_lb : derivImageLowerBound 8 4 = 64 := by native_decide

end S1

/-! ### SBOX2 — Formal certificates -/
namespace S2

theorem perm : isPermCheck sbox2 8 = true := by native_decide
theorem ddt_bounded : ddtBoundCheck sbox2 8 4 = true := by native_decide
theorem ddt_tight : ddtTightCheck sbox2 8 4 = true := by native_decide
theorem walsh_bounded : walshBoundCheck sbox2 8 32 = true := by native_decide
theorem walsh_tight : walshBoundCheck sbox2 8 31 = false := by native_decide
theorem boomerang_bounded :
    boomerangBoundCheck sbox2 sbox2Inv 8 6 = true := by native_decide
theorem boomerang_tight :
    boomerangBoundCheck sbox2 sbox2Inv 8 5 = false := by native_decide

def certificate : Certificate where
  name         := "Camellia-S2"
  bits         := 8
  diffUnif     := 4
  nonlinearity := 112
  walshMax     := 32
  boomerangU   := 6
  isPerm       := true

end S2

/-! ### SBOX3 — Formal certificates -/
namespace S3

theorem perm : isPermCheck sbox3 8 = true := by native_decide
theorem ddt_bounded : ddtBoundCheck sbox3 8 4 = true := by native_decide
theorem ddt_tight : ddtTightCheck sbox3 8 4 = true := by native_decide
theorem walsh_bounded : walshBoundCheck sbox3 8 32 = true := by native_decide
theorem walsh_tight : walshBoundCheck sbox3 8 31 = false := by native_decide
theorem boomerang_bounded :
    boomerangBoundCheck sbox3 sbox3Inv 8 6 = true := by native_decide
theorem boomerang_tight :
    boomerangBoundCheck sbox3 sbox3Inv 8 5 = false := by native_decide

def certificate : Certificate where
  name         := "Camellia-S3"
  bits         := 8
  diffUnif     := 4
  nonlinearity := 112
  walshMax     := 32
  boomerangU   := 6
  isPerm       := true

end S3

/-! ### SBOX4 — Formal certificates -/
namespace S4

theorem perm : isPermCheck sbox4 8 = true := by native_decide
theorem ddt_bounded : ddtBoundCheck sbox4 8 4 = true := by native_decide
theorem ddt_tight : ddtTightCheck sbox4 8 4 = true := by native_decide
theorem walsh_bounded : walshBoundCheck sbox4 8 32 = true := by native_decide
theorem walsh_tight : walshBoundCheck sbox4 8 31 = false := by native_decide
theorem boomerang_bounded :
    boomerangBoundCheck sbox4 sbox4Inv 8 6 = true := by native_decide
theorem boomerang_tight :
    boomerangBoundCheck sbox4 sbox4Inv 8 5 = false := by native_decide

def certificate : Certificate where
  name         := "Camellia-S4"
  bits         := 8
  diffUnif     := 4
  nonlinearity := 112
  walshMax     := 32
  boomerangU   := 6
  isPerm       := true

end S4

end Camellia
