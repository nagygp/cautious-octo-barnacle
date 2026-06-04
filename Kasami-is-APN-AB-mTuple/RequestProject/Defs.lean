import Mathlib

/-!
# Kasami Exponent and Core Definitions

- `d k`:      Kasami exponent `2^{2k} − 2^k + 1`
- `L k x`:    Linearized polynomial `x^{2^k} + x`
- `Cross k s P`: Cross form `s · P^{2^k} + s^{2^k} · P`
- `N k x`:    Norm `x^{2^k + 1}`
- `sVal k t`:  Differential value `(t+1)^d + t^d`
-/

namespace CollisionAnalysis

open Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

def d (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1
def L (k : ℕ) (x : F) : F := x ^ (2 ^ k) + x
def Cross (k : ℕ) (s P : F) : F := s * P ^ (2 ^ k) + s ^ (2 ^ k) * P
def N (k : ℕ) (x : F) : F := x ^ (2 ^ k + 1)
def sVal (k : ℕ) (t : F) : F := (t + 1) ^ d k + t ^ d k

theorem d_pos (k : ℕ) (_hk : k ≥ 1) : 0 < d k := by unfold d; omega

theorem d_mul_gold (k : ℕ) (hk : k ≥ 1) : d k * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  unfold d; zify; rw [Nat.cast_sub (by gcongr <;> linarith)]; push_cast; ring

end CollisionAnalysis
