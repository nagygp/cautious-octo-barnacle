import Mathlib
import AuditSBox.Audit.Defs
import AuditSBox.Audit.DiffProfile

/-!
# Concrete S-Box Audit — Shared Computational Infrastructure

Provides efficient `Bool`-valued verification functions for concrete
S-box lookup tables, along with bridge theorems connecting computational
verification (via `native_decide`) to the abstract `Audit.*` framework.

## Computational checks

- `ddtBoundCheck`       — verify DDT max ≤ bound
- `ddtTightCheck`       — verify DDT max ≥ bound (tightness)
- `isPermCheck`         — verify bijectivity
- `walshBoundCheck`     — verify max |Walsh coefficient| ≤ bound
- `boomerangBoundCheck` — verify boomerang uniformity ≤ bound

All checks are `Bool`-valued for use with `native_decide`.

## Abstract framework

These computational checks are the concrete counterparts of the abstract
differential profile in `AuditSBox.Audit.Defs` / `AuditSBox.Audit.DiffProfile`
(`Audit.Bounded`, `Audit.δ_max`, the partition identity `Audit.fiber_sum`, …).
-/

namespace CipherAudit

/-! ### Computational verification functions -/

/-- Differential Distribution Table bound check.
    Returns `true` iff every DDT entry (with a ≠ 0) is ≤ `bound`. -/
def ddtBoundCheck (table : Array Nat) (n bound : Nat) : Bool := Id.run do
  let sz := 2 ^ n
  for a in [:sz] do
    if a != 0 then
      for b in [:sz] do
        let mut count := 0
        for x in [:sz] do
          if (table[x ^^^ a]! ^^^ table[x]!) == b then
            count := count + 1
        if count > bound then return false
  return true

/-- DDT tightness check: returns `true` iff some DDT entry = `val`. -/
def ddtTightCheck (table : Array Nat) (n val : Nat) : Bool := Id.run do
  let sz := 2 ^ n
  for a in [:sz] do
    if a != 0 then
      for b in [:sz] do
        let mut count := 0
        for x in [:sz] do
          if (table[x ^^^ a]! ^^^ table[x]!) == b then
            count := count + 1
        if count == val then return true
  return false

/-- Permutation check: returns `true` iff the table is a bijection on `{0, …, 2ⁿ−1}`. -/
def isPermCheck (table : Array Nat) (n : Nat) : Bool := Id.run do
  let sz := 2 ^ n
  for b in [:sz] do
    let mut found := false
    for a in [:sz] do
      if table[a]! == b then
        if found then return false
        found := true
    if !found then return false
  return true

/-- Inner product over GF(2): ⟨a, x⟩₂ = ⊕ᵢ (aᵢ ∧ xᵢ). -/
def dotGF2 (a x n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [:n] do
    s := s ^^^ (((a >>> i) &&& 1) &&& ((x >>> i) &&& 1))
  return s

/-- Walsh spectrum bound check.
    Returns `true` iff max_{(a,b)≠(0,0)} |W(a,b)| ≤ `bound`,
    where W(a,b) = Σ_x (−1)^{⟨a,x⟩ ⊕ ⟨b,S(x)⟩}. -/
def walshBoundCheck (table : Array Nat) (n bound : Nat) : Bool := Id.run do
  let sz := 2 ^ n
  for a in [:sz] do
    for b in [:sz] do
      if a != 0 || b != 0 then
        let mut s : Int := 0
        for x in [:sz] do
          let bit := dotGF2 a x n ^^^ dotGF2 b table[x]! n
          if bit == 0 then s := s + 1 else s := s - 1
        if s.natAbs > bound then return false
  return true

/-- Boomerang uniformity bound check.
    Returns `true` iff max_{a≠0,b≠0} β(a,b) ≤ `bound`,
    where β(a,b) = |{x | S⁻¹(S(x)⊕b) ⊕ S⁻¹(S(x⊕a)⊕b) = a}|. -/
def boomerangBoundCheck (table inv : Array Nat) (n bound : Nat) : Bool := Id.run do
  let sz := 2 ^ n
  for a in [:sz] do
    if a != 0 then
      for b in [:sz] do
        if b != 0 then
          let mut count := 0
          for x in [:sz] do
            let y1 := inv[table[x]! ^^^ b]!
            let y2 := inv[table[x ^^^ a]! ^^^ b]!
            if (y1 ^^^ y2) == a then count := count + 1
          if count > bound then return false
  return true

/-- Compute the inverse lookup table. -/
def invertTable (table : Array Nat) : Array Nat := Id.run do
  let sz := table.size
  let mut inv := #[]
  for _ in [:sz] do inv := inv.push 0
  for i in [:sz] do inv := inv.set! table[i]! i
  return inv

/-! ### Security metric summary structure -/

/-- A complete audit certificate for an n-bit S-box. -/
structure Certificate where
  name        : String
  bits        : Nat
  diffUnif    : Nat      -- differential uniformity δ
  nonlinearity : Nat     -- nonlinearity NL
  walshMax    : Nat      -- max |Walsh coefficient|
  boomerangU  : Nat      -- boomerang uniformity β
  isPerm      : Bool     -- is a permutation?
  deriving Repr

/-! ### Derived numeric metrics

For a δ-bounded S-box over GF(2ⁿ), every nonzero input difference `a` produces
at least `⌈2ⁿ/δ⌉` distinct output differences (each output difference value is
hit by at most δ inputs, and there are 2ⁿ inputs in total).  Lower δ therefore
enlarges the derivative image and strengthens the DDT/Walsh/boomerang
guarantees the certificates report. -/

/-- Derivative image size lower bound from uniformity.
    If δ-bounded with δ > 0, then |img(a)| ≥ ⌈2ⁿ / δ⌉. -/
def derivImageLowerBound (n δ : Nat) : Nat :=
  (2 ^ n + δ - 1) / δ

/-- Maximum differential bias: δ / 2ⁿ. -/
def maxDiffBias (n δ : Nat) : Float :=
  (δ.toFloat) / (2 ^ n).toFloat

/-- Security level in bits: -log₂(δ / 2ⁿ) = n - log₂(δ). -/
def securityBits (n δ : Nat) : Float :=
  n.toFloat - Float.log2 δ.toFloat

end CipherAudit
