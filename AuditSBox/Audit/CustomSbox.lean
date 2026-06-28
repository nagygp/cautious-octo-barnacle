import Mathlib
import AuditSBox.Audit.CipherDefs

/-!
# Generic S-Box Auditor — CustomSbox

**Purpose**: Given *any* S-box as a lookup table (`Array Nat`) and a bit-width `n`,
this module automatically computes and certifies all five standard security
properties:

  1. **Bijectivity** — is the S-box a permutation?
  2. **Differential uniformity (δ)** — maximum DDT entry (lower is better)
  3. **Walsh spectrum / nonlinearity** — resistance to linear cryptanalysis
  4. **Boomerang uniformity (β)** — resistance to boomerang attacks
  5. **Derivative image bound** — structural lower bound ⌈2ⁿ/δ⌉ on the
     number of distinct output differences

## How to use

To audit your own S-box, create a new file that imports this module:

```lean
import AuditSBox.Audit.CustomSbox

namespace MySbox

-- Step 1: Define your S-box as a lookup table
def table : Array Nat := #[0x0C, 0x05, 0x06, 0x0B, ...]

-- Step 2: Run the audit
def myAudit : CipherAudit.SboxAudit := CipherAudit.auditSbox "MySbox" 4 table

-- Step 3: Prove formal bounds via native_decide
theorem my_ddt : CipherAudit.ddtBoundCheck table 4 4 = true := by native_decide
theorem my_walsh : CipherAudit.walshBoundCheck table 4 8 = true := by native_decide
-- etc.
end MySbox
```

## What each metric means (plain English)

- **δ (differential uniformity)**: If an attacker chooses a specific input
  difference `a` and observes the output difference, at most `δ` inputs
  produce any given output difference.  Lower δ = harder to attack.
  Optimal is δ = 2 (called "2-uniform"); AES achieves δ = 4.

- **Walsh max / nonlinearity**: Measures how far the S-box is from any
  linear function.  Higher nonlinearity = harder for linear cryptanalysis.
  Nonlinearity = (2^n - walshMax) / 2.

- **β (boomerang uniformity)**: Measures resistance to boomerang-style
  differential attacks (a more advanced attack model). Lower β = better.

- **Derivative image bound**: For a δ-bounded S-box, each nonzero input
  difference `a` produces at least ⌈2ⁿ/δ⌉ distinct output differences.
  This is a direct consequence of δ-uniformity (each output difference is
  produced by at most δ inputs).

## Design

This module is entirely computational — all proofs use `native_decide`,
which compiles the check to native code and runs it exhaustively.
The `SboxAudit` structure collects results for inspection via `#eval`.
-/

namespace CipherAudit

/-! ### Computational audit engine -/

/-- Compute the exact differential uniformity of an S-box. -/
def computeDiffUnif (table : Array Nat) (n : Nat) : Nat := Id.run do
  let sz := 2 ^ n
  let mut maxVal := 0
  for a in [:sz] do
    if a != 0 then
      for b in [:sz] do
        let mut count := 0
        for x in [:sz] do
          if (table[x ^^^ a]! ^^^ table[x]!) == b then
            count := count + 1
        if count > maxVal then maxVal := count
  return maxVal

/-- Compute the exact maximum Walsh coefficient magnitude. -/
def computeWalshMax (table : Array Nat) (n : Nat) : Nat := Id.run do
  let sz := 2 ^ n
  let mut maxVal := 0
  for a in [:sz] do
    for b in [:sz] do
      if a != 0 || b != 0 then
        let mut s : Int := 0
        for x in [:sz] do
          let bit := dotGF2 a x n ^^^ dotGF2 b table[x]! n
          if bit == 0 then s := s + 1 else s := s - 1
        if s.natAbs > maxVal then maxVal := s.natAbs
  return maxVal

/-- Compute the exact boomerang uniformity of an S-box (requires inverse table). -/
def computeBoomerangUnif (table inv : Array Nat) (n : Nat) : Nat := Id.run do
  let sz := 2 ^ n
  let mut maxVal := 0
  for a in [:sz] do
    if a != 0 then
      for b in [:sz] do
        if b != 0 then
          let mut count := 0
          for x in [:sz] do
            let y1 := inv[table[x]! ^^^ b]!
            let y2 := inv[table[x ^^^ a]! ^^^ b]!
            if (y1 ^^^ y2) == a then count := count + 1
          if count > maxVal then maxVal := count
  return maxVal

/-- Full audit result for an S-box (computable, usable with `#eval`). -/
structure SboxAudit where
  /-- Human-readable name -/
  name           : String
  /-- Bit-width of the S-box -/
  bits           : Nat
  /-- Is the S-box a permutation (bijection)? -/
  isPerm         : Bool
  /-- Differential uniformity δ -/
  diffUnif       : Nat
  /-- Maximum Walsh coefficient magnitude -/
  walshMax       : Nat
  /-- Nonlinearity = (2^n - walshMax) / 2 -/
  nonlinearity   : Nat
  /-- Boomerang uniformity β (0 if not a permutation) -/
  boomerangUnif  : Nat
  /-- Derivative image lower bound: ⌈2ⁿ/δ⌉ -/
  derivImageBound : Nat
  /-- Security bits against differential cryptanalysis: n - log₂(δ) -/
  secBits        : Float
  deriving Repr

/-- Run a complete audit on any S-box lookup table.

    **Parameters**:
    - `name`: human-readable identifier for the S-box
    - `n`: bit-width (table should have 2ⁿ entries)
    - `table`: the S-box as a lookup table `Array Nat`

    **Returns**: an `SboxAudit` structure with all five security metrics.

    **Example**:
    ```
    #eval CipherAudit.auditSbox "MyBox" 4 #[1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]
    ```
-/
def auditSbox (name : String) (n : Nat) (table : Array Nat) : SboxAudit :=
  let perm := isPermCheck table n
  let delta := computeDiffUnif table n
  let wmax := computeWalshMax table n
  let inv := invertTable table
  let beta := if perm then computeBoomerangUnif table inv n else 0
  { name           := name
    bits           := n
    isPerm         := perm
    diffUnif       := delta
    walshMax       := wmax
    nonlinearity   := (2 ^ n - wmax) / 2
    boomerangUnif  := beta
    derivImageBound := if delta > 0 then derivImageLowerBound n delta else 2 ^ n
    secBits        := if delta > 0 then securityBits n delta else n.toFloat }

/-- Pretty-print an audit result as a multi-line string. -/
def SboxAudit.display (a : SboxAudit) : String :=
  s!"╔══════════════════════════════════════╗\n" ++
  s!"║  S-Box Audit: {a.name}\n" ++
  s!"╠══════════════════════════════════════╣\n" ++
  s!"║  Bit-width:            {a.bits}\n" ++
  s!"║  Permutation:          {a.isPerm}\n" ++
  s!"║  Differential unif δ:  {a.diffUnif}\n" ++
  s!"║  Walsh max |W|:        {a.walshMax}\n" ++
  s!"║  Nonlinearity:         {a.nonlinearity}\n" ++
  s!"║  Boomerang unif β:     {a.boomerangUnif}\n" ++
  s!"║  Deriv image bound:    ≥ {a.derivImageBound}\n" ++
  s!"║  Security bits:        {a.secBits}\n" ++
  s!"╚══════════════════════════════════════╝"

instance : ToString SboxAudit := ⟨SboxAudit.display⟩

/-! ### Formal certificate helpers

These helpers make it easy to state and prove formal bounds for
a custom S-box. Each takes a lookup table and a bound, and the
proof obligation is just `by native_decide`.
-/

/-- Assert that `table` is a permutation on `{0, …, 2ⁿ - 1}`. -/
def assertPerm (table : Array Nat) (n : Nat) : Prop :=
  isPermCheck table n = true

/-- Assert that the differential uniformity of `table` is ≤ `bound`. -/
def assertDDT (table : Array Nat) (n bound : Nat) : Prop :=
  ddtBoundCheck table n bound = true

/-- Assert that the differential uniformity of `table` is tight at `val`. -/
def assertDDTTight (table : Array Nat) (n val : Nat) : Prop :=
  ddtTightCheck table n val = true

/-- Assert that the maximum Walsh coefficient of `table` is ≤ `bound`. -/
def assertWalsh (table : Array Nat) (n bound : Nat) : Prop :=
  walshBoundCheck table n bound = true

/-- Assert that the boomerang uniformity of `table` is ≤ `bound`. -/
def assertBoomerang (table inv : Array Nat) (n bound : Nat) : Prop :=
  boomerangBoundCheck table inv n bound = true

/-! ### Demo: audit the three standard ciphers via the generic auditor

To try it yourself, uncomment these in a scratch file:
```
#eval auditSbox "AES" 8 AES.sbox       -- takes a few seconds
#eval auditSbox "GIFT" 4 GIFT.sbox     -- fast
#eval auditSbox "ASCON" 5 ASCON.sbox   -- fast
```
-/

end CipherAudit
