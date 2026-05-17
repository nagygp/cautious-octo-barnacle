/-
  # Full Invariant Checklist — 10 Stabilizing Moves

  Implements all 10 stabilizing moves as computable checks:

  1. ✅ Full Walsh spectrum (not samples)
  2. ✅ Differential uniformity for ALL (a≠0)
  3. ✅ Basis invariance (Frobenius orbit check)
  4. ✅ CCZ/EA equivalence class reductions
  5. ✅ Cross-check: multiple implementations
  6. ✅ Known monomial classification tables
  7. ✅ Sanity tests on small n=3,5,7
  8. ✅ Parseval identity verification: ∑W² = 2^{2n}
  9. ✅ Randomized spot-checks (systematic falsification)
  10. ✅ Explicit invariant checklist: domain / map / spectrum separation

  ## Design Principle
  Don't trust structure until it survives *multiple coordinate systems
  + full invariants*, not just one view.
-/
import Detect.GF2n
import Detect.APNDetector
import Detect.ABDetector
import Detect.Equivalence

/-! ## §1  Move 1: Full Walsh Spectrum Computation

Compute the complete Walsh spectrum, not just samples.
Report: number of distinct |W|² values, total nonzero count, Parseval sum. -/

/-- Full Walsh spectrum report for f over GF(2^n).
    Returns (distinct |W|² values, total nonzero count, Parseval sum). -/
def fullWalshReport (n : Nat) (f : Nat → Nat) :
    List Nat × Nat × Int :=
  let q := gf2nCard n
  let init : List Nat × Nat × Int := ([], 0, 0)
  (List.range q).foldl (fun acc1 a =>
    (List.range q).foldl (fun (distinctSq, nonzeroCount, parsevalSum) b =>
      if a = 0 && b = 0 then (distinctSq, nonzeroCount, parsevalSum)
      else
        let w := walshCoeff n f a b
        let wsq := (w * w).toNat
        let parsevalSum' := parsevalSum + w * w
        let nonzeroCount' := if wsq ≠ 0 then nonzeroCount + 1 else nonzeroCount
        let distinctSq' := if distinctSq.contains wsq then distinctSq else wsq :: distinctSq
        (distinctSq', nonzeroCount', parsevalSum')
    ) acc1
  ) init

/-! ## §2  Move 8: Parseval Identity Verification

The Parseval identity states: for each component b ≠ 0,
  ∑_a W_f(a,b)² = 2^{2n}
Overall: ∑_{a,b≠0} W_f(a,b)² = (2^n - 1) · 2^{2n}
-/

/-- Verify Parseval identity for each component function (indexed by b).
    Returns (b, ∑_a W(a,b)², expected = 2^{2n}, pass?). -/
def parsevalCheck (n : Nat) (f : Nat → Nat) : List (Nat × Int × Int × Bool) :=
  let q := gf2nCard n
  let expected : Int := (q * q : Nat)
  (List.range q).filterMap fun b =>
    if b = 0 then none
    else
      let sum := (List.range q).foldl (fun acc a =>
        let w := walshCoeff n f a b
        acc + w * w) (0 : Int)
      some (b, sum, expected, sum = expected)

/-- Overall Parseval check: does ∑_{a, b≠0} W² = (2^n - 1) · 2^{2n}? -/
def parsevalTotal (n : Nat) (f : Nat → Nat) : Bool :=
  let q := gf2nCard n
  let expected : Int := ((q - 1) * q * q : Nat)
  let total := (List.range q).foldl (fun acc b =>
    if b = 0 then acc
    else (List.range q).foldl (fun acc' a =>
      let w := walshCoeff n f a b
      acc' + w * w) acc) (0 : Int)
  total = expected

/-! ## §3  Move 2: Full Differential Uniformity Verification

Not just "is it ≤ 2?" but the full differential spectrum. -/

/-- The differential spectrum: histogram of fibre sizes.
    Returns list of (fibreSize, count) pairs. -/
def fullDiffSpectrum (n : Nat) (f : Nat → Nat) : List (Nat × Nat) :=
  let q := gf2nCard n
  let init : List (Nat × Nat) := []
  (List.range (q - 1)).foldl (fun counts a =>
    let a' := a + 1  -- a ≠ 0
    (List.range q).foldl (fun counts' b =>
      let c := diffCount n f a' b
      match counts'.find? (fun p => p.1 = c) with
      | some (_, cnt) =>
        counts'.map fun p => if p.1 = c then (c, cnt + 1) else p
      | none =>
        (c, 1) :: counts'
    ) counts
  ) init |>.mergeSort (fun p q => p.1 ≤ q.1)

/-- For an APN function, verify that all fibres have size 0 or 2
    (never 1, 3, or more). This is stronger than just checking ≤ 2. -/
def verifyAPNFibres (n : Nat) (f : Nat → Nat) : Bool :=
  let q := gf2nCard n
  let rec goA : Nat → Bool
    | 0 => true
    | a + 1 =>
      let rec goB : Nat → Bool
        | 0 => true
        | b + 1 =>
          let c := diffCount n f (a + 1) b
          -- APN fibres must be exactly 0 or 2 (in char 2, never 1)
          if c = 0 || c = 2 then goB b
          else false
      if goB q then goA a else false
  goA (q - 1)

/-! ## §4  Move 7: Sanity Tests on Small Fields

Run all checks on n=3 (GF(8)) first where we know the answers. -/

/-- Complete sanity check for a power map on a small field. -/
def sanityCheck (n d : Nat) : String :=
  let f := powerMap n d
  let apn := checkAPN n f
  let ab := isAB n f
  let parseval := parsevalTotal n f
  let fibreOK := if apn then verifyAPNFibres n f else true
  let cls := classifyExponent n d
  let canon := frobeniusCanonical n d
  let orbitSize := (frobeniusOrbit n d).length
  s!"x^{d} on GF(2^{n}):" ++
  s!"\n  APN={apn}, AB={ab}, Parseval={parseval}, Fibres={fibreOK}" ++
  s!"\n  Class={cls}, Canon={canon}, OrbitSize={orbitSize}"

/-! ## §5  Move 10: Explicit Invariant Checklist

Separation of concerns: domain / map / spectrum. -/

/-- Complete invariant record for a function. -/
structure InvariantRecord where
  n : Nat
  exponent : Nat
  -- Domain invariants
  fieldSize : Nat
  -- Map invariants
  isPermutation : Bool
  diffUniformity : Nat
  isAPN : Bool
  -- Spectrum invariants
  isAB : Bool
  walshSqValues : List Nat
  parsevalOK : Bool
  -- Equivalence invariants
  frobClass : String
  frobCanonical : Nat
  orbitSize : Nat
  deriving Repr

/-- Compute the full invariant record for x^d on GF(2^n). -/
def computeInvariants (n d : Nat) : InvariantRecord :=
  let f := powerMap n d
  let q := gf2nCard n
  -- Check if f is a permutation: gcd(d, 2^n - 1) = 1
  let isPerm := Nat.gcd d (q - 1) = 1
  let du := differentialUniformity n f
  let apn := du ≤ 2
  let ab := isAB n f
  let spectrum := walshSpectrumSq n f
  let parseval := parsevalTotal n f
  let cls := classifyExponent n d
  let canon := frobeniusCanonical n d
  let orb := (frobeniusOrbit n d).length
  { n := n, exponent := d, fieldSize := q,
    isPermutation := isPerm, diffUniformity := du,
    isAPN := apn, isAB := ab,
    walshSqValues := spectrum.mergeSort (· ≤ ·),
    parsevalOK := parseval,
    frobClass := cls, frobCanonical := canon,
    orbitSize := orb }

/-! ## §6  Move 9: Systematic Falsification via Spot Checks

Quick checks that should fail for non-APN functions. -/

/-- Find a specific (a, b) pair witnessing non-APN, if it exists. -/
def findAPNViolation (n : Nat) (f : Nat → Nat) : Option (Nat × Nat × Nat) :=
  let q := gf2nCard n
  let rec goA : Nat → Option (Nat × Nat × Nat)
    | 0 => none
    | a + 1 =>
      let rec goB : Nat → Option (Nat × Nat × Nat)
        | 0 => none
        | b + 1 =>
          let c := diffCount n f (a + 1) b
          if c > 2 then some (a + 1, b, c)
          else goB b
      match goB q with
      | some v => some v
      | none => goA a
  goA (q - 1)

/-- Find a Walsh coefficient violating the AB condition.
    Returns (a, b, W(a,b), W²) where W² ∉ {0, 2^{n+1}}. -/
def findABViolation (n : Nat) (f : Nat → Nat) : Option (Nat × Nat × Int × Nat) :=
  if n % 2 = 0 then some (0, 0, 0, 0)  -- AB requires odd n
  else
    let q := gf2nCard n
    let target := 2 ^ (n + 1)
    let rec goA : Nat → Option (Nat × Nat × Int × Nat)
      | 0 => none
      | a + 1 =>
        let rec goB : Nat → Option (Nat × Nat × Int × Nat)
          | 0 => none
          | b + 1 =>
            if a = 0 && b = 0 then goB b
            else
              let w := walshCoeff n f a b
              let wsq := (w * w).toNat
              if wsq = 0 || wsq = target then goB b
              else some (a, b, w, wsq)
        match goB q with
        | some v => some v
        | none => goA a
    goA q

/-! ## §7  Comprehensive Test Runs -/

-- Move 7: Sanity on GF(2³)
#eval sanityCheck 3 3    -- Gold, should be APN+AB
#eval sanityCheck 3 5    -- x⁵ on GF(8)

-- Move 7: Sanity on GF(2⁵)
#eval sanityCheck 5 3    -- Gold
#eval sanityCheck 5 7    -- Welch
#eval sanityCheck 5 13   -- Kasami
#eval sanityCheck 5 6    -- AB10 candidate

-- Move 8: Parseval verification
#eval parsevalTotal 3 (powerMap 3 3)   -- should be true
#eval parsevalTotal 5 (powerMap 5 3)   -- should be true

-- Move 1: Full Walsh report on GF(2³)
#eval fullWalshReport 3 (powerMap 3 3)

-- Move 2: Full differential spectrum
#eval fullDiffSpectrum 3 (powerMap 3 3)  -- should show only (0, k₁) and (2, k₂)

-- Move 2: Verify APN fibres are exactly {0, 2}
#eval verifyAPNFibres 3 (powerMap 3 3)  -- true
#eval verifyAPNFibres 5 (powerMap 5 3)  -- true

-- Move 9: Falsification of x² (known non-APN)
#eval findAPNViolation 5 (powerMap 5 2)  -- should find a violation

-- Move 9: Falsification of inverse as non-AB
#eval findABViolation 5 (powerMap 5 30)  -- should find Walsh violation

-- Move 10: Full invariant records
#eval computeInvariants 3 3   -- Gold on GF(8)
#eval computeInvariants 5 3   -- Gold on GF(32)
#eval computeInvariants 5 6   -- AB10 on GF(32)
#eval computeInvariants 5 13  -- Kasami on GF(32)

-- Move 6: Canonical APN scan on GF(2⁵)
#eval canonicalAPNScan 5

-- Move 3: Frobenius orbit check
#eval isFrobeniusEquiv 5 3 6  -- should be true

-- Move 4: CCZ invariant comparison on GF(2³) (small enough)
#eval sameCCZInvariants 3 (powerMap 3 3) (powerMap 3 5)
