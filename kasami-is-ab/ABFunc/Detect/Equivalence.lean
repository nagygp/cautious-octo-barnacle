/-
  # Frobenius Conjugacy Classes & Equivalence Reduction

  Implements stabilizing moves 3, 4, 6, 8 from the invariant checklist:
  - **Move 3**: Basis invariance via Frobenius orbits (polynomial ↔ normal basis)
  - **Move 4**: CCZ/EA equivalence class reductions
  - **Move 6**: Comparison against known monomial classification tables
  - **Move 8**: Frobenius-orbit normalization of exponents

  ## Key Insight
  Two power maps x^d and x^{d'} over GF(2^n) are EA-equivalent iff
  d' is in the Frobenius orbit of d:
    d' ∈ {d · 2^k mod (2^n - 1) : k = 0, …, n-1}
  This reduces the classification space by a factor of ~n.
-/
import Detect.GF2n
import Detect.APNDetector
import Detect.ABDetector

/-! ## §1  Frobenius Orbits (Move 8: Exponent Normalization)

The Frobenius automorphism x ↦ x² acts on power-map exponents by
d ↦ 2d mod (2^n - 1). Two exponents in the same orbit give
EA-equivalent functions. We normalize by taking the minimum. -/

/-- Compute the full Frobenius orbit of exponent d over GF(2^n).
    orbit(d) = {d, 2d, 4d, …, 2^{n-1}·d} mod (2^n - 1). -/
def frobeniusOrbit (n d : Nat) : List Nat :=
  let q := 2 ^ n - 1
  if q = 0 then [d]
  else
    let rec go : Nat → Nat → List Nat
      | 0, _ => []
      | fuel + 1, cur =>
        cur :: go fuel ((cur * 2) % q)
    (go n (d % q)).eraseDups

/-- The canonical (minimum) representative of a Frobenius orbit. -/
def frobeniusCanonical (n d : Nat) : Nat :=
  let orb := frobeniusOrbit n d
  orb.foldl min (orb.head!)

/-- Two exponents are Frobenius-equivalent (EA-equivalent as power maps). -/
def isFrobeniusEquiv (n d₁ d₂ : Nat) : Bool :=
  frobeniusCanonical n d₁ = frobeniusCanonical n d₂

/-! ## §2  Known APN/AB Classification Tables (Move 6)

Known infinite families of APN power functions over GF(2^n):
1. Gold:    d = 2^k + 1,         gcd(k, n) = 1
2. Kasami:  d = 2^{2k} - 2^k + 1, gcd(k, n) = 1
3. Welch:   d = 2^t + 3,         n = 2t + 1
4. Niho:    d = 2^t + 2^{t/2} - 1 (t even) or 2^t + 2^{(3t+1)/2} - 1 (t odd), n = 2t+1
5. Inverse: d = 2^{2t} - 1,      n = 2t + 1
6. Dobbertin: d = 2^{4k} + 2^{3k} + 2^{2k} + 2^k - 1, n = 5k
-/

/-- Check if d is a Gold exponent for GF(2^n). -/
def isGoldExp (n d : Nat) : Bool :=
  (List.range n).any fun k =>
    k ≥ 1 && Nat.gcd k n = 1 && isFrobeniusEquiv n d (2 ^ k + 1)

/-- Check if d is a Kasami exponent for GF(2^n). -/
def isKasamiExp (n d : Nat) : Bool :=
  (List.range n).any fun k =>
    k ≥ 1 && Nat.gcd k n = 1 &&
    (2 ^ (2 * k) ≥ 2 ^ k + 1) &&  -- avoid underflow
    isFrobeniusEquiv n d (2 ^ (2 * k) - 2 ^ k + 1)

/-- Check if d is a Welch exponent for GF(2^n). -/
def isWelchExp (n d : Nat) : Bool :=
  if n % 2 = 0 then false
  else
    let t := n / 2
    isFrobeniusEquiv n d (2 ^ t + 3)

/-- Check if d is an Inverse exponent for GF(2^n). -/
def isInverseExp (n d : Nat) : Bool :=
  isFrobeniusEquiv n d (2 ^ n - 2)  -- x^{q-2} = x^{-1}

/-- Classify a power map exponent into known families. -/
def classifyExponent (n d : Nat) : String :=
  if isGoldExp n d then "Gold"
  else if isKasamiExp n d then "Kasami"
  else if isWelchExp n d then "Welch"
  else if isInverseExp n d then "Inverse"
  else "Unknown/New"

/-! ## §3  Reduced APN/AB Scan (Move 8 Applied)

Scan only canonical representatives — reduces work by factor ~n. -/

/-- Collect all canonical APN exponents over GF(2^n),
    deduplicated by Frobenius orbit. -/
def canonicalAPNScan (n : Nat) : List (Nat × String × Bool × Bool) :=
  let q := 2 ^ n - 1
  let allExps := List.range q |>.map (· + 1)
  -- Deduplicate by Frobenius canonical form
  let canonicals := allExps.foldl (fun acc d =>
    let c := frobeniusCanonical n d
    if acc.any (fun (d', _, _, _) => frobeniusCanonical n d' = c) then acc
    else
      let f := powerMap n d
      let apn := checkAPN n f
      if apn then
        let ab := isAB n f
        let cls := classifyExponent n d
        acc ++ [(d, cls, apn, ab)]
      else acc
  ) []
  canonicals

/-! ## §4  CCZ-Equivalence Invariants (Move 4)

CCZ-equivalence preserves:
- Differential uniformity (δ)
- Walsh spectrum (as a multiset of squared values)
- Extended Walsh spectrum

We compute these invariants to test equivalence. -/

/-- Compute the sorted Walsh squared spectrum (multiset of |W(a,b)|²). -/
def walshSqMultiset (n : Nat) (f : Nat → Nat) : List Nat :=
  let q := gf2nCard n
  let vals := (List.range q).flatMap fun a =>
    (List.range q).filterMap fun b =>
      if a = 0 && b = 0 then none
      else
        let w := walshCoeff n f a b
        some (w * w).toNat
  vals.mergeSort (· ≤ ·)

/-- Check if two functions have the same CCZ invariants
    (differential uniformity + Walsh spectrum). -/
def sameCCZInvariants (n : Nat) (f g : Nat → Nat) : Bool :=
  let du_f := differentialUniformity n f
  let du_g := differentialUniformity n g
  du_f = du_g && (walshSqMultiset n f == walshSqMultiset n g)

/-! ## §5  Tests & Verification -/

-- Frobenius orbits on GF(2^5): 2^5 - 1 = 31
#eval frobeniusOrbit 5 3    -- Gold x³: orbit of 3
#eval frobeniusOrbit 5 7    -- Welch x⁷: orbit of 7
#eval frobeniusOrbit 5 13   -- Kasami x¹³: orbit of 13

-- Canonical representatives
#eval frobeniusCanonical 5 3   -- min of orbit(3)
#eval frobeniusCanonical 5 6   -- orbit(6) = orbit(3·2)?
#eval frobeniusCanonical 5 12  -- orbit(12) = orbit(3·4)?

-- Classification
#eval classifyExponent 5 3    -- "Gold"
#eval classifyExponent 5 13   -- "Kasami"
#eval classifyExponent 5 7    -- "Welch"
#eval classifyExponent 5 30   -- "Inverse"
#eval classifyExponent 5 6    -- "Gold" (Frobenius of x³) or new?

-- Frobenius equivalence: x³ ~ x⁶ ~ x¹² ~ x²⁴ ~ x¹⁷ on GF(2⁵)?
#eval isFrobeniusEquiv 5 3 6   -- true if 6 = 3·2 mod 31
#eval isFrobeniusEquiv 5 3 12  -- true if 12 = 3·4 mod 31

-- Full canonical APN scan on GF(2⁵)
-- Shows only orbit representatives, classified by family
#eval canonicalAPNScan 5

-- CCZ invariant check: x³ vs x⁶ should have same invariants
-- (they're Frobenius-equivalent, hence CCZ-equivalent)
-- Note: walshSqMultiset depends on walshCoeff from ABDetector;
-- this is a heavy computation for GF(2⁵)
-- #eval sameCCZInvariants 5 (powerMap 5 3) (powerMap 5 6)
