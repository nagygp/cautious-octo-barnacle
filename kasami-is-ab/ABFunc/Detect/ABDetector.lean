/-
  # Computable AB (Almost Bent) Detector

  A function f : GF(2^n) → GF(2^n) is **Almost Bent (AB)** if its
  Walsh transform takes values in {0, ±2^{(n+1)/2}}.

  The Walsh transform is:
    W_f(a, b) = Σ_{x ∈ GF(2^n)} (-1)^{Tr(a·x + b·f(x))}

  For a function to be AB, we need n to be odd, and every Walsh
  coefficient W_f(a,b) with (a,b) ≠ (0,0) must satisfy
    W_f(a,b) ∈ {0, ±2^{(n+1)/2}}.

  This module provides a fully computable AB detector via `#eval`.
-/
import Detect.GF2n
import Detect.APNDetector

/-! ## §1  Walsh Transform Computation -/

/-- Compute the Walsh coefficient W_f(a, b) for f : GF(2^n) → GF(2^n).
    Returns a signed integer:
      W_f(a,b) = Σ_x (-1)^{Tr(a·x + b·f(x))}
    where + is XOR (addition in GF(2^n)). -/
def walshCoeff (n : Nat) (f : Nat → Nat) (a b : Nat) : Int :=
  let q := gf2nCard n
  let rec go : Nat → Int → Int
    | 0, acc => acc
    | x + 1, acc =>
      -- Compute Tr(a·x + b·f(x)) ∈ {0, 1}
      let ax := gf2nMul n a x
      let bfx := gf2nMul n b (f x)
      let inner := gf2nTrace n (gf2nAdd ax bfx)
      -- (-1)^inner = 1 if inner = 0, -1 if inner = 1
      let sign : Int := if inner = 0 then 1 else -1
      go x (acc + sign)
  go q 0

/-! ## §2  Walsh Spectrum (set of all |W_f(a,b)|²) -/

/-- Compute the set of distinct |W_f(a,b)|² values for (a,b) ≠ (0,0).
    For an AB function over GF(2^n) with n odd, this should be {0, 2^{n+1}}. -/
def walshSpectrumSq (n : Nat) (f : Nat → Nat) : List Nat :=
  let q := gf2nCard n
  let rec goB : Nat → Nat → List Nat → List Nat
    | 0, _, acc => acc
    | b + 1, a, acc =>
      if a = 0 && b = 0 then goB b a acc  -- skip (0,0) but b here is b+1-1=b
      else
        let w := walshCoeff n f a b
        let wsq := (w * w).toNat
        let acc' := if acc.contains wsq then acc else wsq :: acc
        goB b a acc'
  let rec goA : Nat → List Nat → List Nat
    | 0, acc => acc
    | a + 1, acc =>
      -- For a+1 (which ranges from q-1 down to 0), iterate over all b
      -- But skip (0,0)
      let acc' := goInner n f (a) q acc
      goA a acc'
  goA q []
where
  goInner (n : Nat) (f : Nat → Nat) (a : Nat) : Nat → List Nat → List Nat
    | 0, acc => acc
    | b + 1, acc =>
      if a = 0 && b + 1 = 0 then goInner n f a b acc  -- unreachable for b+1=0
      else if a = 0 && b = 0 then
        -- This is the pair (0, 0) since we pass a directly and b ranges from q-1 to 0
        -- Actually a=0, b+1 means b ranges from 0 to q-1, and b+1-1=b
        -- Let me simplify: we skip (a=0, b=0)
        goInner n f a b acc
      else
        let w := walshCoeff n f a b
        let wsq := (w * w).toNat
        let acc' := if acc.contains wsq then acc else wsq :: acc
        goInner n f a b acc'

/-- Check if f is AB (Almost Bent) over GF(2^n).
    Requirements:
    1. n must be odd
    2. Every Walsh coefficient W_f(a,b) for (a,b) ≠ (0,0) must be
       in {0, ±2^{(n+1)/2}}, equivalently |W|² ∈ {0, 2^{n+1}}. -/
def isAB (n : Nat) (f : Nat → Nat) : Bool :=
  if n % 2 = 0 then false  -- AB requires odd n
  else
    let target := 2 ^ (n + 1)  -- the nonzero |W|² value
    let q := gf2nCard n
    let rec goA : Nat → Bool
      | 0 => true
      | a + 1 =>
        let rec goB : Nat → Bool
          | 0 => true
          | b + 1 =>
            if a = 0 && b = 0 then goB 0  -- skip (0,0), but this is base case
            else
              let w := walshCoeff n f (a) b
              let wsq := (w * w).toNat
              if wsq = 0 || wsq = target then goB b
              else false
        if goB q then goA a else false
    goA q

/-- Full AB report for a power map x^d over GF(2^n). -/
def abReport (n d : Nat) : String :=
  let f := powerMap n d
  let apn := checkAPN n f
  let ab := isAB n f
  let spectrum := walshSpectrumSq n f
  let target := 2 ^ (n + 1)
  s!"GF(2^{n}), f(x) = x^{d}:\n  APN = {apn}\n  AB  = {ab}\n  Walsh |W|² values = {spectrum}\n  Expected AB |W|² = \{0, {target}}"

/-! ## §3  AB Verification of Known Functions -/

-- Gold: x^3 on GF(2^3) — should be AB (n=3 odd)
#eval abReport 3 3

-- Gold: x^3 on GF(2^5) — should be AB (n=5 odd)
#eval abReport 5 3

-- Kasami: x^13 on GF(2^5) — should be AB
-- d = 2^4 - 2^2 + 1 = 13
#eval abReport 5 13

-- Welch: x^7 on GF(2^5) — d = 2^2 + 3 = 7
#eval abReport 5 7

-- x^5 on GF(2^5) — d = 5 (Welch with t=1, n=3)
#eval abReport 5 5

-- Non-AB: x^2 (linear)
#eval abReport 5 2

-- Inverse: x^30 on GF(2^5) — APN but NOT AB
-- (inverse is APN for all n, but AB only for n odd and... actually inverse is not AB)
#eval abReport 5 30

/-! ## §4  Test New AB Conjectures from the Project -/

-- Conjecture AB1: x^{2^k + 2^{⌊k/2⌋} + 1}
-- k=1, n=5: d = 2 + 1 + 1 = 4
#eval abReport 5 4    -- ConjectureAB1 with k=1

-- k=2, n=5: d = 4 + 2 + 1 = 7
#eval abReport 5 7    -- ConjectureAB1 with k=2 (this is Welch!)

-- Conjecture AB3: x^{2^k + 3}
-- k=2, n=7: d = 7
#eval isPowerAPN 7 7

-- Conjecture AB6: Double-Gold x^{(2^j+1)(2^k+1)}
-- j=1, k=2, n=7: d = 3*5 = 15
#eval isPowerAPN 7 15

-- Conjecture AB10: x^6 on GF(2^5)
#eval abReport 5 6

/-! ## §5  Batch AB Scan -/

/-- Scan all power exponents d from 1 to 2^n-2 and report which are AB. -/
def abScan (n : Nat) : List (Nat × Bool × Bool) :=
  let q := gf2nCard n
  List.range (q - 1) |>.map (fun d =>
    let d' := d + 1
    let f := powerMap n d'
    (d', checkAPN n f, isAB n f))
  |>.filter (fun (_, apn, _) => apn)  -- only show APN functions

-- All APN power maps over GF(2^5), with AB status
-- Format: (exponent, isAPN, isAB)
#eval abScan 5

-- All APN power maps over GF(2^7)
-- (this may be slow — GF(2^7) has 128 elements)
-- #eval abScan 7  -- uncomment to run (takes ~minutes)
