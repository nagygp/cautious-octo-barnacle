/-
  # Computable GF(2^n) Arithmetic

  A decidable, `#eval`-friendly representation of GF(2^n) using natural
  numbers as bit-vectors with:
  - Addition = bitwise XOR
  - Multiplication = carry-less polynomial multiplication mod an irreducible polynomial

  This module provides the computational backbone for AB/APN detection.
-/

/-! ## §1  Irreducible Polynomials over GF(2)

We store one Conway/irreducible polynomial per small degree n.
The polynomial is encoded as a natural number whose binary representation
gives the coefficients: bit i is the coefficient of x^i.
E.g., x^3 + x + 1 = 0b1011 = 11.
-/

/-- Irreducible polynomial over GF(2) of degree n, encoded as a Nat.
    Returns 0 if n is not in our table. -/
def irredPoly : Nat → Nat
  | 1 => 0b11          -- x + 1
  | 2 => 0b111         -- x² + x + 1
  | 3 => 0b1011        -- x³ + x + 1
  | 4 => 0b10011       -- x⁴ + x + 1
  | 5 => 0b100101      -- x⁵ + x² + 1
  | 6 => 0b1000011     -- x⁶ + x + 1
  | 7 => 0b10000011    -- x⁷ + x + 1
  | 8 => 0b100011011   -- x⁸ + x⁴ + x³ + x + 1
  | 9 => 0b1000010001  -- x⁹ + x⁴ + 1
  | 10 => 0b10000001001 -- x¹⁰ + x³ + 1
  | 11 => 0b100000000101 -- x¹¹ + x² + 1
  | 12 => 0b1000001010011 -- x¹² + x⁶ + x⁴ + x + 1
  | _ => 0

/-! ## §2  GF(2^n) Arithmetic -/

/-- The number of elements in GF(2^n). -/
def gf2nCard (n : Nat) : Nat := 2 ^ n

/-- Addition in GF(2^n) is bitwise XOR. -/
@[inline] def gf2nAdd (a b : Nat) : Nat := a ^^^ b

/-- Bit-length of a natural number (position of highest set bit + 1). -/
partial def bitLen (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + bitLen (n / 2)

/-- Reduce a polynomial (as Nat) modulo the irreducible polynomial of degree n. -/
partial def gf2nReduce (n : Nat) (a : Nat) : Nat :=
  let p := irredPoly n
  if p = 0 then a % (2 ^ n)
  else
    let bx := bitLen a
    if bx ≤ n then a
    else gf2nReduce n (a ^^^ (p <<< (bx - n - 1)))

/-- Carry-less polynomial multiply (no reduction). -/
partial def clmul (x y : Nat) : Nat :=
  if y = 0 then 0
  else
    let rest := clmul (x <<< 1) (y / 2)
    if y % 2 = 1 then rest ^^^ x else rest

/-- Multiplication in GF(2^n). -/
@[inline] def gf2nMul (n : Nat) (a b : Nat) : Nat :=
  gf2nReduce n (clmul a b)

/-- Exponentiation in GF(2^n) by repeated squaring. -/
partial def gf2nPow (n : Nat) (base exp : Nat) : Nat :=
  if exp = 0 then 1
  else if exp = 1 then gf2nReduce n base
  else
    let half := gf2nPow n (gf2nMul n base base) (exp / 2)
    if exp % 2 = 1 then gf2nMul n base half else half

/-! ## §3  Sanity Checks -/

-- GF(2^3): 8 elements
#eval gf2nCard 3  -- 8

-- In GF(2^3): 3 + 5 = 6 (XOR)
#eval gf2nAdd 3 5  -- 6

-- In GF(2^3): 3 * 5 mod (x³+x+1)
#eval gf2nMul 3 3 5

-- x^7 = 1 in GF(2^3) for any nonzero x (Fermat's little theorem)
#eval gf2nPow 3 3 7  -- should be 1
#eval gf2nPow 3 5 7  -- should be 1
#eval gf2nPow 3 6 7  -- should be 1

-- In GF(2^5): x^31 = 1 for nonzero x
#eval gf2nPow 5 7 31   -- should be 1
#eval gf2nPow 5 13 31  -- should be 1

/-! ## §4  The Absolute Trace: GF(2^n) → GF(2)

Tr(x) = x + x² + x^{2²} + ... + x^{2^{n-1}} (in GF(2^n))

Since the result is in GF(2), the output is 0 or 1.
-/

/-- The absolute trace Tr : GF(2^n) → GF(2), returned as 0 or 1. -/
def gf2nTrace (n : Nat) (x : Nat) : Nat :=
  let rec go : Nat → Nat → Nat → Nat
    | 0, acc, _ => acc
    | fuel + 1, acc, cur =>
      go fuel (gf2nAdd acc cur) (gf2nMul n cur cur)
  (go n 0 x) % 2

-- Trace tests
#eval gf2nTrace 3 1  -- Tr(1) = 1 + 1 + 1 = 1 (n=3 odd)
#eval gf2nTrace 3 0  -- Tr(0) = 0
#eval gf2nTrace 5 1  -- Tr(1) = 1 (n=5 odd)

/-! ## §5  Inner Product via Trace

For a, x ∈ GF(2^n), the "inner product" is Tr(a·x) ∈ GF(2).
This is used to define characters χ_a(x) = (-1)^{Tr(ax)}.
-/

/-- Tr(a·x) in GF(2^n), returned as 0 or 1. -/
@[inline] def gf2nInner (n : Nat) (a x : Nat) : Nat :=
  gf2nTrace n (gf2nMul n a x)
