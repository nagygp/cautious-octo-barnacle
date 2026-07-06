import Mathlib

/-!
# Transcription — a verified DISPROOF of the single-monomial collapse leaf

The leaf `TraceMonomial.kasami_monomial_collapse_one` (and the leaf it feeds,
`TraceMonomial.kasami_autocorr_eq_monomial_addCharSum`) asserts that the Kasami
second-derivative sign-character sum collapses to a **single monomial** additive
character sum:

```
∑_y χ(c₀·((y+1)^{d k} + y^{d k})) = ∑_x χ(c·x^e)   for some c ≠ 0, e ≥ 1,
```

with `d k = 2^{2k} − 2^k + 1` and `χ = (−1)^{Tr}` the `±1`-valued sign character.
**This statement is false.**  This module gives a machine-checked counterexample
over the concrete field `GF(2⁵)`, for *genuine* Kasami parameters `n = 5`, `k = 2`
(so `d k = 13`, `gcd(k,n)=1`, `n` odd, `1 ≤ k < n`), and `c₀ = 1` (which is realized
by `s = a = 1` in the autocorrelation, both nonzero).

## The obstruction

Over `GF(2⁵)` the multiplicative group is cyclic of prime order `31`.  Hence for any
exponent `e ≥ 1` and coefficient `c ≠ 0` the monomial map `x ↦ x^e` is either a
bijection of the field (when `31 ∤ e`, giving `∑_x χ(c·x^e) = ∑_z χ(z) = 0`) or is
constant on the units (when `31 ∣ e`, giving `1 + 31·χ(c) ∈ {32, −30}`).  So **every**
single-monomial sign-character sum over `GF(2⁵)` lies in `{0, −30, 32}`.

But the Kasami second-derivative sum for `d = 13`, `c₀ = 1` equals `8`
(`= 2^{(n+1)/2}`, the almost-bent Walsh value), and `8 ∉ {0, −30, 32}`.  Therefore
no single monomial character sum can equal it: the collapse fails.

The correct (and *green*, already proved) form of this rung is
`GaussSumBridge.kasami_autocorr_eq_gaussSum_sum`, which expresses the
cross-correlation as a **sum of several** Teichmüller Gauss sums
`∑_j (χ₁ʲ)⁻¹(c)·g(χ₁ʲ, χ)` — an integer that need not be any single monomial or any
single Gauss sum (a nonzero Gauss sum over `GF(2⁵)` has modulus `√32`, so `±` one
Gauss sum can never equal an integer of size `8` either).

Everything here is `native_decide`-checked over an explicit computable model of
`GF(2⁵)` (bitmask arithmetic modulo the primitive pentanomial `x⁵ + x² + 1`), so it
depends only on `Lean.ofReduceBool` beyond the standard axioms.

## Model

`GF(2⁵)` is modelled as `Nat` bitmasks `0..31`, with addition `XOR`, multiplication
the carry-less product reduced modulo `x⁵ + x² + 1` (`= 0b100101 = 37`), trace
`Tr(x) = x + x² + x⁴ + x⁸ + x¹⁶`, and sign character `χ(x) = (−1)^{Tr x}`.  The
model is a genuine field: every nonzero element satisfies `x³¹ = 1` and `x ↦ 2^i`
enumerates all units (both facts are themselves `native_decide`-checkable), so the
value-set argument above is valid.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe.MonomialCollapseDisproof

/-- Reduce a bitmask modulo the primitive pentanomial `x⁵ + x² + 1` (`= 37`). -/
def redu (a : Nat) : Nat := Id.run do
  let mut x := a
  for i in (List.range 6).reverse do
    if x >>> (5 + i) &&& 1 == 1 then x := x ^^^ (37 <<< i)
  return x

/-- Field multiplication in `GF(2⁵)`: carry-less product, then reduce. -/
def gmul (a b : Nat) : Nat := Id.run do
  let mut res := 0
  for i in List.range 5 do
    if b >>> i &&& 1 == 1 then res := res ^^^ (a <<< i)
  return redu res

/-- Field exponentiation `a^n` in `GF(2⁵)`. -/
def gpow (a : Nat) : Nat → Nat
  | 0 => 1
  | (n + 1) => gmul a (gpow a n)

/-- Absolute trace `Tr(x) = x + x² + x⁴ + x⁸ + x¹⁶ ∈ {0,1}` (as a bitmask). -/
def gtr (x : Nat) : Nat := Id.run do
  let mut s := 0
  let mut y := x
  for _ in List.range 5 do
    s := s ^^^ y
    y := gmul y y
  return s

/-- The `±1`-valued sign character `χ(x) = (−1)^{Tr x}`. -/
def chi (x : Nat) : Int := if gtr x == 0 then 1 else -1

/-- The Kasami second-derivative sign-character sum
`∑_y χ(c₀·((y+1)^d + y^d))` over `GF(2⁵)` (here `y + 1 = y XOR 1`). -/
def derivSum (d c0 : Nat) : Int := Id.run do
  let mut s : Int := 0
  for y in List.range 32 do
    s := s + chi (gmul c0 ((gpow (y ^^^ 1) d) ^^^ (gpow y d)))
  return s

/-- A single-monomial sign-character sum `∑_x χ(c·x^e)` over `GF(2⁵)`. -/
def monoSum (e c : Nat) : Int := Id.run do
  let mut s : Int := 0
  for x in List.range 32 do
    s := s + chi (gmul c (gpow x e))
  return s

/-- **Model sanity: `GF(2⁵)` is a field.**  Every nonzero element satisfies
`x³¹ = 1`. -/
theorem gpow_card_sub_one : ∀ x, 1 ≤ x → x < 32 → gpow x 31 = 1 := by native_decide

/-- **Model sanity: `2` is a primitive element**, so the units are exactly the
powers `2^i`, `0 ≤ i < 31` (they are pairwise distinct). -/
theorem two_is_primitive :
    (List.range 31 |>.map (fun i => gpow 2 i)).Nodup := by native_decide

/-- **The Kasami sum value.**  For genuine Kasami parameters `n = 5`, `k = 2`
(`d = 13`) and `c₀ = 1`, the second-derivative sign-character sum equals `8`. -/
theorem derivSum_value : derivSum 13 1 = 8 := by native_decide

/-- **Every single-monomial sum lies in `{0, −30, 32}`.**  For all `e, c` with
`1 ≤ e, c < 32` (which, since `x^e` depends only on `e mod 31` on units and `c`
ranges over all units, covers *all* nonzero monomial sums), the value
`∑_x χ(c·x^e)` is one of `0`, `−30`, `32`. -/
theorem monoSum_value_set :
    ∀ e < 32, ∀ c < 32, 1 ≤ e → 1 ≤ c →
      monoSum e c = 0 ∨ monoSum e c = -30 ∨ monoSum e c = 32 := by native_decide

/-- **The single-monomial collapse fails (verified counterexample).**  Over
`GF(2⁵)` with `d = 13` and `c₀ = 1`, no single-monomial sign-character sum
`∑_x χ(c·x^e)` (any `c ≠ 0`, any `e ≥ 1`) equals the Kasami second-derivative sum
`∑_y χ((y+1)¹³ + y¹³) = 8`.  Hence the leaf `kasami_monomial_collapse_one` is false
as stated. -/
theorem monomial_collapse_fails :
    ∀ e < 32, ∀ c < 32, 1 ≤ e → 1 ≤ c → monoSum e c ≠ derivSum 13 1 := by
  native_decide

end Vanish.Foundations.FirstPrinciples.Transcribe.MonomialCollapseDisproof
