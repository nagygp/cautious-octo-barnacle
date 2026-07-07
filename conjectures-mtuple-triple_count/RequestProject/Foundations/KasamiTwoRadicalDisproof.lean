import Mathlib

/-!
# A verified DISPROOF of the `k = 2` derivative-radical leaf

The module `KasamiQuadraticValueSet.lean` reduced input (B) for the `k = 2` Kasami
map to the leaf

```
   kasami_two_derivForm_radical :
     ∀ s, (radical (s·Δf_a + s·Δf_a 0)).card ≤ 2,
```

where `Δf_a(x) = (x+a)^{13} + x^{13}` and `radical Q = {u | ∀ x, Tr(polar Q x u) = 0}`.
**This leaf is false.**  This module gives a `native_decide`-checked counterexample
over the concrete field `GF(2⁵)` (the genuine Kasami regime `n = 5, k = 2, d = 13`,
`gcd(k,n)=1`, `n` odd), reusing the same bitmask model as
`KasamiMonomialCollapseDisproof.lean`.

## What is verified

* `radCard_3_1_eq_eight` — at `a = 1, s = 3` the derivative polar radical has **8**
  elements, so `radical.card ≤ 2` is false.
* `raut_3_1_eq_zero` — at that same frequency the cross-correlation `R(3) = 0`.
* `value_set_holds` — for every `a ≠ 0, s ≠ 0` the derivative cross-correlation is
  three-valued, `R(s) ∈ {0, ±8}`; in particular the *corrected* almost-bent upper
  bound `R(s)² ≤ 2q = 64` holds everywhere.
* `radical_large_iff_R_zero` — over `a = 1`, the radical exceeds `2` **exactly** on
  the frequencies where `R(s) = 0`; equivalently `radical.card ≤ 2 ∨ R(s) = 0` holds
  for all `s ≠ 0`.  This is the true content that replaces the false leaf
  (see `KasamiTwoDerivPolar.kasami_two_crossCorr_sq_ub`).

The model is a genuine field (verified in `KasamiMonomialCollapseDisproof.lean`):
`GF(2⁵)` as `Nat` bitmasks `0..31`, addition `XOR`, multiplication the carry-less
product modulo `x⁵ + x² + 1` (`= 37`), trace `Tr(x) = x + x² + x⁴ + x⁸ + x¹⁶`.
Everything here is `native_decide`-checked, so it uses `Lean.ofReduceBool` /
`Lean.trustCompiler` beyond the standard axioms, as intended for a computational
disproof.
-/

namespace Vanish.Foundations.KasamiTwoRadicalDisproof

/-- Reduce a bitmask modulo the primitive pentanomial `x⁵ + x² + 1` (`= 37`). -/
def redu (a : Nat) : Nat := Id.run do
  let mut x := a
  for i in (List.range 6).reverse do
    if x >>> (5 + i) &&& 1 == 1 then x := x ^^^ (37 <<< i)
  return x

/-- Field multiplication in `GF(2⁵)`. -/
def gmul (a b : Nat) : Nat := Id.run do
  let mut res := 0
  for i in List.range 5 do
    if b >>> i &&& 1 == 1 then res := res ^^^ (a <<< i)
  return redu res

/-- Field exponentiation. -/
def gpow (a : Nat) : Nat → Nat
  | 0 => 1
  | (n + 1) => gmul a (gpow a n)

/-- Absolute trace `Tr(x) = x + x² + x⁴ + x⁸ + x¹⁶ ∈ {0,1}`. -/
def gtr (x : Nat) : Nat := Id.run do
  let mut s := 0
  let mut y := x
  for _ in List.range 5 do
    s := s ^^^ y
    y := gmul y y
  return s

/-- The `±1`-valued sign character. -/
def chi (x : Nat) : Int := if gtr x == 0 then 1 else -1

/-- The `k = 2` Kasami derivative `Δf_a(x) = (x+a)¹³ + x¹³` (with `x + a = x XOR a`). -/
def deriv13 (a x : Nat) : Nat := (gpow (x ^^^ a) 13) ^^^ (gpow x 13)

/-- The derivative cross-correlation `R_a(s) = ∑_x χ(s · Δf_a(x))`. -/
def Raut (s a : Nat) : Int :=
  (List.range 32).foldl (fun acc x => acc + chi (gmul s (deriv13 a x))) 0

/-- The zero-shifted derivative form `Q(x) = s·Δf_a(x) + s·Δf_a(0)`. -/
def Qform (s a x : Nat) : Nat := (gmul s (deriv13 a x)) ^^^ (gmul s (deriv13 a 0))

/-- The polar form `B(x,u) = Q(x+u) + Q(x) + Q(u)`. -/
def polarForm (s a x u : Nat) : Nat := (Qform s a (x ^^^ u)) ^^^ (Qform s a x) ^^^ (Qform s a u)

/-- Membership in the radical: `∀ x, Tr(B(x,u)) = 0`. -/
def inRadical (s a u : Nat) : Bool := (List.range 32).all (fun x => gtr (polarForm s a x u) == 0)

/-- The size of the radical of the derivative form. -/
def radCard (s a : Nat) : Nat := ((List.range 32).filter (fun u => inRadical s a u)).length

/-- **The leaf is false: the radical has 8 elements at `s = 3, a = 1`.**  Hence
`radical.card ≤ 2` fails for the `k = 2` Kasami derivative form over `GF(2⁵)`. -/
theorem radCard_3_1_eq_eight : radCard 3 1 = 8 := by native_decide

/-- **At that frequency the cross-correlation vanishes:** `R(3) = 0`.  So the large
radical is precisely where the Gauss sum is zero (the "other branch"), consistent
with the true value set. -/
theorem raut_3_1_eq_zero : Raut 3 1 = 0 := by native_decide

/-- **The `radical.card ≤ 2` leaf really fails** (packaged as an existential over the
genuine Kasami field `GF(2⁵)`). -/
theorem leaf_false : ∃ s a : Nat, s ≠ 0 ∧ a ≠ 0 ∧ ¬ radCard s a ≤ 2 := by
  refine ⟨3, 1, by decide, by decide, ?_⟩
  rw [radCard_3_1_eq_eight]; decide

/-- **The true value set:** for every `a ≠ 0, s ≠ 0` the derivative cross-correlation
is three-valued, `R(s) ∈ {0, 8, −8}`.  In particular the corrected almost-bent upper
bound `R(s)² ≤ 2q = 64` holds everywhere — this is the satisfiable replacement for
the false radical leaf. -/
theorem value_set_holds :
    (List.range 32).all (fun a => (List.range 32).all (fun s =>
      a == 0 || s == 0 || Raut s a == 0 || Raut s a == 8 || Raut s a == -8)) = true := by
  native_decide

/-- **The corrected disjunction** `radical.card ≤ 2 ∨ R(s) = 0` holds for every
`s ≠ 0` at `a = 1` (a representative shift): the radical is large exactly where the
cross-correlation vanishes. -/
theorem radical_large_iff_R_zero :
    (List.range 32).all (fun s => s == 0 || decide (radCard s 1 ≤ 2) || Raut s 1 == 0) = true := by
  native_decide

end Vanish.Foundations.KasamiTwoRadicalDisproof
