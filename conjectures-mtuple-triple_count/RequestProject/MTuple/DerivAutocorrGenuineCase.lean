import Mathlib

/-!
# The derivative autocorrelation of a genuine AB Kasami map is *not* three-valued

The earlier `k = 2` Kasami m-tuple count reduced to a Wiener–Khinchin bridge
`hWK`, equivalently the derivative-autocorrelation fourth-moment value

  `∑_{s ≠ 0} R_a(s)⁴ = 2·q³`  ⟺  `preCount 4 (·^{d 2}) 1 (fun _ => 1) = q³ + 2q²`,

which was hoped to be a consequence of the Kasami map being almost bent (AB).

A previous refutation used only `GF(8)` (`n = 3`), where the Kasami exponent
`d 2 = 13 ≡ 6 (mod 7)` *degenerates* to the inverse map and the derivative image
is an affine subspace — arguably not a "genuine" Kasami case.  This module gives a
**genuine, machine-checked** counterexample over `GF(2⁹)`, where `x ↦ x¹³` is a
bona-fide, non-degenerate almost-bent Kasami map, and shows the bridge value is
nevertheless wrong there.

All facts below are proved by `native_decide` over an explicit, self-contained
computable model of `GF(2ⁿ)` (`Nat` with XOR addition and carry-less
multiplication modulo an irreducible polynomial `p`), independent of the project's
noncomputable field/character API:

* `gf512_is_field`     — `p = x⁹+x⁴+1` (`= 529`) is irreducible, so the model is a
  genuine field (every nonzero `a` satisfies `a^{511} = 1`);
* `kasami9_is_apn`     — `x ↦ x¹³` is APN over `GF(2⁹)` (every derivative fibre has
  `≤ 2` points);
* `kasami9_is_ab`      — a component `Tr(x¹³)` is almost bent: its Walsh spectrum
  is three-valued `{0, ±2⁵}` (`W² ∈ {0, 1024}`);
* `kasami9_deriv_takes_2A` — yet the *derivative autocorrelation* `R_1(s)` attains
  the value `2·2⁵ = 64`, i.e. it is **not** confined to `{0, ±2⁵}`;
* `kasami9_deriv_fourth_moment_ne` — consequently the fourth-moment/`preCount`
  bridge value fails: the derivative additive energy is `134987776`, not the
  claimed `q³ + 2q² = 134742016` (equivalently `∑_{s≠0} R_1(s)⁴ ≠ 2q³`).

**Conclusion.** Almost-bentness (a property of the two-variable *Walsh* spectrum)
does **not** force the one-variable *derivative autocorrelation* to be
three-valued; the `2q³` bridge is genuinely false for AB Kasami maps with
`n ≥ 9`, so the count cannot be completed via that route.  The honest, true
replacement is the computable criterion in
`RequestProject/MTuple/VanishCriterion.lean`.
-/

namespace MTuple.DerivAutocorrGenuineCase

/-! ## A self-contained computable model of `GF(2ⁿ)` -/

/-- Reduce `x` modulo the degree-`n` polynomial `p` (with top bit at position `n`). -/
def gfreduce (p n : Nat) (x : Nat) : Nat := Id.run do
  let mut r := x
  for i in List.range (n - 1) do
    let bit := 2 * n - 2 - i
    if r &&& (1 <<< bit) ≠ 0 then r := r ^^^ (p <<< (bit - n))
  return r

/-- Carry-less (polynomial) multiplication over `GF(2)`. -/
def clmul (a b : Nat) : Nat := Id.run do
  let mut r := 0
  for i in List.range 32 do
    if b &&& (1 <<< i) ≠ 0 then r := r ^^^ (a <<< i)
  return r

/-- Field multiplication in the model `GF(2ⁿ) = ℕ / (p)`. -/
def gfmul (p n a b : Nat) : Nat := gfreduce p n (clmul a b)

/-- Field exponentiation `a^e` by square-and-multiply. -/
def gfpow (p n a e : Nat) : Nat := Id.run do
  let mut r := 1; let mut base := a; let mut ee := e
  for _ in List.range 30 do
    if ee &&& 1 = 1 then r := gfmul p n r base
    base := gfmul p n base base; ee := ee >>> 1
  return r

/-- Absolute trace `Tr(y) = ∑_{i<n} y^{2^i} ∈ {0,1}`. -/
def gftrace (p n y : Nat) : Nat := Id.run do
  let mut acc := 0; let mut cur := y
  for _ in List.range n do
    acc := acc ^^^ cur; cur := gfmul p n cur cur
  return acc

/-- The irreducible polynomial `x⁹ + x⁴ + 1` used for `GF(2⁹)`. -/
def p9 : Nat := 529

/-! ## The five machine-checked facts over `GF(2⁹)` -/

/-- `p9` gives a genuine field: every nonzero element has multiplicative order
dividing `511`, i.e. `a^{511} = 1`. -/
def fieldCheck (p n : Nat) : Bool := Id.run do
  let q := 1 <<< n
  let mut ok := true
  for a in List.range q do
    if a ≠ 0 then
      if gfpow p n a (q - 1) ≠ 1 then ok := false
  return ok

/-- `x ↦ x^d` is APN: for every nonzero shift `a`, every derivative fibre has
`≤ 2` points. -/
def apnCheck (p n d : Nat) : Bool := Id.run do
  let q := 1 <<< n
  let mut ok := true
  for a in List.range q do
    if a ≠ 0 then
      let mut cnt : Array Nat := Array.replicate q 0
      for x in List.range q do
        let z := (gfpow p n x d) ^^^ (gfpow p n (x ^^^ a) d)
        cnt := cnt.set! z (cnt[z]! + 1)
      for z in List.range q do
        if cnt[z]! > 2 then ok := false
  return ok

/-- The `b = 1` Walsh component is three-valued: `W_1(a)² ∈ {0, 2^{n+1}}` for all
`a` (the AB signature `{0, ±2^{(n+1)/2}}`). -/
def walshThreeValuedCheck (p n d : Nat) : Bool := Id.run do
  let q := 1 <<< n
  let mut F : Array Nat := Array.mkEmpty q
  for x in List.range q do
    F := F.push (gfpow p n x d)
  let mut ok := true
  for a in List.range q do
    let mut acc : Int := 0
    for x in List.range q do
      if gftrace p n ((gfmul p n a x) ^^^ (F[x]!)) = 0 then acc := acc + 1 else acc := acc - 1
    let sq := acc * acc
    if sq ≠ 0 ∧ sq ≠ (2 ^ (n + 1) : Int) then ok := false
  return ok

/-- Whether the derivative autocorrelation `R_1(s) = ∑_x χ(s·Δf_1 x)` attains the
value `v` for some `s` (`f = x^d`, shift `a = 1`). -/
def derivTakesValue (p n d : Nat) (v : Int) : Bool := Id.run do
  let q := 1 <<< n
  let mut D : Array Nat := Array.mkEmpty q
  for x in List.range q do
    D := D.push ((gfpow p n x d) ^^^ (gfpow p n (x ^^^ 1) d))
  let mut found := false
  for s in List.range q do
    let mut acc : Int := 0
    for x in List.range q do
      if gftrace p n (gfmul p n s (D[x]!)) = 0 then acc := acc + 1 else acc := acc - 1
    if acc = v then found := true
  return found

/-- The derivative additive energy `N = #{(x₁,x₂,x₃,x₄) : Δf_1 x₁ + ⋯ + Δf_1 x₄ = 0}`,
computed by convolution.  This equals `q · preCount 4 (·^d) 1 (fun _ => 1)` divided
by nothing — it *is* `preCount 4 (·^d) 1 (fun _ => 1)` and also `q³ · (∑_s R_1(s)⁴)⁻¹`
scaling; concretely `∑_s R_1(s)⁴ = q · N`. -/
def derivFourthCount (p n d : Nat) : Nat := Id.run do
  let q := 1 <<< n
  let mut D : Array Nat := Array.mkEmpty q
  for x in List.range q do
    D := D.push ((gfpow p n x d) ^^^ (gfpow p n (x ^^^ 1) d))
  let mut P : Array Nat := Array.replicate q 0
  for x1 in List.range q do
    for x2 in List.range q do
      P := P.set! (D[x1]! ^^^ D[x2]!) (P[(D[x1]! ^^^ D[x2]!)]! + 1)
  let mut N := 0
  for z in List.range q do N := N + P[z]! * P[z]!
  return N

/-- `GF(2⁹)` (via `x⁹+x⁴+1`) is a genuine field. -/
theorem gf512_is_field : fieldCheck p9 9 = true := by native_decide

/-- `x ↦ x¹³` is APN over `GF(2⁹)`. -/
theorem kasami9_is_apn : apnCheck p9 9 13 = true := by native_decide

/-- `x ↦ x¹³` is almost bent over `GF(2⁹)`: the `Tr(x¹³)` Walsh component is
three-valued, `W² ∈ {0, 2¹⁰}`. -/
theorem kasami9_is_ab : walshThreeValuedCheck p9 9 13 = true := by native_decide

/-- Yet the derivative autocorrelation `R_1(s)` attains the value `2·2⁵ = 64`, so
it is **not** confined to the AB three-valued set `{0, ±2⁵}`. -/
theorem kasami9_deriv_takes_2A : derivTakesValue p9 9 13 64 = true := by native_decide

/-- The derivative additive energy over `GF(2⁹)` is `134987776`. -/
theorem kasami9_deriv_fourth_count : derivFourthCount p9 9 13 = 134987776 := by native_decide

/-- **The `2q³` bridge value is false for a genuine AB Kasami map** (`n = 9`).  The
derivative additive energy (`= preCount 4 (·^{13}) 1 (fun _ => 1)`) is `134987776`,
not the claimed `q³ + 2q² = 134742016`; equivalently `∑_{s≠0} R_1(s)⁴ ≠ 2q³`.
This holds even though `x¹³` is a genuine APN, almost-bent Kasami map here
(`kasami9_is_apn`, `kasami9_is_ab`, `gf512_is_field`). -/
theorem kasami9_deriv_fourth_moment_ne :
    derivFourthCount p9 9 13 ≠ 512 ^ 3 + 2 * 512 ^ 2 := by
  rw [kasami9_deriv_fourth_count]; decide

end MTuple.DerivAutocorrGenuineCase
