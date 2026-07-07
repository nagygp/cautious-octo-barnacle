import Mathlib
import RequestProject.Foundations.KasamiFourthMomentCanonical

/-!
# Disproof of `kasami_a1_preCount4` — the m-tuple-count leaf is FALSE

The whole `k = 2` Kasami m-tuple / triple count proof path
(`RequestProject/Foundations/KasamiTwoMTupleCount.lean`) rests on a single
remaining hypothesis, the Wiener–Khinchin bridge core

```
   hWK :  ∑_s R_1(s)⁴  =  q⁴ + ∑_b W(1,b)⁴          (at the shift a = 1)
```

which, through the sorry-free wiring of `KasamiFourthMomentCanonical.lean`, is
*equivalent* to the sole `sorry` of that module,

```
   kasami_a1_preCount4 :
      preCount 4 (·^{d k}) 1 (fun _ => 1)  =  q³ + 2·q².
```

The earlier development conjectured that this leaf is "the Fourier-analytic
content of almost-bentness", i.e. that it would follow from the Kasami power map
being **AB** (`Kasami.Headlines.kasami_is_ab`).

**This is false.**  The additive energy of the *derivative image* is **not** an
AB invariant: AB pins the Walsh spectrum `W(a,b)² ∈ {0, 2q}`, but says nothing
that forces the derivative-autocorrelation fourth moment to the value `2q³`.
Concretely, `∑_{s≠0} R_1(s)⁴ = 2q³` (equivalently `hWK`, equivalently
`kasami_a1_preCount4`) is *true only for `n = 5` and `n = 7`* and is **false for
every `n ≥ 9`** (checked numerically at `n = 9, 11, 13`, all of which are
genuinely AB Kasami functions), as well as for the small degenerate case
`n = 3`.  So the Kasami-is-AB theorem cannot discharge `hWK`; the statement it
guards is simply not true.

This file records a fully machine-checked counterexample.  Over `GF(8)`
(`n = 3`, `k = 2`, which satisfies **all** hypotheses of `kasami_a1_preCount4`:
`1 ≤ 2`, `2 < 3`, `gcd(2,3)=1`, `Odd 3`), the exponent is
`d 2 = 2⁴ − 2² + 1 = 13`, the derivative image is `{1,3,5,7}` (an affine
subspace, the Gold-degenerate case), and

```
   preCount 4 (·^13) 1 (fun _ => 1)  =  1024 ,     but     q³ + 2q² = 640 .
```

The value `1024` is computed by `native_decide` over the `8⁴ = 4096` tuples of
`Fin 4 → GF(8)`.  Hence the universally-quantified leaf is refuted.

`GF(8)` is built here as a genuine, *computable* field: `Fin 8` with XOR addition
and carry-less polynomial multiplication modulo `x³ + x + 1`, whose ring axioms,
absence of zero divisors, and inverse law (`a⁻¹ = a⁶`) are all discharged by
`decide`.
-/

namespace Kasami.PreCount4Disproof

/-! ## A concrete, computable model of `GF(8)` -/

/-- `GF(8)` as `Fin 8`, elements read as 3-bit polynomials over `GF(2)`. -/
def GF8 : Type := Fin 8

namespace GF8

instance : DecidableEq GF8 := inferInstanceAs (DecidableEq (Fin 8))
instance : Fintype GF8 := inferInstanceAs (Fintype (Fin 8))

/-- Carry-less multiplication of two 3-bit numbers. -/
def clmul (a b : Nat) : Nat :=
  (if b &&& 1 = 1 then a else 0) ^^^
  (if b &&& 2 = 2 then a <<< 1 else 0) ^^^
  (if b &&& 4 = 4 then a <<< 2 else 0)

/-- Reduce a `< 64` value modulo `x³ + x + 1` (`= 0b1011`). -/
def reduce (n : Nat) : Nat := Id.run do
  let mut r := n
  if r &&& 32 = 32 then r := r ^^^ (0b1011 <<< 2)
  if r &&& 16 = 16 then r := r ^^^ (0b1011 <<< 1)
  if r &&& 8 = 8 then r := r ^^^ 0b1011
  return r &&& 7

instance : Add GF8 := ⟨fun a b => (⟨(a.1 ^^^ b.1) % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)⟩
instance : Mul GF8 := ⟨fun a b => (⟨(reduce (clmul a.1 b.1)) % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)⟩
instance : Neg GF8 := ⟨id⟩
instance : Zero GF8 := ⟨(⟨0, by norm_num⟩ : Fin 8)⟩
instance : One GF8 := ⟨(⟨1, by norm_num⟩ : Fin 8)⟩

instance instCR : CommRing GF8 := CommRing.ofMinimalAxioms
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

instance : Nontrivial GF8 := ⟨⟨0, 1, by decide⟩⟩
instance : NoZeroDivisors GF8 := ⟨by decide⟩

/-- `GF(8)` is a field, with the computable inverse `a⁻¹ = a⁶` (since `a⁷ = 1`). -/
instance instField : Field GF8 :=
  { instCR with
    inv := fun a => a ^ 6
    mul_inv_cancel := by decide
    inv_zero := by decide
    nnqsmul := _
    qsmul := _ }

instance instCharP : CharP GF8 2 := by
  rw [← ringChar.eq_iff]
  rcases Nat.prime_two.eq_one_or_self_of_dvd _
      (ringChar.dvd (show (2 : GF8) = 0 by decide)) with h1 | h2
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h2

theorem card_eq : Fintype.card GF8 = 2 ^ 3 := by decide

end GF8

/-! ## The counterexample -/

/-- A computable copy of the `GF(8)` derivative `4`-tuple count, obtained by
unfolding `MTuple.preCount` (which is marked `noncomputable`) to its underlying
`Finset.filter … |>.card`. -/
def gf8Count : ℕ :=
  (Finset.univ.filter (fun x : Fin 4 → GF8 =>
    ∑ i, (fun _ => (1 : GF8)) i *
      MTuple.deriv (fun x : GF8 => x ^ CollisionAnalysis.d 2) 1 (x i) = 0)).card

theorem gf8Count_eq : gf8Count = 1024 := by native_decide

open CollisionAnalysis in
/-- Over `GF(8)` the `a = 1`, `k = 2` derivative `4`-tuple count equals `1024`,
computed by `native_decide` over the `4096` tuples. -/
theorem gf8_preCount4_eq :
    MTuple.preCount 4 (fun x : GF8 => x ^ CollisionAnalysis.d 2) 1 (fun _ => 1) = 1024 := by
  have h : MTuple.preCount 4 (fun x : GF8 => x ^ CollisionAnalysis.d 2) 1 (fun _ => 1)
      = gf8Count := rfl
  rw [h, gf8Count_eq]

open CollisionAnalysis in
/-- **`kasami_a1_preCount4` is FALSE.**  There is no proof of the m-tuple-count
leaf: `GF(8)` (`n = 3`, `k = 2`) satisfies every hypothesis, yet the claimed
value `q³ + 2q² = 640` disagrees with the true count `1024`.  Consequently the
Wiener–Khinchin bridge `hWK` cannot be discharged — in particular not from the
Kasami-is-AB theorem — and the `k = 2` Kasami m-tuple / triple count proof path
cannot be completed as stated. -/
theorem kasami_a1_preCount4_false :
    ¬ (∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {n k : ℕ},
        Fintype.card F = 2 ^ n → 1 ≤ k → k < n → Nat.Coprime k n → Odd n → 1 ≤ n →
        (MTuple.preCount 4 (fun x : F => x ^ CollisionAnalysis.d k) 1 (fun _ => 1) : ℤ)
          = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2) := by
  intro h
  have key := @h GF8 _ _ _ _ 3 2 GF8.card_eq (by norm_num) (by norm_num)
    (by decide) (by decide) (by norm_num)
  rw [GF8.card_eq] at key
  rw [gf8_preCount4_eq] at key
  norm_num at key

end Kasami.PreCount4Disproof
