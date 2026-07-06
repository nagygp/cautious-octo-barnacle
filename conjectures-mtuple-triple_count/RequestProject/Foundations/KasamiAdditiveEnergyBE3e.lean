import RequestProject.Foundations.KasamiAdditiveEnergyBE3b
import Mathlib

/-!
# Foundations, Layer BE3.3.1 — the off-diagonal energy as the second-derivative collision moment

This module supplies the **structural reduction requested for direction (B)**: it
feeds the second-order-derivative collision counts directly into the
`offDiagEnergy` reduction of BE3.1/BE3.2, turning input (B)'s remaining content
into an *exact* statement about the **second-difference collision distribution**
of the derivative map.  The remaining (open) content is then exactly the
per-value *multiplicity* computation — the AB-vs-APN distinction — which is what
the deep core BE3.3 must evaluate.

## The mathematical content

Recall (BE3.1) `offDiagEnergy S = ∑_{z≠0} r_S(z)²` and (BE3.2) the 4-to-1 lift
`4·r_S(z) = derivPairCount f a z`, where `derivPairCount f a z` counts the ordered
argument pairs `(x,y)` with `Δf_a x + Δf_a y = z` and, after the substitution
`y = x+w`, equals the total fiber count of the **second-order derivative**
`Δ_w Δf_a (x) = Δf_a(x+w) + Δf_a x` (`derivPairCount_eq_secondDeriv`):

```
   derivPairCount f a z = ∑_w #{x : Δf_a(x+w) + Δf_a x = z}.
```

Squaring the 4-to-1 lift gives the **exact** identity

```
   16 · offDiagEnergy(Im Δf_a) = ∑_{z≠0} derivPairCount(f,a,z)²
```

(`sixteen_mul_offDiagEnergy_eq_derivPairCount_sq`), so input (B)'s off-diagonal
value `16·offDiagEnergy = q³ − 2q²` (BE3.1) is **equivalent** to the
second-derivative collision moment

```
   ∑_{z≠0} derivPairCount(f,a,z)² = q³ − 2q²
```

(`offDiagEnergy_value_iff_derivPairCount_sq`), and the full additive-energy value
`16·E(Im Δf_a) = q³ + 2q²` reduces to the same collision-moment statement
(`additiveEnergy_value_iff_derivPairCount_sq`).  This pins the remaining deep core
of input (B) **entirely** on the second-difference collision distribution
`derivPairCount(f,a,·)` — the per-value multiplicities of the second-order
derivative — exactly the AB-spectrum input flagged as the open content.

## What is established (sorry-free)

* `sixteen_mul_offDiagEnergy_eq_derivPairCount_sq` — the exact identity
  `16·offDiagEnergy = ∑_{z≠0} derivPairCount²` (APN `f`, `a ≠ 0`).
* `offDiagEnergy_value_iff_derivPairCount_sq` — input (B)'s off-diagonal value
  rephrased as the collision moment `∑_{z≠0} derivPairCount² = q³ − 2q²`.
* `additiveEnergy_value_iff_derivPairCount_sq` — the full additive-energy value
  rephrased likewise (chaining BE3.1's `additiveEnergy_value_iff_offDiagEnergy`).
* `derivPairCount_eq_secondDeriv_sum` — the collision count as the second-order
  derivative fiber sum (re-export of BE3.2 for downstream multiplicity work).

## Scope

This layer is sorry-free; it is the project-internal **reduction** of input (B)
to the second-derivative collision moment, built entirely on BE3.1/BE3.2 (needs no
theory absent from Mathlib).  The *evaluation* of that moment — the exact
per-value multiplicities of the second-order derivative (the AB three-valued
spectrum, which fails for APN-but-not-AB functions) — is the open deep core,
deliberately neither axiomatized nor `sorry`-ed.

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (additive energy, representation
function); Carlet, Ch. 6 (APN/AB functions, second-order derivatives);
Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The exact off-diagonal energy / collision-moment identity -/

/-
**The off-diagonal energy is the second-derivative collision moment.**  For an
APN `f` and `a ≠ 0`, squaring the 4-to-1 lift `4·r_S(z) = derivPairCount f a z`
gives the exact identity

  `16·offDiagEnergy(Im Δf_a) = ∑_{z≠0} derivPairCount(f,a,z)²`.
-/
theorem sixteen_mul_offDiagEnergy_eq_derivPairCount_sq (f : F → F) (hf : IsAPN f)
    (a : F) (ha : a ≠ 0) :
    16 * offDiagEnergy (derivImage f a)
      = ∑ z ∈ univ.erase (0 : F), (derivPairCount f a z) ^ 2 := by
  rw [offDiagEnergy, Finset.mul_sum];
  exact Finset.sum_congr rfl fun x hx => by rw [ ← four_mul_reprCount_eq_derivPairCount f hf a ha x ] ; ring;

/-! ## 2. Input (B)'s off-diagonal value as the collision moment -/

/-
**Input (B)'s off-diagonal value, rephrased as the collision moment.**  For an
APN `f` and `a ≠ 0` (writing `q = |F|`), the off-diagonal value
`16·offDiagEnergy = q³ − 2q²` is equivalent to the second-derivative collision
moment `∑_{z≠0} derivPairCount(f,a,z)² = q³ − 2q²`.
-/
theorem offDiagEnergy_value_iff_derivPairCount_sq (f : F → F) (hf : IsAPN f)
    (a : F) (ha : a ≠ 0) :
    (16 * (offDiagEnergy (derivImage f a) : ℤ)
        = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2)
      ↔ ((∑ z ∈ univ.erase (0 : F), (derivPairCount f a z) ^ 2 : ℤ)
          = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2) := by
  have := Vanish.Foundations.sixteen_mul_offDiagEnergy_eq_derivPairCount_sq f hf a ha;
  norm_cast;
  rw [ this ]

/-! ## 3. The full additive-energy value as the collision moment -/

/-
**The additive-energy value, rephrased as the collision moment.**  For an APN
`f`, `a ≠ 0`, and `|F| = 2ⁿ`, the AB additive-energy value
`16·E(Im Δf_a) = q³ + 2q²` is equivalent to the second-derivative collision moment
`∑_{z≠0} derivPairCount(f,a,z)² = q³ − 2q²`.  This pins the remaining deep core of
input (B) entirely on the second-difference collision distribution.
-/
theorem additiveEnergy_value_iff_derivPairCount_sq (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    (16 * (additiveEnergy (derivImage f a) : ℤ)
        = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2)
      ↔ ((∑ z ∈ univ.erase (0 : F), (derivPairCount f a z) ^ 2 : ℤ)
          = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2) := by
  convert Vanish.Foundations.additiveEnergy_value_iff_offDiagEnergy n hn hcard f hf a ha |> Iff.trans <| Vanish.Foundations.offDiagEnergy_value_iff_derivPairCount_sq f hf a ha using 1

/-! ## 4. The collision count as the second-order derivative fiber sum -/

/-- **The collision count is the second-order derivative fiber sum** (re-export of
BE3.2 `derivPairCount_eq_secondDeriv` for downstream multiplicity work):
`derivPairCount f a z = ∑_w #{x : Δf_a(x+w) + Δf_a x = z}`.  The open content of
BE3.3 is the per-value distribution of these second-order-derivative fibers. -/
theorem derivPairCount_eq_secondDeriv_sum (f : F → F) (a z : F) :
    derivPairCount f a z
      = ∑ w : F, (univ.filter (fun x : F => deriv f a (x + w) + deriv f a x = z)).card :=
  derivPairCount_eq_secondDeriv f a z

end Vanish.Foundations