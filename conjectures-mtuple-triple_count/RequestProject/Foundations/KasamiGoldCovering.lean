import RequestProject.Foundations.KasamiEq12Substitution
import RequestProject.Foundations.KasamiEvenMCubing
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-2: the substitution covering

This module is the **second from-scratch foundational module of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), building on DD-fp-1
(`KasamiEq12Substitution.lean`) and the even-`m` GF(4) substrate
(`KasamiEvenMCubing.lean`).

Equation (12) realizes the Kasami cross-correlation as a GF(4)-coset average of
Gold Gauss sums *via the substitution* `x = u^{2^k+1}`.  For that averaging to
have the `1/3` weight, the substitution map

```
   u ↦ u^{2^k+1}    on   GF(2ⁿ)ˣ
```

must be **3-to-1**, with fibres the cosets of `GF(4)ˣ` (the cube roots of unity).
The number of preimages of any value in the image equals the size of the kernel
`{u : u^{2^k+1} = 1}`, which in the cyclic group `GF(2ⁿ)ˣ` of order `q − 1` is

```
   #{u : u^{2^k+1} = 1} = gcd(2^k+1, q−1).
```

For `n` even and `gcd(k,n) = 1` this gcd is `3` (one has
`gcd(2^k+1, 2^n−1) = 2^{gcd(k,n)}+1 = 3` since `n` is even), and the kernel is
exactly the group of cube roots of unity `GF(4)ˣ` — the even-`m` substrate of
`KasamiEvenMCubing.lean`.  The covering condition is carried here as the
hypothesis `gcd(2^k+1, q−1) = 3`.

This module establishes, from Mathlib's cyclic-group / `pow_gcd_card_eq_one_iff`
machinery and the project's `card_cubeRootsOne`:

* the **kernel identification** `{u : u^{2^k+1} = 1} = {u : u^3 = 1}`
  (`goldPow_torsion_eq_cubeRoots`) — the fibres are GF(4)ˣ-cosets;
* the **kernel size** `#{u : u^{2^k+1} = 1} = 3` (`goldPow_torsion_card`);
* the **3-to-1 covering**: every value in the image of `u ↦ u^{2^k+1}` has
  exactly three preimages (`goldPow_fiber_card`).

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite-group algebra and
introduces no axioms; the GF(4)-coset *character-sum* derivation of equation (12)
itself (`h12`, core DD-fp-3) and the rank evaluation (`hrank`, core DD-fp-5)
remain the deep frontier.

## Sources

Dillon–Dobbertin, *New cyclic difference sets with Singer parameters*
(FFA 2004), §7 (eq. (12)); Lidl–Niederreiter, *Finite Fields*, Ch. 6.
-/

namespace Vanish.Foundations

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The kernel of the substitution map is the cube roots of unity -/

/-
**Kernel identification.**  When `gcd(2^k+1, q−1) = 3`, the kernel of the
substitution map `u ↦ u^{2^k+1}` on `GF(2ⁿ)ˣ` coincides with the cube roots of
unity (`GF(4)ˣ`), because in a finite group `u^{2^k+1} = 1 ↔ u^{gcd(2^k+1, |G|)} = 1`.
-/
theorem goldPow_torsion_eq_cubeRoots {k : ℕ}
    (hgcd : Nat.gcd (2 ^ k + 1) (Fintype.card Fˣ) = 3) :
    (univ.filter (fun g : Fˣ => g ^ (2 ^ k + 1) = 1))
      = (univ.filter (fun g : Fˣ => g ^ 3 = 1)) := by
  ext g
  simp [hgcd];
  rw [ ← hgcd, pow_gcd_card_eq_one_iff ]

/-
**Kernel size.**  For `n` even and `gcd(2^k+1, q−1) = 3`, the kernel of the
substitution map has exactly three elements — the order of `GF(4)ˣ`.
-/
theorem goldPow_torsion_card {n k : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n)
    (hgcd : Nat.gcd (2 ^ k + 1) (Fintype.card Fˣ) = 3) :
    (univ.filter (fun g : Fˣ => g ^ (2 ^ k + 1) = 1)).card = 3 := by
  convert Vanish.Foundations.card_cubeRootsOne hcard hn using 1;
  convert congr_arg Finset.card ( Vanish.Foundations.goldPow_torsion_eq_cubeRoots hgcd ) using 1

/-! ## 2. The substitution map is a 3-to-1 covering -/

/-
**The substitution map is 3-to-1.**  For `n` even and `gcd(2^k+1, q−1) = 3`,
every value in the image of `u ↦ u^{2^k+1}` on `GF(2ⁿ)ˣ` has exactly three
preimages.  This is the covering structure (fibres = GF(4)ˣ-cosets) behind the
`1/3` weight in the GF(4)-coset average of equation (12).
-/
theorem goldPow_fiber_card {n k : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n)
    (hgcd : Nat.gcd (2 ^ k + 1) (Fintype.card Fˣ) = 3)
    (y : Fˣ) (hy : y ∈ Set.range (fun g : Fˣ => g ^ (2 ^ k + 1))) :
    (univ.filter (fun g : Fˣ => g ^ (2 ^ k + 1) = y)).card = 3 := by
  obtain ⟨ x, rfl ⟩ := hy;
  convert goldPow_torsion_card hcard hn hgcd using 1;
  convert MonoidHom.card_fiber_eq_of_mem_range ( powMonoidHom ( 2 ^ k + 1 ) : Fˣ →* Fˣ ) _ _ using 1;
  · exact ⟨ x, rfl ⟩;
  · exact ⟨ 1, by simp +decide ⟩

end Vanish.Foundations