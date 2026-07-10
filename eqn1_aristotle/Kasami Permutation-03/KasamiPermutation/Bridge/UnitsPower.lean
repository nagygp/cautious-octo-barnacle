import Mathlib
import KasamiPermutation.Core.KasamiAPN

/-!
# A units-functor bridge for power maps, and an alternative proof of the Gold permutation

## The bridge philosophy

Several headline results of this development are ultimately statements that a
*power map* `x ↦ xᵃ` is a bijection of a finite field `F = 𝔽_{2ⁿ}`.  The
project's foundational layer (`FiniteFieldCharTwo.pow_field_bijective`, in
`FiniteField/ExpArith.lean`) proves this from scratch by inverting `a` modulo
`|F| − 1` and hand-checking the zero/nonzero cases.

Here we give the same fact a **structural, Caramello-style proof by bridge**.  The
relevant "two theories" are:

* the **field with a power map** `(F, x ↦ xᵃ)`, and
* the **cyclic group with a power map** `(Fˣ, u ↦ uᵃ)`.

They are connected by the **units functor** `F ↦ Fˣ` — a *non-faithful* map that
forgets the single point `0`.  The one invariant that has to survive the passage
is a purely numerical one: the coprimality of the exponent `a` with the group
order `|Fˣ| = |F| − 1`.  On the group side the bijectivity of the power map is a
one-liner from Mathlib's cyclic-group machinery
(`powCoprime` / `Nat.Coprime.pow_left_bijective`); the bridge then transports it
back across the forgotten point `0`.

This isolates the actual content (a group-theoretic invariant) from the
field-specific bookkeeping, and lets us re-derive the **Gold permutation**
headline (`KasamiPerm.MCMtoAPN.gold_permutation`) through the bridge.

## Contents

* `units_pow_bijective` — the group side: `u ↦ uᵃ` is a bijection of `Fˣ` when
  `gcd(|F| − 1, a) = 1` (Mathlib `powCoprime`, transported along
  `Fintype.card_units`).
* `pow_field_bijective_via_units` — the bridge: the same coprimality makes
  `x ↦ xᵃ` a bijection of `F` (for `a > 0`), obtained by transporting
  `units_pow_bijective` across the forgotten `0`.
* `gold_permutation_via_units` — an alternative proof of the Gold-permutation
  headline `y ↦ y^{2ᵏ+1}`, routed through the bridge and the arithmetic
  invariant `KasamiAPN.gold_coprime`.
-/

namespace KasamiPerm.FieldBridge

open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

/-- **The group side of the bridge.**  On the multiplicative group `Fˣ` of a
finite field, the power map `u ↦ uᵃ` is a bijection whenever the exponent `a` is
coprime to the group order `|Fˣ| = |F| − 1`.

This is Mathlib's cyclic-group power bijection `powCoprime` transported along
`Fintype.card_units`; no field-specific reasoning is used. -/
lemma units_pow_bijective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a) :
    Function.Bijective (fun u : Fˣ => u ^ a) := by
  have hcard : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  exact (powCoprime (n := a) (by rw [hcard]; exact ha)).bijective

/-- **The bridge.**  For a finite field `F`, the power map `x ↦ xᵃ` is a bijection
of `F` whenever `a > 0` and `a` is coprime to `|F| − 1`.

The proof transports the group-side bijection `units_pow_bijective` across the
single point `0` forgotten by the units functor: away from `0` the map is the
units power map (injective by the bridge invariant), and `0` is its own unique
`a`-th root because `a > 0`.  Finiteness upgrades injectivity to bijectivity.

This is a structural alternative to `FiniteFieldCharTwo.pow_field_bijective`. -/
lemma pow_field_bijective_via_units {a : ℕ}
    (ha : Nat.Coprime (Fintype.card F - 1) a) (ha_pos : 0 < a) :
    Function.Bijective (fun x : F => x ^ a) := by
  have hb := units_pow_bijective (F := F) ha
  have hinj : Function.Injective (fun x : F => x ^ a) := by
    intro x y hxy
    simp only at hxy
    rcases eq_or_ne x 0 with hx | hx
    · rcases eq_or_ne y 0 with hy | hy
      · rw [hx, hy]
      · exact absurd hxy.symm (by rw [hx, zero_pow ha_pos.ne']; exact pow_ne_zero a hy)
    · rcases eq_or_ne y 0 with hy | hy
      · exact absurd hxy (by rw [hy, zero_pow ha_pos.ne']; exact pow_ne_zero a hx)
      · have hu : Units.mk0 x hx ^ a = Units.mk0 y hy ^ a := by
          apply Units.ext; push_cast; simpa using hxy
        simpa using congrArg (Units.val) (hb.injective hu)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- **The Gold permutation, via the bridge.**

An alternative proof of the headline `KasamiPerm.MCMtoAPN.gold_permutation`:
`y ↦ y^{2ᵏ+1}` is a bijection of `𝔽_{2ⁿ}` when `0 < k`, `n` is odd and
`gcd(k, n) = 1`.

The only content beyond the generic power bridge `pow_field_bijective_via_units`
is the numerical invariant `gcd(2ᵏ + 1, 2ⁿ − 1) = 1` (`KasamiAPN.gold_coprime`),
which is exactly the coprimality the bridge consumes. -/
theorem gold_permutation_via_units [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hn_pos : 0 < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    Function.Bijective (fun y : F => y ^ (2 ^ k + 1)) := by
  apply pow_field_bijective_via_units
  · rw [hn]; exact (KasamiAPN.gold_coprime hk hn_pos hcop hn_odd).symm
  · positivity

end KasamiPerm.FieldBridge
