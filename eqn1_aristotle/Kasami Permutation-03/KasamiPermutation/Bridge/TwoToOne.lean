import Mathlib

/-!
# The Artin–Schreier map is two-to-one, via the fiber–kernel bridge

## The structural heart of the APN property

Corollary 2 of Dobbertin (1999) — that Kasami power functions are APN — reduces,
after the key-identity factorisation, to the fact that the Artin–Schreier map
```
   ℘ : x ↦ x² + x
```
is **exactly two-to-one** in characteristic `2` (its fibres are the pairs
`{x, x+1}`).  The project proves the general Frobenius-shift form
`t ↦ t^{2ᵏ} + t` (`KasamiPerm.Headlines.frob_shift_two_to_one`) by an explicit
computation that also needs finiteness and `gcd(k, n) = 1`.

This module gives the base map `℘` a **structural, Caramello-style proof by
bridge**.  The relevant abstraction is that `℘` is a *homomorphism of additive
groups*: the two "theories" are

* the **field with the map `℘`**, and
* the **additive group `(F, +)` with the homomorphism `℘`**,

connected by the forgetful functor `Field ⤳ AddGroup`.  Once `℘` is seen as an
`AddMonoidHom`, Mathlib's `AddMonoidHom.fiberEquivKer` gives *for free* that every
fibre of `℘` is a coset of the kernel, hence equinumerous with it.  The only
remaining content is the tiny invariant `ker ℘ = {0, 1}` (a two-element set), and
two-to-one-ness drops out.

A pleasant consequence of routing through the coset bridge: the argument needs
**no finiteness of `F`** — every fibre of `℘` has exactly two elements in *any*
field of characteristic `2`, finite or not.

## Contents

* `artinSchreierHom` — `℘(x) = x² + x` bundled as an `F →+ F`.
* `artinSchreierHom_ker` — the invariant `ker ℘ = {0, 1}`.
* `artinSchreier_fiber_card` / `artinSchreier_two_to_one` — every fibre has
  exactly two elements (`ncard = 2`), the two-to-one heart of Corollary 2.
* `artinSchreier_fiber_eq` — the fibre over `℘ x` is exactly `{x, x+1}`.
-/

namespace KasamiPerm.FieldBridge

open scoped Classical

variable {F : Type*} [Field F] [CharP F 2]

/-- The **Artin–Schreier map** `℘(x) = x² + x`, bundled as an additive group
homomorphism.  Additivity is the char-2 freshman's dream `(x+y)² = x² + y²`. -/
def artinSchreierHom (F : Type*) [Field F] [CharP F 2] : F →+ F where
  toFun x := x ^ 2 + x
  map_zero' := by ring
  map_add' x y := by
    have h : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by simpa using add_pow_char x y (p := 2)
    rw [h]; ring

@[simp] lemma artinSchreierHom_apply (x : F) : artinSchreierHom F x = x ^ 2 + x := rfl

/-- **The kernel invariant.**  The kernel of `℘` is the two-element prime field
`{0, 1}`: `x² + x = x·(x+1) = 0` forces `x = 0` or `x = 1`. -/
lemma artinSchreierHom_ker : ((artinSchreierHom F).ker : Set F) = {0, 1} := by
  ext y
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, artinSchreierHom_apply,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hfac : y * (y + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h0 | h1
    · exact Or.inl h0
    · right; linear_combination h1 - (CharTwo.add_self_eq_zero (1 : F))
  · rintro (rfl | rfl) <;> simp [CharTwo.add_self_eq_zero]

/-- The kernel of `℘` has exactly two elements. -/
lemma artinSchreierHom_ker_card : Nat.card ((artinSchreierHom F).ker) = 2 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, artinSchreierHom_ker,
    Set.ncard_pair (zero_ne_one)]

/-- **The two-to-one heart of Corollary 2, via the fiber–kernel bridge.**

Every fibre of the Artin–Schreier map `℘(x) = x² + x` has exactly two elements.
The fibre over `℘ x` is a coset of the kernel by `AddMonoidHom.fiberEquivKer`,
hence equinumerous with `ker ℘ = {0, 1}`.  No finiteness of `F` is required. -/
theorem artinSchreier_fiber_card (x : F) :
    {y : F | y ^ 2 + y = x ^ 2 + x}.ncard = 2 := by
  have hset : {y : F | y ^ 2 + y = x ^ 2 + x}
      = (artinSchreierHom F) ⁻¹' {(artinSchreierHom F) x} := by
    ext y; simp
  rw [hset, ← Nat.card_coe_set_eq,
    Nat.card_congr ((artinSchreierHom F).fiberEquivKer x), artinSchreierHom_ker_card]

/-- **The fibres are the pairs `{x, x+1}`.**  The concrete two-to-one description
matching `KasamiPerm.Headlines.frob_shift_two_to_one` (at `k = 1`). -/
theorem artinSchreier_fiber_eq (x : F) :
    {y : F | y ^ 2 + y = x ^ 2 + x} = {x, x + 1} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hmem : y ^ 2 + y = x ^ 2 + x ↔ y - x ∈ (artinSchreierHom F).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]; simp
  have hset : (y - x ∈ (artinSchreierHom F).ker) ↔ (y - x = 0 ∨ y - x = 1) := by
    rw [← SetLike.mem_coe, artinSchreierHom_ker]; simp
  rw [hmem, hset, sub_eq_zero, sub_eq_iff_eq_add, add_comm 1 x]

/-- The Artin–Schreier map is two-to-one (`KasamiPerm.Headlines.TwoToOne`-style),
finiteness-free. -/
theorem artinSchreier_two_to_one :
    ∀ x : F, {y : F | y ^ 2 + y = x ^ 2 + x}.ncard = 2 :=
  artinSchreier_fiber_card

end KasamiPerm.FieldBridge
