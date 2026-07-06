import Mathlib

/-!
# Foundations, Layer 1 — Fourier inversion and solution counting via additive characters

This module is the **most foundational layer** of the "Kasami is Vanish" tower.
It is written to be *self-contained* (it imports only Mathlib), *general* (it
talks about arbitrary finite abelian groups and finite fields, never about
Kasami, APN, or cryptography), and therefore **directly upstreamable** to
Mathlib or submittable as a stand-alone "verification pearl".

Everything here is rooted in two pieces of existing Mathlib machinery:

* `AddChar.sum_apply_eq_ite` — Pontryagin self-duality of a finite abelian
  group: `∑ ψ : AddChar V ℂ, ψ a = if a = 0 then |V| else 0`.
* `AddChar.sum_mulShift` — orthogonality of a *primitive* additive character of
  a finite commutative ring into a domain:
  `∑ x, ψ (x * b) = if b = 0 then |R| else 0`.

From these we build, in increasing specificity, the lemmas that the rest of the
project (and any finite-Fourier solution-counting argument) needs.

## The DAG of this layer

```
  Mathlib.AddChar.sum_apply_eq_ite ─┐
                                    ├─▶ card_solutions_mul_eq_sum_addChar   (Pearl 1)
  Mathlib.AddChar.sum_mulShift  ────┼─▶ card_solutions_mul_eq_field_sum     (Pearl 2)
                                    │        │
            addChar_map_sum ────────┴────────┴─▶ card_linear_tuple          (Pearl 3)
                                                       │
                                       spectrum_split  ┘
                                                       ▼
                                            card_linear_tuple_of_vanish      (Pearl 4)
```

## Design notes (clean-code principles applied)

Following *The Art of Clean Code* (Mayer, 2022) we keep each declaration to a
**single responsibility**, give it a **descriptive, intention-revealing name**,
and **build on existing abstractions rather than re-deriving them** (DRY): the
orthogonality relations are taken verbatim from Mathlib, never re-proved.  The
lemmas are arranged as a small **dependency DAG**, lowest/most-general first, so
that downstream files depend only on the precise statement they need.
-/

namespace Vanish.Foundations

open AddChar Finset BigOperators

/-! ## A bookkeeping lemma: characters turn finite sums into finite products -/

/-- An additive character sends a finite sum to the product of its values.
This is just the `MonoidHom` property of `AddChar`, packaged over `Finset`. -/
theorem addChar_map_sum {A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) {ι : Type*} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, map_add_eq_mul, ih]

/-! ## Pearl 1 — solution counting in an arbitrary finite abelian group

Over `ℂ`, using Pontryagin self-duality, the number of solutions of `g s = 0`
equals the *average over all characters* of the character sum `∑ s, ψ (g s)`.
This is the abstract Fourier-inversion counting identity. -/

/-- **Fourier inversion counting (finite abelian group).** For a finite abelian
group `V` and any `g : S → V` on a finite type `S`,
`|V| · #{s | g s = 0} = ∑_ψ ∑_s ψ (g s)`, the sum ranging over all
complex-valued additive characters of `V`. -/
theorem card_solutions_mul_eq_sum_addChar
    {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    {S : Type*} [Fintype S] [DecidableEq S] (g : S → V) :
    (Fintype.card V : ℂ) * ((univ.filter (fun s => g s = 0)).card : ℂ)
      = ∑ ψ : AddChar V ℂ, ∑ s, ψ (g s) := by
  rw [Finset.sum_comm]
  simp_rw [AddChar.sum_apply_eq_ite, ← Finset.sum_filter]
  rw [Finset.sum_const]
  simp [mul_comm]

/-! ## Pearl 2 — solution counting in a finite field via a primitive character

Over a finite field `F`, a single *primitive* character `ψ` (into any domain
`R'`) already separates points, and the characters can be parametrized by the
field elements `t` through `x ↦ ψ (t * x)`.  This is the form actually used by
finite-field character-sum arguments. -/

/-- **Fourier inversion counting (finite field).** For a finite field `F`, a
primitive additive character `ψ : AddChar F R'` into a domain `R'`, and any
`g : S → F` on a finite type `S`,
`|F| · #{s | g s = 0} = ∑_{t : F} ∑_s ψ (t * g s)`. -/
theorem card_solutions_mul_eq_field_sum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {S : Type*} [Fintype S] [DecidableEq S] (g : S → F) :
    (Fintype.card F : R') * ((univ.filter (fun s => g s = 0)).card : R')
      = ∑ t : F, ∑ s, ψ (t * g s) := by
  rw [Finset.sum_comm]
  simp_rw [AddChar.sum_mulShift _ hψ]
  push_cast
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  simp [mul_comm]

/-! ## Pearl 3 — the linear m-tuple count

Specializing Pearl 2 to the *linear* condition `∑ i, c i * w i (x i) = 0` over
tuples `x : ι → F`, the character sum factors as a product over the coordinates
(the coordinates are independent), turning the count into the "spectral" form
`∑_t ∏_i (∑_y ψ (t * (c i * w i y)))`.  This is the general statement of which
the project's `MTuple.card_mul_preCount` is the special case `w i = Δf_a`. -/

/-- **Linear m-tuple Fourier inversion.** For a finite field `F`, a primitive
character `ψ`, coefficients `c : ι → F`, and per-coordinate weight functions
`w : ι → F → F`,
`|F| · #{x : ι → F | ∑ i, c i * w i (x i) = 0} = ∑_t ∏_i ∑_y ψ (t * (c i * w i y))`. -/
theorem card_linear_tuple
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → F) (w : ι → F → F) :
    (Fintype.card F : R') *
        ((univ.filter (fun x : ι → F => ∑ i, c i * w i (x i) = 0)).card : R')
      = ∑ t : F, ∏ i, ∑ y : F, ψ (t * (c i * w i y)) := by
  rw [card_solutions_mul_eq_field_sum hψ (fun x : ι → F => ∑ i, c i * w i (x i))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum, addChar_map_sum]

/-! ## Pearl 4 — the vanishing criterion

Splitting off the `t = 0` term of the spectral sum (which always equals
`|F|^{|ι|}`), the count is exactly `|F|^{|ι|-1}` precisely when the
*nonzero-frequency* spectral sum vanishes.  This is the abstract content of the
project's `Vanish` condition. -/

/-- The `t = 0` term of the spectral sum is `|F|^{|ι|}`. -/
theorem spectrum_zero_term
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R']
    (ψ : AddChar F R')
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → F) (w : ι → F → F) :
    (∏ i, ∑ y : F, ψ ((0 : F) * (c i * w i y)))
      = (Fintype.card F : R') ^ (Fintype.card ι) := by
  simp [Finset.card_univ]

/-- Split the spectral sum into its `t = 0` term and the nonzero-frequency sum. -/
theorem spectrum_split
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R']
    {ι : Type*} [Fintype ι] (S : F → R')
    (h0 : S 0 = (Fintype.card F : R') ^ (Fintype.card ι)) :
    (∑ t : F, S t)
      = (Fintype.card F : R') ^ (Fintype.card ι)
        + ∑ t ∈ univ.erase (0 : F), S t := by
  rw [← Finset.add_sum_erase univ S (Finset.mem_univ 0), h0]

/-- **Vanishing criterion.** If the nonzero-frequency spectral sum vanishes, the
linear m-tuple count satisfies `|F| · count = |F|^{|ι|}`. -/
theorem card_linear_tuple_of_vanish
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → F) (w : ι → F → F)
    (hv : ∑ t ∈ univ.erase (0 : F), ∏ i, ∑ y : F, ψ (t * (c i * w i y)) = 0) :
    (Fintype.card F : R') *
        ((univ.filter (fun x : ι → F => ∑ i, c i * w i (x i) = 0)).card : R')
      = (Fintype.card F : R') ^ (Fintype.card ι) := by
  rw [card_linear_tuple hψ,
      spectrum_split (fun t => ∏ i, ∑ y : F, ψ (t * (c i * w i y)))
        (spectrum_zero_term ψ c w), hv, add_zero]

end Vanish.Foundations
