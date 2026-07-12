import Mathlib

/-!
# The abstract scaffold — an abelian group with an endomorphism

The categorical / algebraic core underneath the whole step `(1) ⟹ (2)` of
Dobbertin's Theorem 1 is *one* gadget:

> an additive abelian group `A` together with an endomorphism `φ : A →+ A`.

Equivalently `A` is a module over the ring `ℤ[t]` with `t` acting as `φ`; the
endomorphism lives in the ring `AddMonoid.End A`, where multiplication is
composition and `1` is the identity.  Inside that ring live the two elements that
generate everything the paper needs:

* the **norm / geometric element** `iterSum φ len = ∑_{i<len} φⁱ` (the "loop");
* the **augmentation** `φ - 1` (Artin–Schreier `℘`).

The single load-bearing algebraic fact is the *geometric telescoping*

```
   (φ - 1) ∘ (∑_{i<len} φⁱ)  =  φ^len - 1,
```

the additive shadow of the geometric series / additive Hilbert 90.  It holds for
*any* endomorphism of *any* abelian group — no field, no characteristic, no
finiteness.  Both telescoping identities the paper uses are instances of it, and
its finite-order corollary (`iterSum_fixed_of_orderly`) is the reason a trace
lands in the fixed subgroup.

Nothing in this file mentions `𝔽₂`, Frobenius, or characteristic `2`; those enter
only when the scaffold is *specialized* in `DobbertinLego/Frobenius` and
`DobbertinLego/Loop`.
-/

namespace Dobbertin.Lego

open Finset

variable {A : Type*} [AddCommGroup A]

/-- **The norm / geometric element** `iterSum φ len = ∑_{i<len} φⁱ`, applied to
`x`.  Summing the endomorphism `φ` along its own iterates is the abstract "loop":
`Σ φⁱ x`. -/
def iterSum (φ : AddMonoid.End A) (len : ℕ) (x : A) : A := ∑ i ∈ range len, (φ ^ i) x

@[simp] lemma iterSum_zero (φ : AddMonoid.End A) (x : A) : iterSum φ 0 x = 0 := by
  simp [iterSum]

/-- Peel off the top iterate of the norm element. -/
lemma iterSum_succ (φ : AddMonoid.End A) (len : ℕ) (x : A) :
    iterSum φ (len + 1) x = iterSum φ len x + (φ ^ len) x := by
  simp [iterSum, sum_range_succ]

/-- **The geometric telescoping** `(φ - 1) ∘ (∑_{i<len} φⁱ) = φ^len - 1`,
written pointwise.  Applying one more `φ` to the norm element and subtracting the
element itself cancels every interior iterate, leaving the two endpoints:

```
   φ (iterSum φ len x) - iterSum φ len x = (φ^len) x - x.
```

This is the additive Hilbert 90 / geometric-series identity, and the sole
identity wiring the norm element back to the plain iterates `φ^m`.  It is entirely
generic: it needs only that `φ` is an endomorphism of an abelian group. -/
theorem iterSum_telescope (φ : AddMonoid.End A) (len : ℕ) (x : A) :
    φ (iterSum φ len x) - iterSum φ len x = (φ ^ len) x - x := by
  induction len with
  | zero => simp
  | succ m ih =>
    have hcomp : φ ((φ ^ m) x) = (φ ^ (m + 1)) x := by rw [pow_succ']; rfl
    simp only [iterSum, sum_range_succ, map_add] at *
    rw [hcomp]; abel_nf; abel_nf at ih; linear_combination (norm := abel) ih

/-- **Finite-order corollary: the norm element lands in the fixed subgroup.**  If
`φ` has order dividing `n` (`φ^n = 1`, e.g. Frobenius on a finite field), then the
full-length norm element `iterSum φ n x` is fixed by `φ`.  Immediate from the
telescope, since `φ^n - 1 = 0`. -/
theorem iterSum_fixed_of_orderly {n : ℕ} (φ : AddMonoid.End A) (hφ : φ ^ n = 1)
    (x : A) : φ (iterSum φ n x) = iterSum φ n x := by
  have h := iterSum_telescope φ n x
  rw [hφ] at h
  simpa using sub_eq_zero.mp (by simpa using h)

end Dobbertin.Lego
