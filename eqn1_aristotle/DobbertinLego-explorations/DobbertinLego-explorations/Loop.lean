import Mathlib
import DobbertinLego.Frobenius
import DobbertinLego.Endo

/-!
# Gadget **L** — the linearized loop as an instance of the norm element

The second LEGO brick: the Frobenius endomorphism of gadget **F** *closed into a
loop of length `len` with a step `step`*,

```
   loop step len x = ∑_{j<len} frob (j·step) x  =  ∑_{j<len} x^{2^{j·step}}.
```

This is exactly the abstract **norm element** `iterSum` of `DobbertinLego/Endo`
applied to the Frobenius endomorphism `frobEndo step` (`loop_eq_iterSum`).  Two of
the paper's objects are this one gadget at different settings:

* `step = 1`  gives the **absolute trace** `Tr(x) = ∑_{i<n} x^{2^i}`;
* `step = k`  gives the **partial trace** `P(x) = ∑_{j<k'} x^{2^{jk}}`.

Because `loop` *is* the abstract norm element, the Artin–Schreier telescope
`loop_telescope` is no longer a bespoke induction: it is the generic
`iterSum_telescope` read in characteristic `2` (where `−1 = +1`).  Both telescoping
identities the paper uses are instances of this one generic lemma.
-/

namespace Dobbertin.Lego

open Finset

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- **Gadget L.**  The linearized loop `loop step len x = ∑_{j<len} x^{2^{j·step}}`
— gadget F summed along a step-`step` arithmetic progression of exponents. -/
def loop (step len : ℕ) (x : F) : F := ∑ j ∈ range len, frob (j * step) x

omit [Fintype F] [CharP F 2] in
@[simp] lemma loop_zero_len (step : ℕ) (x : F) : loop step 0 x = 0 := by simp [loop]

omit [Fintype F] [CharP F 2] in
/-- Peel off the top summand of the loop. -/
lemma loop_succ (step len : ℕ) (x : F) :
    loop step (len + 1) x = loop step len x + frob (len * step) x := by
  simp [loop, sum_range_succ]

omit [Fintype F] in
/-- **L is the abstract norm element.**  The loop is `iterSum` of the Frobenius
endomorphism `frobEndo step`: `loop step len x = ∑_{j<len} (frobEndo step)ʲ x`.
This identification is what turns the paper's telescoping into an instance of the
generic `iterSum_telescope`. -/
lemma loop_eq_iterSum (step len : ℕ) (x : F) :
    loop step len x = iterSum (frobEndo step) len x := by
  simp [loop, iterSum, frobEndo_pow_apply]

omit [Fintype F] in
/-- **The telescope connective** (Artin–Schreier), now a *specialization* of the
generic endomorphism telescope `iterSum_telescope`.  Applying one more Frobenius
step to the loop and adding the loop back cancels every interior power, leaving the
two endpoints:

```
   frob step (loop step len x) + loop step len x = frob (len·step) x + x.
```

Mechanism: `loop` is the norm element (`loop_eq_iterSum`), so the abstract
`(φ−1)∘∑φⁱ = φ^len − 1` applies with `φ = frobEndo step`; in characteristic `2`
the subtraction becomes addition.  The paper's "add the `2^k`-th power to itself"
is exactly one use of this. -/
lemma loop_telescope (step len : ℕ) (x : F) :
    frob step (loop step len x) + loop step len x = frob (len * step) x + x := by
  have h := iterSum_telescope (frobEndo (F := F) step) len x
  rw [frobEndo_pow_apply, ← loop_eq_iterSum, frobEndo_apply,
    sub_eq_add_neg, sub_eq_add_neg] at h
  simpa [CharTwo.neg_eq] using h

end Dobbertin.Lego
