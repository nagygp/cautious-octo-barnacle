import Mathlib
import DobbertinLego.Frobenius

/-!
# Gadget **L** — the linearized loop, and the telescope connective

The second LEGO brick: the Frobenius map of gadget **F** *closed into a loop of
length `len` with a step `step`*,

```
   loop step len x = ∑_{j<len} frob (j·step) x  =  ∑_{j<len} x^{2^{j·step}}.
```

Two of the paper's objects are just this one gadget at different settings:

* `step = 1`  gives the **absolute trace** `Tr(x) = ∑_{i<n} x^{2^i}`;
* `step = k`  gives the **partial trace** `P(x) = ∑_{j<k'} x^{2^{jk}}`.

The single **connective** that glues **L** back to **F** is the Artin–Schreier
telescope `loop_telescope`: the interior powers cancel in characteristic `2`,
leaving just the two endpoints.  Both telescoping identities the paper uses are
instances of this one lemma.
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
/-- **The telescope connective** (Artin–Schreier).  Applying one more Frobenius
step to the loop and adding the loop back cancels every interior power, leaving
the two endpoints:

```
   frob step (loop step len x) + loop step len x = frob (len·step) x + x.
```

This is the sole identity that wires gadget **L** to gadget **F**; the paper's
"add the `2^k`-th power to itself" is exactly one use of it. -/
lemma loop_telescope (step len : ℕ) (x : F) :
    frob step (loop step len x) + loop step len x = frob (len * step) x + x := by
  induction len with
  | zero => simp [loop, frob, CharTwo.add_self_eq_zero]
  | succ m ih =>
    rw [loop_succ, frob_add, frob_comp, show step + m * step = (m + 1) * step from by ring]
    have key : frob step (loop step m x) + frob ((m + 1) * step) x
        + (loop step m x + frob (m * step) x)
        = (frob step (loop step m x) + loop step m x)
          + (frob ((m + 1) * step) x + frob (m * step) x) := by ring
    rw [key, ih]
    rw [show ∀ a b c : F, (a + b) + (c + a) = c + b from fun a b c => by
      rw [show (a + b) + (c + a) = (a + a) + (b + c) from by ring,
        CharTwo.add_self_eq_zero, zero_add, add_comm]]

end Dobbertin.Lego
