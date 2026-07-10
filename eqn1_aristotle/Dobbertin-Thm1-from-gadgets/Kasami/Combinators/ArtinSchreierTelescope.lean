import Mathlib
import Kasami.Gadgets.Frobenius
import Kasami.Gadgets.TraceLoop

/-!
# Combinator — the Artin–Schreier telescope (glue L to F)

The first *combinator* of the toolkit: it wires the trace loop **L**
(`Kasami.Gadgets.traceLoop`) to the Frobenius map **F**
(`Kasami.Gadgets.frobeniusPow`).  Two glued facts result.

* `traceLoop_artin_schreier` — the **telescoping identity**
  `L_k(x² + x) = x^{2^k} + x`.  The loop turns the Artin–Schreier element
  `x² + x` into a single Frobenius difference: every intermediate power cancels.
  (Char-2 commutative ring; no field hypotheses.)
* `traceLoop_frobenius_invariant` — at full length the absolute trace is
  **Frobenius-invariant**: `L_n(x^{2^k}) = L_n(x)`.  Closing the loop (`|F| = 2ⁿ`)
  makes each doubling step invisible to the trace.
* `traceLoop_artin_schreier_zero` — hence `L_n(t^{2^k} + t) = 0`: the image of
  the doubling-minus-identity map lies in the kernel of the trace.  This is the
  exact fact the Kasami permutation argument consumes when linearising equation
  (1).

These three are the "telescope + kernel" content that lets the permutation half
of the paper be assembled from L and F alone.
-/

namespace Kasami.Combinators

open Finset Kasami.Gadgets

/-- **The telescoping identity.**  In characteristic two the trace loop sends the
Artin–Schreier element `x² + x` to the Frobenius difference `x^{2^k} + x`:
```
   L_k(x² + x) = ∑_{i<k} (x² + x)^{2^i} = x^{2^k} + x,
```
each summand `(x²+x)^{2^i} = x^{2^{i+1}} + x^{2^i}` being the gap between
consecutive Frobenius powers, so the sum telescopes. -/
theorem traceLoop_artin_schreier {F : Type*} [CommRing F] [CharP F 2] (k : ℕ) (x : F) :
    traceLoop k (x ^ 2 + x) = x ^ (2 ^ k) + x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction k with
  | zero => simp [traceLoop, CharTwo.add_self_eq_zero]
  | succ k ih =>
      rw [traceLoop_succ, ih]
      have e : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ (k + 1)) := by rw [← pow_mul, ← pow_succ']
      have hstep : (x ^ 2 + x) ^ (2 ^ k) = x ^ (2 ^ (k + 1)) + x ^ (2 ^ k) := by
        rw [add_pow_char_pow (R := F) (p := 2) (n := k) (x ^ 2) x, e]
      rw [hstep]
      have h2 : x ^ (2 ^ k) + x ^ (2 ^ k) = 0 := CharTwo.add_self_eq_zero _
      linear_combination h2

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- **Frobenius-invariance of the absolute trace.**  At full length `n`
(`|F| = 2ⁿ`) the trace is unchanged by any number of doubling steps:
`L_n(x^{2^k}) = L_n(x)`.  One step follows from the Frobenius-equivariance of L
and its idempotence; iterate. -/
theorem traceLoop_frobenius_invariant {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (x : F) :
    traceLoop n (x ^ (2 ^ k)) = traceLoop n x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : x ^ (2 ^ (k + 1)) = (x ^ (2 ^ k)) ^ 2 := by
        rw [← pow_mul, ← pow_succ]
      rw [hstep, traceLoop_frobenius, traceLoop_sq hn, ih]

/-- **The trace kills the Artin–Schreier image.**  `L_n(t^{2^k} + t) = 0`: the
image of `x ↦ x^{2^k} + x` lies in the kernel of the absolute trace. -/
theorem traceLoop_artin_schreier_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (t : F) :
    traceLoop n (t ^ (2 ^ k) + t) = 0 := by
  rw [traceLoop_add, traceLoop_frobenius_invariant hn, CharTwo.add_self_eq_zero]

end Field

end Kasami.Combinators
