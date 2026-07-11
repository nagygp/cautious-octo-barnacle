import Mathlib
import Kasami.Gadgets.TraceLoop

/-!
# Combinator — the categorical trace pattern (L is the field trace)

The trace loop **L** (gadget `Kasami.Gadgets.traceLoop`) is not an ad-hoc sum: it
*is* the field trace, i.e. the one categorical "open a loop, insert a map, close
it, keep what returns" move.  For a finite extension the categorical/library
trace `Algebra.trace K L` is computed (Mathlib's
`FiniteField.algebraMap_trace_eq_sum_pow`) by the Frobenius sum
`∑_{i<[L:K]} x^{(#K)^i}` — which over the prime field `𝔽₂ = ZMod 2` is exactly
`traceLoop`.

So the loop applied to the multiplication maps `m_x` of the field recovers L, and
"a trace description of a set" (the difference-set half of the paper) is reading
that set through the same pairing.  This module records the identification, tying
the elementary building block to the library's `Algebra.trace`.

* `traceLoop_eq_algebraMap_trace` — `traceLoop [L:𝔽₂] x` is `Algebra.trace 𝔽₂ L x`
  pushed back into `L` along `algebraMap`.
-/

namespace Kasami.Combinators

open Kasami.Gadgets

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]

/-- **The trace loop is the categorical/library trace.**  At full length
`n = [L : 𝔽₂]`, the loop `traceLoop n` equals Mathlib's `Algebra.trace (ZMod 2) L`
pushed into `L` along `algebraMap` — the single evaluation/coevaluation move
applied to the field's multiplication maps. -/
theorem traceLoop_eq_algebraMap_trace (x : L) :
    letI := ZMod.algebra L 2
    traceLoop (Module.finrank (ZMod 2) L) x
      = algebraMap (ZMod 2) L (Algebra.trace (ZMod 2) L x) := by
  letI := ZMod.algebra L 2
  rw [FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) L x]
  unfold traceLoop
  have : Nat.card (ZMod 2) = 2 := by simp
  rw [this]

end Kasami.Combinators
