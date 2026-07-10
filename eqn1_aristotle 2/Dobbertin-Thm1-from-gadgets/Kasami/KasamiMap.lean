import Mathlib
import Kasami.Gadgets.Frobenius
import Kasami.Gadgets.TraceLoop
import Kasami.Combinators.StepTrace

/-!
# The Kasami map, assembled from the building blocks

Dobbertin's generalized Kasami polynomial is nothing but the three primitive
bricks snapped together:
```
   q_α(z) =  ( S_{k,k'}(z)  +  α · L_n(z) )  ·  z^{(2ⁿ−1) − (2^k+1)}.
             └── numeratorSum ─┘   └─ traceLoop ─┘   └──── power / gadget C ────┘
```

* `numeratorSum` (`S`) is the step-`2^k` combinator (numerator engine);
* `traceLoop` (`L`) is the linearized trace block, weighted by the bit `α`;
* the trailing power realises the denominator `1 / z^{2^k+1}` on the field
  (`0/0 = 0`), its exponent living in gadget-C coset arithmetic.

`kasamiMap` is *definitionally* the paper's `Dobbertin1999.Paper.qKasami`
(`kasamiMap_eq_qKasami`), so the permutation criterion proved for the engine
transfers verbatim to this block-assembled form.
-/

namespace Kasami

open Finset Kasami.Gadgets Kasami.Combinators

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The **Kasami map** `q_α`, assembled from the building blocks: the step-`2^k`
numerator `S`, the trace loop `L` (weighted by the bit `α`), and the coset power
that clears the denominator. -/
def kasamiMap (n k k' α : ℕ) (z : F) : F :=
  (numeratorSum k k' z + (α : F) * traceLoop n z) * z ^ (2 ^ n - 1 - (2 ^ k + 1))

omit [Fintype F] [CharP F 2] in
@[simp] lemma kasamiMap_zero_pt (n k k' α : ℕ) :
    kasamiMap (F := F) n k k' α 0 = 0 := by
  unfold kasamiMap numeratorSum traceLoop
  have h1 : (∑ i ∈ Finset.Icc 1 k', (0 : F) ^ (2 ^ (i * k))) = 0 :=
    Finset.sum_eq_zero fun i _ => zero_pow (pow_ne_zero _ (by norm_num))
  have h2 : (∑ i ∈ Finset.range n, (0 : F) ^ (2 ^ i)) = 0 :=
    Finset.sum_eq_zero fun i _ => zero_pow (pow_ne_zero _ (by norm_num))
  rw [h1, h2]; ring

end Kasami
