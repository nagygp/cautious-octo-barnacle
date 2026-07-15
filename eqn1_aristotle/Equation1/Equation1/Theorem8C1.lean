import Mathlib
import Dobbertin1999MVP.Equation1.FiniteFieldPrereqs
import Dobbertin1999MVP.Equation1.Theorem5

/-!
# Equation (1) MVP — trace facts and the trace-version map `gmap`

The three `Dobbertin.Thm8C1` declarations on the dependency path of equation (1):
the trace is idempotent under squaring (`trace_sq`), hence a bit (`trace_bit`),
and the trace-version Kasami map `g(x) = q^{(Tr x)}(x)` (`gmap`).  Copied verbatim
from `Theorem8C1.lean`; nothing else from that file is needed.
-/

namespace Dobbertin.Thm8C1

open scoped BigOperators
open Dobbertin.Thm5 DempwolffMueller

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## Elementary trace facts -/

/-
On `𝔽_{2ⁿ}` the absolute trace is idempotent under squaring:
`Tr(x)² = Tr(x)`.
-/
theorem trace_sq {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    (truncTrace n x) ^ 2 = truncTrace n x := by
  have := @truncTrace_sq_add_self F _ _ n x;
  simp_all +decide [ ← hn, FiniteField.pow_card ];
  grind

/-
On `𝔽_{2ⁿ}` the absolute trace is a bit: `Tr(x) ∈ {0,1}`.
-/
theorem trace_bit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    truncTrace n x = 0 ∨ truncTrace n x = 1 := by
  have := trace_sq hn x; simp_all +decide [ pow_succ' ] ;
  grind

/-! ## The trace-version permutation `g` -/

/-- The **trace version** `g(x) = q^{(Tr x)}(x)` of the Kasami polynomial: it uses
the actual trace `Tr(x)` in place of a constant bit. -/
noncomputable def gmap (n k kk : ℕ) (x : F) : F := qeps n k kk (truncTrace n x) x

end Field

end Dobbertin.Thm8C1
