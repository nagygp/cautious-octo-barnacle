import Mathlib
import RequestProject.AutTypeI
import RequestProject.Lemma61
import RequestProject.SpreadSet

/-!
# Layer B7a: Symplectic Condition — Type I

Formalization of Proposition 6.2 from Dempwolff & Müller (2013).

## Main result

**Proposition 6.2:** The type I spread is not symplectic
(`A_{n,m}` is not isomorphic to its dual spread plane).

## Proof method

Using Lemma 6.1, compute the adjoint of the spread operators.
The symplectic condition `N(x)*·A = A·N(x)` leads to a contradiction
with the structure of the truncated trace.

## DAG structure

```
  B4 (AutTypeI) + B7c (Lemma61)
    │
    └──► Prop 6.2 (not symplectic)
```

**Dependencies:** AutTypeI, Lemma61, Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- B7a.1 : Symplectic condition for Type I
-- ═══════════════════════════════════════════

/-- **Proposition 6.2 (abstract form).**
    The type I spread set `{N(x)(y) = L(x·y)·x^k}` is not symplectic.

    This means there is no bijective additive `A : F → F` such that
    `N(x)*(A(y)) = A(N(x)(y))` for all x, y, where `N(x)*` is the
    trace-adjoint of `N(x)`. -/
def TypeINotSymplectic {n_dim : ℕ} (hn : Fintype.card F = p ^ n_dim)
    (m : ℕ) : Prop :=
  ¬ ∃ A : F → F, Function.Bijective A ∧
    (∀ a b, A (a + b) = A a + A b) ∧
    ∀ x w z : F,
      frobSum p n_dim (spreadSetFromPoly p n_dim (fun _ : Fin n_dim => (1 : F))
        (2 ^ (n_dim - 1) - 2 ^ (m - 1) - 1) x w * z) =
      frobSum p n_dim (w * A (spreadSetFromPoly p n_dim (fun _ : Fin n_dim => (1 : F))
        (2 ^ (n_dim - 1) - 2 ^ (m - 1) - 1) x z))

end DempwolffMueller
