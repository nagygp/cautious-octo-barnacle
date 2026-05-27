import Mathlib
import RequestProject.AutBase
import RequestProject.TraceNorm

/-!
# Layer B7c: Lemma 6.1 — Adjoint of Semilinear Operators

Formalization of Lemma 6.1 from Dempwolff & Müller (2013), Section 6.

## Main results

1. **Adjoint of T_k(b)** (Lemma 6.1(a)):
   `T_k(b)* = T_{-k}(b^{p^{-k}})`, i.e., the trace-adjoint of the
   semilinear operator `x ↦ b · x^{p^k}` is `x ↦ b^{p^{n-k}} · x^{p^{n-k}}`.

2. **Symplectic spread condition** (Lemma 6.1(b)):
   A spread set `{N(x)}` is symplectic iff there exists `A ∈ GL(F)` with
   `N(x)* · A = A · N(x)` for all x.

## DAG structure

```
  B1 (AutBase: semilinearOp)
    │
    └──► Lemma 6.1(a) (adjoint of T_k(b))
           │
           └──► Lemma 6.1(b) (symplectic condition)
```

**Dependencies:** Layer B1 (`AutBase.lean`), Layer F2 (`TraceNorm.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]
variable {n : ℕ} (hn : Fintype.card F = p ^ n)

/-
═══════════════════════════════════════════
Lemma 6.1(a) : Adjoint of T_k(b)
═══════════════════════════════════════════

**Adjoint identity for semilinear operators.**
    `Tr(T_k(b)(w) · z) = Tr(w · T_{n-k}(b^{p^{n-k}})(z))`.

    Proof: `Tr(b·w^{p^k} · z) = Tr((w·(b·z)^{p^{n-k}})^{p^k})`
    by product-Frobenius, and `Tr(x^{p^k}) = Tr(x)`.
-/
lemma semilinearOp_trace_adjoint (hn' := hn) (k : ℕ) (hk : k ≤ n) (b w z : F) :
    frobSum p n (semilinearOp p k b w * z) =
    frobSum p n (w * semilinearOp p (n - k) (b ^ (p ^ (n - k))) z) := by
      -- Apply the lemma `trace_prod_frob` to rewrite the left-hand side.
      have h_trace : frobSum p n ((b * w ^ (p ^ k)) * z) = frobSum p n (w ^ (p ^ k) * (b * z)) := by
        ring;
      convert trace_prod_frob p hn w ( b * z ) k hk using 1 ; simp +decide [ semilinearOp ];
      rw [ mul_pow ]

-- Lemma 6.1(a) is semilinearOp_trace_adjoint above.

-- ═══════════════════════════════════════════
-- Lemma 6.1(a) corollaries
-- ═══════════════════════════════════════════

/-- **Adjoint of T_0(b) is T_0(b).**
    The adjoint of a scalar multiplication is itself. -/
lemma semilinearOp_adjoint_zero (b w z : F) :
    frobSum p n (semilinearOp p 0 b w * z) =
    frobSum p n (w * semilinearOp p 0 b z) := by
  simp only [semilinearOp, pow_zero, pow_one]; ring_nf

-- ═══════════════════════════════════════════
-- Lemma 6.1(b) : Symplectic spread condition
-- ═══════════════════════════════════════════

/-- **Symplectic condition.**
    A spread set `{N(x)}` is symplectic iff there exists a bijective
    additive map `A : F → F` such that `N(x)* · A = A · N(x)` for all x,
    where `*` denotes the trace-adjoint.

    This is stated as a predicate on a family of operators. -/
def IsSymplecticSpread
    (N : F → F → F)
    (Nadj : F → F → F)
    (hAdj : ∀ a w z, frobSum p n (N a w * z) = frobSum p n (w * Nadj a z)) :
    Prop :=
  ∃ A : F → F, Function.Bijective A ∧
    (∀ a b, A (a + b) = A a + A b) ∧
    ∀ a w, Nadj a (A w) = A (N a w)

end DempwolffMueller