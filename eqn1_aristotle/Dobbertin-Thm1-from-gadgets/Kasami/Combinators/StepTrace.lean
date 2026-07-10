import Mathlib
import Kasami.Gadgets.Frobenius
import Kasami.Gadgets.TraceLoop

/-!
# Combinator — linearized change of variable (the step-`2^k` trace)

The second combinator: a **basis change of the loop**.  Instead of inserting the
Frobenius map `φ : x ↦ x²` (gadget F), insert its `k`-th power `φ^k : x ↦ x^{2^k}`
and close *that* into a loop.  The result is the **step-`2^k` partial trace**
```
   P_{k,k'}(x) = ∑_{j<k'} x^{2^{jk}},
```
the linearized (additive) polynomial built from `φ^k`.  It is `traceLoop` read in
the "doubling-by-`k`" basis, and it is the numerator engine of the Kasami map.

Contents:

* `stepTrace`                  — `P_{k,k'}` above;
* `numeratorSum`               — `S_{k,k'}(x) = ∑_{i=1}^{k'} x^{2^{ik}}`, the
  Kasami numerator;
* `stepTrace_add`              — `P` is additive (linearized);
* `numeratorSum_eq_stepTrace_frob` — `S = φ^k(P) = P^{2^k}`: the numerator is the
  Frobenius-`2^k` image of the partial trace;
* `stepTrace_telescope` — the change-of-variable telescope
  `P^{2^k} + P = x^{2^{k'k}} + x`, the step-`k` analogue of the Artin–Schreier
  glue.

Char-2 commutative ring; no field/Fermat hypotheses.
-/

namespace Kasami.Combinators

open Finset Kasami.Gadgets

/-- The **step-`2^k` partial trace** `P_{k,k'}(x) = ∑_{j<k'} x^{2^{jk}}` — the
trace loop built from the Frobenius power `φ^k` (a linearized change of variable
of `traceLoop`). -/
def stepTrace {F : Type*} [CommSemiring F] (k k' : ℕ) (x : F) : F :=
  ∑ j ∈ Finset.range k', x ^ (2 ^ (j * k))

/-- The **Kasami numerator sum** `S_{k,k'}(x) = ∑_{i=1}^{k'} x^{2^{ik}}`. -/
def numeratorSum {F : Type*} [CommSemiring F] (k k' : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))

/-- `P` is additive (a linearized polynomial), by the char-2 freshman's dream. -/
lemma stepTrace_add {F : Type*} [CommSemiring F] [CharP F 2] (k k' : ℕ) (x y : F) :
    stepTrace k k' (x + y) = stepTrace k k' x + stepTrace k k' y := by
  simp only [stepTrace, ← Finset.sum_add_distrib]
  congr 1; ext j; exact add_pow_char_pow (p := 2) (n := j * k) x y

/-- **`S = P^{2^k}`.**  The numerator sum is the Frobenius-`2^k` image of the
partial trace (a re-indexing `i = j + 1`). -/
lemma numeratorSum_eq_stepTrace_frob {F : Type*} [CommSemiring F] [CharP F 2]
    (k k' : ℕ) (x : F) :
    numeratorSum k k' x = (stepTrace k k' x) ^ (2 ^ k) := by
  unfold numeratorSum stepTrace
  rw [sum_pow_char_pow, ← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by simp)
  intro i hi
  rw [← pow_mul, ← pow_add]
  ring_nf

/-- **The change-of-variable telescope.**  The step-`k` analogue of the
Artin–Schreier glue: `P^{2^k} + P = x^{2^{k'k}} + x` in characteristic two. -/
lemma stepTrace_telescope {F : Type*} [CommSemiring F] [CharP F 2] (k k' : ℕ) (x : F) :
    (stepTrace k k' x) ^ (2 ^ k) + stepTrace k k' x = x ^ (2 ^ (k' * k)) + x := by
  unfold stepTrace
  rw [sum_pow_char_pow]
  induction k' with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have e1 : ∀ j : ℕ, (x ^ (2 ^ (j * k))) ^ (2 ^ k) = x ^ (2 ^ ((j + 1) * k)) := by
        intro j; rw [← pow_mul, ← pow_add]; ring_nf
      rw [e1]
      have hcalc :
          (∑ j ∈ Finset.range m, (x ^ (2 ^ (j * k))) ^ (2 ^ k)) + x ^ (2 ^ ((m + 1) * k))
            + ((∑ j ∈ Finset.range m, x ^ (2 ^ (j * k))) + x ^ (2 ^ (m * k)))
          = ((∑ j ∈ Finset.range m, (x ^ (2 ^ (j * k))) ^ (2 ^ k))
              + (∑ j ∈ Finset.range m, x ^ (2 ^ (j * k))))
            + x ^ (2 ^ ((m + 1) * k)) + x ^ (2 ^ (m * k)) := by ring
      rw [hcalc, ih]
      have h2 : x ^ (2 ^ (m * k)) + x ^ (2 ^ (m * k)) = 0 := CharTwo.add_self_eq_zero _
      calc x ^ (2 ^ (m * k)) + x + x ^ (2 ^ ((m + 1) * k)) + x ^ (2 ^ (m * k))
          = (x ^ (2 ^ (m * k)) + x ^ (2 ^ (m * k))) + x + x ^ (2 ^ ((m + 1) * k)) := by ring
        _ = x ^ (2 ^ ((m + 1) * k)) + x := by rw [h2]; ring

end Kasami.Combinators
