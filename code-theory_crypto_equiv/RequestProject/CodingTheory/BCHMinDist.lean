import Mathlib
import RequestProject.CodingTheory.BCHBound
import RequestProject.CodingTheory.LinearCode

/-!
# Tying the BCH bound into the `LinearCode` minimum-distance API

This module connects the abstract **BCH bound** of
`RequestProject/CodingTheory/BCHBound.lean` to the linear-code minimum-distance
machinery of `RequestProject/CodingTheory/LinearCode.lean`
(`CodingTheory.minWeight` / `CodingTheory.minDist`).

Fix distinct nonzero nodes `x₀, …, x_{n-1}` (for a genuine BCH code, the powers of
a primitive `n`-th root of unity). The **BCH code** of designed distance `δ` is the
linear subspace of words whose `δ − 1` consecutive *syndromes*
`S_l(c) = ∑_i c_i · x_i^{b+l}` (`l = 0, …, δ − 2`) all vanish; this is the kernel
of the consecutive-syndrome linear map, hence a `Submodule`.

The BCH bound (`bch_bound`) says every nonzero codeword has Hamming weight `≥ δ`.
Phrased through the `LinearCode` API this is exactly

```
δ ≤ minWeight (bchCode x b δ) = minDist (bchCode x b δ),
```

i.e. the designed distance is a genuine lower bound for the code's minimum
distance — the classical statement of the BCH bound for cyclic codes.

## Main results

* `bchCode` — the BCH code as a `Submodule F (Fin n → F)`.
* `mem_bchCode` — membership characterisation (the vanishing syndromes).
* `bchCode_minWeight_ge` — `δ ≤ minWeight (bchCode x b δ)`.
* `bchCode_minDist_ge` — `δ ≤ minDist (bchCode x b δ)` (the BCH bound through the
  linear-code minimum-distance API).
-/

open Finset BigOperators

namespace CodingTheory
namespace BCH

open scoped Classical

variable {F : Type*} [Field F]

/-- The **BCH code** of designed distance `δ` with nodes `x` and offset `b`: the
words `c : Fin n → F` whose `δ − 1` consecutive syndromes
`∑_i c_i · x_i^{b+l}` (`l = 0, …, δ − 2`) all vanish. As the common kernel of the
syndrome linear functionals, this is a linear subspace. -/
def bchCode {n : ℕ} (x : Fin n → F) (b δ : ℕ) : Submodule F (Fin n → F) where
  carrier := { c | ∀ l : ℕ, l < δ - 1 → ∑ i, c i * (x i) ^ (b + l) = 0 }
  add_mem' := by
    intro a c ha hc l hl
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha l hl, hc l hl, add_zero]
  zero_mem' := by intro l hl; simp
  smul_mem' := by
    intro r c hc l hl
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc l hl, mul_zero]

/-- A word lies in the BCH code iff its `δ − 1` consecutive syndromes vanish. -/
theorem mem_bchCode {n : ℕ} (x : Fin n → F) (b δ : ℕ) (c : Fin n → F) :
    c ∈ bchCode x b δ ↔ ∀ l : ℕ, l < δ - 1 → ∑ i, c i * (x i) ^ (b + l) = 0 :=
  Iff.rfl

/-
**The BCH bound through the minimum-weight API.** For distinct nonzero nodes,
the designed distance `δ` is a lower bound for the minimum weight of the BCH code:
`δ ≤ minWeight (bchCode x b δ)`.
-/
theorem bchCode_minWeight_ge {n : ℕ} (x : Fin n → F)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0) (b δ : ℕ)
    (hC : bchCode x b δ ≠ ⊥) :
    δ ≤ minWeight (bchCode x b δ) := by
  obtain ⟨c, hc⟩ := exists_eq_minWeight hC;
  exact hc.2.2 ▸ bch_bound x hx hx0 c hc.2.1 b δ ( by simpa [ mem_bchCode ] using hc.1 )

/-- **The BCH bound through the minimum-distance API.** For distinct nonzero
nodes, the designed distance `δ` is a lower bound for the minimum distance of the
BCH code: `δ ≤ minDist (bchCode x b δ)`. -/
theorem bchCode_minDist_ge {n : ℕ} (x : Fin n → F)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0) (b δ : ℕ)
    (hC : bchCode x b δ ≠ ⊥) :
    δ ≤ minDist (bchCode x b δ) := by
  rw [minDist_eq_minWeight]
  exact bchCode_minWeight_ge x hx hx0 b δ hC

end BCH
end CodingTheory