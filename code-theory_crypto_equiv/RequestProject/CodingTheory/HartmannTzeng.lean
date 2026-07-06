import Mathlib
import RequestProject.CodingTheory.BCHBound
import RequestProject.CodingTheory.BCHMinDist
import RequestProject.CodingTheory.BCHPrimitiveRoot

/-!
# The Hartmann–Tzeng / Roos direction: BCH bound along an arithmetic progression

This module generalises the consecutive-zeros BCH bound of
`RequestProject/CodingTheory/BCHBound.lean` in the **Hartmann–Tzeng / Roos**
direction, where the defining set of zeros need not be a block of *consecutive*
powers but an **arithmetic progression** `b, b + c, b + 2c, …` of exponents.

The key observation is the decimation principle underlying Hartmann–Tzeng and
Roos: if `α` is a primitive `n`-th root of unity and the step `c` is coprime to
`n`, then `α^c` is *again* a primitive `n`-th root of unity. Writing the
arithmetic-progression syndromes
`∑_i c_i · α^{i(b + l·c)} = ∑_i (c_i α^{ib}) · (α^c)^{i·l}`
exhibits them as the *consecutive* syndromes (offset `0`, step `1`) of the
re-weighted word `c_i' = c_i · α^{ib}` with respect to the new primitive root
`α^c`. Since re-weighting by the nonzero factors `α^{ib}` preserves the support,
the ordinary BCH bound applied to `α^c` transfers verbatim:

> a nonzero word with `δ − 1` zeros in arithmetic progression (step coprime to
> `n`) has Hamming weight at least `δ`.

This is the simplest member of the Hartmann–Tzeng / Roos family of bounds and the
natural stepping stone from the classical BCH bound toward them.

## Main results

* `bch_bound_arith` — the BCH bound along an arithmetic progression of zeros for
  primitive-root nodes (step coprime to the order).
* `bchCodeArith` — the corresponding cyclic code (kernel of the
  arithmetic-progression syndromes), with `mem_bchCodeArith`.
* `bchCodeArith_minDist_ge` — the designed distance is a lower bound for its
  minimum distance.
-/

open Finset BigOperators

namespace CodingTheory
namespace BCH

variable {F : Type*} [Field F]

/-
A primitive root raised to a power coprime to its order is again primitive of
the same order.
-/
theorem orderOf_pow_coprime {α : F} {n c : ℕ} (hc0 : c ≠ 0) (hcop : Nat.Coprime n c)
    (hα : orderOf α = n) : orderOf (α ^ c) = n := by
  rw [ orderOf_pow' ] <;> aesop

/-
**The BCH bound along an arithmetic progression (Hartmann–Tzeng/Roos step).**
For a primitive `n`-th root of unity `α` and a step `c` coprime to `n`, a nonzero
word with `δ − 1` zeros in the arithmetic progression of exponents
`b, b + c, …, b + (δ−2)c` has Hamming weight at least `δ`.
-/
theorem bch_bound_arith [DecidableEq F] {α : F} {n : ℕ}
    (hα : orderOf α = n) (cstep : ℕ) (hc0 : cstep ≠ 0)
    (hcop : Nat.Coprime n cstep)
    (w : Fin n → F) (hw : w ≠ 0) (b δ : ℕ)
    (hsyn : ∀ l : ℕ, l < δ - 1 → ∑ i, w i * (α ^ (i : ℕ)) ^ (b + l * cstep) = 0) :
    δ ≤ hammingNorm w := by
  convert bch_bound ( primitiveRootNodes ( α ^ cstep ) n ) ?_ ?_ ( fun i => w i * ( α ^ ( i : ℕ ) ) ^ b ) ?_ 0 δ ?_ using 1;
  · by_cases hα0 : α = 0 <;> simp_all +decide [ hammingNorm ];
    aesop;
  · exact primitiveRoot_nodes_injective ( orderOf_pow_coprime hc0 hcop hα );
  · intro i hi; simp_all +decide [ primitiveRootNodes ] ;
    cases n <;> simp_all +decide;
    exact Fin.elim0 i;
  · intro h; simp_all +decide [ funext_iff ] ;
    obtain ⟨ x, hx ⟩ := hw; specialize h x; simp_all +decide ;
    exact absurd hα ( by linarith [ Fin.is_lt x ] );
  · intro l hl; convert hsyn l hl using 2; simp +decide [ pow_add, pow_mul', primitiveRootNodes ] ; ring;

/-- The **arithmetic-progression BCH code**: words whose `δ − 1` zeros lie in the
arithmetic progression of exponents `b, b + c, …` (step `c`). -/
def bchCodeArith {n : ℕ} (x : Fin n → F) (b cstep δ : ℕ) : Submodule F (Fin n → F) where
  carrier := { w | ∀ l : ℕ, l < δ - 1 → ∑ i, w i * (x i) ^ (b + l * cstep) = 0 }
  add_mem' := by
    intro a c ha hc l hl
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha l hl, hc l hl, add_zero]
  zero_mem' := by intro l hl; simp
  smul_mem' := by
    intro r c hc l hl
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc l hl, mul_zero]

/-- Membership in the arithmetic-progression BCH code. -/
theorem mem_bchCodeArith {n : ℕ} (x : Fin n → F) (b cstep δ : ℕ) (w : Fin n → F) :
    w ∈ bchCodeArith x b cstep δ
      ↔ ∀ l : ℕ, l < δ - 1 → ∑ i, w i * (x i) ^ (b + l * cstep) = 0 :=
  Iff.rfl

/-
**The Hartmann–Tzeng/Roos-step bound through the minimum-distance API.**
-/
theorem bchCodeArith_minDist_ge [DecidableEq F] {α : F} {n : ℕ}
    (hα : orderOf α = n) (cstep : ℕ) (hc0 : cstep ≠ 0)
    (hcop : Nat.Coprime n cstep) (b δ : ℕ)
    (hC : bchCodeArith (primitiveRootNodes α n) b cstep δ ≠ ⊥) :
    δ ≤ minDist (bchCodeArith (primitiveRootNodes α n) b cstep δ) := by
  -- By definition of minimum distance, there exists a codeword $w$ such that $w \neq 0$ and $\text{hammingNorm}(w) = \text{minDist}(C)$.
  obtain ⟨w, hw1, hw2⟩ : ∃ w ∈ bchCodeArith (primitiveRootNodes α n) b cstep δ, w ≠ 0 ∧ hammingNorm w = minDist (bchCodeArith (primitiveRootNodes α n) b cstep δ) := by
    obtain ⟨w, hw⟩ := exists_eq_minWeight hC;
    grind +suggestions;
  exact hw2.2 ▸ bch_bound_arith hα cstep hc0 hcop w hw2.1 b δ ( by simpa [ mem_bchCodeArith, primitiveRootNodes ] using hw1 )

end BCH
end CodingTheory