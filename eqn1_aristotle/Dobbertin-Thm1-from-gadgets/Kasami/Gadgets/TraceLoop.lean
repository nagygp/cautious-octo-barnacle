import Mathlib
import Kasami.Gadgets.Frobenius

/-!
# Gadget L — the linearized trace loop

The second primitive LEGO brick: the **linearized trace** obtained by *closing
the Frobenius map into a loop*,
```
   L_m(x) = ∑_{i<m} x^{2^i}  =  x + φ(x) + φ²(x) + … + φ^{m-1}(x),
```
i.e. the running sum of the doubling map `φ` (gadget F).  At full length
`m = n` (where `|F| = 2ⁿ`) this is the absolute trace of `𝔽_{2ⁿ}` over `𝔽₂`.

Core properties packaged here:

* `traceLoop`             — the loop `∑_{i<m} x^{2^i}`;
* `traceLoop_add`         — **L is additive** (linearized), by the freshman's
  dream: it is a homomorphism of the additive group;
* `traceLoop_frobenius`   — **L is Frobenius-equivariant**: `L(φ x) = φ(L x)`;
* `traceLoop_sq`, `traceLoop_isBit` — at full length the trace is **idempotent**
  (`L(x)² = L(x)`), hence a *bit* `L(x) ∈ {0,1}` (it lands in the prime field).

The Artin–Schreier telescoping identity that glues L back to F lives in the
combinator module `Kasami.Combinators.ArtinSchreierTelescope`.  This block needs
only `Mathlib` (plus gadget F for vocabulary).
-/

namespace Kasami.Gadgets

open Finset

/-- The **linearized trace loop** `L_m(x) = ∑_{i<m} x^{2^i}` — the Frobenius map
of gadget F summed (closed into a loop) over `m` steps. -/
def traceLoop {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

@[simp] lemma traceLoop_zero_len {F : Type*} [CommSemiring F] (x : F) :
    traceLoop 0 x = 0 := by simp [traceLoop]

lemma traceLoop_succ {F : Type*} [CommSemiring F] (m : ℕ) (x : F) :
    traceLoop (m + 1) x = traceLoop m x + x ^ (2 ^ m) := by
  simp [traceLoop, Finset.sum_range_succ]

@[simp] lemma traceLoop_zero {F : Type*} [CommSemiring F] (m : ℕ) :
    traceLoop m (0 : F) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i _
  exact zero_pow (pow_ne_zero i (by norm_num))

/-- **L is additive.**  The linearized trace loop is a homomorphism of the
additive group, by the char-2 freshman's dream `(x+y)^{2^i} = x^{2^i} + y^{2^i}`. -/
lemma traceLoop_add {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x y : F) :
    traceLoop m (x + y) = traceLoop m x + traceLoop m y := by
  simp only [traceLoop, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_char_pow (p := 2) (n := i) x y

/-- **L is Frobenius-equivariant.**  Closing the loop commutes with the inserted
map: `L(x²) = L(x)²`. -/
lemma traceLoop_frobenius {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x : F) :
    traceLoop m (x ^ 2) = (traceLoop m x) ^ 2 := by
  simp only [traceLoop, sum_pow_char (p := 2)]
  congr 1; ext i; rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **The telescoping half-step** `L(x)² + L(x) = x^{2^m} + x` (valid over any
char-2 commutative ring; no field/Fermat hypotheses).  This is the algebraic
heart of the Artin–Schreier combinator. -/
lemma traceLoop_sq_add_self {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x : F) :
    traceLoop m x ^ 2 + traceLoop m x = x ^ (2 ^ m) + x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction m with
  | zero => simp [traceLoop, CharTwo.add_self_eq_zero]
  | succ m ih =>
      have hsq : (traceLoop m x + x ^ (2 ^ m)) ^ 2
          = traceLoop m x ^ 2 + (x ^ (2 ^ m)) ^ 2 := by
        have h := add_pow_char_pow (R := F) (p := 2) (n := 1)
          (traceLoop m x) (x ^ (2 ^ m))
        simpa using h
      rw [traceLoop_succ, hsq, ← pow_mul, ← pow_succ]
      calc traceLoop m x ^ 2 + x ^ (2 ^ (m + 1)) + (traceLoop m x + x ^ (2 ^ m))
          = (traceLoop m x ^ 2 + traceLoop m x) + x ^ (2 ^ (m + 1)) + x ^ (2 ^ m) := by ring
        _ = (x ^ (2 ^ m) + x) + x ^ (2 ^ (m + 1)) + x ^ (2 ^ m) := by rw [ih]
        _ = x ^ (2 ^ (m + 1)) + x := by
              have h2 : x ^ (2 ^ m) + x ^ (2 ^ m) = 0 := CharTwo.add_self_eq_zero _
              calc (x ^ (2 ^ m) + x) + x ^ (2 ^ (m + 1)) + x ^ (2 ^ m)
                  = (x ^ (2 ^ m) + x ^ (2 ^ m)) + x + x ^ (2 ^ (m + 1)) := by ring
                _ = x ^ (2 ^ (m + 1)) + x := by rw [h2]; ring

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- **At full length the trace is idempotent under squaring:** `L(x)² = L(x)`.
When `|F| = 2ⁿ` the loop closes (`x^{2ⁿ} = x`), so the half-step
`L(x)² + L(x) = x^{2ⁿ} + x` collapses to `L(x)² = L(x)`. -/
lemma traceLoop_sq {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    (traceLoop n x) ^ 2 = traceLoop n x := by
  have h := traceLoop_sq_add_self (F := F) n x
  rw [← hn, FiniteField.pow_card, CharTwo.add_self_eq_zero] at h
  -- h : traceLoop n x ^ 2 + traceLoop n x = 0
  have h2 : traceLoop n x ^ 2 = -(traceLoop n x) := by linear_combination h
  rw [h2, CharTwo.neg_eq]

/-- **The trace is a bit:** `L(x) ∈ {0,1}`, i.e. it lands in the prime field
`𝔽₂`.  Immediate from idempotence `L(x)² = L(x)`. -/
lemma traceLoop_isBit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    traceLoop n x = 0 ∨ traceLoop n x = 1 := by
  have h := traceLoop_sq hn x
  have : traceLoop n x * (traceLoop n x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

end Field

end Kasami.Gadgets
