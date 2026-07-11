import Mathlib
import Kasami.KasamiMap
import Equation1.Setup
import Equation1.Equation1

/-!
# Result — the Kasami permutation criterion (assembled from the blocks)

The headline of the permutation half of Dobbertin's paper (his *Theorem 1*),
stated for the block-assembled `Kasami.kasamiMap` and named by its role:

> **`kasamiMap_isPermutation_iff`** — the Kasami map `q_α` is a *permutation* of
> `𝔽_{2ⁿ}` **iff** `k' + α·n` is odd.

The proof is pure composition: `kasamiMap` is definitionally the paper's
`qKasami` (`kasamiMap_eq_qKasami`), so the criterion is exactly the engine's
`theorem_1`, whose internal argument is the L/F/C bricks and the Artin–Schreier
telescope wired together.

Two named specialisations record the two cases the paper actually uses:

* `traceFreeKasami_isPermutation_iff` (`α = 0`) — the **trace-free** map is a
  permutation iff `k'` is odd (Dobbertin's Theorem 5);
* `traceVersionKasami_isPermutation_iff` (`α = 1`) — the **trace-version** map is
  a permutation iff `k' + n` is odd.

The value-at-`1` invariant `kasamiMap_one_isBit` records the elementary necessary
direction (the map fixes `0`, and its value at `1` is the parity bit).
-/

namespace Kasami

open Dobbertin1999.Paper

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {n k k' : ℕ}

omit [Fintype F] [CharP F 2] in
/-- **The block-assembled Kasami map is the paper's `q_α`.**  Definitional: the
numerator sum, trace loop and coset power match term for term. -/
lemma kasamiMap_eq_qKasami (α : ℕ) (z : F) :
    kasamiMap n k k' α z = qKasami n k k' α z := rfl

/-- **The Kasami permutation criterion (Theorem 1).**  `q_α` is a permutation of
`𝔽_{2ⁿ}` iff `k' + α·n` is odd. -/
theorem kasamiMap_isPermutation_iff (hn : Fintype.card F = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (hk0 : 0 < k)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (α : ℕ) (hα : α = 0 ∨ α = 1) :
    Function.Bijective (kasamiMap (F := F) n k k' α) ↔ (k' + α * n) % 2 = 1 := by
  have hfun : kasamiMap (F := F) n k k' α = qKasami n k k' α :=
    funext fun z => kasamiMap_eq_qKasami α z
  rw [hfun]
  exact theorem_1 hn hk hcop hk' hk0 hexp α hα

/-- **Trace-free case (`α = 0`, Dobbertin's Theorem 5).**  The trace-free Kasami
map is a permutation iff `k'` is odd. -/
theorem traceFreeKasami_isPermutation_iff (hn : Fintype.card F = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (hk0 : 0 < k)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    Function.Bijective (kasamiMap (F := F) n k k' 0) ↔ k' % 2 = 1 := by
  rw [kasamiMap_isPermutation_iff hn hk hcop hk' hk0 hexp 0 (Or.inl rfl)]
  simp

/-- **Trace-version case (`α = 1`).**  The trace-version Kasami map is a
permutation iff `k' + n` is odd. -/
theorem traceVersionKasami_isPermutation_iff (hn : Fintype.card F = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (hk0 : 0 < k)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    Function.Bijective (kasamiMap (F := F) n k k' 1) ↔ (k' + n) % 2 = 1 := by
  rw [kasamiMap_isPermutation_iff hn hk hcop hk' hk0 hexp 1 (Or.inr rfl)]
  simp

omit [Fintype F] in
/-- **The value-at-`1` parity invariant.**  `q_α(1) = 0` iff `k' + α·n` is even —
the elementary "only if" obstruction (`q_α` fixes `0`, so if it is a permutation
it cannot also vanish at `1`). -/
theorem kasamiMap_one_isBit (α : ℕ) :
    kasamiMap (F := F) n k k' α 1 = 0 ↔ (k' + α * n) % 2 = 0 :=
  qKasami_one_eq_zero_iff α

end Kasami
