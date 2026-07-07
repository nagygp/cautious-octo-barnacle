import RequestProject.Physics.HammingScheme
import RequestProject.CodingTheory.Krawtchouk

/-!
# Bose–Mesner algebra of the Hamming scheme: valencies are Krawtchouk values

This module connects the **association-scheme** layer
(`RequestProject/Physics/HammingScheme.lean`) to the **Krawtchouk polynomials**
(`RequestProject/CodingTheory/Krawtchouk.lean`), the transition matrix of the
MacWilliams/Delsarte theory.

In the Bose–Mesner algebra of the Hamming scheme `H(n, q)`, the `i`-th adjacency
matrix `A_i` (the indicator of the distance-`i` relation) acts on the additive
character basis with the **Krawtchouk values as eigenvalues**: the eigenvalue of
`A_i` on the trivial (all-ones) eigenspace is the valency `v_i`, and this is
exactly the Krawtchouk value `K_i(0) = C(n,i)(q-1)^i`.  This is the first entry
of the eigenvalue matrix `P` whose entries `P_{i}(k) = K_i(k)` re-home the
Delsarte LP bound inside the scheme.

## Main results

* `hammingValency_cast` — `v_i = C(n,i)·(q-1)^i` over `ℤ`, with the genuine
  integer `(q-1)` (no truncated subtraction), valid since `q = #F ≥ 1`.
* `hammingValency_eq_krawtchouk_zero` — **valency = Krawtchouk value at `0`**:
  `(v_i : ℤ) = K_i(0)`, the first column of the eigenvalue matrix of the
  Bose–Mesner algebra.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
The valency `v_i = C(n,i)(q-1)^i` cast to `ℤ`, with the genuine integer
difference `(q-1)` (no truncated natural subtraction): valid because `q ≥ 1`.
-/
theorem hammingValency_cast (n i : ℕ) (q : ℕ) (hq : 1 ≤ q) :
    (hammingValency n q i : ℤ) = (n.choose i : ℤ) * ((q : ℤ) - 1) ^ i := by
  unfold hammingValency; rw [ Nat.cast_mul ] ; rw [ Nat.cast_pow ] ; rw [ Nat.cast_sub hq ] ; ring;

/-
**The valencies of the Hamming scheme are the Krawtchouk values at `0`.**
`(v_i : ℤ) = K_i(0) = C(n,i)(q-1)^i`.  This is the first column of the eigenvalue
matrix `P_{i}(k) = K_i(k)` of the Bose–Mesner algebra of `H(n, q)`.
-/
theorem hammingValency_eq_krawtchouk_zero (i : ℕ) :
    (hammingValency (Fintype.card ι) (Fintype.card F) i : ℤ)
      = krawtchouk (Fintype.card F) (Fintype.card ι) i 0 := by
  have := hammingValency_cast ( Fintype.card ι ) i ( Fintype.card F ) ( Fintype.card_pos ) ; simp_all +decide [ hammingValency ] ;
  cases this <;> simp_all +decide [ krawtchouk_eval_zero ]

end CodingTheory