import Mathlib
import RequestProject.Foundations.AdjointTransfer.TraceNondeg

/-!
# Layer T2: Adjoint Linear Maps via Trace Duality

Given the nondegenerate bilinear form `B(x, y) = Tr_n(x · y)` on GF(2^n),
we establish the trace-adjoint properties for Frobenius powers and the
partial trace map.

## Mathematical content

- **Adjoint of Frobenius**: `Tr_n(x^{2^j} · y) = Tr_n(x · y^{2^{n-j}})`.
- **Adjoint of partial trace**: `Tr_n(S_k(x) · y) = Tr_n(x · S_k*(y))`
  where `S_k*(y) = ∑_{i=0}^{k-1} y^{2^{n-i}}`.
- **S_k* equals S_k composed with Frobenius power**: `S_k*(y) = S_k(y)^{2^{n-k}}`.

## DAG Dependencies

- `TraceNondeg` (trace nondegeneracy theorem, `Tr_n` definition)

## Downstream consumers

- `AdjointTransfer` (Lemma 3.1 uses adjoint explicitly)
- `MCMBridge` (needs adjoint of S_k)
-/

namespace AdjointTransfer

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Additive (GF(2)-linear) maps on F -/

/-- An additive map `L : F → F` is GF(2)-linear iff `L(x + y) = L(x) + L(y)`.
    In char 2 this is the same as being an additive group homomorphism. -/
structure GF2Linear (F : Type*) [Field F] [CharP F 2] where
  toFun : F → F
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

instance : CoeFun (GF2Linear F) (fun _ => F → F) := ⟨GF2Linear.toFun⟩

/-- The Frobenius power map `x ↦ x^{2^j}` as a GF2Linear map. -/
def frobPow (j : ℕ) : GF2Linear F where
  toFun x := x ^ (2 ^ j)
  map_add' x y := by rw [add_pow_char_pow (p := 2)]

/-- The partial trace `S_k(x) = ∑_{i=0}^{k-1} x^{2^i}` as a GF2Linear map. -/
def partialTrace (k : ℕ) : GF2Linear F where
  toFun x := ∑ i ∈ Finset.range k, x ^ (2 ^ i)
  map_add' x y := by
    simp only [← Finset.sum_add_distrib]
    congr 1; ext i
    rw [add_pow_char_pow (p := 2)]

/-! ## Frobenius adjoint property -/

/-
**Adjoint of Frobenius**: `Tr_n(x^{2^j} · y) = Tr_n(x · y^{2^{n-j}})` for `j ≤ n`.

    **Proof**: By Frobenius invariance, `Tr_n(x · y^{2^{n-j}})
    = Tr_n((x · y^{2^{n-j}})^{2^j}) = Tr_n(x^{2^j} · y^{2^n}) = Tr_n(x^{2^j} · y)`
    since `y^{2^n} = y`.
-/
lemma frobPow_adjoint_spec {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n)
    (j : ℕ) (hj : j ≤ n) (x y : F) :
    Tr_n n (x ^ (2 ^ j) * y) = Tr_n n (x * y ^ (2 ^ (n - j))) := by
  convert Tr_n_frob_pow hn ( x * y ^ 2 ^ ( n - j ) ) j using 1 ; ring;
  rw [ ← pow_add, add_tsub_cancel_of_le hj ];
  rw [ ← hn, FiniteField.pow_card ]

/-! ## Partial trace adjoint property -/

/-
The adjoint of `S_k` is `S_k*(y) = ∑_{i=0}^{k-1} y^{2^{n-i}}`.

    Follows from summing frobPow_adjoint_spec over `i = 0, ..., k-1`.
-/
lemma partialTrace_adjoint_spec {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n)
    (k : ℕ) (hk : k ≤ n) (x y : F) :
    Tr_n n ((partialTrace k : GF2Linear F) x * y) =
    Tr_n n (x * ∑ i ∈ Finset.range k, y ^ (2 ^ (n - i))) := by
  unfold partialTrace;
  simp +decide only [mul_comm, Finset.mul_sum _ _ _];
  induction' k with k ih;
  · rfl;
  · simp_all +decide [ Finset.sum_range_succ, Tr_n_add ];
    rw [ ih hk.le, mul_comm ];
    rw [ frobPow_adjoint_spec hn hn_pos k hk.le ]

/-! ## S_k* as Frobenius composition of S_k -/

/-- `S_k*(y) = ∑_{i=0}^{k-1} y^{2^{n-i}}` equals `S_k(y)^{2^{n-k}}`.

    **Proof**: `(∑_{i<k} y^{2^i})^{2^{n-k}} = ∑_{i<k} y^{2^{i+n-k}}`
    by char 2 linearity. Reindexing and using `y^{2^n} = y` gives
    `∑_{i<k} y^{2^{n-(k-1-i)}} = ∑_{i<k} y^{2^{n-i}}`. -/
lemma adjoint_partialTrace_eq_frob {n k : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k ≤ n) (y : F) :
    (∑ i ∈ Finset.range k, y ^ (2 ^ (n - i))) =
    (∑ i ∈ Finset.range k, y ^ (2 ^ i)) ^ (2 ^ (n - k)) := by
  sorry  -- T2.adjoint_partialTrace_eq_frob

/-! ## Composition of GF2Linear maps -/

/-- Composition of GF2Linear maps. -/
def GF2Linear.comp (L M : GF2Linear F) : GF2Linear F where
  toFun x := L (M x)
  map_add' x y := by rw [M.map_add', L.map_add']

/-! ## The "x ↦ L(x) · x^a" combined map -/

/-- The combined map `x ↦ L(x) · x^a` for GF2Linear `L` and exponent `a`. -/
def combinedMap (L : GF2Linear F) (a : ℕ) (x : F) : F := L x * x ^ a

/-- The combined map sends nonzero to nonzero when L(x) ≠ 0. -/
lemma combinedMap_ne_zero (L : GF2Linear F) (a : ℕ) {x : F} (hx : x ≠ 0)
    (hL : L x ≠ 0) : combinedMap L a x ≠ 0 :=
  mul_ne_zero hL (pow_ne_zero _ hx)

end AdjointTransfer