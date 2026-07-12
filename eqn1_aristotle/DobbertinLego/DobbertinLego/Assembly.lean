import Mathlib
import DobbertinLego.Loop

/-!
# Assembly — the paper's objects as thin wrappers over the two bricks

Every definition of the paper's step `(1) ⟹ (2)` is now a one-liner over the two
LEGO bricks **F** (`frob`) and **L** (`loop`):

| paper object        | LEGO expression                    |
|---------------------|------------------------------------|
| trace `Tr(x)`       | `loop 1 n x`                       |
| partial trace `P(x)`| `loop k k' x`                      |
| numerator sum `S(x)`| `frob k (loop k k' x)`             |

Two facts of the paper drop out of the single telescope connective
`loop_telescope`:

* `trace_isBit` — `Tr(x) ∈ {0,1}` (telescope at `step = 1`, `len = n`);
* `partialTrace_telescope` — `S(x) + P(x) = x² + x` (telescope at `step = k`,
  `len = k'`, using `k·k' ≡ 1 (mod n)`).

And `numeratorSum_eq_frob_partialTrace` (`S = P^{2^k}`) holds **by definition**.
-/

namespace Dobbertin.Lego

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- Absolute **trace** `Tr(x) = ∑_{i<n} x^{2^i}` — gadget **L** at `step = 1`. -/
def trace (n : ℕ) (x : F) : F := loop 1 n x

/-- **Partial trace** `P(x) = ∑_{j<k'} x^{2^{jk}}` — gadget **L** at `step = k`. -/
def partialTrace (k k' : ℕ) (x : F) : F := loop k k' x

/-- **Numerator sum** `S(x) = ∑_{i=1}^{k'} x^{2^{ik}}` — the Frobenius-`2^k`
image of the partial trace, `S = frob k P`. -/
def numeratorSum (k k' : ℕ) (x : F) : F := frob k (loop k k' x)

/-- **Equation (1)** of the paper, cleared of denominators:
`c · x^{2^k+1} = S(x) + α · Tr(x)`. -/
def equation1 (n k k' α : ℕ) (c x : F) : Prop :=
  c * x ^ (2 ^ k + 1) = numeratorSum k k' x + (α : F) * trace n x

/-- The **linearized polynomial** `ℓ(x) = c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1`
of equation (2). -/
def linearized (k : ℕ) (c x : F) : F :=
  c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1

omit [Fintype F] [CharP F 2] in
/-- `S = P^{2^k}`: holds definitionally (`numeratorSum = frob k (partialTrace)`). -/
lemma numeratorSum_eq_frob_partialTrace (k k' : ℕ) (x : F) :
    numeratorSum k k' x = partialTrace k k' x ^ (2 ^ k) := rfl

/-- **The trace is a bit.**  On `𝔽_{2ⁿ}`, `Tr(x) = 0 ∨ Tr(x) = 1`.  One use of
the telescope connective at `step = 1`, `len = n`: `Tr² + Tr = frob n x + x = 0`,
so `Tr² = Tr`. -/
lemma trace_isBit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    trace n x = 0 ∨ trace n x = 1 := by
  unfold trace
  have ht := loop_telescope (F := F) 1 n x
  rw [Nat.mul_one, frob_card hn] at ht
  have hf : frob 1 (loop 1 n x) = loop 1 n x ^ 2 := by simp [frob]
  rw [hf, CharTwo.add_self_eq_zero, CharTwo.add_eq_zero] at ht
  have h : loop 1 n x * (loop 1 n x - 1) = 0 := by linear_combination ht
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

/-- **Artin–Schreier telescoping** of the partial trace.  On `𝔽_{2ⁿ}` with
`k·k' ≡ 1 (mod n)`, `S(x) + P(x) = x² + x`.  One use of the telescope connective
at `step = k`, `len = k'`, collapsing `frob (k'·k) x` to `x²` by periodicity. -/
lemma partialTrace_telescope {n k k' : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) (x : F) :
    numeratorSum k k' x + partialTrace k k' x = x ^ 2 + x := by
  have ht := loop_telescope (F := F) k k' x
  have hx2 : frob (k' * k) x = x ^ 2 := by
    rw [frob_periodic hn, Nat.mul_comm k' k, hkk']; simp [frob]
  rw [hx2] at ht
  simpa [numeratorSum, partialTrace] using ht

end Dobbertin.Lego
