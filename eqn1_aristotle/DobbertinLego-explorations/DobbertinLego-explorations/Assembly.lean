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

/-- **The trace is a bit.**  On `𝔽_{2ⁿ}`, `Tr(x) = 0 ∨ Tr(x) = 1`.  The trace is
the norm element of the finite-order Frobenius `frobEndo 1` (order `n`), so the
abstract fixed-point corollary `iterSum_fixed_of_orderly` gives `Tr² = Tr`
(`Tr` lands in the fixed subgroup `𝔽₂`), whence `Tr ∈ {0,1}`. -/
lemma trace_isBit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    trace n x = 0 ∨ trace n x = 1 := by
  unfold trace
  -- the Frobenius has finite order `n`: `(frobEndo 1)^n = frobEndo n = 1`
  have horder : (frobEndo (F := F) 1) ^ n = 1 := by
    rw [frobEndo_pow, Nat.mul_one]; exact frobEndo_pow_card hn
  -- the norm element is fixed by Frobenius: `Tr² = Tr`
  have hfix := iterSum_fixed_of_orderly (frobEndo (F := F) 1) horder x
  rw [← loop_eq_iterSum, frobEndo_apply] at hfix
  have hsq : loop 1 n x ^ 2 = loop 1 n x := by simpa [frob] using hfix
  have h : loop 1 n x * (loop 1 n x - 1) = 0 := by linear_combination hsq
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
