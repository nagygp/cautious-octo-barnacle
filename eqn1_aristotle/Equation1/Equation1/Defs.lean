import Mathlib

/-!
# Equation (1) MVP — pure definitions (engine-free)

The elementary definitions used to state the opening of Dobbertin's Theorem 1
and its equation (1).  Everything here is a plain definition depending only on
`Mathlib`; none of the finite-field engine is required.

* `Tr`      — the absolute trace `Tr(x) = ∑_{i<n} x^{2^i}`;
* `qKasami` — the generalized Kasami polynomial `q_α` (with the `0/0 = 0`
  convention, so the denominator `x^{2^k+1}` is realised as the power
  `x^{(2ⁿ−1)−(2^k+1)}`);
* `eqn1`    — equation (1), the equation `q_α(x) = c` cleared of denominators;
* `ell`, `ell0`, `Qmap` — the auxiliary polynomials of equation (2).
-/

namespace Dobbertin1999.Paper

open scoped BigOperators
open Finset

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

/-- The absolute **trace** `Tr : 𝔽_{2ⁿ} → 𝔽₂ ⊆ L`, `Tr(x) = ∑_{i<n} x^{2^i}`. -/
def Tr (n : ℕ) (x : L) : L := ∑ i ∈ Finset.range n, x ^ (2 ^ i)

/-- The **generalized Kasami polynomial** `q_α`, as a genuine function on
`L = 𝔽_{2ⁿ}` (with `0/0 = 0`):
`q_α(z) = (Σ_{i=1}^{k'} z^{2^{ik}} + α·Tr(z)) · z^{(2ⁿ−1)−(2^k+1)}`. -/
def qKasami (n k k' : ℕ) (α : ℕ) (z : L) : L :=
  ((∑ i ∈ Finset.Icc 1 k', z ^ (2 ^ (i * k))) + (α : L) * Tr n z)
    * z ^ (2 ^ n - 1 - (2 ^ k + 1))

/-- Equation (1): the equation `q_α(x) = c` cleared of denominators,
`c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`. -/
def eqn1 (n k k' : ℕ) (α : ℕ) (c x : L) : Prop :=
  c * x ^ (2 ^ k + 1) = (∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))) + (α : L) * Tr n x

/-- The linearized polynomial `ℓ(x) = c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x + 1` of
equation (2), obtained by adding to (1) its `2^k`-th power. -/
def ell (k : ℕ) (c x : L) : L :=
  c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1

/-- The homogeneous part `ℓ₀(x) = ℓ(x) + 1` of (2). -/
def ell0 (k : ℕ) (c x : L) : L := ell (L := L) k c x + 1

/-- The quadratic-type map `Q(x) = c·x^{2^k} + γ²·x + γ` used in Case 2. -/
def Qmap (k : ℕ) (c γ x : L) : L := c * x ^ (2 ^ k) + γ ^ 2 * x + γ

end Dobbertin1999.Paper
