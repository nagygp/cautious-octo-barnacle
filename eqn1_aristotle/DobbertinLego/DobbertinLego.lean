import Mathlib
import DobbertinLego.Frobenius
import DobbertinLego.Loop
import DobbertinLego.Assembly

/-!
# Dobbertin, Theorem 1 — step `(1) ⟹ (2)`, built from two LEGO bricks

A self-contained, minimal formalisation of the opening step of Theorem 1 in

> H. Dobbertin, *Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets*, NATO Sci. Ser. C **542**, 1999, pp. 133–158,

rebuilt so that the **entire** proof snaps together from just two primitive
building blocks and one connective:

* **Gadget F** — the Frobenius `frob r x = x^{2^r}` (`DobbertinLego/Frobenius`);
* **Gadget L** — the linearized loop `loop step len x = ∑_{j<len} x^{2^{j·step}}`
  (`DobbertinLego/Loop`);
* the **telescope connective** `loop_telescope`, the sole identity wiring L to F.

From these, `trace`, `partialTrace`, `numeratorSum` are one-line wrappers
(`DobbertinLego/Assembly`), the paper's two auxiliary facts (`trace_isBit`,
`partialTrace_telescope`) are two uses of the connective, and this file glues
them into the headline.

## What this file adds

* `linearized_eq_zero_of_solution` — the linearization step ("add the `2^k`-th
  power of (1) to itself and divide by `x^{2^k}`");
* `equation2_of_equation1` — the headline `(1) ⟹ (2)`.

## Note on `x ≠ 0`

The hypothesis `x ≠ 0` is genuinely required: at `x = 0` the cleared equation (1)
holds vacuously (`0 = 0`), yet `ℓ(0) = 1 ≠ 0`.
-/

namespace Dobbertin.Lego

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- **The linearization step.**  For `x ≠ 0`, a bit `ε ∈ {0,1}`, and
`k·k' ≡ 1 (mod n)`, the working equation `S(x) + ε = c·x^{2^k+1}` implies
`ℓ(x) = c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1 = 0`.

Mechanism: solve for `P` using `S = P^{2^k}` (definitional) and the telescope
`S + P = x² + x`; raise to the `2^k` power (Frobenius is additive, `ε^{2^k}=ε`);
cancel `ε` and divide by `x^{2^k} ≠ 0`. -/
lemma linearized_eq_zero_of_solution {n k k' : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) {ε : F} (hε : ε = 0 ∨ ε = 1) {c x : F} (hx : x ≠ 0)
    (hsol : numeratorSum k k' x + ε = c * x ^ (2 ^ k + 1)) :
    linearized k c x = 0 := by
  unfold linearized
  set P := partialTrace k k' x with hPdef
  set S := numeratorSum k k' x with hSdef
  have hS : S = P ^ (2 ^ k) := numeratorSum_eq_frob_partialTrace k k' x
  have hP : S + P = x ^ 2 + x := partialTrace_telescope hn hkk' x
  -- `ε^{2^k} = ε` because `ε` is a bit
  have hεpow : ε ^ (2 ^ k) = ε := by
    rcases hε with rfl | rfl <;> simp [zero_pow (show (2 : ℕ) ^ k ≠ 0 by positivity)]
  -- solve equation (1) for `P`
  have hP_sub : P = (x ^ 2 + x) + c * x ^ (2 ^ k + 1) + ε := by
    rw [hS] at hP; grind +ring
  -- raise to the `2^k` power (Frobenius is additive), giving `S` in closed form
  have hS_pow : S = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k)
      + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) + ε := by
    rw [hS, hP_sub, add_pow_char_pow, add_pow_char_pow, add_pow_char_pow, hεpow]
  -- cancel `ε` to isolate the core relation between the powers of `x`
  have h_core : c * x ^ (2 ^ k + 1)
      = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k) + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) := by
    grind +ring
  -- divide by `x^{2^k} ≠ 0`
  apply mul_left_cancel₀ (pow_ne_zero (2 ^ k) hx)
  rw [mul_zero]
  -- reduce the compound exponents to the atoms `x^{2^k}` and `x^{2^{2k}}`
  have e1 : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ k) * x ^ (2 ^ k) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  have hexp : (2 ^ k + 1) * 2 ^ k = 2 ^ (2 * k) + 2 ^ k := by
    rw [add_mul, one_mul, ← pow_add, two_mul]
  have e2 : (c * x ^ (2 ^ k + 1)) ^ (2 ^ k)
      = c ^ (2 ^ k) * (x ^ (2 ^ (2 * k)) * x ^ (2 ^ k)) := by
    rw [mul_pow, ← pow_mul, hexp, pow_add]
  rw [e1, e2] at h_core
  -- after substitution every term appears twice, so it vanishes in characteristic 2
  linear_combination (norm := ring_nf) h_core
  simp [CharTwo.two_eq_zero]

/-- **Step (1) ⟹ (2) of Dobbertin's Theorem 1.**  Over `F = 𝔽_{2ⁿ}` with
`k·k' ≡ 1 (mod n)`, for `α ∈ {0,1}` and every nonzero `x`, equation (1) implies
the linearized equation (2) `ℓ(x) = 0`. -/
theorem equation2_of_equation1 {n k k' α : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) (hα : α = 0 ∨ α = 1) {c x : F} (hx : x ≠ 0)
    (h : equation1 n k k' α c x) :
    linearized k c x = 0 := by
  -- collapse the trace term `α · Tr(x)` to a bit `ε ∈ {0,1}`
  have hbit : (α : F) * trace n x = 0 ∨ (α : F) * trace n x = 1 := by
    have hαcast : (α : F) = 0 ∨ (α : F) = 1 := by rcases hα with rfl | rfl <;> simp
    rcases hαcast with h0 | h1
    · exact Or.inl (by rw [h0, zero_mul])
    · rw [h1, one_mul]; exact trace_isBit hn x
  -- apply the linearization step with `ε = α · Tr(x)`
  exact linearized_eq_zero_of_solution hn hkk' hbit hx h.symm

end Dobbertin.Lego
