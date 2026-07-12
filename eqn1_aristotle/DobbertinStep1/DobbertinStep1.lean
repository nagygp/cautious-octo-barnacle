import Mathlib
import DobbertinStep1.Defs
import DobbertinStep1.Frobenius
import DobbertinStep1.Trace
import DobbertinStep1.Telescope
import DobbertinStep1.Linearize

/-!
# Dobbertin, Theorem 1 — the first step `(1) ⟹ (2)` (MVP)

A self-contained, minimal formalisation of the opening step of the proof of
Theorem 1 in

> H. Dobbertin, *Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets*, NATO Sci. Ser. C **542**, 1999, pp. 133–158.

Dobbertin's text:

> "Adding the `2^k`-th power of this equation to itself we get … and consequently
> `ℓ(x) = c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1 = 0`."   (equation (2))

Over `F = 𝔽_{2ⁿ}`, this module proves that equation (1)

```
   c · x^{2^k+1} = ∑_{i=1}^{k'} x^{2^{ik}} + α · Tr(x)                (1)
```

implies equation (2) `ℓ(x) = 0`, for every nonzero `x` and every `α ∈ {0,1}`.

## Structure

| module | contents |
|--------|----------|
| `Defs`       | definitions: `trace`, `numeratorSum`, `partialTrace`, `equation1`, `linearized` |
| `Frobenius`  | `pow_two_pow_mod` — Frobenius periodicity `x^{2^r} = x^{2^{r mod n}}` |
| `Trace`      | `trace_eq_zero_or_one` — the trace is a bit (the "= 0 or 1" input) |
| `Telescope`  | `partialTrace_telescope` — the Artin–Schreier telescoping `P^{2^k}+P = x²+x` |
| `Linearize`  | `linearized_eq_zero_of_solution` — the working equation ⟹ `ℓ(x) = 0` |
| `DobbertinStep1` | the headline `equation2_of_equation1` |

## Note on `x ≠ 0`

The hypothesis `x ≠ 0` is genuinely required: at `x = 0` the cleared equation (1)
holds vacuously (`0 = 0`), yet `ℓ(0) = 1 ≠ 0`.  This matches Dobbertin, who works
with the nonzero solutions of `q_α(x) = c`.
-/

namespace Dobbertin.Step1

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

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
    · rw [h1, one_mul]; exact trace_eq_zero_or_one hn x
  -- apply the linearized-equation lemma with `ε = α · Tr(x)`
  exact linearized_eq_zero_of_solution hn hkk' hbit hx h.symm

end Dobbertin.Step1
