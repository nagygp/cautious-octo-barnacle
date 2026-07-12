# Audit — `DobbertinStep1` modules

**Question.** Is the `DobbertinStep1` development true end-to-end and faithful to
the mathematics of Dobbertin's paper (*Kasami Power Functions, Permutation
Polynomials and Cyclic Difference Sets*, 1999), Theorem 1, first step (1) ⟹ (2)?

**Verdict.** Yes. The library builds, is `sorry`/`axiom`-free, the headline
theorem depends only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`, and every definition and lemma matches the paper's text. The one
subtlety (the `x ≠ 0` hypothesis) is genuine, correctly handled, and documented.

## 1. Mechanical status

* `lake build` succeeds (all modules compile).
* No `sorry`, `admit`, or `axiom` anywhere in `DobbertinStep1/` or
  `DobbertinStep1.lean`.
* `#print axioms Dobbertin.Step1.equation2_of_equation1` = `propext`,
  `Classical.choice`, `Quot.sound` — no custom/non-standard axioms.

## 2. Faithfulness of the definitions (paper ↔ Lean)

The paper states equations (1) and (2) verbatim (p. 136):

> equation (1): `c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`
> equation (2): `ℓ(x) = c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x + 1 = 0`

| Paper | Lean (`Defs.lean`) | Match |
|-------|--------------------|-------|
| `Tr(x) = Σ_{i<n} x^{2^i}` (absolute trace onto 𝔽₂) | `trace n x = ∑ i ∈ range n, x^(2^i)` | ✓ |
| `Σ_{i=1}^{k'} x^{2^{ik}}` | `numeratorSum k k' x = ∑ i ∈ Icc 1 k', x^(2^(i*k))` | ✓ |
| eqn (1) (cleared) | `equation1 : c*x^(2^k+1) = numeratorSum + (α)*trace` | ✓ |
| `ℓ(x)` of eqn (2) | `linearized : c^(2^k)*x^(2^(2*k)) + x^(2^k) + c*x + 1` | ✓ |
| `k' ≡ 1/k (mod n)`, i.e. `k·k' ≡ 1 (mod n)` | hypothesis `k*k' % n = 1` | ✓ |
| `Tr(x) ∈ 𝔽₂` | `trace_eq_zero_or_one : trace = 0 ∨ trace = 1` | ✓ |

The auxiliary `partialTrace k k' x = ∑_{j<k'} x^{2^{jk}}` is an internal device
(not in the paper) satisfying `numeratorSum = partialTrace^{2^k}`; it is only used
to organise the telescoping and does not alter the statement.

## 3. Faithfulness of the derivation (1) ⟹ (2)

The paper's one-line argument is "add the `2^k`-th power of (1) to itself, then
divide by `x^{2^k}`". Expanded, this is exactly what the Lean proof does:

1. `2^k`-power of (1) (char-2 Frobenius is additive; `α^{2^k}=α`,
   `Tr(x)^{2^k}=Tr(x)`):
   `c^{2^k} x^{2^{2k}+2^k} = Σ_{i=2}^{k'+1} x^{2^{ik}} + α·Tr(x)`.
2. Adding to (1), the middle sum telescopes (terms `i=2..k'` cancel in char 2),
   the `α·Tr(x)` terms cancel, leaving
   `c x^{2^k+1} + c^{2^k} x^{2^{2k}+2^k} = x^{2^k} + x^{2^{(k'+1)k}}`.
3. `k'k ≡ 1 (mod n)` ⇒ `x^{2^{k'k}} = x^2` ⇒ `x^{2^{(k'+1)k}} = x^{2^{k+1}}`.
4. Divide by `x^{2^k}` (needs `x ≠ 0`): `c x + c^{2^k} x^{2^{2k}} = 1 + x^{2^k}`,
   i.e. `ℓ(x) = 0`.

In Lean this is realised through:
* `Frobenius.pow_two_pow_mod` — `x^{2^r}=x^{2^{r mod n}}` (step 3).
* `Trace.trace_eq_zero_or_one` — trace is a bit, so `α·Tr(x)=ε∈{0,1}` and
  `ε^{2^k}=ε` (step 1).
* `Telescope.numeratorSum_eq_partialTrace_frob` + `partialTrace_telescope` —
  the telescoping (`P^{2^k}+P = x²+x`) packaging steps 1–3.
* `Linearize.linearized_eq_zero_of_solution` — solves for `P`, re-raises to the
  `2^k` power, cancels `ε`, and divides by `x^{2^k}` (step 4).

Each step was re-derived by hand and agrees with the machine proof.

## 4. The `x ≠ 0` hypothesis is correct, not a defect

Equation (1) is the *denominator-cleared* form of `q_α(x)=c`; clearing
`x^{2^k+1}` introduces the spurious root `x=0` (both sides are `0`). But
`ℓ(0) = 1 ≠ 0`, so the implication (1) ⟹ (2) genuinely fails at `x=0`. The
paper's "divide by `x^{2^k}`" silently assumes `x ≠ 0`, exactly the Lean
hypothesis. This is faithful and is documented in the module docstrings.

## 5. Hypotheses are minimal and honest

The paper's Theorem 1 also assumes `gcd(k,n)=1`, `k<n`, and the parity condition
`k'+αn ≡ 1 (mod 2)`. None of these is needed for the *first step* (1) ⟹ (2):
the parity condition is used later (uniqueness/root counting), and `gcd(k,n)=1`,
`k<n` are subsumed by the direct hypothesis `k·k' % n = 1`. The formalization
correctly omits the unused hypotheses rather than carrying them as decoration.
The statement is not weakened or vacuous: `equation1` is a real equality between
field elements and the conclusion `linearized k c x = 0` is the paper's eqn (2).

## Conclusion

`DobbertinStep1` is a correct, complete, and faithful formalisation of the first
step (1) ⟹ (2) of Dobbertin's Theorem 1. No gaps, no cheats, no non-standard
axioms.
