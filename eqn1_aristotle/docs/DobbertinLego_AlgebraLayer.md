# The trace/telescope layer over a finite commutative 𝔽₂-algebra

`DobbertinLego/AlgebraLayer.lean` carries out the "next step" of the refactor: it
states the whole trace/telescope layer of Dobbertin's step (1) ⟹ (2) over an
**arbitrary finite commutative 𝔽₂-algebra** `R` (a commutative ring with
`CharP R 2`), and confines field-ness to a single division step.

## Setting

* Ring generality: `variable {R : Type*} [CommRing R] [CharP R 2]`.
  A commutative ring of characteristic 2 is exactly a commutative 𝔽₂-algebra
  (the structure map is the unique `ZMod 2 → R`). **No field, no domain, no
  integrality, no finiteness of `R`.**
* The only genuinely arithmetic input — that the Frobenius has finite order — is an
  explicit hypothesis `frobAEndo 1 ^ n = 1`. Over the finite field `𝔽_{2ⁿ}` this is
  Fermat (`frobAEndo_pow_card_field`).

## What is proved with only `[CommRing R] [CharP R 2]`

| declaration | statement |
|---|---|
| `frobA`, `frobAEndo` | Frobenius `x ↦ x^{2ʳ}` as a map / additive endomorphism |
| `frobA_add` | additivity (char 2, `add_pow_char_pow`) — not field-ness |
| `loopA`, `traceA`, `partialTraceA`, `numeratorSumA` | the paper's objects as `iterSum` norm elements |
| `loopA_telescope` | Artin–Schreier telescope (from `iterSum_telescope`) |
| `frobA_periodic` | exponent periodicity, from `frobAEndo 1 ^ n = 1` |
| `traceA_fixed`, `traceA_frob_fixed` | the trace is fixed by Frobenius: `Tr(x)^{2ᵏ} = Tr(x)` |
| `partialTraceA_telescope` | `S(x) + P(x) = x² + x` |
| `alg_linearized_mul` | **`x^{2ᵏ} · ℓ(x) = 0`** — the load-bearing identity, no division |

Note in particular `traceA_frob_fixed`: it gives `ε^{2ᵏ} = ε` for `ε = α·Tr(x)`
*without* needing `ε ∈ {0,1}`, so the reduction "trace is a bit" — which does need
field-ness — is never used in the linearization.

## Where field-ness enters — exactly one place

`[NoZeroDivisors R]` (supplied by any integral domain, in particular any field)
appears in exactly one mathematically load-bearing lemma:

* **`alg_linearized_eq_zero`** — cancels the nonzero factor `x^{2ᵏ}` from
  `alg_linearized_mul` to conclude `ℓ(x) = 0`. This is the formal counterpart of the
  paper's "divide by `x^{2ᵏ}`".

`alg_equation2_of_equation1` is the headline over `R`; it merely threads that one
lemma. `equation2_of_equation1_of_finField` records that a finite field is one
instance (Fermat discharges the finite-order hypothesis), so the original field
development is recovered as the `IsDomain` specialization of this strictly more
general statement.

## Soundness

The module is `sorry`-free; `alg_linearized_mul`, `alg_equation2_of_equation1`, and
`equation2_of_equation1_of_finField` depend only on `propext`, `Classical.choice`,
`Quot.sound`.
