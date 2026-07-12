import Mathlib
import DobbertinLego.Endo

/-!
# The trace / telescope layer over a finite commutative `𝔽_q`-algebra

The concrete development (`DobbertinLego/Frobenius`, `Loop`, `Assembly`) and the
headline `Dobbertin.Lego.equation2_of_equation1` are written over a finite *field*
`F = 𝔽_{2ⁿ}`.  This module carries out the **next step**: it lifts the entire
trace / telescope layer off of fields and onto an *arbitrary finite commutative
`𝔽₂`-algebra* `R` equipped with the Frobenius endomorphism, and it pins down the
one place where field-ness is genuinely used.

## What is an "`𝔽₂`-algebra"?

A commutative ring `R` with `CharP R 2` is precisely a commutative `𝔽₂`-algebra
(the unique ring map `𝔽₂ = ZMod 2 → R` is its structure map).  We take `R` at this
generality — **no field, no domain, no integrality, no finiteness assumption on the
ring itself** — and supply the only genuinely arithmetic input, that the Frobenius
has finite order, as an explicit hypothesis `frobAEndo 1 ^ n = 1` (over the finite
field `𝔽_{2ⁿ}` this is Fermat, `frobAEndo_pow_card_field`).

## The layer, and where field-ness enters

Everything up to and including the raw linearization identity is proved with only
`[CommRing R] [CharP R 2]`:

* `frobA`, `frobAEndo`      — the Frobenius `x ↦ x^{2ʳ}` as a map and as an element
  of `AddMonoid.End R` (additivity is char-2, `add_pow_char_pow`, not field);
* `loopA`, `traceA`, `partialTraceA`, `numeratorSumA` — the paper's objects, now
  over `R`, all instances of the abstract norm element `iterSum`;
* `loopA_telescope`         — the Artin–Schreier telescope (from `iterSum_telescope`);
* `frobA_periodic`, `traceA_fixed`, `traceA_frob_fixed`, `partialTraceA_telescope`
  — periodicity and the "trace is fixed by Frobenius" corollary, all from the
  finite-order hypothesis alone;
* `alg_linearized_mul`      — **the load-bearing identity**
  `x^{2ᵏ} · ℓ(x) = 0`, proved in `R` with no division whatsoever.

Field-ness is then confined to a **single** lemma:

* `alg_linearized_eq_zero`  — cancels `x^{2ᵏ} ≠ 0` to conclude `ℓ(x) = 0`.  This is
  the *only* declaration in the module carrying `[NoZeroDivisors R]`; it is the
  exact spot where the paper "divides by `x^{2ᵏ}`".

`alg_equation2_of_equation1` is the headline over `R`, and
`equation2_of_equation1_of_finField` records that a finite field is one instance,
so the field development is recovered as the `IsDomain` specialization of this
strictly more general statement.
-/

namespace Dobbertin.Lego.Alg

open Finset

/-! ## The Frobenius endomorphism over a commutative `𝔽₂`-algebra -/

variable {R : Type*} [CommRing R] [CharP R 2]

/-- **Frobenius over the algebra.** `frobA r x = x^{2ʳ}`, the `r`-fold squaring map
of the commutative `𝔽₂`-algebra `R`. -/
def frobA (r : ℕ) (x : R) : R := x ^ (2 ^ r)

omit [CharP R 2] in
@[simp] lemma frobA_zero (x : R) : frobA 0 x = x := by simp [frobA]

/-- **Additivity is characteristic `2`, not field-ness.** `(x+y)^{2ʳ} = x^{2ʳ}+y^{2ʳ}`
holds in any commutative ring of characteristic `2` (`add_pow_char_pow`). -/
lemma frobA_add (r : ℕ) (x y : R) : frobA r (x + y) = frobA r x + frobA r y :=
  add_pow_char_pow x y 2 r

omit [CharP R 2] in
/-- Iterates compose: `frobA a (frobA b x) = frobA (a+b) x`. -/
lemma frobA_comp (a b : ℕ) (x : R) : frobA a (frobA b x) = frobA (a + b) x := by
  simp only [frobA]; rw [← pow_mul, ← pow_add]; ring_nf

/-- **Frobenius as an additive endomorphism** `frobAEndo step ∈ AddMonoid.End R`;
its additivity (`frobA_add`) is the bridge to the abstract scaffold
`DobbertinLego/Endo`. -/
def frobAEndo (step : ℕ) : AddMonoid.End R := AddMonoidHom.mk' (frobA step) (frobA_add step)

@[simp] lemma frobAEndo_apply (step : ℕ) (x : R) : frobAEndo step x = frobA step x := rfl

/-- **Iterates are ring powers**: `(frobAEndo step)ʲ x = frobA (j·step) x`. -/
lemma frobAEndo_pow_apply (step j : ℕ) (x : R) :
    (frobAEndo (R := R) step ^ j) x = frobA (j * step) x := by
  induction j with
  | zero => simp [frobA]
  | succ m ih =>
    rw [pow_succ']
    show frobAEndo step ((frobAEndo step ^ m) x) = _
    rw [ih]; simp only [frobAEndo_apply, frobA_comp]; ring_nf

/-! ## The paper's objects as norm elements over `R` -/

/-- The **loop** `loopA step len x = ∑_{j<len} x^{2^{j·step}}` — the abstract norm
element `iterSum` of the Frobenius `frobAEndo step`. -/
def loopA (step len : ℕ) (x : R) : R := iterSum (frobAEndo step) len x

/-- **The Artin–Schreier telescope over `R`**, a specialization of the generic
`iterSum_telescope`:
`frobA step (loopA step len x) + loopA step len x = frobA (len·step) x + x`.
Needs only characteristic `2` (where `−1 = +1`); no field, no finiteness. -/
lemma loopA_telescope (step len : ℕ) (x : R) :
    frobA step (loopA step len x) + loopA step len x = frobA (len * step) x + x := by
  have h := iterSum_telescope (frobAEndo (R := R) step) len x
  rw [frobAEndo_pow_apply, sub_eq_add_neg, sub_eq_add_neg] at h
  simpa [loopA, CharTwo.neg_eq] using h

/-- Absolute **trace** `Tr(x) = ∑_{i<n} x^{2ⁱ}` — the loop at `step = 1`. -/
def traceA (n : ℕ) (x : R) : R := loopA 1 n x

/-- **Partial trace** `P(x) = ∑_{j<k'} x^{2^{jk}}` — the loop at `step = k`. -/
def partialTraceA (k k' : ℕ) (x : R) : R := loopA k k' x

/-- **Numerator sum** `S(x) = frobA k (P(x)) = P(x)^{2ᵏ}`. -/
def numeratorSumA (k k' : ℕ) (x : R) : R := frobA k (loopA k k' x)

/-- `S = P^{2ᵏ}` holds definitionally. -/
lemma numeratorSumA_eq (k k' : ℕ) (x : R) :
    numeratorSumA k k' x = partialTraceA k k' x ^ (2 ^ k) := rfl

/-! ## Consequences of the Frobenius having finite order

The only genuinely arithmetic input to the layer is that the Frobenius has finite
order, `frobAEndo 1 ^ n = 1`.  Everything below is derived from *that hypothesis
alone* — still no field, no domain, no finiteness of `R`. -/

/-- **Periodicity of the exponent.** If `frobAEndo 1 ^ n = 1` then
`frobA r x = frobA (r % n) x`. -/
lemma frobA_periodic {n : ℕ} (hord : frobAEndo (R := R) 1 ^ n = 1) (r : ℕ) (x : R) :
    frobA r x = frobA (r % n) x := by
  have e1 : frobA r x = (frobAEndo (R := R) 1 ^ r) x := by rw [frobAEndo_pow_apply, mul_one]
  have e2 : frobA (r % n) x = (frobAEndo (R := R) 1 ^ (r % n)) x := by
    rw [frobAEndo_pow_apply, mul_one]
  rw [e1, e2]; congr 1
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm]
  rw [pow_add, pow_mul, hord, one_pow, one_mul]

/-- **The trace is fixed by the Frobenius.** From the fixed-point corollary
`iterSum_fixed_of_orderly`: `frobA 1 (Tr x) = Tr x`, i.e. `Tr(x)² = Tr(x)`. -/
lemma traceA_fixed {n : ℕ} (hord : frobAEndo (R := R) 1 ^ n = 1) (x : R) :
    frobA 1 (traceA n x) = traceA n x := by
  have h := iterSum_fixed_of_orderly (frobAEndo (R := R) 1) hord x
  simpa [traceA, loopA, frobAEndo_apply] using h

/-- Every Frobenius power fixes the trace: `frobA k (Tr x) = Tr x`, i.e.
`Tr(x)^{2ᵏ} = Tr(x)`.  (This is what makes `ε = α·Tr(x)` satisfy `ε^{2ᵏ} = ε`
without ever asking `ε ∈ {0,1}`, so field-ness is not needed here.) -/
lemma traceA_frob_fixed {n : ℕ} (hord : frobAEndo (R := R) 1 ^ n = 1) (k : ℕ) (x : R) :
    frobA k (traceA n x) = traceA n x := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hstep : frobA (m + 1) (traceA n x) = frobA 1 (frobA m (traceA n x)) := by
      rw [frobA_comp]; ring_nf
    rw [hstep, ih, traceA_fixed hord]

/-- **Artin–Schreier telescoping of the partial trace over `R`.** With
`frobAEndo 1 ^ n = 1` and `k·k' ≡ 1 (mod n)`, `S(x) + P(x) = x² + x`. -/
lemma partialTraceA_telescope {n k k' : ℕ} (hord : frobAEndo (R := R) 1 ^ n = 1)
    (hkk' : k * k' % n = 1) (x : R) :
    numeratorSumA k k' x + partialTraceA k k' x = x ^ 2 + x := by
  have ht := loopA_telescope (R := R) k k' x
  have hx2 : frobA (k' * k) x = x ^ 2 := by
    rw [frobA_periodic hord, Nat.mul_comm k' k, hkk']; simp [frobA]
  rw [hx2] at ht
  simpa [numeratorSumA, partialTraceA] using ht

/-! ## The linearization: the load-bearing identity, then the single division -/

/-- **The load-bearing identity — no field, no division.** In any commutative
`𝔽₂`-algebra `R`, if
`S = P^{2ᵏ}`, `S + P = x² + x`, `ε^{2ᵏ} = ε`, and `S + ε = c·x^{2ᵏ+1}`, then

```
   x^{2ᵏ} · (c^{2ᵏ} x^{2^{2k}} + x^{2ᵏ} + c x + 1) = 0.
```

Solve for `P`, raise to the `2ᵏ` power (Frobenius additivity + `ε^{2ᵏ}=ε`), cancel
`ε`, and factor out `x^{2ᵏ}`; every remaining term appears an even number of times
and vanishes in characteristic `2`.  Crucially this is an equation *in `R`*: nothing
is divided. -/
lemma alg_linearized_mul (k : ℕ) {c x ε S P : R}
    (hS : S = P ^ (2 ^ k)) (hSP : S + P = x ^ 2 + x)
    (hεfix : ε ^ (2 ^ k) = ε) (hsol : S + ε = c * x ^ (2 ^ k + 1)) :
    x ^ (2 ^ k) * (c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1) = 0 := by
  have hP_sub : P = (x ^ 2 + x) + c * x ^ (2 ^ k + 1) + ε := by grind +ring
  have hS_pow : S = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k)
      + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) + ε := by
    rw [hS, hP_sub, add_pow_char_pow, add_pow_char_pow, add_pow_char_pow, hεfix]
  have h_core : c * x ^ (2 ^ k + 1)
      = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k) + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) := by grind +ring
  have e1 : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ k) * x ^ (2 ^ k) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  have hexp : (2 ^ k + 1) * 2 ^ k = 2 ^ (2 * k) + 2 ^ k := by
    rw [add_mul, one_mul, ← pow_add, two_mul]
  have e2 : (c * x ^ (2 ^ k + 1)) ^ (2 ^ k)
      = c ^ (2 ^ k) * (x ^ (2 ^ (2 * k)) * x ^ (2 ^ k)) := by
    rw [mul_pow, ← pow_mul, hexp, pow_add]
  rw [e1, e2] at h_core
  linear_combination (norm := ring_nf) h_core
  simp [CharTwo.two_eq_zero]

/-- **The one and only place field-ness enters.** Adding `[NoZeroDivisors R]`
(supplied by any integral domain, in particular any field) lets us cancel the
nonzero factor `x^{2ᵏ}` from `alg_linearized_mul` and conclude `ℓ(x) = 0`.  This is
the formal counterpart of the paper's "divide by `x^{2ᵏ}`". -/
lemma alg_linearized_eq_zero [NoZeroDivisors R] (k : ℕ) {c x ε S P : R}
    (hS : S = P ^ (2 ^ k)) (hSP : S + P = x ^ 2 + x)
    (hεfix : ε ^ (2 ^ k) = ε) (hsol : S + ε = c * x ^ (2 ^ k + 1)) (hx : x ≠ 0) :
    c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1 = 0 :=
  (mul_eq_zero.mp (alg_linearized_mul k hS hSP hεfix hsol)).resolve_left (pow_ne_zero _ hx)

/-! ## The headline over `R` -/

/-- **Equation (1)** over `R`: `c · x^{2ᵏ+1} = S(x) + α·Tr(x)`. -/
def equation1A (n k k' α : ℕ) (c x : R) : Prop :=
  c * x ^ (2 ^ k + 1) = numeratorSumA k k' x + (α : R) * traceA n x

/-- The **linearized polynomial** `ℓ(x) = c^{2ᵏ} x^{2^{2k}} + x^{2ᵏ} + c x + 1`. -/
def linearizedA (k : ℕ) (c x : R) : R :=
  c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1

/-- **Step (1) ⟹ (2) over an arbitrary finite commutative `𝔽₂`-algebra that is a
domain.** The trace / telescope layer (`partialTraceA_telescope`, `traceA_frob_fixed`)
supplies the algebraic hypotheses, and `alg_linearized_eq_zero` performs the single
field-dependent division.  The finite-order input is the hypothesis
`frobAEndo 1 ^ n = 1`; over `𝔽_{2ⁿ}` it is Fermat (`frobAEndo_pow_card_field`). -/
theorem alg_equation2_of_equation1 [NoZeroDivisors R] {n k k' α : ℕ}
    (hord : frobAEndo (R := R) 1 ^ n = 1) (hkk' : k * k' % n = 1)
    (hα : α = 0 ∨ α = 1) {c x : R} (hx : x ≠ 0)
    (h : equation1A n k k' α c x) :
    linearizedA k c x = 0 := by
  set ε : R := (α : R) * traceA n x with hε
  have hεfix : ε ^ (2 ^ k) = ε := by
    have hfrob : ε ^ (2 ^ k) = frobA k ε := rfl
    rw [hfrob, hε]
    rcases hα with rfl | rfl
    · simp [frobA, zero_pow (show (2 : ℕ) ^ k ≠ 0 by positivity)]
    · have h1 : ((1 : ℕ) : R) = 1 := by norm_cast
      rw [h1, one_mul, traceA_frob_fixed hord]
  have hS : numeratorSumA k k' x = partialTraceA k k' x ^ (2 ^ k) := numeratorSumA_eq k k' x
  have hSP : numeratorSumA k k' x + partialTraceA k k' x = x ^ 2 + x :=
    partialTraceA_telescope hord hkk' x
  have hsol : numeratorSumA k k' x + ε = c * x ^ (2 ^ k + 1) := h.symm
  exact alg_linearized_eq_zero k hS hSP hεfix hsol hx

/-! ## A finite field is one instance

Over the finite field `𝔽_{2ⁿ}` the finite-order hypothesis is Fermat, so the
field development is recovered as the `IsDomain` specialization of the algebra
headline above. -/

/-- **Fermat supplies the finite-order hypothesis over `𝔽_{2ⁿ}`.**  When
`Fintype.card F = 2ⁿ`, `frobAEndo 1 ^ n = 1`. -/
lemma frobAEndo_pow_card_field {F : Type*} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hn : Fintype.card F = 2 ^ n) : frobAEndo (R := F) 1 ^ n = 1 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [frobAEndo_pow_apply]
  simp only [mul_one, frobA]
  rw [← hn, FiniteField.pow_card]; rfl

/-- **The field case as a specialization.** Over `F = 𝔽_{2ⁿ}` the algebra headline
`alg_equation2_of_equation1` applies verbatim, with `frobAEndo_pow_card_field`
discharging the finite-order hypothesis and `IsDomain`/field-ness discharging the
single division.  This shows the field development is the `IsDomain` instance of the
strictly more general algebra statement. -/
theorem equation2_of_equation1_of_finField {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n k k' α : ℕ} (hn : Fintype.card F = 2 ^ n) (hkk' : k * k' % n = 1)
    (hα : α = 0 ∨ α = 1) {c x : F} (hx : x ≠ 0)
    (h : equation1A n k k' α c x) :
    linearizedA k c x = 0 :=
  alg_equation2_of_equation1 (frobAEndo_pow_card_field hn) hkk' hα hx h

end Dobbertin.Lego.Alg
