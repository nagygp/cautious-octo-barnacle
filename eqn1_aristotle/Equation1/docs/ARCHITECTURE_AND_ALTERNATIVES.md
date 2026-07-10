# Dobbertin Theorem 1 — Equation (1) & the step (1) ⟹ (2)

Verification report, dependency architecture, and alternative formalisation paths
for the `Dobbertin1999MVP.Equation1.*` library.

Reference: H. Dobbertin, *Kasami Power Functions, Permutation Polynomials and
Cyclic Difference Sets*, pp. 135–136 (Theorem 1).

---

## 1. Verification status (end-to-end)

The library **builds cleanly** and the requested results are **complete, sorry-free,
and rest only on the standard axioms** `propext`, `Classical.choice`, `Quot.sound`
(checked with `#print axioms` / `lean_verify`):

| Paper object | Lean declaration (`Dobbertin1999.Paper`) | status |
|---|---|---|
| Equation (1), `c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)` | `def eqn1` | faithful definition |
| **(1) ⟹ (2)** (add the `2^k`-th power) → `ℓ(x)=0` | `theorem eqn2_of_eqn1` | ✅ proved |
| Theorem 1 statement (`q_α` a permutation ⇔ `k'+α·n ≡ 1 (mod 2)`) | `theorem theorem_1` | ✅ proved |
| "only if" at the value `q_α(1)` | `qKasami_one_eq_zero_iff` (in `Setup`) | ✅ proved |
| Case 1 (`ℓ` has a unique root when `c ≠ γ^{2^k+1}+γ`) | `theorem_1_case1` | ✅ proved |
| Case 2 factorisation `ℓ = Q^{2^k} + f·Q` | `ell_eq_Q` | ✅ proved |
| Case 2 (unique nonzero solution of (1)) | `theorem_1_case2` | ✅ proved |

> **Note on the build.** The delivered sources imported modules under the prefix
> `Dobbertin1999MVP.Equation1.*` but the files were laid out under `Equation1/`,
> so the project did not compile as shipped. The files were relocated to
> `Dobbertin1999MVP/Equation1/` (matching the imports and the `README`) and the
> `lakefile.toml` library target was updated accordingly. No proof content was
> changed.

### 1.1 Faithfulness to the paper, and the two documented corrections

The definitions transcribe the paper literally (trace `Tr(x)=∑_{i<n} x^{2^i}`;
`q_α` realised with the `1/z^{2^k+1} ↦ z^{(2ⁿ-1)-(2^k+1)}` convention exactly as
the paper prescribes; `ℓ(x)=c^{2^k}x^{2^{2k}}+x^{2^k}+cx+1`).

Two internal statements were minimally strengthened with an `x ≠ 0` side
condition, and the reason is documented in-file next to each:

* **`eqn2_of_eqn1`.** At `x = 0` the *cleared* equation (1) reads `0 = 0` and is
  vacuously true, yet `ℓ(0) = 1 ≠ 0`. So "(1) ⟹ ℓ=0" needs `x ≠ 0`. This is an
  artefact of clearing denominators; the paper argues about `q_α(x)=c` where the
  `x=0` case is handled separately by `q_α(0)=0`.
* **`theorem_1_case2`.** `x = 0` always satisfies the cleared `eqn1`, so counting
  *all* solutions never gives 1. The paper's "exactly one of the roots solves (1)"
  is faithfully the count of **nonzero** solutions (requiring `c ≠ 0`, i.e. `γ ≠ 1`).

These are the honest, minimal adjustments needed because the Lean statement works
with the polynomial-cleared form `eqn1` rather than the rational identity `q_α(x)=c`.

---

## 2. Dependency architecture (Mathlib → headline results)

Eight modules in four layers. Arrows are `import`/`uses` edges.

```
                         ┌─────────────┐
                         │   Mathlib   │  (finite fields, char 2, Nat gcd, ncard)
                         └──────┬──────┘
              ┌─────────────────┼──────────────────────────┐
              ▼                 ▼                           ▼
        ┌──────────┐   ┌───────────────────────┐    (used directly by
        │  Defs    │   │  FiniteFieldPrereqs    │     every layer below)
        │ Tr,qKasami│  │  (DempwolffMueller)    │
        │ eqn1,ell │   │  frob_*, pow_field_bij,│
        │ ell0,Qmap│   │  truncTrace(+add,sq)   │
        └────┬─────┘   └───────────┬───────────┘
             │            ┌────────┼─────────────┐
             │            ▼        ▼              ▼
             │      ┌──────────┐ ┌────────────┐ (Thm5 also feeds Thm8C1)
             │      │ Theorem5 │ │Theorem8Trace│
             │      │(Dobbertin│ │(Dobbertin   │
             │      │  .Thm5)  │ │  .Thm8)     │
             │      │ qeps,    │ │trace_frob_  │
             │      │ ell_of_eq│ │ shift,      │
             │      │ ell0_root│ │trace_artin_ │
             │      │ _imp_img,│ │ schreier    │
             │      │ Q_factor,│ └──────┬──────┘
             │      │ theorem_5│        │
             │      └────┬─────┘        │
             │           ▼              │
             │     ┌────────────┐       │
             │     │ Theorem8C1 │◄──────┘
             │     │(.Thm8C1)   │
             │     │ trace_sq,  │
             │     │ trace_bit, │
             │     │ gmap       │
             │     └─────┬──────┘
             │           ▼
             │     ┌──────────────┐
             │     │  Q1General   │
             │     │ (.Thm8C1Gen) │
             │     │ gmap_biject- │
             │     │  ive_iff …   │
             │     └──────┬───────┘
             │            │
      ┌──────┴────────┐   │
      ▼               ▼   ▼
 ┌─────────┐    ┌──────────────────────────────┐
 │  Setup  │    │        Equation1             │  ← headline thread
 │ inv_mod │    │ theorem_1, eqn2_of_eqn1,     │
 │ _exists,│    │ theorem_1_case1, ell_eq_Q,   │
 │ qKasami_│    │ theorem_1_case2              │
 │ one_… │      │ (+ bridges qKasami↔qeps/gmap)│
 └─────────┘    └──────────────────────────────┘
```

### 2.1 Layer-by-layer

1. **`Defs`** — pure definitions, Mathlib only. No proofs.
2. **`FiniteFieldPrereqs`** (`DempwolffMueller`) — the finite-field engine, all
   reduced to a handful of Mathlib facts (see §3): Frobenius as a bijection,
   the coprime-power bijection `x ↦ xᵃ`, and the truncated trace `L(x)=∑ x^{2^i}`
   with its additivity and the Artin–Schreier telescoping `L(x)²+L(x)=x^{2^m}+x`.
3. **`Theorem5`** (`Dobbertin.Thm5`) — the `α = 0` backbone. `qeps` is `q_ε`; the
   engine proves `theorem_5` (permutation criterion for the trace-free map) and,
   crucially for equation (1), the three "reduction" lemmas reused downstream:
   `ell_of_eq` ((1)→(2) telescoping), `ell0_root_imp_image` (Case 1), and
   `Q_factor` (Case 2 factorisation).
4. **`Theorem8Trace`** (`Dobbertin.Thm8`) — the two trace identities:
   Frobenius-invariance `Tr(x^{2^k})=Tr(x)` and `Tr(t^{2^k}+t)=0`.
5. **`Theorem8C1`** (`Dobbertin.Thm8C1`) — `Tr(x)∈{0,1}` (`trace_bit`, via
   `trace_sq`) and the trace-version map `gmap x = qeps (Tr x) x`.
6. **`Q1General`** (`Dobbertin.Thm8C1Gen`) — the `α = 1` backbone:
   `gmap_bijective_iff`, the trace-version analogue of `theorem_5`.
7. **`Setup`** — the engine-free opening of the proof (number theory + values at
   `0` and `1`): `inv_mod_exists`, `qKasami_zero`, `qKasami_one`,
   `qKasami_one_eq_zero_iff` (the "only if" part).
8. **`Equation1`** — the thread. Three bridge lemmas identify the paper's `q_α`
   with the library polynomials: `qKasami_zero_eq_qeps` (`α=0 → qeps`),
   `qKasami_one_eq_gmap` (`α=1 → gmap`), and `qKasami_mul_unit` (clearing the
   denominator on units). Then:
   * `theorem_1` = `theorem_5` (α=0) ⊕ `gmap_bijective_iff` (α=1), glued by the bridges;
   * `eqn2_of_eqn1` = `Thm5.ell_of_eq` + `Thm8C1.trace_bit`;
   * `theorem_1_case1` = `Thm5.ell0_root_imp_image`;
   * `ell_eq_Q` = `Thm5.Q_factor`;
   * `theorem_1_case2` = `theorem_1` (surjectivity) + `qKasami_mul_unit`.

---

## 3. Mathlib foundations actually used

The whole development bottoms out on a small, stable Mathlib surface:

* **Finite-field Frobenius / Fermat.** `FiniteField.pow_card`
  (`x^{|F|}=x`), `FiniteField.pow_card_sub_one_eq_one` (`x^{|F|-1}=1` for `x≠0`),
  `iterateFrobenius_inj`. These power `frob_cycle`, `frob_mod`, `frob_bijective`
  and the denominator-clearing `qKasami_mul_unit`.
* **Characteristic 2.** `CharP`, `CharTwo.two_eq_zero`, `CharTwo.add_self_eq_zero`,
  `add_pow_char_pow` (freshman's dream) — used pervasively, especially in
  `truncTrace_add`, `truncTrace_sq_add_self`, and every `ring`/`grind` step.
* **Number theory of Mersenne numbers.** `Nat.pow_sub_one_gcd_pow_sub_one`
  (`gcd(2^k-1,2^n-1)=2^{gcd(k,n)}-1`) and
  `Nat.exists_mul_mod_eq_one_of_coprime` → `mersenne_coprime`, `inv_mod_exists`.
* **Finite pigeonhole.** `Finite.injective_iff_surjective` — the recurring device
  turning "injective" into "bijective/permutation" on a finite field.
* **Set cardinality.** `Set.ncard_eq_one`, `Set.eq_singleton_iff_unique_mem` — the
  "exactly one solution" statements of Cases 1 and 2.

---

## 4. Alternative foundations & proof paths

Different starting points that could reach the same headline results, with trade-offs.

### 4.1 Choice of the field object
* **Current:** an abstract `[Field L] [Fintype L] [CharP L 2]` with a hypothesis
  `Fintype.card L = 2^n`. *Pro:* maximally general, no dependence on a concrete
  construction; every statement is about "any `𝔽_{2ⁿ}`". *Con:* every fact about
  cardinality must be threaded through `hn`.
* **Alternative A — `GaloisField 2 n`.** Use Mathlib's `GaloisField p n`
  (with `Fact (0 < n)`), which *packages* `card (GaloisField 2 n) = 2^n`
  (`GaloisField.card`). Removes the `hn` hypothesis threading, at the cost of
  tying results to the specific model and adding coercions when specialising.
* **Alternative B — `ZMod`-based tower / `SplittingField`.** Heavier; not
  recommended — more coercion overhead with no payoff here.

### 4.2 Representation of the trace
* **Current:** the *truncated* absolute trace defined by hand,
  `truncTrace n x = ∑_{i<n} x^{2^i}`, with `trace_bit`, additivity, and the
  Artin–Schreier telescoping proved from scratch. *Pro:* self-contained,
  computational, `ring`-friendly. *Con:* re-proves standard trace facts.
* **Alternative — Mathlib `Algebra.trace` / `FiniteField` trace API.** Mathlib has
  `Algebra.trace`, `Algebra.trace_trace`, and additive-Galois trace machinery
  (`traceForm`, `trace_eq_sum_...`). One could identify `truncTrace n` with the
  `𝔽₂`-trace of `𝔽_{2ⁿ}/𝔽₂` and inherit additivity/surjectivity/`Tr∈{0,1}` from
  the general theory (`Algebra.trace_surjective`, separability). *Pro:* connects to
  the general library, less bespoke proving. *Con:* the identification
  `Algebra.trace = ∑ x^{2^i}` itself needs a proof (`trace_eq_sum_of_...` via the
  power basis / Galois conjugates), which for a bespoke, `ring`-heavy argument like
  this may cost more than it saves.

### 4.3 The "permutation" criterion (heart of Theorem 1)
* **Current:** finite injectivity ⇒ bijectivity, plus an explicit **root-count**
  argument (`root_count`, `root_count_image`) bounding the number of solutions of
  the linearised `ℓ`/`Q` equations. This mirrors the paper.
* **Alternative A — linearised-polynomial / 𝔽₂-linear-map kernel.** `ℓ` and `ℓ₀`
  are 𝔽₂-linear (additive `q`-polynomials). Model them as `LinearMap (ZMod 2) L L`
  and use rank–nullity: "permutation ⇔ trivial kernel". This replaces ad-hoc root
  counting with `LinearMap.injective_iff_surjective` + kernel dimension. *Pro:*
  conceptually clean, reusable; *Con:* setting up the 𝔽₂-module structure and the
  `q`-polynomial-as-linear-map bridge is upfront work.
* **Alternative B — degree/`card_roots` of `Polynomial`.** Encode `ℓ` as an actual
  `Polynomial L` and bound roots by degree (`Polynomial.card_roots_le_degree`).
  *Pro:* uses Mathlib's polynomial root theory directly; *Con:* the exponents are
  `2^{2k}` etc., so the polynomial has large formal degree — the degree bound is
  weak and the additive (linearised) structure is the real reason for ≤ 4 roots,
  which the degree bound does not capture. The additive-kernel route (A) is the
  faithful one.

### 4.4 The (1) ⟹ (2) step specifically
* **Current:** `eqn2_of_eqn1` adds the `2^k`-power of (1) to itself and telescopes
  via `Thm5.ell_of_eq` (built on `truncTrace_sq_add_self` and `trace_bit`).
* **Alternative — direct Frobenius-additive computation.** Since squaring is a ring
  homomorphism in char 2, `(eqn1)^{2^k} + (eqn1)` can be expanded by `add_pow_char_pow`
  and simplified purely by `ring`/`linear_combination`, using only
  `Tr(x)²=Tr(x)` and `Tr(x^{2^k})=Tr(x)`. This is essentially what the current
  proof does under the hood; one could inline it and drop the dependence on the
  `Thm5` reduction lemma, trading reuse for a shorter dependency chain for *this one*
  statement.

### 4.5 Number-theoretic opening
* **Current:** `inv_mod_exists` from `Nat.pow_sub_one_gcd_pow_sub_one`. This is the
  cleanest available route; no strong alternative is warranted.

### 4.6 Recommended minimal path (if re-deriving from scratch)
1. `GaloisField 2 n` (§4.1-A) to eliminate `hn` threading.
2. Keep the hand-rolled `truncTrace` (it is small and `ring`-friendly) **or** invest
   once in the `Algebra.trace` identification if the trace theory will be reused.
3. Prove the permutation criterion via the **𝔽₂-linear-kernel** view (§4.3-A) —
   the most reusable foundation for the whole Kasami/MCM family in the paper.
4. Derive (1)⟹(2) by the direct Frobenius-additive computation (§4.4).

The present library instead optimises for a **self-contained, minimal** extract
(everything closed down to a small Mathlib surface, no external Kasami theory),
which is the right choice for a verified MVP of exactly equation (1) and its
first step.
