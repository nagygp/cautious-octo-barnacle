# Sorry DAG Decomposition — Layered Dependency Skeletons

This document decomposes every remaining `sorry` in the project into a DAG of
tiny lemmas/sub-lemmas. Each leaf performs **one** algebraic manipulation or
logical deduction. Difficulty labels:

| Label | Meaning |
|-------|---------|
| **easy** | Single tactic / Mathlib one-liner / definitional unfolding |
| **meh** | Requires a short chain of rewrites, case splits, or a known Mathlib pattern |
| **hard** | Deep argument, multi-step reasoning, or novel algebraic insight |

---

## 1. `adjoint_swap_bij` — AdjointBij.lean:98

**Statement.** If `Tr` is nondegenerate, `L₁` and `L₂` are additive trace-adjoints,
`x ↦ L₁(x)·x^e` is bijective, and `e·l ≡ 1 (mod |F|−1)`,
then `x ↦ L₂(x)·x^l` is bijective.

**Proof sketch.** This is a specialized instantiation of Lemma 3.1
(`lemma_3_1` in Lemma31.lean) with `M(x) = x^e` and `M⁻¹(x) = x^l`.
The chain is: wrap the additive `L₁`, `L₂` as `K`-linear maps, build
`M` and `M⁻¹`, verify all hypotheses of `lemma_3_1`, then convert
injectivity to bijectivity on a finite type.

### Sub-lemma DAG

```
AB3.1  ──► AB3.2  ──► AB3.3  ──► AB3.4  ──► adjoint_swap_bij
```

#### AB3.1 `pow_map_is_mul_bij` — **meh**
```
-- The power map x ↦ x^e is a multiplicative bijection when gcd(e, |F|−1) = 1.
-- Wraps pow_field_bijective + mul_pow.
lemma pow_map_is_mul_bij (e : ℕ) (he : Nat.Coprime e (Fintype.card F - 1)) (he_pos : 0 < e) :
    Function.Bijective (fun x : F => x ^ e) ∧
    ∀ a b : F, (a * b) ^ e = a ^ e * b ^ e
```

#### AB3.2 `pow_map_inv_is_mul` — **meh**
```
-- The inverse power map x ↦ x^l is multiplicative and is a left/right inverse of x ↦ x^e.
-- Uses pow_pow_eq_self and mul_pow.
lemma pow_map_inv_is_mul (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1)) :
    (∀ a b : F, (a * b) ^ l = a ^ l * b ^ l) ∧
    (∀ x : F, (x ^ e) ^ l = ... ) -- not literally id on 0, need case split
```

#### AB3.3 `additive_to_linear_map` — **meh**
```
-- Wrap a bare additive function F → F into a GF(p)-linear map F →ₗ[GF(p)] F.
-- This is needed to apply lemma_3_1 which works with LinearMap.
-- Requires showing that L(c·x) = c·L(x) for c ∈ GF(p), which follows from
-- L being a sum of Frobenius powers (each of which fixes GF(p)).
```

#### AB3.4 `frobSum_as_linear_map` — **hard**
```
-- The frobSum (trace) as a K-linear form, wrapping frobSum into a LinearMap
-- and establishing its nondegeneracy matches the hypothesis of lemma_3_1.
-- The hard part is interfacing between the bare function frobSum and the
-- LinearMap + Algebra infrastructure that lemma_3_1 expects.
```

#### AB3.5 `adjoint_swap_bij_assembly` — **hard**
```
-- Final assembly: instantiate lemma_3_1 with all the pieces above,
-- convert Function.Injective to Function.Bijective on Fintype.
-- Hard because of the extensive type-class and coercion management.
```

---

## 2. `adjoint_swap_bijective` — Thm32Kprime.lean:153

**Statement.** Same as `adjoint_swap_bij` but with `truncTrace n` instead of `frobSum p n`.

**Proof sketch.** Either directly invoke `adjoint_swap_bij` (since `truncTrace n` for char 2
is `frobSum 2 n`), or replicate the argument. The key is that `truncTrace n = frobSum 2 n`.

### Sub-lemma DAG

```
ASB.1  ──► adjoint_swap_bijective
```

#### ASB.1 `truncTrace_eq_frobSum` — **easy**
```
-- truncTrace n x = frobSum 2 n x (definitional equality or short simp)
lemma truncTrace_eq_frobSum (n : ℕ) (x : F) :
    truncTrace n x = frobSum 2 n x
```

#### ASB.2 `adjoint_swap_bijective_from_bij` — **meh**
```
-- Convert adjoint_swap_bij (which uses frobSum) to the truncTrace formulation.
-- Rewrite hypotheses using ASB.1 and apply adjoint_swap_bij.
```

---

## 3. `LxXk'_bijective_v2` — Thm32Kprime.lean:210

**Statement.** `L(X)·X^{k'}` is a permutation polynomial.

**Proof sketch.** Chain:
1. `LxXk_bijective` (already proved) gives bijectivity of `L(X)·X^k`.
2. `LadjXe_bijective` (already proved) transfers to `L*(X)·X^{k·2^{n-m+1}}`.
3. `adjoint_swap_bijective` (sorry #2 above) transfers to `L₂(X)·X^l`.
4. `exp_k'_eq_on_units` (already proved) identifies the exponent.

### Sub-lemma DAG

```
LK1  ──► LK2  ──► LK3  ──► LxXk'_bijective_v2
```

#### LK1 `trace_nondeg_truncTrace` — **meh**
```
-- Nondegeneracy of truncTrace n (= full trace) on GF(2^n).
-- Wraps trace_nondegenerate from TraceNorm.lean.
lemma trace_nondeg_truncTrace (hn : Fintype.card F = 2 ^ n) (hn1 : 1 ≤ n)
    (x : F) (hx : x ≠ 0) : ∃ y, truncTrace n (x * y) ≠ 0
```

#### LK2 `exp_identification` — **meh**
```
-- The exponent e = k · 2^{n-m+1} and l satisfy e·l ≡ 1 mod (2^n - 1).
-- Chains exp_mod_chain, exists_pow_inverse', and coprime_of_mul_mod_one.
```

#### LK3 `LxXk'_assembly` — **hard**
```
-- Final assembly: combine LadjXe_bijective + adjoint_swap_bijective + exp_k'_eq_on_units
-- to conclude bijectivity of L(X)·X^{k'}.
-- Requires matching exponents modulo 2^n - 1 and substituting on units.
```

---

## 4. `LxXk'_bijective` — Thm32.lean:700

**Statement.** Same conclusion as `LxXk'_bijective_v2` but in the Thm32.lean namespace.

**Proof sketch.** Direct invocation of `LxXk'_bijective_v2` from Thm32Kprime.lean,
or replicate the chain. Should be a thin wrapper.

### Sub-lemma DAG

```
LK'1  ──► LxXk'_bijective
```

#### LK'1 `LxXk'_wrap` — **easy**
```
-- Import and apply LxXk'_bijective_v2 with the appropriate parameters.
-- May need to add `import RequestProject.Thm32Kprime` to Thm32.lean.
```

---

## 5. `bij_of_additive_pow_twist` — NormPower.lean:115

**Statement.** If `L(x)·x^k` is bijective, `(x^b)^p = x^b` for x ≠ 0,
and `gcd(b+1, |F|−1) = 1`, then `L(x)·x^{k+b}` is bijective.

**Proof sketch.** The map `x ↦ x^b` sends nonzero elements to GF(p)*.
So `L(x)·x^{k+b} = L(x)·x^k · x^b`. Since `x^b ∈ GF(p)` and L is GF(p)-linear,
we can absorb `x^b` into the linear part. The key is that `x ↦ (L(x)·x^k) · x^b`
is a composition of a bijection with a "scalar twist" that preserves bijectivity
due to the coprimality condition.

### Sub-lemma DAG

```
NP1  ──► NP2  ──► NP3  ──► NP4  ──► bij_of_additive_pow_twist
```

#### NP1 `frob_fixed_in_subfield` — **meh**
```
-- If x^p = x then x ∈ GF(p), i.e., x is a root of X^p - X.
-- In a field of char p, the elements with x^p = x form the prime subfield.
lemma frob_fixed_in_subfield {x : F} (hx : x ^ p = x) :
    ∃ c : ZMod p, (algebraMap (ZMod p) F) c = x
```

#### NP2 `scalar_twist_preserves_inj` — **hard**
```
-- If f is injective and c(x) is a "scalar" (i.e., c(x) ∈ GF(p) for x ≠ 0),
-- and the map x ↦ f(x) · c(x) has the property that c is determined by
-- the power map with coprime exponent, then x ↦ f(x) · c(x) is injective.
--
-- Core argument: if L(x)·x^k·x^b = L(y)·y^k·y^b with x ≠ y,
-- then since x^b, y^b ∈ GF(p), we can use the GF(p)-linearity of L
-- and the structure of the equation to derive a contradiction.
```

#### NP3 `coprime_power_unit_bijection` — **meh**
```
-- If gcd(b+1, |F|-1) = 1, then x ↦ x^{b+1} is bijective on F.
-- This is just pow_field_bijective with the right coprimality argument.
```

#### NP4 `twist_assembly` — **hard**
```
-- Assembly: L(x)·x^{k+b} = L(x)·x^k · x^b.
-- Factor through the scalar twist argument.
-- Show injectivity, conclude bijectivity on Fintype.
```

---

## 6. `spread_condition_iff_perm_poly` — SpreadSet.lean:99

**Statement.** `{N(x)}` is a spread set (all differences bijective) iff
`P(z) = L(z)·z^k` is injective.

**Proof sketch.** Forward: if `N(x) - N(y)` is bijective for all `x ≠ y`,
then for `x ≠ y`, `z ↦ L((x-y)z)·(x-y)^k - ...` is bijective, which
after substitution gives `P` injective.
Backward: if `P` is injective, then for `x ≠ y`, substitute `z' = (x-y)·z`
to reduce `N(x) - N(y)` to a composition involving `P`.

### Sub-lemma DAG

```
SC1  ──► SC2  ──► SC3  ──► spread_condition_iff_perm_poly
```

#### SC1 `spread_diff_factor` — **meh**
```
-- N(x)(z) - N(y)(z) = L(xz)·x^k - L(yz)·y^k.
-- For x ≠ y, substitute z' = (x-y)⁻¹·z and use additivity of L.
-- Show: the difference map factors through P composed with a linear substitution.
lemma spread_diff_factor (L : F → F) (hL_add : ...) (k : ℕ) (x y : F) (hxy : x ≠ y) :
    ∀ z, L (x * z) * x ^ k - L (y * z) * y ^ k = ... 
```

#### SC2 `perm_poly_inj_iff_diff_bij_forward` — **hard**
```
-- Forward direction: P injective ⟹ all spread differences bijective.
-- Uses the substitution z → (x-y)·z and the factorization from SC1.
```

#### SC3 `perm_poly_inj_iff_diff_bij_backward` — **hard**
```
-- Backward direction: all spread differences bijective ⟹ P injective.
-- Take x = 1, y = 0 (or any convenient pair) to extract P directly.
```

---

## 7. `spread_diff_via_subst` — SpreadAlg.lean:61

**Statement.** For `x ≠ y` with `L` bijective:
`z ↦ L(xz)·x^k - L(yz)·y^k` bijective ↔ `z ↦ L((x-y)z)·(x-y)^k` bijective.

**Proof sketch.** Factor: `L(xz)·x^k - L(yz)·y^k`
= `L((x-y)z)·x^k + L(yz)·(x^k - y^k)` by additivity of L. Hmm, this doesn't
directly simplify... The real argument is:
- Substituting `z → (x-y)⁻¹·w` and using linearity/bijectivity of `L` shows
  that the bijectivity of the difference is equivalent to bijectivity of the
  "normalized" form with `x-y` factored out.

### Sub-lemma DAG

```
SD1  ──► SD2  ──► SD3  ──► spread_diff_via_subst
```

#### SD1 `linear_subst_bijective` — **easy**
```
-- If L is bijective and c ≠ 0, then z ↦ L(c·z) is bijective.
-- Composition of bijections: z ↦ c·z is bij (mul by unit), then L is bij.
```

#### SD2 `spread_diff_normalize` — **hard**
```
-- The core algebraic manipulation:
-- z ↦ L(xz)·x^k - L(yz)·y^k  is bijective
-- iff  z ↦ L((x-y)z) · (x-y)^k  is bijective.
-- This requires carefully tracking the substitution and using
-- multiplicativity of the power map and additivity of L.
```

#### SD3 `spread_diff_via_subst_assembly` — **meh**
```
-- Combine SD1 and SD2 to get the iff statement.
```

---

## 8. `prop_3_5_abstract` — Prop35.lean:78

**Statement.** If `x^b ∈ GF(p)` for all nonzero x, and L commutes with GF(p) scalars,
then `L(X)·X^k` and `L(X)·X^{k+b}` define equivalent spread sets.

**Proof sketch.** Define the rescaling bijection `φ(x) = x^{1+ℓb}` where `ℓ`
is determined by the norm condition. Then show `N₂(φ(x))(y) = N₁(x)(y)` for all y.
This reduces to: `L(x^{1+ℓb}·y)·(x^{1+ℓb})^{k+b} = L(xy)·x^k`.

### Sub-lemma DAG

```
P5.1  ──► P5.2  ──► P5.3  ──► P5.4  ──► prop_3_5_abstract
```

#### P5.1 `gfp_scalar_commute` — **easy**
```
-- If c^p = c and L commutes with GF(p)-scalars, then L(c·x) = c·L(x).
-- Direct from hypothesis hL_comm.
```

#### P5.2 `norm_power_rescale` — **meh**
```
-- If x^b ∈ GF(p) (i.e., (x^b)^p = x^b), then x^{b·p} = x^b,
-- and x^{b(1+ℓb)} has specific factorization properties.
```

#### P5.3 `rescaling_bijection` — **meh**
```
-- If gcd(1+ℓb, |F|-1) = 1 then x ↦ x^{1+ℓb} is a bijection.
-- Or alternatively, construct the bijection more directly from the
-- fixed-field structure.
```

#### P5.4 `spread_equiv_via_rescaling` — **hard**
```
-- The main identity: L(φ(x)·y)·φ(x)^{k+b} = L(x·y)·x^k
-- where φ(x) = x^{1+ℓb} (or appropriate rescaling).
-- Requires detailed power arithmetic and GF(p)-linearity of L.
```

---

## 9. `typeI_inverse_GF2_coeffs` — AutTypeI.lean:77

**Statement.** The inverse polynomial `L⁻¹(X)` of the truncated trace
has all elements in GF(2), i.e., `(L⁻¹(x))^2 = L⁻¹(x)`.

**Proof sketch.** Since L = truncated trace with all coefficients 1 (in GF(2)),
and L is a bijective GF(2)-linear map, its inverse `L⁻¹` is also GF(2)-linear.
Being GF(2)-linear means `L⁻¹(x)^2 = L⁻¹(x^2)` (Frobenius), and since L
has coefficients in GF(2), so does `L⁻¹` (the matrix inverse of a GF(2)-matrix
is a GF(2)-matrix).

The actual statement is about `Function.invFun`, which requires showing that
the functional inverse of a GF(2)-linear bijection preserves the GF(2) property.

### Sub-lemma DAG

```
TI1  ──► TI2  ──► TI3  ──► typeI_inverse_GF2_coeffs
```

#### TI1 `invFun_of_bijective_eq_inverse` — **easy**
```
-- Function.invFun of a bijective function equals the actual inverse.
-- invFun f (f x) = x when f is bijective.
```

#### TI2 `gf2_linear_inv_is_gf2_linear` — **hard**
```
-- If L is GF(2)-linear and bijective on GF(2^n), then L⁻¹ is GF(2)-linear.
-- Key: L⁻¹(x^2) = L⁻¹(x)^2 because L(y^2) = L(y)^2 (Frobenius)
-- so if L(y) = x then L(y^2) = x^2 hence L⁻¹(x^2) = y^2 = (L⁻¹(x))^2.
```

#### TI3 `invFun_frob_fixed` — **meh**
```
-- Translate TI2 to the Function.invFun formulation:
-- (Function.invFun L x)^2 = Function.invFun L x
-- This follows from L⁻¹(x)^2 = L⁻¹(x^2) applied with x = x,
-- and the fact that on GF(2^n), the image of L⁻¹ on a Frobenius-fixed
-- element... Actually the statement is stronger: L⁻¹(x) ∈ GF(2) for all x.
-- Wait, that can't be right for general x. Let me re-read...
```

**Re-reading the statement:** The sorry says `(Function.invFun L x)^2 = Function.invFun L x`.
This says `L⁻¹(x) ∈ GF(2)` for ALL `x`. That would mean `L⁻¹` maps F into GF(2),
which would make `L⁻¹` have rank 1. That seems wrong unless the statement is about
the coefficients of L⁻¹ as an additive polynomial.

Actually, looking more carefully at the Lean code: the `Function.invFun` is applied to
`(fun x : F => ∑ i ∈ range m, x ^ (2 ^ i))` and the variable `x`. This literally says
"the preimage of x under L satisfies y^2 = y", i.e., `L⁻¹(x) ∈ GF(2)`.

This is **false** in general! For a generic `x ∈ GF(2^n)`, `L⁻¹(x)` is not in GF(2).
This sorry may represent a **false statement** that needs to be corrected or removed.

#### Assessment: **likely false** — needs verification

---

## Global Dependency DAG

```
                    ┌─────────────────────────────────────────┐
                    │        ALREADY PROVED (no sorry)        │
                    │                                         │
                    │  lemma_3_1 (Lemma31.lean)               │
                    │  LxXk_bijective (Thm32.lean Layer 11)   │
                    │  LadjXe_bijective (Thm32Kprime.lean)    │
                    │  exp_k'_eq_on_units (Thm32Kprime.lean)  │
                    │  frobSum_adjoint_Ico (TraceNorm.lean)    │
                    │  trace_nondegenerate (TraceNorm.lean)    │
                    │  pow_field_bijective (ExpArith.lean)     │
                    │  pow_pow_eq_self (ExpArith.lean)         │
                    │  frob_comp_bijective_right (FrobAlg)     │
                    └────────────┬────────────────────────────┘
                                 │
          ┌──────────────────────┼──────────────────────┐
          │                      │                      │
          ▼                      ▼                      ▼
   ┌─────────────┐      ┌──────────────┐      ┌──────────────┐
   │ adjoint_    │      │ bij_of_      │      │ spread_diff_ │
   │ swap_bij    │      │ additive_    │      │ via_subst    │
   │ (AB.3)      │      │ pow_twist    │      │ (SA.1)       │
   │ AdjointBij  │      │ (NP.3b)      │      │ SpreadAlg    │
   │ .lean:98    │      │ NormPower    │      │ .lean:61     │
   └──────┬──────┘      │ .lean:115    │      └──────┬───────┘
          │              └──────┬───────┘             │
          ▼                     │                     ▼
   ┌──────────────┐             │            ┌───────────────┐
   │ adjoint_swap │             │            │ spread_cond_  │
   │ _bijective   │             │            │ iff_perm_poly │
   │ (Thm32Kprime│             │            │ (SpreadSet    │
   │ .lean:153)   │             │            │ .lean:99)     │
   └──────┬───────┘             │            └───────────────┘
          │                     │
          ▼                     │
   ┌──────────────┐             │
   │ LxXk'_bij_  │             ▼
   │ v2 (Thm32   │     ┌───────────────┐
   │ Kprime:210) │     │ prop_3_5_     │
   └──────┬───────┘     │ abstract      │
          │             │ (Prop35:78)   │
          ▼             └───────────────┘
   ┌──────────────┐
   │ LxXk'_bij   │     ┌───────────────┐
   │ (Thm32:700) │     │ typeI_inverse │
   └──────────────┘     │ _GF2_coeffs  │
                        │ (AutTypeI:77)│
                        │ ⚠ likely     │
                        │   FALSE      │
                        └───────────────┘
```

---

## Priority Order (bottom-up proof strategy)

### Phase 1: Core Engine (unblocks everything downstream)
1. **`adjoint_swap_bij`** (AdjointBij.lean) — instantiation of Lemma 3.1
2. **`adjoint_swap_bijective`** (Thm32Kprime.lean) — thin wrapper

### Phase 2: Main Theorem Completion
3. **`LxXk'_bijective_v2`** (Thm32Kprime.lean) — assembly
4. **`LxXk'_bijective`** (Thm32.lean) — wrapper / import

### Phase 3: Extensions
5. **`bij_of_additive_pow_twist`** (NormPower.lean) — independent
6. **`prop_3_5_abstract`** (Prop35.lean) — independent
7. **`spread_diff_via_subst`** (SpreadAlg.lean) — independent
8. **`spread_condition_iff_perm_poly`** (SpreadSet.lean) — depends on 7

### Phase 4: Investigate
9. **`typeI_inverse_GF2_coeffs`** (AutTypeI.lean) — likely false, needs audit

---

## Skeleton Lean Files

Each sorry has a corresponding skeleton `.lean` file with the full sub-lemma DAG:

| Sorry Cluster | Skeleton File |
|---------------|---------------|
| `adjoint_swap_bij` | `RequestProject/AdjointBijSkeleton.lean` |
| `bij_of_additive_pow_twist` | `RequestProject/NormPowerSkeleton.lean` |
| `spread_diff_via_subst` + `spread_condition_iff_perm_poly` | `RequestProject/SpreadSkeleton.lean` |
| `prop_3_5_abstract` | `RequestProject/Prop35Skeleton.lean` |
| `adjoint_swap_bijective` + `LxXk'_bijective_v2` + `LxXk'_bijective` | `RequestProject/Thm32KprimeSkeleton.lean` |
| `typeI_inverse_GF2_coeffs` (⚠ FALSE) | `RequestProject/AutTypeISkeleton.lean` |

## Inline Skeleton Excerpts

The following sections contain key excerpts from the skeleton code.
Each lemma is annotated with its difficulty.

### Skeleton for `adjoint_swap_bij` decomposition

```lean
-- In AdjointBij.lean, replace the sorry with:

-- AB3.1 [meh]: Power map is multiplicative bijection
private lemma pow_map_mul_bij_aux (e : ℕ)
    (he_cop : Nat.Coprime e (Fintype.card F - 1)) (he_pos : 0 < e) :
    Function.Bijective (fun x : F => x ^ e) :=
  pow_field_bijective he_cop.symm he_pos

-- AB3.2 [easy]: Power map inverse round-trip
private lemma pow_round_trip (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    {x : F} (hx : x ≠ 0) :
    (x ^ e) ^ l = x :=
  pow_pow_eq_self hel hx

-- AB3.3 [easy]: Reverse round-trip
private lemma pow_round_trip_rev (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    {x : F} (hx : x ≠ 0) :
    (x ^ l) ^ e = x := by sorry
-- Proof idea: l * e ≡ 1 mod (|F|-1) by commutativity of mul, then pow_pow_eq_self.

-- AB3.4 [hard]: Injectivity transfer via Lemma 3.1 instantiation
-- This is the main content: instantiate lemma_3_1 with M = pow e.
-- The difficulty is building the K-linear map wrappers and matching types.
private lemma inj_transfer_via_lemma31
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F)
    (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (e l : ℕ) (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hinj : Function.Injective (fun x : F => L₁ x * x ^ e)) :
    Function.Injective (fun x : F => L₂ x * x ^ l) := by sorry

-- AB3.5 [easy]: Convert injective to bijective on Fintype
private lemma bij_of_inj_fintype (f : F → F) (hinj : Function.Injective f) :
    Function.Bijective f :=
  ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
```

### Skeleton for `LxXk'_bijective_v2` decomposition

```lean
-- LK1 [meh]: Nondegeneracy wrapper
private lemma trace_nondeg_wrap (hn : Fintype.card F = 2 ^ n) (hn1 : 1 ≤ n) :
    ∀ x : F, x ≠ 0 → ∃ y, truncTrace n (x * y) ≠ 0 := by sorry
-- Proof: truncTrace n = frobSum 2 n, then trace_nondegenerate.

-- LK2 [meh]: Exponent product identity
private lemma exp_product_mod (m : ℕ) (hm_pos : 1 < m) (hm_lt : m < n)
    (k' : ℕ)
    (hk' : (2^(n-1) - 2^(m-1) - 1) * k' % (2^n-1) = 2^(m-1) % (2^n-1)) :
    (2^(n-1) - 2^(m-1) - 1) * (k' * 2^(n-m+1)) % (2^n-1) = 1 % (2^n-1) := by sorry
-- Proof: apply exp_mod_chain.

-- LK3 [meh]: L₁ additivity
private lemma Ladj_add (m : ℕ) (hm : m ≤ n) (a b : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), (a + b) ^ (2 ^ i)) =
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), a ^ (2 ^ i)) +
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), b ^ (2 ^ i)) := by sorry
-- Proof: distribute Frobenius over addition, split sum.

-- LK4 [hard]: Assembly — the full proof of LxXk'_bijective_v2
-- Combines all the above pieces.
```

### Skeleton for `bij_of_additive_pow_twist` decomposition

```lean
-- NP.A [meh]: x^b ∈ GF(p)* for nonzero x implies x^{b(p-1)} = 1
private lemma pow_b_unit_order (b : ℕ)
    (hb_fixed : ∀ x : F, x ≠ 0 → (x ^ b) ^ p = x ^ b)
    {x : F} (hx : x ≠ 0) :
    x ^ (b * (p - 1)) = 1 := by sorry
-- Proof: (x^b)^p = x^b ⟹ x^{bp} = x^b ⟹ x^{b(p-1)} = 1.

-- NP.B [meh]: x ↦ x^{b+1} bijective from coprimality
private lemma pow_b_plus_one_bij (b : ℕ)
    (hcop : Nat.Coprime (b + 1) (Fintype.card F - 1)) :
    Function.Bijective (fun x : F => x ^ (b + 1)) := by sorry
-- Proof: apply pow_field_bijective.

-- NP.C [hard]: Main injectivity argument
-- If L(x)·x^k is bijective, (x^b)^p = x^b for x≠0, and gcd(b+1,|F|-1)=1,
-- then L(x)·x^{k+b} is injective.
-- Key idea: L(x)·x^{k+b} = L(x)·x^k · x^b.
-- If L(x)·x^{k+b} = L(y)·y^{k+b} then
-- L(x)·x^k · x^b = L(y)·y^k · y^b.
-- Since x ↦ x^{b+1} is bijective, can use substitution...
-- Actually the argument is more subtle and uses the linearity of L
-- over GF(p) combined with the scalar nature of x^b.
```

---

## Summary Table

| # | Sorry | File:Line | Depends On | Difficulty | Key Technique |
|---|-------|-----------|------------|------------|---------------|
| 1 | `adjoint_swap_bij` | AdjointBij:98 | lemma_3_1 | **hard** | Lemma 3.1 instantiation with power maps |
| 2 | `adjoint_swap_bijective` | Thm32Kprime:153 | #1 | **meh** | Wrapper around #1 |
| 3 | `LxXk'_bijective_v2` | Thm32Kprime:210 | #2, LadjXe | **hard** | Chain of Frobenius + adjoint |
| 4 | `LxXk'_bijective` | Thm32:700 | #3 | **easy** | Import + apply |
| 5 | `bij_of_additive_pow_twist` | NormPower:115 | (independent) | **hard** | GF(p)-scalar absorption |
| 6 | `spread_condition_iff_perm_poly` | SpreadSet:99 | #7 | **hard** | Spread ↔ perm poly equivalence |
| 7 | `spread_diff_via_subst` | SpreadAlg:61 | (independent) | **hard** | Substitution + L-bijectivity |
| 8 | `prop_3_5_abstract` | Prop35:78 | (independent) | **hard** | Spread equivalence via rescaling |
| 9 | `typeI_inverse_GF2_coeffs` | AutTypeI:77 | (independent) | **⚠ FALSE** | Statement is wrong; see AutTypeISkeleton.lean |
