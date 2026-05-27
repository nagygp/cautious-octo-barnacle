import Mathlib

/-!
# Skeleton: typeI_inverse_GF2_coeffs — AUDIT

## Status: ⚠️ FALSE AS STATED

The statement `typeI_inverse_GF2_coeffs` in `AutTypeI.lean:77` claims:

```
∀ x : F, (Function.invFun (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i)) x) ^ 2 =
  Function.invFun (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i)) x
```

This says `L⁻¹(x) ∈ GF(2)` for ALL `x ∈ F`, i.e., the inverse of the
truncated trace maps everything into GF(2).

**This is false when `m > 1` and `n > 1`.**

**Proof that it's false:** `L` is bijective `GF(2^n) → GF(2^n)`, so `L⁻¹`
is also bijective `GF(2^n) → GF(2^n)`. If `L⁻¹(x) ∈ GF(2)` for all `x`,
then `im(L⁻¹) ⊆ GF(2)`, which has at most 2 elements. But bijectivity
requires `|im(L⁻¹)| = |GF(2^n)| = 2^n > 2` when `n > 1`. Contradiction.

## Likely intended statement

The intended statement is probably one of:
1. **L⁻¹ has coefficients in GF(2)**: i.e., when L⁻¹ is written as a
   linearized polynomial `L⁻¹(x) = ∑ cᵢ x^{2^i}`, each `cᵢ ∈ GF(2)`,
   meaning `cᵢ² = cᵢ`.
2. **L⁻¹ commutes with Frobenius**: `L⁻¹(x²) = L⁻¹(x)²`.

Both of these are TRUE and follow from L having coefficients in GF(2):
- L(x) = ∑ x^{2^i} has all coefficients = 1 ∈ GF(2).
- The inverse of a GF(2)-linear bijection is GF(2)-linear.
- A GF(2)-linear map on GF(2^n) commutes with Frobenius.

## Corrected sub-lemma DAG (for statement 2)

```
  CT.1 (L is GF(2)-linear)                    [easy]
    │
    ├──► CT.2 (L commutes with Frobenius)       [easy]
    │
    ├──► CT.3 (inverse of bij commutes w/ Frob) [meh]
    │
    └──► CT.4 (L⁻¹ commutes with Frobenius)     [meh]
```

### CT.1 [easy]
```
lemma truncTrace_gf2_linear (m : ℕ) (x : F) :
    truncTrace m (x ^ 2) = (truncTrace m x) ^ 2
```
Proof: Each (x^2)^{2^i} = x^{2^{i+1}}, so the sum shifts. In char 2,
(∑ a_i)^2 = ∑ a_i^2, which is the shifted sum.

### CT.2 [easy]
```
lemma truncTrace_frob (m : ℕ) (x : F) :
    truncTrace m (x ^ 2) = (truncTrace m x) ^ 2
```
Same as CT.1 — this is `truncTrace_frob_comm` with j = 1.

### CT.3 [meh]
```
lemma bij_inv_commutes_frob (f : F → F)
    (hf_bij : Function.Bijective f)
    (hf_frob : ∀ x, f (x ^ 2) = (f x) ^ 2) :
    ∀ x, Function.invFun f (x ^ 2) = (Function.invFun f x) ^ 2
```
Proof: Let y = f⁻¹(x). Then f(y) = x. We want f⁻¹(x²) = y².
Since f(y²) = f(y)² = x², we have f⁻¹(x²) = y² = (f⁻¹(x))².

### CT.4 [meh] — The corrected statement
```
lemma typeI_inverse_frob_comm (m : ℕ)
    (hbij : Function.Bijective (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i))) :
    ∀ x : F,
      Function.invFun (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i)) (x ^ 2) =
      (Function.invFun (fun x : F => ∑ i ∈ range m, x ^ (2 ^ i)) x) ^ 2
```
-/
