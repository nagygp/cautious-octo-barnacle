import Mathlib
import RequestProject.Foundations.DicksonPoly
import RequestProject.Foundations.AdjointTransfer.AdjointTransfer

/-!
# Layer T5: The MCM Bridge — From Dickson Injectivity to mcm_permutation

This is the final bridge module that connects the proved
`dicksonF_injective_on_units'` to the target `mcm_permutation`.

## The complete proof chain

```
dicksonF_injective_on_units' (DicksonPoly.lean, proved ✅)
  "f_k is injective on F*"
    │
    ▼  [S_sq_mul_eq_dicksonF: S_k(y⁻¹)² · y^{q+1} = f_k(y)]
    │
G(y) = S_k(y)² / y^{q+1} is injective on F*
    │
    ▼  [G_factors_through_sq: G = G_half²]
    ▼  [Frobenius bijective ⟹ G_half injective]
    │
G_half(y) = S_k(y) · y^{halfExp} is injective on F*
    │
    ▼  [adjoint_transfer_injective (Lemma 3.1)]
    │
S_k*(y) · y^{dualExp} is injective on F*
    │
    ▼  [adjoint_partialTrace_eq_frob_Sk: S_k* = S_k^{2^{n-k}}]
    │
S_k(y)^{2^{n-k}} · y^{dualExp} is injective on F*
    │
    ▼  [Frobenius cycling + exponent mod arithmetic]
    │
S_k(y)^{q+1} · y^{expM k n} is injective on F*
    │
    ▼  [expM k n = 2^n - 1 - 2^k, y^{expM} = y^{-q}]
    │
M(y) = S_k(y)^{q+1} / y^q is injective on F*  (= mcm_permutation ✅)
```

## DAG Dependencies

- `DicksonPoly` (dicksonF_injective_on_units', S_sq_mul_eq_dicksonF)
- `AdjointTransfer` (the transfer theorem, Sk_combined_injective)

## Target

- Provides the proof of `mcm_permutation` in `KasamiCollisionMVP.lean`
-/

namespace AdjointTransfer.MCMBridge

open Finset BigOperators DicksonKasami AdjointTransfer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The MCM Bridge Theorem -/

/-- **The MCM bridge theorem**: combining all layers T1-T4 plus Dickson injectivity,
    we get `S_k(y)^{q+1} / y^q` is injective on F*.

    This is exactly `mcm_permutation` from `KasamiCollisionMVP.lean`,
    stated in the cross-product form:
    `S_k(y₁)^{q+1} · y₂^q = S_k(y₂)^{q+1} · y₁^q → y₁ = y₂`.

    **Proof**: Apply `Sk_combined_injective` from Layer T4, feeding in
    `dicksonF_injective_on_units'` from `DicksonPoly.lean` as the hypothesis. -/
theorem mcm_permutation_bridge
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n)
    {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (hk_odd : Odd k) (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (y₁ y₂ : F) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (h_eq : (∑ i ∈ Finset.range k, y₁ ^ (2 ^ i)) ^ (2 ^ k + 1) * y₂ ^ (2 ^ k) =
            (∑ i ∈ Finset.range k, y₂ ^ (2 ^ i)) ^ (2 ^ k + 1) * y₁ ^ (2 ^ k)) :
    y₁ = y₂ :=
  Sk_combined_injective hn hn_pos hk hkn hk_odd hgcd hn_odd
    (fun a b ha hb hab => dicksonF_injective_on_units' hn k hk hk_odd hgcd ha hb hab)
    y₁ y₂ hy₁ hy₂ h_eq

/-! ## Connection to KasamiCollisionMVP.lean

To close the remaining sorry in `KasamiCollisionMVP.lean`, one would:

1. Import this module
2. In `mcm_permutation`, invoke `mcm_permutation_bridge` with appropriate arguments
3. The `S_k` definition in KasamiCollisionMVP matches our `partialTrace`:
   `S_k k y = ∑ i ∈ range k, y ^ (2 ^ i) = (partialTrace k).toFun y`

Note: `mcm_permutation` in KasamiCollisionMVP requires `k < n` (derivable from
`gcd(k,n) = 1` and `n > 1`, which follows from `n` odd and `n > 0`).
-/

/-! ## DAG Summary

```
                    TraceNondeg (T1)
                    ┌──────┴──────┐
                    │             │
               AdjointMap (T2)   │
                    │             │
                    ├─────────────┤
                    │             │
              ExpTransfer (T3)   │
                    │             │
                    ▼             │
            AdjointTransfer (T4) │
                    │             │
                    ▼             ▼
              MCMBridge (T5) ◄── DicksonPoly (proved ✅)
                    │
                    ▼
            mcm_permutation (KasamiCollisionMVP.lean)
                    │
                    ▼
            kasami_is_apn_mvp (proved, modulo mcm_permutation)
```

### Layer inventory

| Layer | File | Key theorems | # sorries |
|-------|------|-------------|-----------|
| T1 | `TraceNondeg.lean` | `trace_bilinear_nondegenerate`, `Tr_kernel_card` | 6 |
| T2 | `AdjointMap.lean` | `trAdjoint_spec`, `trAdjoint_frobPow`, `trAdjoint_partialTrace` | 7 |
| T3 | `ExpTransfer.lean` | `expG_add_qp1`, `expM_add_q`, `dualExp_to_M` | 8 |
| T4 | `AdjointTransfer.lean` | `adjoint_transfer_injective`, `Sk_combined_injective` | 6 |
| T5 | `MCMBridge.lean` | `mcm_permutation_bridge` | 0 (delegates to T4) |
| ✅ | `DicksonPoly.lean` | `dicksonF_injective_on_units'` | 0 |
-/

end AdjointTransfer.MCMBridge
