# Summary of changes for run 318ff552-f70d-4d35-8592-60b8c13d0531
I decomposed the two original black-boxed known results into five independent sub-results (plus two opaque definitions), each capturing a single mathematical fact, and showed how they compose logically:

**§2a [APN] — Almost Perfect Nonlinearity (2 sub-results):**
- `kasami_is_APN`: The Kasami function is APN when gcd(k,n) = 1 (black box)
- `delta_card_of_APN`: APN ⟹ |Δ| = |F|/2 (black box)
- `kasamiDelta_card'`: **Derived** — |Δ| = 2^(n−1), by composing [APN] + [APN → |Δ|] + arithmetic

**§2b [Four] — Fourier Identity (1 sub-result + 1 opaque def):**
- `walshTripleSum`: Opaque definition of the Walsh triple-product sum
- `fourier_triple_identity`: |F| · κ = walshTripleSum (black box)

**§2c [AB] — Almost Bent Spectral Collapse (2 sub-results + 1 opaque def):**
- `IsAB`: Opaque definition of the Almost Bent property
- `kasami_is_AB`: Kasami is AB when n is odd (black box)
- `AB_spectral_collapse`: AB ⟹ walshTripleSum = |Δ|³ (black box)
- `fourier_and_spectral_collapse`: **Derived** — |F| · κ = |Δ|³, by composing [Four] + [AB] + [AB → Collapse]

**Logical dependency diagram** (included in the file header):
```
  [APN] ──→ [APN → |Δ|] ──→ kasamiDelta_card'
                                      │
  [Four] ──→ fourier_triple_identity   │
                      │                │
  [AB] ──→ [AB → Collapse]            │
                      │                │
                      ▼                ▼
            fourier_and_spectral_collapse
                      │                │
                      ▼                ▼
            kasami_triple_count' (calc chain)
```

The main theorem's calc chain now explicitly shows which sub-result justifies each step. The file builds successfully with `sorry` only in the 5 black-boxed theorems and 2 opaque definitions — all derived results and the main theorem compile cleanly.