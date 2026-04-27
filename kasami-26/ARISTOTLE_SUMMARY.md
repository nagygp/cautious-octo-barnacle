# Summary of changes for run e08c4e14-05eb-4bfa-a826-b2b1ae0a1b41
Created `RequestProject/KasamiBridgeLemmas.lean` — a fully type-checked Lean 4 skeleton that decomposes the four bridge gaps for `kasami_is_ab` into 21 tiny lemmas (all `sorry`-ed, all compiling).

### File structure

**Infrastructure.** `GaloisField 2 m` with a noncomputable `Fintype` instance, the absolute trace `AbsTr`, iterated Frobenius `φ`, and the Kasami exponent `kasD k = 2^(2k) − 2^k + 1`.

**Bridge 1 — Layer 2 gap** (Q_a as a quadratic form over F₂):
| Lemma | Statement |
|---|---|
| `add_pow_two_pow` | (x+y)^(2^i) = x^(2^i) + y^(2^i) in char 2 |
| `kasami_cross_terms` | Cross-term expansion of (x+y)^d + x^d + y^d |
| `Ba_add_right` | B_a is additive in its second argument |
| `Ba_symm` | B_a is symmetric |
| `Qa_smul` | Q_a(c·x) = c·Q_a(x) for c ∈ F₂ |

**Bridge 2 — Layer 2→3** (B_a = Tr(y · L_a(x))):
| Lemma | Statement |
|---|---|
| `trace_frob_eq` | Tr(x^(2^i)) = Tr(x) |
| `trace_sq_eq` | Tr(x²) = Tr(x) |
| `frob_card_eq_id` | x^(2^m) = x in GF(2^m) |
| `La_additive` | L_a(x+y) = L_a(x) + L_a(y) |
| `Ba_eq_trace_La` | **Key bridge**: B_a(x,y) = Tr(y · L_a(x)) |

**Bridge 3 — Layer 3→4** (kernel classification → Gauss sum):
| Lemma | Statement |
|---|---|
| `kerLa_add_mem` | ker(L_a) closed under addition |
| `kerLa_card_le` | \|ker(L_a)\| ≤ 2^k |
| `kerLa_card_dichotomy` | \|ker(L_a)\| ∈ {1, 2} (using gcd(k, 2k+1)=1) |
| `radical_eq_kerLa` | rad(Q_a) = ker(L_a) |
| `expSum_sq_eq` | S(a)² = 2^m · \|ker(L_a)\| |
| `rank_parity_cases` | rank parity: odd when \|ker\|=1, even when \|ker\|=2 |

**Bridge 4 — Layer 4→5** (exponential sum → WHT values):
| Lemma | Statement |
|---|---|
| `gauss_sum_odd_rank` | ∑(-1)^Q(x) = 0 when rank is odd |
| `gauss_sum_even_rank` | (∑(-1)^Q(x))² = 2^(m+r) when rank is even |
| `kasami_expSum_values` | S(a) ∈ {0, ±2^(k+1)} |
| `two_pow_sq` | 2^(2k+2) = (2^(k+1))² (arithmetic) |
| `wht_eq_expSum` | WHT(b) = S(a) for some a (completing the square) |

**Main theorem:** `kasami_is_ab` — for all b, WHT(b) ∈ {0, ±2^(k+1)}.

A full dependency tree is included in the file header as an ASCII diagram.