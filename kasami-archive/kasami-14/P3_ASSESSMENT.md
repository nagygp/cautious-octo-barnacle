# Assessment: Can the Theory Verify P₃?

## Answer: **Not yet.** The theory has substantial infrastructure but is missing 3 critical theorems.

---

## What P₃ States

For `gcd(k,n) = 1`, `n` odd, `n ≥ 3`, and nonzero `v₁ ≠ v₂` in `F_{2^n}`:

```
|{(x,y,z) ∈ Δ³ : v₁·x + v₂·y + (v₁+v₂)·z = 0}| = 2^{2n-3}
```

where `Δ = {b^d + (b+1)^d + 1 : b ∈ F_{2^n}}` and `d = 4^k − 2^k + 1`.

---

## Current Sorry Status (3 remaining)

### Critical Path for P₃ (2 sorries)

| # | Sorry | File | Difficulty | Description |
|---|-------|------|-----------|-------------|
| 1 | **`kasami_is_ab`** | `KasamiFunction.lean:62` | ★★★★★ | The Kasami function `x ↦ x^{4^k-2^k+1}` is Almost Bent when `gcd(k,n)=1` and `n` odd. Theorem of Kasami (1971) / Canteaut-Charpin-Dobbertin (2000). |
| 2 | **`ab_implies_vanishing`** | `TripleCount.lean:120` | ★★★★☆ | AB implies `AlmostBentVanishing`: the triple character sum evaluates to `2^{3n-3}`. |

### Independent (not in P₃ critical path)

| # | Sorry | File | Difficulty | Description |
|---|-------|------|-----------|-------------|
| 3 | **`ab_implies_apn`** | `AlmostBent.lean:96` | ★★★☆☆ | AB ⟹ APN via fourth-moment identity. Proved in repo iteration 11 in a different framework. |

---

## What IS Fully Proved (sorry-free)

### In this project (`RequestProject/Kasami/`)

| Module | Key Results | Lines |
|--------|------------|-------|
| **Basic.lean** | `F2n n = GaloisField 2 n`, char-2 arithmetic, `card = 2^n`, power map | ~75 |
| **Trace.lean** | `tr2_sq`, `tr2_surjective`, `tr2_kernel_card`, `tr2_balanced` | ~100 |
| **AdditiveCharacter.lean** | `chi_add`, `chi_orthogonality`, `chi_sum`, `chi_inner_product` | ~130 |
| **WalshHadamard.lean** | `wht_parseval`, `wht_inversion`, `wht_sum`, `wht_abs_le` | ~140 |
| **AlmostBent.lean** | `ab_nonzero_count`, `ab_fourth_moment` | ~75 |
| **KasamiExponent.lean** | `kasamiExp_coprime`, `kasamiExp_permutation`, `kasamiExp_odd` | ~110 |
| **KasamiFunction.lean** | `kasamiF`, `kasamiDeltaGen`, `kasamiF_zero/one` | ~55 |
| **DifferenceSet.lean** | `kasamiDelta`, `kasami_P1`, `deltaCharSum` | ~45 |
| **TripleCount.lean** | `tripleCount_charSum_eq`, `tripleCount_from_vanishing` | ~120 |
| **KasamiP3.lean** | `kasami_P3_from_constructed_chi`, proof structure | ~55 |
| **FourthMoment.lean** | `wht2_power_scaling`, `power_ab_all_components`, `derivCount_even` | ~85 |

### In other repo iterations (not integrated)

| Iteration | Module | Key Results | Sorry-free? |
|-----------|--------|------------|-------------|
| `kasami-theory-04` | `GoldP3.lean` | **Gold case P₃ (k=1) fully proved** | ✅ |
| `kasami-theory-05` | `DualP3.lean` | **P₃ ↔ Dual P₃ equivalence** | ✅ |
| `kasami-theory-07` | `Char2GaussSum.lean` | Gauss sum `G(Q)² = 2^n` for char-2 quadratic forms | ✅ |
| `kasami-theory-08` | `APN/*.lean` | APN/AB definitions, Parseval, autocorrelation-Walsh identity (35/36 theorems) | 1 sorry (`ab_implies_apn`) |
| `kasami-09` | `LinearizedPoly/*.lean` | Kernel theory: `|ker(M_k)| = 2^{gcd(k,n)}`, L_k classification | 1 sorry (`kasamiDiff_eq_implies_linearized`) |
| `kasami-10` | `WalshHadamard/*.lean` | WHT: Parseval, inversion, convolution, fourth moment bound | ✅ |
| `kasami-11` | `BoolFun/*.lean` | **AB ⟹ APN proved** (in GF(2)^n framework) | ✅ |
| `kasami-12` | `Kasami/*.lean` | Full dual group orthogonality, Plancherel, Fourier inversion | ✅ |
| `kasami-13` | `Kasami/*.lean` | Cross-correlation, three-valued characterization | 1 sorry (`kasami_is_ab`) |

---

## What's Missing and Why

### 1. `kasami_is_ab` — The Deep Algebraic Theorem

**What it requires (not yet formalized):**
- **Quadratic form rank analysis over GF(2):** For the Kasami function `f(x) = x^d`, the Walsh coefficient `W_f(a)` can be expressed as a Gauss sum of the quadratic form `Q_a(x) = Tr(a·x^d)`. The rank of Q_a determines `|W_f(a)|`.
- **Linearized polynomial kernel dimension:** The radical of Q_a is controlled by the kernel of `L_k(x) = x^{2^{2k}} + x^{2^k} + x`. When `gcd(k,n) = 1` and `n` is odd, this kernel is trivial or 1-dimensional.
- **Canteaut-Charpin-Dobbertin factorization:** The Kasami derivative `f(x+a) + f(x)` factors through a linearized polynomial, connecting differential properties to the kernel structure.

**Partial infrastructure exists:** Iteration 07 has char-2 Gauss sums, iteration 09 has linearized polynomial kernel theory, but neither is complete enough to close `kasami_is_ab`.

**Estimated effort:** 1,000–2,000 lines of new Lean code, requiring:
- Port char-2 Gauss sums to work with `GaloisField 2 n` (not just `Fin n → ZMod 2`)
- Complete the CCD factorization (still sorry'd in iteration 09)
- Connect quadratic form rank to linearized polynomial kernel dimension
- Assembly

### 2. `ab_implies_vanishing` — The Bridge Theorem

**What it requires:**
- **AB ⟹ APN:** Need to port the proof from iteration 11 (done for `Fin n → ZMod 2`) to the `GaloisField 2 n` framework. The FourthMoment.lean module now provides the scaling argument for power functions.
- **|Δ| = 2^{n-1}:** Follows from APN via 2-to-1 delta generator.
- **Triple sum splitting:** Split at a=0 (gives |Δ|³) and show nonzero terms vanish.
- **Nonzero terms vanishing:** This is the hardest sub-step, requiring expressing `S_Δ(c)` via autocorrelation/WHT, then evaluating the triple product using the AB spectrum.

**Estimated effort:** 500–1,000 lines of new Lean code.

### 3. `ab_implies_apn` — Independent Result

Already proved in iteration 11 in a different framework (BoolFun over `Fin n → ZMod 2`). The proof structure is known. Porting requires building the two-argument Walsh transform infrastructure and the fourth moment identity in the current framework. The FourthMoment.lean module provides some of the necessary scaffolding.

---

## The Proof Architecture

```
kasami_P3
  ├── kasami_P3_from_constructed_chi  ✅
  │     ├── tripleCount_from_vanishing  ✅
  │     │     └── tripleCount_charSum_eq  ✅
  │     │           └── chi_sum (orthogonality)  ✅
  │     └── AlmostBentVanishing
  │           └── ab_implies_vanishing  ❌ SORRY
  │                 ├── AB ⟹ APN  ❌ (needed for |Δ| = 2^{n-1})
  │                 │     └── Fourth moment identity  ❌ (partially built)
  │                 ├── |Δ| = 2^{n-1}  ❌ (follows from APN)
  │                 └── Nonzero terms vanish  ❌ (deep character analysis)
  └── kasami_is_ab  ❌ SORRY
        ├── Linearized polynomial kernel  (partially built in iter 09)
        ├── Quadratic form rank analysis  (partially built in iter 07)
        └── CCD factorization  ❌ (sorry'd in iter 09)
```

---

## What Would It Take to Complete?

### Option A: Full General Proof (~2,500–4,000 lines)
Build all missing infrastructure from scratch:
1. Port and complete linearized polynomial kernel theory (~500 lines)
2. Build quadratic form → Gauss sum connection over GF(2^n) (~500 lines)
3. Prove CCD factorization and kasami_is_ab (~500 lines)
4. Port AB⟹APN from iteration 11 (~300 lines)
5. Prove ab_implies_vanishing via split approach (~500 lines)
6. Integration and assembly (~200 lines)

### Option B: Axiomatic Bridge (~200 lines)
Accept `kasami_is_ab` and `ab_implies_vanishing` as axioms (or parameters) and verify the rest. The existing code already does this via `kasami_P3_from_constructed_chi`, which takes `AlmostBentVanishing` as an explicit hypothesis.

### Option C: Special Case (Already Done)
The Gold case (k=1) is fully proved in iteration 04. This serves as a proof-of-concept that the framework works end-to-end.

---

## What Was Added in This Session

1. **`FourthMoment.lean`** (sorry-free, ~85 lines):
   - Extended Walsh transform `wht2 f a b = ∑_x χ(ax + bf(x))`
   - `wht2_power_scaling`: For power functions, `W(a,b) = W(a·c⁻¹, 1)` where `c^d = b`
   - `power_ab_all_components`: One-component AB implies full AB for power functions
   - `derivCount_even`: Derivative counts are always even (involution argument)

---

## References

- **Kasami (1971)** — *Information and Control* 18(4), 369–394
- **Canteaut, Charpin, Dobbertin (2000)** — *SIAM J. Discrete Math.* 13(1), 105–138
- **Carlet (2021)** — *Boolean Functions for Cryptography and Coding Theory*, Cambridge, Ch. 6
- **Gold (1968)** — *IEEE Trans. IT* 14(1), 154–156
