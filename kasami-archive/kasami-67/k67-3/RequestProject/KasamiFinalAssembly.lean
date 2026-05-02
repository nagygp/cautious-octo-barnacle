/-
# KasamiFinalAssembly.lean — Complete Assembly of the Kasami Triple Count Proof

This file assembles the complete, zero-sorry proof of the P₃ triple count
for Almost Bent functions over GF(2^n), linking all verified modules.

## Proof Chain (all imported, zero sorries)

1. **Defs.lean**: Core definitions (KasamiContext, walshTransform, IsAlmostBent, tripleCount)
2. **TraceNondeg.lean**: Trace non-degeneracy for finite field extensions
   - `trace_nondegenerate_finiteField`: ∀ z, (∀ x, Tr(x·z) = 0) → z = 0
3. **KasamiPolarExpansion.lean**: Gold/Kasami polar expansion
   - `gold_polar_expand`: (x+y)^{2^k+1} + x^{2^k+1} + y^{2^k+1} = x·y^{2^k} + x^{2^k}·y
   - `kasami_polar_expansion`: Tr(a · polar(x,y)) = Tr(x · L_a(y))
   - `kasami_radical_eq_kernel`: rad(Q_a) = ker(L_a)
4. **PolarFormBridge.lean**: Abstract bridge theorem + kernel bound
   - `bridge_radical_kernel`: rad(Q) = ker(L) via trace non-degeneracy
   - `kasami_kernel_small`: |ker(L_a)| ≤ 2
5. **WalshP3.lean**: Spectral analysis
   - `character_orthogonality`: ∑_a (-1)^{Tr(ax)} = 0 for x ≠ 0
   - `walsh_parseval`: ∑_a W_f(a)² = |F|²
6. **KasamiFinal.lean**: Final proof assembly
   - `walsh_sum_from_f0`: ∑_a W(a) = |F| when f(0)=0
   - `ab_walsh_cube_sum`: ∑_a W(a)³ = 2^{2n+1} for balanced AB functions
   - `triple_correlation_eq_walsh_cubes`: |F|·C₃ = ∑_a W(a)³
   - `triple_count_balanced_expansion`: 8·T₃ = |F|² - C₃
   - `p3_triple_count_corrected`: T₃ = 2^{2n-3} - 2^{n-2}

## Main Result

For an Almost Bent function f : GF(2^n) → GF(2) with n odd, n ≥ 3,
the number of pairs (x, y) such that f(x) = f(y) = f(x+y) = 1 is:

    T₃ = 2^{2n-3} - 2^{n-2}

## Note on the Original Conjecture

The original conjecture stated T₃ = 2^{2n-3}. This was corrected during
formalization: a direct computation over GF(2³) with d=3 gives T₃ = 6,
not 8 = 2^{2·3-3}. The correct formula 2^{2n-3} - 2^{n-2} = 8 - 2 = 6
matches. The error in the original was in the Walsh convolution identity
linking T₃ to ∑W³; the correct relationship goes through the triple
correlation function C₃ and the balanced expansion 8·T₃ = |F|² - C₃.
-/

import RequestProject.Defs
import RequestProject.TraceNondeg
import RequestProject.KasamiPolarExpansion
import RequestProject.PolarFormBridge
import RequestProject.WalshP3
import RequestProject.KasamiFinal

/-! ## Re-export of the main theorem for convenience -/

/-- The complete P₃ triple count theorem for Almost Bent functions.

For an Almost Bent function f : GF(2^n) → GF(2) with n odd, n ≥ 3,
f(0) = 0, and f balanced (W_f(0) = 0):

    T₃ = 2^{2n-3} - 2^{n-2}

All hypotheses are satisfied by the Kasami power function
f(x) = Tr(x^d) where d = 2^{2k} - 2^k + 1 and n = 2k+1:
- AB property: follows from dim(rad(Q_a)) ≤ 1 (via kasami_radical_eq_kernel
  and kasami_kernel_small)
- f(0) = 0: Tr(0) = 0
- Balanced: x ↦ x^d is a permutation since gcd(d, 2^n-1) = 1

The proof chain:
1. 8·T₃ = |F|² - C₃  (triple_count_balanced_expansion)
2. |F|·C₃ = ∑W(a)³   (triple_correlation_eq_walsh_cubes)
3. ∑W(a)³ = 2^{2n+1}  (ab_walsh_cube_sum)
4. C₃ = 2^{n+1}, so 8·T₃ = 2^{2n} - 2^{n+1}
5. T₃ = 2^{2n-3} - 2^{n-2}
-/
theorem kasami_triple_count_assembly
    (n : ℕ) (hn : 3 ≤ n) (hn_odd : Odd n)
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (hcard : Fintype.card F = 2 ^ n)
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_zero : Tr 0 = 0)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (f : F → ZMod 2)
    (hAB : IsAlmostBent F Tr f ((n + 1) / 2))
    (hf0 : f 0 = 0)
    (hbal : walshTransform F Tr f 0 = 0) :
    tripleCount F Tr f = (2 : ℤ) ^ (2 * n - 3) - (2 : ℤ) ^ (n - 2) :=
  p3_triple_count_corrected n hn hn_odd F hcard Tr hTr_add hTr_zero hTr_sep f hAB hf0 hbal
