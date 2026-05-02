/-
# Kasami Power Function P₃ Triple Count — Unified Proof

This project merges two approaches (kasami-65 "Top-Down" and kasami-66 "Bottom-Up")
to provide a verified proof of the P₃ triple count formula for Almost Bent functions.

## Module Structure

### Algebraic Foundations (from kasami-66, 0 sorry each)
- `CCDCounting.lean`: Frobenius-GCD theorem, CCD kernel bound, gcd(k, 2k+1)=1
- `KasamiPolarExpansion.lean`: Polar expansion, trace adjoint, radical = kernel
- `GoldKernelBound.lean`: |ker(L_a)| ≤ 2 for Gold linearized operator

### Fourier Analysis (from kasami-65, 0 sorry each)
- `Defs.lean`: Core definitions (walshTransform, IsAlmostBent, tripleCount)
- `WalshFourier.lean`: Character orthogonality, Parseval's identity

### Final Assembly (0 sorry)
- `KasamiFinalAssembly.lean`: The corrected triple count theorem

## Main Result

`p3_triple_count_corrected`: For an Almost Bent function f : GF(2^n) → GF(2)
with n odd, n ≥ 3, f(0) = 0, and f balanced:

    T₃ = 2^{2n-3} - 2^{n-2}

All proofs are machine-verified with zero sorry.
-/

-- Algebraic foundations
import RequestProject.CCDCounting
import RequestProject.KasamiPolarExpansion
import RequestProject.GoldKernelBound

-- Fourier analysis
import RequestProject.Defs
import RequestProject.WalshFourier

-- Final assembly
import RequestProject.KasamiFinalAssembly
