/-
# Kasami P₃ Proof Project

A formalization of P₃ for Kasami/Gold functions over finite fields of
characteristic 2, with supporting theory for Fourier analysis on finite fields.

## Modules

1. **TraceChar** — Additive characters of finite fields via trace
   - `χ` : canonical additive character χ(a,x) = (-1)^{Tr(ax)}
   - Character orthogonality, dual orthogonality
   - Trace fiber balance and kernel cardinality
   - **Fully proved** (0 sorry)

2. **WalshHadamard** — Walsh–Hadamard transform
   - `walshCoeff` : Walsh coefficients Ŝ(b) = ∑ f(x)χ(b,x)
   - Parseval's identity, convolution theorem, inversion formula
   - **Fully proved** (0 sorry)

3. **SpectralIdentity** — The spectral identity (bridge spatial ↔ spectral)
   - `spectral_identity` : ∑ Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c)) = |F|·N(c)
   - `ratio_reduction` : reducing (v₁,v₂) to normalized form
   - **Fully proved** (0 sorry)

4. **APNTheory** — APN and AB function theory
   - `kasamiExponent`, `isAPN`, `AlmostBentVanishing`
   - `P3_from_AB` : AlmostBentVanishing ⟹ P₃
   - **Fully proved** (0 sorry)

5. **LinearizedPoly** — Linearized polynomials over F_{2^n}
   - `artinSchreier` : x ↦ x² + x, its kernel {0,1}, image = ker(Tr)
   - `IsLinearized`, `L_op`, `L_op_linearized`
   - `gold_delta_eq_trace_kernel` : Δ₁ = ker(Tr)
   - **Fully proved** (0 sorry)

6. **GoldP3** — Gold case P₃ (k = 1)
   - Walsh spectrum of ker(Tr): Ŝ(b) = |K| if b ∈ {0,1}, else 0
   - `trace_annihilator` : K^⊥ = {0, 1}
   - `gold_P3` : |F|·N(c) = |ker(Tr)|³ for c ≠ 0, 1
   - **Fully proved** (0 sorry)
   - Standard axioms only: propext, Classical.choice, Quot.sound

7. **KasamiFramework** — General Kasami framework
   - `general_P3` : P₃ from AlmostBentVanishing (proved)
   - `kasami_AB_vanishing` : 3-valued Walsh spectrum (**sorry** — deep theorem)
   - `kasami_P3` : general P₃ (uses kasami_AB_vanishing)

## Proof Status

| Result | Status |
|--------|--------|
| `spectral_identity` | ✅ Fully proved |
| `P3_from_AB` | ✅ Fully proved |
| `gold_P3` | ✅ Fully proved, zero sorry, standard axioms |
| `parseval` | ✅ Fully proved |
| `walsh_inversion` | ✅ Fully proved |
| `walshCoeff_conv` | ✅ Fully proved |
| `kasami_AB_vanishing` | ⚠️ Sorry — requires formalization of Kasami 1971 |
-/

import RequestProject.TraceChar
import RequestProject.WalshHadamard
import RequestProject.SpectralIdentity
import RequestProject.APNTheory
import RequestProject.LinearizedPoly
import RequestProject.GoldP3
import RequestProject.KasamiFramework
