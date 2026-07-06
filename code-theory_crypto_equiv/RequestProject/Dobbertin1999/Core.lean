import RequestProject.FiniteField.Thm32
import RequestProject.FiniteField.ExpArith
import RequestProject.APN.Defs
import RequestProject.Core.CrossFormAnalysis
import RequestProject.Core.KasamiAPN
import RequestProject.Walsh.Transform

/-!
# Dobbertin (1999) — the Mathlib-rooted foundational core

This module is **Layer 0** of the full-paper roadmap
([`DOBBERTIN1999_FULL_ROADMAP.md`](../../DOBBERTIN1999_FULL_ROADMAP.md)) for

> Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets"*, NATO Sci. Ser. C **542**, Kluwer, 1999, pp. 133–158.

It is the **established core rooted in Mathlib**: a single, discoverable
re-export of the finite-field / trace / exponent-arithmetic / additive-character
prerequisites that every higher layer of the transcription rests on.  Nothing new
is proved here — each item below is an existing, `sorry`-free declaration of the
project, presented with a clean, upstreamable signature so the higher layers
(the MCM engine, Corollary 2, Theorem 1, and the difference-set family) import
*this* rather than reaching into scattered internal files.

The whole core rests only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.

## Contents

### Linearized (truncated) trace — the numerator building block of `q_α`, `P_β`
* `truncTrace m x = Σ_{i<m} x^{2^i}` and its `𝔽₂`-linearity (`truncTrace_add`);
* the telescoping / Artin–Schreier identities
  (`truncTrace_sq_add_self`, `truncTrace_artin_schreier`).

### Kasami-exponent arithmetic
* `kasamiD k = 2^{2k} − 2^k + 1` (the Kasami exponent `d`);
* `kasamiD_coprime_card_sub_one` (`gcd(d, 2ⁿ−1) = 1`), the reason `x ↦ x^d`
  permutes the field.

### The MCM permutation engine (Müller–Cohen–Matthews / Dempwolff–Müller)
* `mcm_engine` — `x ↦ L_m(x)·x^{2^{n-1}−2^{m-1}−1}` is a bijection;
* `mcm_engine_ktransfer` — the `k′`-transfer shape consumed by the APN/Theorem 1
  chain.

### The additive sign character and its orthogonality (the Fourier layer)
* `signChar x = χ(x) = (−1)^{Tr x}`, multiplicativity (`signChar_mul`), and the
  two orthogonality relations (`signChar_sum`, `signChar_sum_dual`).
-/

namespace Dobbertin1999.Core

/-! ## Linearized (truncated) trace -/

/-- The **linearized (truncated) trace** `L_m(x) = Σ_{i=0}^{m-1} x^{2^i}`, the
numerator building block of the MCM polynomial `P_β` and the generalized Kasami
polynomial `q_α`.  (Re-export of `DempwolffMueller.truncTrace`.) -/
abbrev truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  DempwolffMueller.truncTrace m x

/-- `L_m` is `𝔽₂`-linear: `L_m(x + y) = L_m(x) + L_m(y)`. -/
alias truncTrace_add := DempwolffMueller.truncTrace_add

/-- Telescoping: `L_m(x)² + L_m(x) = x^{2^m} + x`. -/
alias truncTrace_sq_add_self := DempwolffMueller.truncTrace_sq_add_self

/-- Artin–Schreier telescoping: `L_k(x² + x) = x^{2^k} + x` (the identity tying
the Kasami derivative to the linearized trace). -/
alias truncTrace_artin_schreier := KasamiAPN.truncTrace_artin_schreier

/-! ## Kasami-exponent arithmetic -/

/-- The **Kasami exponent** `d(k) = 2^{2k} − 2^k + 1`.  (Re-export of
`CollisionAnalysis.d`.) -/
abbrev kasamiD (k : ℕ) : ℕ := CollisionAnalysis.d k

/-- `gcd(d(k), 2ⁿ − 1) = 1` under the Kasami conditions — the reason the Kasami
power map `x ↦ x^{d(k)}` is a permutation of `𝔽_{2ⁿ}`. -/
alias kasamiD_coprime_card_sub_one := CollisionAnalysis.d_coprime_card_sub_one

/-! ## The MCM permutation engine (Müller–Cohen–Matthews) -/

/-- **MCM permutation engine** (Dempwolff–Müller Theorem 3.2).  For `m` odd,
`1 < m < n`, `gcd(m, n) = 1`, the map `x ↦ L_m(x)·x^{2^{n-1}−2^{m-1}−1}` is a
bijection of `𝔽_{2ⁿ}`. -/
alias mcm_engine := DempwolffMueller.theorem_3_2

/-- **MCM engine, `k′`-transfer form** — `x ↦ L_m(x)·x^{k'}` for any `k'` with the
transfer congruence `(2^{n-1}−2^{m-1}−1)·k' ≡ 2^{m-1} (mod 2ⁿ−1)`.  This is the
shape the APN chain (and Theorem 1) consume. -/
alias mcm_engine_ktransfer := DempwolffMueller.LxXk'_bijective

/-! ## The additive sign character (the Fourier layer) -/

/-- The **additive sign character** `signChar x = (−1)^{Tr x}`, valued in `ℤ`.
(Re-export of `WalshAB.χ`.) -/
noncomputable abbrev signChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] (x : F) : ℤ :=
  WalshAB.χ x

/-- Multiplicativity of the sign character: `signChar (x + y) = signChar x · signChar y`. -/
alias signChar_mul := WalshAB.χ_mul

/-- Character orthogonality (Schur): `∑_x signChar (c·x)` is `#F` if `c = 0`, else `0`. -/
alias signChar_sum := WalshAB.χ_sum_eq

/-- Dual orthogonality relation. -/
alias signChar_sum_dual := WalshAB.χ_sum_dual

end Dobbertin1999.Core
