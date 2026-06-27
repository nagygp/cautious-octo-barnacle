import CodeTheoryCryptoEquiv.Core.KasamiAB
import CodeTheoryCryptoEquiv.DiffUniformity.KasamiDiffUniformity

/-!
# Kasami APN & AB — headline entry point

This module is the single, discoverable entry point for the two first-principles
results of the Kasami development.  It lives at the top of the self-contained
module tree `CodeTheoryCryptoEquiv/`, whose layered layout is
described in `CodeTheoryCryptoEquiv/README.md`.

Throughout, `F` is a finite field of characteristic two with
`Fintype.card F = 2 ^ n`, and `d k = 2^{2k} − 2^k + 1` is the Kasami exponent
(`CollisionAnalysis.d`).  The standing Kasami hypotheses are `1 ≤ k < n`,
`gcd(k, n) = 1` and `n` odd.

## The two headlines

* `kasami_is_apn` — the Kasami power map `x ↦ x ^ d k` is **APN**
  (almost perfect nonlinear): every nonzero derivative is at most two-to-one.
* `kasami_is_ab` — the Kasami power map is **AB** (almost bent): its Walsh
  squares take values in `{0, 2^{n+1}}`.

Both are proved from first principles; see `CodeTheoryCryptoEquiv/Core/KasamiAB.lean`
(assembly), `CodeTheoryCryptoEquiv/Core/KasamiAPN.lean` / `Core/KasamiEvenK.lean`
(the APN core) and `CodeTheoryCryptoEquiv/Walsh/` (the moment method for AB).

## Abstract foundation

The APN statement is also available as a specialization of the
characteristic-free differential-uniformity foundation
(`CodeTheoryCryptoEquiv/DiffUniformity/DifferentialUniformity.lean`):
`kasami_is_apn_diffUnif` says the Kasami map has differential uniformity exactly
two, and the bridges `walshIsAPN_iff_diffUnif_le_two` /
`kasamiIsAPN_iff_diffUnif_le_two` identify the project's APN predicates with that
abstract notion.

On the parity hypotheses: `Odd n` is genuinely required by the present AB proof
(and by the Gold-permutation step of the APN proof); the underlying
Müller–Cohen–Matthews permutation input (`DempwolffMueller.theorem_3_2`) needs
only `Odd k` and `gcd(k, n) = 1`, with no condition on the parity of `n`.
-/

namespace Kasami.Headlines

/-- **Kasami is APN.** The Kasami power map `x ↦ x ^ d k` over `GF(2ⁿ)`
(`1 ≤ k < n`, `gcd(k,n)=1`, `n` odd) is almost perfect nonlinear: every nonzero
derivative fibre has at most two points. -/
alias kasami_is_apn := KasamiAB.kasami_is_apn_pred

/-- **Kasami is APN, differential-uniformity form.** The Kasami power map has
differential uniformity exactly two (`APNLib.IsAPN`). -/
alias kasami_is_apn_diffUnif := APNLib.kasami_isAPN_diffUnif

/-- **Kasami is AB.** The Kasami power map `x ↦ x ^ d k` over `GF(2ⁿ)`
(`1 ≤ k < n`, `gcd(k,n)=1`, `n` odd) is almost bent: its Walsh squares lie in
`{0, 2^{n+1}}`.

This uses `WalshAB.IsAB`, which quantifies over every **input** mask `a ≠ 0`
(all output masks `b`).  For the literature-standard almost-bent condition,
quantifying over every **output** mask `b ≠ 0` (all input masks `a`, including
`a = 0`), see `kasami_is_ab_outputMask`; for the Kasami permutation the two
forms are equivalent. -/
alias kasami_is_ab := KasamiAB.kasami_is_ab

/-- **Kasami is AB — literature-faithful (output-mask) form.** For every nonzero
output mask `b` and every input mask `a` (including `a = 0`), the Walsh square
of `x ↦ x ^ d k` lies in `{0, 2^{n+1}}`.  This is the standard almost-bent
condition on the component functions `Tr (b · x^{d k})`, `b ≠ 0`. -/
alias kasami_is_ab_outputMask := KasamiAB.kasami_is_ab_outputMask

end Kasami.Headlines
