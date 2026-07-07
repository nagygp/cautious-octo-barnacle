import RequestProject.Dobbertin1999.Core
import RequestProject.Dobbertin1999.AdditivePolyRootCount
import RequestProject.Dobbertin1999.MCM
import RequestProject.Dobbertin1999.MCMtoAPN
import RequestProject.Dobbertin1999.APN
import RequestProject.Dobbertin1999.GenKasamiPoly
import RequestProject.Dobbertin1999.Theorem1
import RequestProject.Dobbertin1999.Singer

/-!
# Dobbertin (1999) — MCM, MCM → APN, APN: transcription entry point

This is the single entry point for a faithful, end-to-end formalisation of the
**MCM**, **MCM → APN**, and **APN** parts of

> Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets"*, in *Difference Sets, Sequences and their Correlation
> Properties*, NATO Sci. Ser. C **542**, Kluwer Academic Publishers, 1999,
> pp. 133–158.

The three parts are transcribed in

* `RequestProject/Dobbertin1999/MCM.lean` — the Müller–Cohen–Matthews permutation
  polynomial theorem (Section 2 / the MCM engine);
* `RequestProject/Dobbertin1999/MCMtoAPN.lean` — the bridge (key identity, Gold
  permutation, MCM ∘ Gold injectivity, two-to-one collapse) used in the proof of
  Corollary 2;
* `RequestProject/Dobbertin1999/APN.lean` — Corollary 2: Kasami power functions
  are APN.

Every statement is proved by **reusing** the project's existing, `sorry`-free
finite-field and Kasami development
(`RequestProject/FiniteField/Thm32.lean`, `RequestProject/Core/KasamiAPN.lean`,
`RequestProject/Core/KasamiAB.lean`); the transcription re-presents those results
in the structure and notation of the paper.

## The MCM → APN chain, end to end

```
Dobbertin1999.MCM.mcm_permutation_ktransfer        (Müller–Cohen–Matthews / Theorem 1 engine)
        │   x ↦ L_k(x)·x^{k'} is a permutation of 𝔽_{2ⁿ}
        ▼
Dobbertin1999.MCMtoAPN.kasami_key_identity          ((x+1)^d + x^d + 1)·(x²+x)^{2^k} = (x^{2^k}+x)^{2^k+1}
Dobbertin1999.MCMtoAPN.gold_permutation             y ↦ y^{2^k+1} bijective
Dobbertin1999.MCMtoAPN.mcm_injective_bridge         MCM ∘ Gold injectivity
Dobbertin1999.MCMtoAPN.kasami_collision_forces_equal_u   collision ⟹ x²+x = y²+y
        │   (t ↦ t^{2^k}+t is two-to-one)
        ▼
Dobbertin1999.APN.kasami_is_apn                     Corollary 2: x ↦ x^d is APN
Dobbertin1999.APN.kasami_is_apn_solution_count      Nyberg form: 0 or exactly 2 solutions
```

The whole chain is `sorry`-free and rests only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Dobbertin1999.Headlines

/-- **MCM permutation theorem** (Müller–Cohen–Matthews). See
`Dobbertin1999.MCM.mcm_permutation`. -/
alias mcm_permutation := Dobbertin1999.MCM.mcm_permutation

/-- **MCM permutation theorem, `k'`-transfer form** — the shape consumed by the
APN chain.  See `Dobbertin1999.MCM.mcm_permutation_ktransfer`. -/
alias mcm_permutation_ktransfer := Dobbertin1999.MCM.mcm_permutation_ktransfer

/-- **The key identity** linking the Kasami derivative to the Gold exponent.  See
`Dobbertin1999.MCMtoAPN.kasami_key_identity`. -/
alias kasami_key_identity := Dobbertin1999.MCMtoAPN.kasami_key_identity

/-- **Corollary 2** — Kasami power functions are APN (collision form).  See
`Dobbertin1999.APN.kasami_is_apn`. -/
alias kasami_is_apn := Dobbertin1999.APN.kasami_is_apn

/-- **Corollary 2** — Kasami power functions are APN (Nyberg solution-count form).
See `Dobbertin1999.APN.kasami_is_apn_solution_count`. -/
alias kasami_is_apn_solution_count := Dobbertin1999.APN.kasami_is_apn_solution_count

/-! ## Layer A — additive / linearized-polynomial root count (upstreamable)

New foundational, Mathlib-rooted layer for the full-paper transcription (see
`DOBBERTIN1999_FULL_ROADMAP.md`).  Each is `sorry`-free on the standard axioms. -/

/-- **Root count of a linearized equation.** `Σ_{i<m} a i · x^{2^i} = c` has `0`
or `#(ker L)` solutions.  See
`Dobbertin1999.AdditivePolyRootCount.card_fiber_linearized`. -/
alias card_fiber_linearized := Dobbertin1999.AdditivePolyRootCount.card_fiber_linearized

/-- **`t ↦ t^{2^k} + t` is two-to-one** (the collapse step of Corollary 2 /
Theorem 1), over `𝔽_{2ⁿ}` with `gcd(k, n) = 1`.  See
`Dobbertin1999.AdditivePolyRootCount.frobSubSelf_two_to_one`. -/
alias frobSubSelf_two_to_one := Dobbertin1999.AdditivePolyRootCount.frobSubSelf_two_to_one

/-! ## Layer B — the generalized Kasami / MCM / linearized polynomials

Function-level definitions of the paper's Section 2 polynomials, sitting on the
core, with the root count of the linearized `ℓ` obtained from Layer A.  Each is
`sorry`-free on the standard axioms. -/

/-- **The generalized Kasami polynomial `q_α`** (Dobbertin's `Q_{k,k'}`).  See
`Dobbertin1999.GenKasamiPoly.genKasamiPoly`. -/
alias genKasamiPoly := Dobbertin1999.GenKasamiPoly.genKasamiPoly

/-- **The MCM polynomial `P_β`** of the paper's Section 2.  See
`Dobbertin1999.GenKasamiPoly.mcmPoly`. -/
alias mcmPoly := Dobbertin1999.GenKasamiPoly.mcmPoly

/-- **Root count of the linearized polynomial `ℓ` of eq. (2), via Layer A** —
`ℓ(x) = 0` has `0` or `#(ker L)` solutions.  See
`Dobbertin1999.GenKasamiPoly.affineLinPoly_root_count`. -/
alias affineLinPoly_root_count := Dobbertin1999.GenKasamiPoly.affineLinPoly_root_count

/-! ## Layer C — Theorem 1 / the permutation-polynomial pillar

The permutation-polynomial content the paper's title advertises: the Kasami power
function is a permutation, and its derivative is a two-to-one map (via Layer A's
two-to-one result).  Each is `sorry`-free on the standard axioms. -/

/-- **The Kasami power function is a permutation of `𝔽_{2ⁿ}`.**  See
`Dobbertin1999.Theorem1.kasamiPow_bijective`. -/
alias kasamiPow_bijective := Dobbertin1999.Theorem1.kasamiPow_bijective

/-- **The Kasami derivative `x ↦ (x+1)^d + x^d` is a two-to-one map** (Dobbertin /
Dillon–Dobbertin).  See `Dobbertin1999.Theorem1.kasamiDeriv_two_to_one`. -/
alias kasamiDeriv_two_to_one := Dobbertin1999.Theorem1.kasamiDeriv_two_to_one

/-! ## Layer D — cyclic difference sets with Singer parameters

The Singer difference-set foundation of the paper's third pillar, built on the
additive-character Fourier bridge.  Each is `sorry`-free on the standard axioms. -/

/-- **The Singer set `{x ∈ L* : Tr x = 0}` is a cyclic difference set with Singer
parameters** `(2ⁿ − 1, 2^{n-1} − 1, 2^{n-2} − 1)`.  See
`Dobbertin1999.Singer.singer_isMulDifferenceSet`. -/
alias singer_isMulDifferenceSet := Dobbertin1999.Singer.singer_isMulDifferenceSet

/-- **Size of the Singer set** `= 2^{n-1} − 1`.  See
`Dobbertin1999.Singer.singerSet_card`. -/
alias singerSet_card := Dobbertin1999.Singer.singerSet_card

end Dobbertin1999.Headlines
