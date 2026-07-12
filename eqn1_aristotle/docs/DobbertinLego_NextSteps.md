# Dobbertin Lego — further abstraction of step (1) ⟹ (2)

This note records four abstraction steps built on top of the `DobbertinLego`
library.  Every declaration below is `sorry`-free and depends only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.

## 1. `φⁿ = 1` from finite dimension, not raw cardinality
File: `DobbertinLego/CategoryTheory.lean`.

The identity `φⁿ = 1` (i.e. the Frobenius is annihilated by `Xⁿ − 1`) is now
sourced from the **order** of the Frobenius equalling the object's dimension,
rather than from Fermat/`FiniteField.pow_card`:

- `algEndToLin` — the multiplicative map `(F →ₐ[𝔽₂] F) →* Module.End 𝔽₂ F`.
- `frobLin_orderOf` — `orderOf (frobeniusAlgHom) = [F : 𝔽₂]`
  (`FiniteField.orderOf_frobeniusAlgHom`).
- `frobLin_pow_finrank` — `φ^{[F:𝔽₂]} = 1`, proved by transporting
  `pow_orderOf_eq_one` across `algEndToLin` (no `FiniteField.pow_card`).
- `frobLin_pow_card` — the old `φⁿ = 1` (`#F = 2ⁿ`), now re-derived from
  `frobLin_pow_finrank` + `finrank_eq`.

`[F : 𝔽₂]` is the dimension of `F` as a dualizable / finite-dimensional object of
`FGModuleCat 𝔽₂`, so finite order is read off the object's finite dimension. (A
fully generic categorical eval/coeval *trace* is not yet in Mathlib; the paper
trace ↔ `Algebra.trace 𝔽₂ F` link is `Categorical.trace_eq_algebraMap_trace`.)

## 2. Collapse the type-class bundle into the object
File: `DobbertinLego/ObjectFirst.lean`.

Primary datum: `F` as an object of `Mod_{𝔽₂}` — `[Field F] [Fintype F]
[Algebra (ZMod 2) F]` — with multiplication supplied by the monoid object.

- `objCharP` — `CharP F 2` is now a **derived instance**
  (`charP_of_injective_algebraMap`), not a hypothesis.
- `objAlg`, `objMonObj` — `F` as an `AlgCat 𝔽₂` / commutative monoid object of
  `ModuleCat 𝔽₂` (the source of multiplication).
- `objFrobLin`, `objFrobLin_telescope`, `objFrobLin_pow_finrank`, `objTrace_isBit`
  — the categorical chain re-run with the object's own algebra instance, entirely
  in universe `0` (no `Type` / `Type*` split).
- `equation2_of_equation1_obj` — the headline `(1) ⟹ (2)` with the collapsed
  bundle.

(Field-ness and finiteness remain genuine hypotheses: a commutative monoid object
of `ModuleCat 𝔽₂` is an algebra, not automatically a finite field.)

## 3. Frobenius as internal arrow data
File: `DobbertinLego/CategoryTheory.lean`.

- `frobMor : End (ModuleCat.of 𝔽₂ F)` — the Frobenius as a literal **morphism** of
  `ModuleCat 𝔽₂`, the preimage of `frobLin` under `ModuleCat.endRingEquiv`
  (`endRing_iso`).
- `endRing_iso_frobMor` — the equiv carries `frobMor` back to `frobLin`.
- `frobMor_telescope` — the telescope run *inside* the categorical endomorphism
  ring `End X` (an instance of `preadditive_telescope`), then transported.

## 4. Generalize the base field `𝔽₂ ⟶ 𝔽_q`
File: `DobbertinLego/GenBase.lean`.

The base-agnostic machinery over an arbitrary finite base field `𝔽_q` (`q = pˢ`),
exposing which steps need characteristic `2`:

- `baseFrob`, `baseFrobEndo` — the relative Frobenius `x ↦ x^{pˢ}` as an additive
  endomorphism (additivity is characteristic-`p`, `add_pow_char_pow`).
- `baseFrobEndo_pow`, `baseFrobEndo_pow_card` — iterates `x ↦ x^{qʳ}` and Fermat
  `φⁿ = 1` on `𝔽_{qⁿ}`.
- `baseTrace`, `baseTrace_telescope` — the relative trace and its Artin–Schreier
  telescope (`iterSum_telescope`, **no characteristic used**).
- `baseTrace_fixed` — the relative trace lands in the base field `𝔽_q`.
- `neg_eq_self`, `sq_self_iff_bit` — the two genuinely characteristic-`2` inputs
  isolated (`−1 = +1`; the fixed set of the absolute Frobenius is `{0,1} = 𝔽₂`).
- `baseTrace_isBit` — the char-`2` "trace is a bit" recovered as the `p = 2, s = 1`
  instance of the generic development.
