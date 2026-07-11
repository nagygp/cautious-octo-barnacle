# Equation (1) — self-contained MVP

This folder isolates exactly the material needed, end to end, for **equation (1)**
in the proof of Dobbertin's *Theorem 1*:

```
   c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)                     (1)
```

Entry point: `Dobbertin1999MVP/Equation1.lean` (module `Dobbertin1999MVP.Equation1`),
which re-exports the headline statements under
`Dobbertin1999.Equation1.Headlines`.

## Modules

| file | contents | depends on |
|------|----------|------------|
| `Defs.lean` | pure definitions `Tr`, `qKasami` (= `q_α`), `eqn1`, `ell`, `ell0`, `Qmap` | Mathlib only |
| `Setup.lean` | **engine-free** opening of the proof: `mersenne_coprime` / `inv_mod_exists` (`(2^k−1)⁻¹ mod (2ⁿ−1)` exists), `qKasami_zero` (`q_α(0)=0`), `Tr_one`, `qKasami_one` (`q_α(1)=k'+α·n`), `qKasami_one_eq_zero_iff` (the "only if" part) | Mathlib + `Defs` |
| `FiniteFieldPrereqs.lean` | minimal `DempwolffMueller` finite-field lemmas (Frobenius + truncated trace) | Mathlib |
| `Theorem5.lean` | the `Dobbertin.Thm5` lemmas on the dependency path | prereqs |
| `Theorem8Trace.lean` | the two `Dobbertin.Thm8` trace lemmas used | prereqs |
| `Theorem8C1.lean` | `trace_sq`, `trace_bit`, `gmap` | prereqs, `Theorem5` |
| `Q1General.lean` | the parity-general `q₁` criterion `gmap_bijective_iff` and support | `Theorem5`, `Theorem8Trace`, `Theorem8C1` |
| `Equation1.lean` | the equation-(1) thread: `theorem_1`, `eqn2_of_eqn1` ((1) ⟹ (2)), `theorem_1_case1`, `ell_eq_Q`, `theorem_1_case2` | all of the above |

Each module keeps only the declarations on the transitive dependency path of the
equation-(1) statements — the minimal set closed down to `Mathlib`. Everything is
`sorry`-free and rests only on the axioms `propext`, `Classical.choice`,
`Quot.sound`.

The two paper statements whose original skeleton forms were not provable as
stated (`eqn2_of_eqn1`, `theorem_1_case2`) carry a `**Correction.**` note
explaining the minimal faithful adjustment (the `x = 0` degeneracy).
