# Dependency DAG: Mathlib → headline of (1) ⟹ (2)

The headline for the "(1) ⟹ (2)" step of Theorem 1 is

```
Dobbertin1999.Paper.eqn2_of_eqn1
  (re-exported as Dobbertin1999.Equation1.Headlines.eqn2_of_eqn1)
```

Statement: for `x ≠ 0`, if equation (1) `eqn1 n k k' α c x` holds, then equation (2)
`ell k c x = 0`.

Below is the **exact transitive dependency DAG** of that theorem, restricted to the
project's own declarations (everything else it uses is Mathlib). Edges point
`A → B` meaning "`A` is proved using `B`". Auto-generated `._proof_*` / `._simp_*`
helper terms produced by the elaborator are omitted from the picture (they carry no
mathematical content); they are listed at the end for completeness.

## Layered view (Mathlib at the bottom, headline at the top)

```
                         eqn2_of_eqn1              ← Equation1/Equation1.lean   [(1) ⟹ (2)]
              ┌───────────────┼───────────────┬─────────────┐
              │               │               │             │
        Thm5.ell_of_eq   Thm8C1.trace_bit   eqn1        ell  (def)            ← the 3 substantive inputs
              │               │               │
   ┌──────────┼─────┐        │              Tr (def)
   │          │     │        │
 pTrace_    sTrace_ bit_pow  trace_sq
 telescope  eq_pTrace          │
   │  │        │        ┌──────┼──────────────┐
   │  │      pTrace,   truncTrace   truncTrace_sq_add_self
   │  │      sTrace      (def)              │
   │  pow_frob_kk'                     truncTrace (def)
   │      │
 pTrace_  frob_mod
 telescope_raw │
   │        frob_cycle
 pTrace (def)

        ── everything below the named lemmas rests directly on Mathlib ──
```

## The three branches that meet at `eqn2_of_eqn1`

`eqn2_of_eqn1` = `Dobbertin.Thm5.ell_of_eq` applied with a side condition
`Tr x ∈ {0,1}` (from `Dobbertin.Thm8C1.trace_bit`), unfolding the definitions
`eqn1`, `ell`, `Tr`.

1. **Telescoping / Artin–Schreier branch → `Dobbertin.Thm5.ell_of_eq`**
   (file `Equation1/Theorem5.lean`, the real content of (1) ⟹ (2)):
   - `ell_of_eq` → `pTrace`, `sTrace`, `sTrace_eq_pTrace`, `pTrace_telescope`, `bit_pow`
   - `pTrace_telescope` → `pTrace`, `pTrace_telescope_raw`, `pow_frob_kk'`
   - `pTrace_telescope_raw` → `pTrace`
   - `sTrace_eq_pTrace` → `pTrace`, `sTrace`
   - `pow_frob_kk'` → `DempwolffMueller.frob_mod`
   - `DempwolffMueller.frob_mod` → `DempwolffMueller.frob_cycle`
   - `DempwolffMueller.frob_cycle`, `pTrace`, `sTrace`, `bit_pow` → **Mathlib**

2. **Trace-parity branch → `Dobbertin.Thm8C1.trace_bit`** (`Tr x ∈ {0,1}`)
   (files `Equation1/Theorem8C1.lean`, `Equation1/FiniteFieldPrereqs.lean`):
   - `trace_bit` → `Dobbertin.Thm8C1.trace_sq`, `DempwolffMueller.truncTrace`
   - `trace_sq` → `DempwolffMueller.truncTrace`, `DempwolffMueller.truncTrace_sq_add_self`
   - `truncTrace_sq_add_self`, `truncTrace` (def) → **Mathlib**

3. **Definitions branch** (`Equation1/Defs.lean`):
   - `eqn1` → `Tr`
   - `Tr`, `ell` → **Mathlib**

## Module-level DAG (which files feed which)

```
Mathlib
  ├── Equation1/Defs.lean                (Tr, ell, eqn1)
  ├── Equation1/FiniteFieldPrereqs.lean  (frob_cycle→frob_mod; truncTrace, truncTrace_sq_add_self)
  │        │
  │        ├── Equation1/Theorem5.lean   (pTrace/sTrace telescoping ⇒ ell_of_eq)
  │        └── Equation1/Theorem8C1.lean (trace_sq ⇒ trace_bit)
  │                 │
  └─────────────────┴──── Equation1/Equation1.lean (eqn2_of_eqn1)
```

## Not on this path

`Equation1/Theorem8Trace.lean` and `Equation1/Q1General.lean` (and the full
`theorem_1` / `theorem_1_case1` / `theorem_1_case2` bijectivity machinery) are
**not** used by `eqn2_of_eqn1`; the (1) ⟹ (2) step alone needs only the two
lemmas `Thm5.ell_of_eq` and `Thm8C1.trace_bit` plus the definitions.

## Auto-generated helper terms (elaborator artifacts, no math content)

`ell_of_eq._proof_1_1..4`, `trace_sq._proof_1_1`, `trace_bit._proof_1_1`,
`truncTrace_sq_add_self._simp_1_1/2`. These are the closure/simp/proof terms the
compiler emits for the named lemmas above and depend only on those same named
lemmas / Mathlib.
```
