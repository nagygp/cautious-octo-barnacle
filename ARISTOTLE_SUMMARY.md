# Summary of changes for run 1a1845f8-3f4b-4f74-aa01-f776b83e7dfd
Connected each of the two folders to its own runnable Lean library and gave each a README that maps the module DAG.

## What I did

Both folders previously contained loose `.lean` files whose `import RequestProject.*` paths matched no library and so did not build (and the root `lakefile.toml` had invalid glob entries). I turned each into a distinct, buildable `lean_lib` target of the root package (which already vendors a fully-built Mathlib), so the two libraries coexist without module-name collisions.

- **`code-theory_crypto_equiv/`** → library `CodeTheoryCryptoEquiv`. Moved all module folders/`Headlines.lean` under `code-theory_crypto_equiv/CodeTheoryCryptoEquiv/` (via `git mv`, preserving history) and rewrote every `RequestProject.` reference to `CodeTheoryCryptoEquiv.`.
- **`conjectures-mtuple-triple_count/`** → library `ConjecturesMTupleTripleCount`. Same treatment under `conjectures-mtuple-triple_count/ConjecturesMTupleTripleCount/`, rewriting `RequestProject.` → `ConjecturesMTupleTripleCount.`.

This mirrors the existing `Kasami-APN-AB/` layout (a named container folder holding a uniquely-named module root), which I left untouched.

Two small fixes were needed to make the conjectures library actually compile (it referenced things that did not exist before):
- Added the missing aggregator module `ConjecturesMTupleTripleCount/MTuple.lean` (re-exports `MTuple.Count` and `MTuple.Disproof`) so `import ...MTuple` resolves.
- Added `MTuple.triple_count_of_vanish`, the `m = 3` specialization of the already-proven `MTuple.imgCount_of_vanish`, which several `Foundations/` modules used but which had no definition.

Updated the root `lakefile.toml` to declare the two libraries with the correct `srcDir`/glob and set them as the default targets.

## READMEs (DAG maps)

- `code-theory_crypto_equiv/README.md` and `conjectures-mtuple-triple_count/README.md` each describe the library's purpose, its entry point(s), and a layer-by-layer dependency DAG (arrows = imports) with a per-directory/per-module role table.

## Verification

- `lake build CodeTheoryCryptoEquiv` and `lake build ConjecturesMTupleTripleCount` both succeed; a full `lake build` completes successfully.
- `ConjecturesMTupleTripleCount` is entirely `sorry`-free. In `CodeTheoryCryptoEquiv` the only real `sorry`s are in `DiffUniformity/DifferentialUniformityUpstreamSkeleton.lean`, which is an explicit placeholder skeleton (advertised as such in its own header); everything else is complete. No `axiom` or `@[implemented_by]` declarations were introduced.

No user content was deleted — files were relocated and their import prefixes updated, and the previously-broken references were repaired rather than removed.