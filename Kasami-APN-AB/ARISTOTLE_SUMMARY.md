# Summary of changes for run 20d4e061-b8cf-4e16-86c4-0992598a39b1
Refactored the Kasami APN & AB development into a standalone, self-contained library rooted at `RequestProject/`, with `RequestProject/Headlines.lean` as the single entry point.

What changed:
- Moved all module folders (`APN/`, `Core/`, `DiffUniformity/`, `FiniteField/`, `Support/`, `Walsh/`) and `Headlines.lean` into `RequestProject/` (via `git mv`, preserving history).
- Rewrote every `import` from the old `RequestProject.KasamiHeadlines.*` module paths to `RequestProject.*`, matching the new physical layout (the old paths did not match the file locations, so the project did not build before).
- Updated the in-source docstring/comment path references (e.g. in `Headlines.lean`, `Core/KasamiAB.lean`, `DiffUniformity/KasamiDiffUniformity.lean`, `Walsh/WalshDivisibility.lean`) to the new `RequestProject/...` paths.
- Simplified `lakefile.toml` to a single library `RequestProject` (glob `RequestProject.+`, default target `RequestProject`), replacing the previous per-folder libraries.
- Updated `README.md` to describe the new `RequestProject/`-rooted layout and entry point.

Verification:
- `lake build` completes successfully for the whole library, including `RequestProject.Headlines` (only pre-existing linter warnings, no errors).
- No real `sorry` remains (only the word appears inside a comment).
- The three headline results — `Kasami.Headlines.kasami_is_apn`, `kasami_is_ab`, and `kasami_is_apn_diffUnif` — each depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

The result is a standalone verified whole with `Headlines.lean` as its entry, with module folders under `RequestProject/` rather than `KasamiHeadlines/`.