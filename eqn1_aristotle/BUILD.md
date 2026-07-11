# Building this project

This is a single Lake project (`RequestProject`, Lean `v4.28.0`, Mathlib `v4.28.0`)
that bundles the five Lean developments as separate libraries. Each folder builds
on its own or all together.

## Build everything

```
lake build
```

## Build a single library

| Folder                     | Lake target            | Module root            |
| -------------------------- | ---------------------- | ---------------------- |
| `Equation1/`               | `Equation1`            | `Equation1`            |
| `Kasami Permutation-03/`   | `KasamiPermutation03`  | `KasamiPermutation`    |
| `Kasami-Thm1-from-gadgets/`| `KasamiThm1`           | `Kasami`               |
| `Kasami-permutations-01/`  | `KasamiPermutations01` | `KasamiPermutations`   |
| `KasamiPermutations-02/`   | `KasamiPermutations02` | `KasamiPermutations2`  |

For example:

```
lake build Equation1
lake build KasamiThm1
```

## Notes on the fixes applied

* The root `lakefile.toml` now points each library at its folder via `srcDir`
  and lists valid module globs (the previous globs contained spaces/hyphens,
  which Lake rejects).
* Import prefixes were corrected to match the file layout:
  `Dobbertin1999MVP.Equation1.*` → `Equation1.*` (in `Equation1/`) and
  `RequestProject.KasamiPermutation.*` → `KasamiPermutation.*` (in
  `Kasami Permutation-03/`).
* `Kasami-Thm1-from-gadgets/` genuinely depends on `Equation1/`
  (it imports `Equation1.Setup` and `Equation1.Equation1`); this resolves
  automatically within the combined project.
* `Kasami-permutations-01/` and `KasamiPermutations-02/` were both rooted at the
  identical module namespace `KasamiPermutations`, which made them collide (a
  build of one silently pulled in the other's files). Only the *module path* of
  the `-02` copy was remapped to `KasamiPermutations2` (directory/file names and
  `import` lines); the in-file `namespace` declarations and all mathematics are
  unchanged.

## Not built: `FibonacciTracePattern.lean`

The stray root file `FibonacciTracePattern.lean` imports
`RequestProject.ModelChecking.TransitionSystem` and uses many `ModelChecking.*`
declarations, but no `ModelChecking` library is present anywhere in the project.
It therefore cannot compile and is intentionally excluded from the build targets.
It is left in place (unchanged) so nothing is lost; to build it you would need to
supply the missing `ModelChecking` library.
