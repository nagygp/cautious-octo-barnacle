import RequestProject.Steiner.Foundations.CharacterDuality
import RequestProject.Steiner.Foundations.PowerPermutation
import RequestProject.Steiner.Foundations.CharacterSum

/-!
# Foundations — bottom-up MVP layer (rooted in Mathlib)

Aggregator for the *first principles* foundational layers of the Flystel
formalisation.  Each module here is **fully proved from Mathlib** (no `sorry`,
no `opaque`, no new axioms) and sits at the bottom of the dependency DAG
described in `ROADMAP.md`.

* `RequestProject.Foundations.CharacterDuality` — F1: every additive character is
  a `mulShift` of the fundamental character (`exists_eq_fundamental_smul`).
* `RequestProject.Foundations.PowerPermutation` — F2: `x ↦ xᵈ` permutes `Fq` iff
  `gcd(d, #Fq − 1) = 1` (`powMap_bijective_iff`).
* `RequestProject.Foundations.CharacterSum` — F3 (algebraic core): the reusable
  exponential-sum invariants (norm bound, variable-separation factorization,
  re-indexing invariance, shift-invariance of the norm).
-/
