-- Headline results (Theorem 1 permutation criterion + Corollary 2 APN).
import RequestProject.KasamiPermutation.Headlines.PermutationCriterionAndAPN
import RequestProject.KasamiPermutation.Headlines.TraceVersionCriterion
import RequestProject.KasamiPermutation.Headlines.InvariantAndClassifier
-- Structural distillation: the general obstruction and the context classifier.
import RequestProject.KasamiPermutation.Structural.Obstruction
import RequestProject.KasamiPermutation.Structural.ContextClassifier
-- MCM permutation engine and the field-level structural bridges.
import RequestProject.KasamiPermutation.MCM.ToAPN
import RequestProject.KasamiPermutation.Bridge

/-!
# Kasami permutation polynomials and APN power functions — theory root

This is the umbrella import for the Kasami-permutation development (a functional
re-organisation of Dobbertin's 1999 paper skeleton).  Importing this file pulls in
the whole theory: the finite-field toolbox, the recurrence/cubic machinery, the
trace-free and trace-version permutation criteria, the MCM → APN bridge, and the
headline results together with their structural distillation.

See `RequestProject/KasamiPermutation/MODULE_MAP.md` for the role of each module.
-/
