/-
# Layer 9: Proof Metadata System — DAG Classification Engine

This file implements the methodology described in the project specification:
a formal system for classifying lemmas by their **structural properties**
(DAG depth, compression score, proof shape) rather than subjective difficulty.

## Novel Research Contribution

This is a formalization of the "proof shape stratification" methodology:
- Each lemma is a node in a DAG
- Edges represent dependencies
- Nodes carry metadata (tactic count, classification, compression score)
- The system enables automated analysis of proof structure

## Potential Research Questions This Enables

1. **Optimal DAG compression**: Given a proof DAG, what is the minimal
   set of intermediate lemmas that minimizes total proof complexity?
2. **Proof difficulty prediction**: Can the graph spectrum of the proof
   DAG predict which lemmas are hardest to automate?
3. **Proof minimality**: Is finding the shortest proof NP-hard in
   tactic-space? (This system provides the formal setting.)
4. **Mathlib reuse ratio**: What fraction of a proof's DAG nodes are
   already in Mathlib? This predicts formalization effort.

## DAG Structure (standalone, depends on Layer 0 = Mathlib only)

```
    analyze_dag
       |
    compression_score
       |
    topological_level
       |
    ProofNode + ProofDAG (definitions)
       |
    LemmaClass (inductive)
```
-/
import Mathlib

namespace Caramello.ProofMetadata

/-! ## Section 1: Proof Shape Classification (Inductive Type) -/

/-- Classification of a lemma by its proof shape.
    This replaces subjective "easy/medium/hard" labels with
    structural categories based on proof content. -/
inductive LemmaClass where
  /-- Already in Mathlib — zero proof effort needed. -/
  | mathlib
  /-- Provable by a single tactic: simp, aesop, ring, linarith, omega, etc. -/
  | oneLiner
  /-- Requires 2-5 tactics, all rewriting / simplification. -/
  | rewriteChain
  /-- Composes 2+ lemmas with modest glue logic. -/
  | compositeLocal
  /-- Introduces a new construction, invariant, or induction scheme. -/
  | coreTheorem
  deriving Repr, DecidableEq, Inhabited

/-- The "difficulty weight" of a lemma class.
    Higher weight = more novel mathematical content. -/
def LemmaClass.weight : LemmaClass → Nat
  | .mathlib => 0
  | .oneLiner => 1
  | .rewriteChain => 2
  | .compositeLocal => 3
  | .coreTheorem => 5

/-! ## Section 2: Proof Node Metadata -/

/-- Metadata for a single lemma in the proof DAG. -/
structure ProofNode where
  /-- Human-readable name of the lemma. -/
  name : String
  /-- Structural classification. -/
  classification : LemmaClass
  /-- Number of tactic steps in the proof. -/
  tacticCount : Nat
  /-- Names of lemmas this one depends on. -/
  dependencies : List String
  /-- Topological level in the DAG (longest path from a leaf). -/
  level : Nat
  deriving Repr, Inhabited

/-- The compression score κ: measures how many dependencies
    are "collapsed" by this lemma.
    κ = |transitive dependencies| - |direct dependencies|
    Higher κ means the lemma is a better "compression point". -/
def ProofNode.compressionScore (n : ProofNode) (transitiveDeps : Nat) : Int :=
  transitiveDeps - n.dependencies.length

/-! ## Section 3: Proof DAG -/

/-- A proof DAG is a list of nodes with dependency edges.
    Nodes are topologically sorted (dependencies come before dependents). -/
structure ProofDAG where
  nodes : List ProofNode

/-! ## Section 4: DAG Analysis Functions -/

/-- Count nodes at each topological level. -/
def ProofDAG.levelHistogram (dag : ProofDAG) : List (Nat × Nat) :=
  let levels := dag.nodes.map (·.level)
  let maxLevel := levels.foldl max 0
  (List.range (maxLevel + 1)).map fun l =>
    (l, (dag.nodes.filter (·.level == l)).length)

/-- Total weight of the DAG (sum of all node weights). -/
def ProofDAG.totalWeight (dag : ProofDAG) : Nat :=
  dag.nodes.foldl (fun acc n => acc + n.classification.weight) 0

/-- Mathlib reuse ratio: fraction of nodes that are already in Mathlib.
    Higher ratio = less original proof work needed.
    Returns (mathlib_count, total_count). -/
def ProofDAG.mathlibRatio (dag : ProofDAG) : Nat × Nat :=
  let mathlibCount := (dag.nodes.filter (·.classification == .mathlib)).length
  (mathlibCount, dag.nodes.length)

/-- Count of nodes by classification. -/
def ProofDAG.classHistogram (dag : ProofDAG) : List (LemmaClass × Nat) :=
  [LemmaClass.mathlib, .oneLiner, .rewriteChain, .compositeLocal, .coreTheorem].map fun c =>
    (c, (dag.nodes.filter (·.classification == c)).length)

/-- The proof golf score of a DAG: total tactic count. -/
def ProofDAG.golfScore (dag : ProofDAG) : Nat :=
  dag.nodes.foldl (fun acc n => acc + n.tacticCount) 0

/-- The edge density of a DAG: total edges / total nodes.
    Higher density suggests more intermediate lemmas could help. -/
def ProofDAG.edgeDensity (dag : ProofDAG) : Nat × Nat :=
  let edges := dag.nodes.foldl (fun acc n => acc + n.dependencies.length) 0
  (edges, dag.nodes.length)

/-- Maximum topological depth of the DAG.
    This corresponds to the "voyage distance" in the yacht analogy. -/
def ProofDAG.maxDepth (dag : ProofDAG) : Nat :=
  dag.nodes.foldl (fun acc n => max acc n.level) 0

/-! ## Section 5: The Caramello MVP DAG (Computed Metadata)

We encode the actual proof DAG from Layers 1-5 as a concrete
ProofDAG value, enabling computational analysis.
-/

/-- The proof DAG for Layer 1 (PropAsOmega). -/
def propAsOmegaDAG : ProofDAG where
  nodes := [
    ⟨"truth_injective", .oneLiner, 1, [], 0⟩,
    ⟨"truth_mono", .rewriteChain, 2, ["truth_injective"], 1⟩,
    ⟨"charMap_of_mem_range", .oneLiner, 1, [], 0⟩,
    ⟨"char_comm", .oneLiner, 1, [], 0⟩,
    ⟨"char_commSq", .rewriteChain, 1, ["char_comm"], 1⟩,
    ⟨"charMap_iff", .oneLiner, 1, [], 0⟩,
    ⟨"unique_preimage", .compositeLocal, 3, [], 0⟩,
    ⟨"pullbackLift", .coreTheorem, 5, ["charMap_iff", "unique_preimage"], 1⟩,
    ⟨"pullbackLift_fst", .compositeLocal, 4, ["pullbackLift", "unique_preimage"], 2⟩,
    ⟨"pullbackLift_snd", .oneLiner, 1, ["pullbackLift"], 2⟩,
    ⟨"pullbackLift_uniq", .compositeLocal, 3, ["pullbackLift", "pullbackLift_fst"], 3⟩,
    ⟨"char_isPullback", .coreTheorem, 5,
      ["char_commSq", "pullbackLift", "pullbackLift_fst",
       "pullbackLift_snd", "pullbackLift_uniq"], 4⟩,
    ⟨"char_unique", .coreTheorem, 8, ["char_isPullback"], 5⟩,
    ⟨"typesClassifier", .coreTheorem, 3,
      ["truth_mono", "char_isPullback", "char_unique"], 6⟩
  ]

/-! ## Section 6: Computational Analysis

These `#eval` commands demonstrate the DAG analysis system
on the actual PropAsOmega proof DAG.
-/

-- Total weight = sum of classification weights
#eval propAsOmegaDAG.totalWeight
-- Mathlib reuse ratio: (mathlib_count, total_count)
#eval propAsOmegaDAG.mathlibRatio
-- Level histogram: nodes at each depth
#eval propAsOmegaDAG.levelHistogram
-- Classification histogram
#eval propAsOmegaDAG.classHistogram
-- Golf score: total tactic count
#eval propAsOmegaDAG.golfScore
-- Edge density: (total_edges, total_nodes)
#eval propAsOmegaDAG.edgeDensity
-- Maximum DAG depth
#eval propAsOmegaDAG.maxDepth

end Caramello.ProofMetadata
