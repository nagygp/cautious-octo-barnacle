import Mathlib
import DobbertinStep1

/-!
# The proof space of step (1) ⟹ (2), as a `SimpleGraph`

The module-level dependency structure of the `DobbertinStep1` MVP, encoded as an
honest `SimpleGraph` on the finite set of modules, with a proof that it is
**connected**: every module is linked, through its dependency chain, down to the
common `Mathlib` base.  This is the Lean counterpart of the dependency diagrams
in `docs/DobbertinStep1_Map.tex`.
-/

namespace Dobbertin.Step1.ProofSpace

/-- The modules of the MVP (the nodes of its dependency DAG).  `mathlibBase` is
the common `Mathlib` foundation; `mvpRoot` is the headline module
`DobbertinStep1`. -/
inductive Node
  | mathlibBase | defs | frob | traceMod | telescope | linearize | mvpRoot
  deriving DecidableEq, Fintype

open Node

/-- The directed dependency relation `dep a b = "module a depends on module b"`,
transcribed from the `import` structure of the library. -/
def dep : Node → Node → Prop
  | defs, mathlibBase => True
  | frob, mathlibBase => True
  | traceMod, defs => True
  | telescope, defs => True
  | telescope, frob => True
  | linearize, defs => True
  | linearize, telescope => True
  | mvpRoot, defs => True
  | mvpRoot, frob => True
  | mvpRoot, traceMod => True
  | mvpRoot, telescope => True
  | mvpRoot, linearize => True
  | _, _ => False

instance : DecidableRel dep := by
  intro a b; cases a <;> cases b <;> unfold dep <;> infer_instance

/-- The undirected **proof-space graph** underlying the dependency DAG. -/
def depGraph : SimpleGraph Node := SimpleGraph.fromRel dep

/-- Adjacency follows from a dependency edge. -/
theorem adj_of_dep (a b : Node) (h : dep a b) : depGraph.Adj a b := by
  refine ⟨?_, Or.inl h⟩
  rintro rfl; cases a <;> simp_all [dep]

/-- Every module is reachable, through its dependency chain, from the `Mathlib`
base node. -/
theorem reach_mathlibBase (v : Node) : depGraph.Reachable mathlibBase v := by
  have hd : depGraph.Reachable mathlibBase defs :=
    (adj_of_dep defs mathlibBase trivial).symm.reachable
  cases v
  · exact SimpleGraph.Reachable.refl _
  · exact hd
  · exact (adj_of_dep frob mathlibBase trivial).symm.reachable
  · exact hd.trans (adj_of_dep traceMod defs trivial).symm.reachable
  · exact hd.trans (adj_of_dep telescope defs trivial).symm.reachable
  · exact hd.trans (adj_of_dep linearize defs trivial).symm.reachable
  · exact hd.trans (adj_of_dep mvpRoot defs trivial).symm.reachable

/-- **The proof space of step (1) ⟹ (2) is connected**: every module is linked,
through its dependencies, to the common `Mathlib` base. -/
theorem depGraph_connected : depGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨mathlibBase, reach_mathlibBase⟩

end Dobbertin.Step1.ProofSpace
