import Mathlib
import RequestProject.KasamiPhase2

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
attribute [local instance] ZMod.algebra

theorem test (k : ℕ) (a x y : F) :
    bilinForm k a x y = AbsTrace (x * linPolyLA k a y) := by
  sorry
