/-
  Main.lean

  Root module for the Kasami / APN / AB formalization project.
  Imports Mathlib and opens commonly used namespaces.
-/
import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

-- Disable auto-implicit to keep variable declarations explicit.
set_option relaxedAutoImplicit false
set_option autoImplicit false
