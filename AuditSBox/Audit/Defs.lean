import Mathlib

/-!
# S-Box Audit — Core Definitions

Shared definitions for auditing endomorphisms over finite fields of
characteristic 2.  Every subsequent audit module imports this file.

## Definitions

- `D f a x`      — difference operator f(x+a) − f(x)
- `fiber f a b`   — solution set {x | D f a x = b}
- `δ_pair f a b`  — fiber cardinality at (a, b)
- `δ_max f`       — differential uniformity  max_{a≠0,b} δ(a,b)
- `img f a`        — derivative image {D f a x | x}
- `Bounded ω f`   — ∀ a≠0, ∀ b, δ(a,b) ≤ ω
- `Uniform ω f`   — ∀ a≠0, ∀ b, δ(a,b) ∈ {0, ω}
-/

open Finset Fintype BigOperators

noncomputable section

namespace Audit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Difference operator: `D f a x = f(x+a) − f(x)`. -/
def D (f : F → F) (a x : F) : F := f (x + a) - f x

/-- Fiber: `{x | D f a x = b}`. -/
def fiber (f : F → F) (a b : F) : Finset F :=
  univ.filter fun x => D f a x = b

/-- Fiber cardinality at `(a,b)`. -/
def δ_pair (f : F → F) (a b : F) : ℕ := (fiber f a b).card

/-- Derivative image: `{D f a x | x ∈ F}`. -/
def img (f : F → F) (a : F) : Finset F := univ.image (D f a)

/-- Differential uniformity: `max_{a≠0, b} δ(a,b)`. -/
def δ_max (f : F → F) : ℕ :=
  Finset.sup (univ.filter (· ≠ (0 : F)) ×ˢ univ)
    (fun p => δ_pair f p.1 p.2)

/-- `f` is ω-bounded: every nontrivial fiber has size ≤ ω. -/
def Bounded (ω : ℕ) (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F, δ_pair f a b ≤ ω

/-- `f` is ω-uniform: every nontrivial fiber has size 0 or ω. -/
def Uniform (ω : ℕ) (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F, δ_pair f a b = 0 ∨ δ_pair f a b = ω

end Audit

end
