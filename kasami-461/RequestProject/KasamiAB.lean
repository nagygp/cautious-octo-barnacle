/-
  KasamiAB.lean — The "Glue" linking the Kasami linearized-polynomial kernel
  to the radical of the associated quadratic form.

  The Kasami exponent is `d = 2^{2k} - 2^k + 1` with `n = 2k+1` (odd).
  Over `GF(2^n)`, the power map `x ↦ x^d` induces a quadratic form
  `Q(x) = Tr(a·x^d + b·x)` via the absolute trace.
  The *radical* of the associated bilinear form `B(x,z) = Q(x⊕z) ⊕ Q(x) ⊕ Q(z)`
  is exactly the kernel of the linearized polynomial
  `L_k(z) = z^{2^{2k}} + z^{2^k} + z`.
-/
import Mathlib
import RequestProject.Mathlib.QuadraticFourier

set_option maxHeartbeats 800000

/-! ### Abstract Setup

We work over `GF(2^n)` modeled abstractly.
Since Mathlib does not yet provide a fully bundled `GF(2^n)` with trace,
we set up the minimum interface needed for the structural identity.
-/

/-- Abstract trace map from a finite field of characteristic 2 to `ZMod 2`.
    Bundled with the properties we need (additivity, non-degeneracy). -/
structure TraceMap (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] where
  toFun : 𝔽 → ZMod 2
  map_add : ∀ x y : 𝔽, toFun (x + y) = toFun x + toFun y
  map_zero : toFun 0 = 0
  nondeg : ∀ c : 𝔽, (∀ x : 𝔽, toFun (c * x) = 0) → c = 0

namespace Kasami

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [CharP 𝔽 2]
variable (Tr : TraceMap 𝔽)

/-- The Kasami exponent `d = 2^{2k} - 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The linearized polynomial `L_k(z) = z^{2^{2k}} + z^{2^k} + z`. -/
noncomputable def L (k : ℕ) (z : 𝔽) : 𝔽 :=
  z ^ (2 ^ (2 * k)) + z ^ (2 ^ k) + z

/-- The quadratic form `Q_ab(x) = Tr(a · x^d + b · x)`. -/
noncomputable def Q_ab (k : ℕ) (a b x : 𝔽) : ZMod 2 :=
  Tr.toFun (a * x ^ kasamiExp k + b * x)

/-- The associated "bilinear" form (symmetric since char = 2):
    `B_ab(x, z) = Q_ab(x + z) + Q_ab(x) + Q_ab(z)`. -/
noncomputable def B_ab (k : ℕ) (a b x z : 𝔽) : ZMod 2 :=
  Q_ab Tr k a b (x + z) + Q_ab Tr k a b x + Q_ab Tr k a b z

/-- The radical of the quadratic form `Q_ab`:
    `rad(Q_ab) = { z : 𝔽 | ∀ x, B_ab(x, z) = 0 }`. -/
noncomputable def radical (k : ℕ) (a b : 𝔽) : Set 𝔽 :=
  { z : 𝔽 | ∀ x : 𝔽, B_ab Tr k a b x z = 0 }

/-- The kernel of the linearized polynomial:
    `ker(L_k) = { z : 𝔽 | L_k(z) = 0 }`. -/
def kerL (k : ℕ) : Set 𝔽 :=
  { z : 𝔽 | L k z = 0 }

/-! ### Step 3 — The "Glue": Kernel = Radical

**Proof sketch:**
1. Expand `B_ab(x, z)` using linearity of `Tr` and char 2 simplifications.
2. For Kasami exponent `d = 2^{2k} - 2^k + 1`, cross-terms reduce to
   `x · L_k(z)` via Frobenius automorphisms and trace identities.
3. Therefore `B_ab(x, z) = Tr(a · x · L_k(z))`.
4. Non-degeneracy of `Tr` gives the result.
-/

/-- **Intermediate step**: The bilinear form reduces to trace of a product
involving `L_k`. This is the core algebraic identity. -/
theorem bilinear_eq_trace_L (k : ℕ) (a b x z : 𝔽) :
    B_ab Tr k a b x z = Tr.toFun (a * x * L k z) := by
  sorry

/-- **kasami_radical_is_kernel**: The radical of `Q_ab` is exactly
the kernel of the linearized polynomial `L_k`, provided `a ≠ 0`. -/
theorem kasami_radical_is_kernel (k : ℕ) (a b : 𝔽) (ha : a ≠ 0) :
    radical Tr k a b = kerL k := by
  ext z
  simp only [radical, kerL, Set.mem_setOf_eq]
  constructor
  · -- (⊆) z ∈ rad(Q_ab) → L_k(z) = 0
    intro h
    -- Step 1: rewrite B_ab in terms of Tr and L_k
    have h1 : ∀ x : 𝔽, Tr.toFun (a * x * L k z) = 0 := by
      intro x; rw [← bilinear_eq_trace_L]; exact h x
    -- Step 2: rearrange to use non-degeneracy
    have h2 : ∀ x : 𝔽, Tr.toFun ((a * L k z) * x) = 0 := by
      intro x; have := h1 x; ring_nf at this ⊢; exact this
    -- Step 3: non-degeneracy gives a * L_k(z) = 0
    have h3 : a * L k z = 0 := Tr.nondeg _ h2
    -- Step 4: since a ≠ 0, L_k(z) = 0
    exact (mul_eq_zero.mp h3).resolve_left ha
  · -- (⊇) L_k(z) = 0 → z ∈ rad(Q_ab)
    intro hz x
    calc B_ab Tr k a b x z
        = Tr.toFun (a * x * L k z) := bilinear_eq_trace_L Tr k a b x z
      _ = Tr.toFun (a * x * 0) := by rw [hz]
      _ = Tr.toFun 0 := by ring_nf
      _ = 0 := Tr.map_zero

end Kasami
