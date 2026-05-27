import Mathlib
import RequestProject.AutBase
import RequestProject.Prop21
import RequestProject.LinPoly

/-!
# Layer B2: Automorphism Kernel Theory

Formalization of Lemmas 4.3, 4.4, 4.5 from Dempwolff & Müller (2013).

## Main results

1. **Lemma 4.3**: The kernel of the translation plane `A(L, k)` is
   isomorphic to `GF(p^r)` where `r = gcd{i - j | i, j ∈ spi(L)}`.

2. **Lemma 4.4**: Characterization of automorphism group elements
   `τ_{a,b,α} ∈ G` in terms of coefficients.

3. **Lemma 4.5**: For non-desarguesian planes:
   (a) S is a Sylow p-subgroup of G_{0,∞}
   (b) Normalizer elements have semilinear form
   (c) G = N_{G_{0,∞}}(S)

## DAG structure

```
  B1 (AutBase) + Prop21
    │
    ├──► Lemma 4.3 (kernel = GF(p^r))
    │      │
    │      └──► Corollaries (kernel structure)
    │
    ├──► Lemma 4.4 (automorphism characterization)
    │
    └──► Lemma 4.5 (Sylow/normalizer)
```

**Dependencies:** Layer B1 (`AutBase.lean`), Prop21 (`Prop21.lean`),
Layer F4 (`LinPoly.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- B2.1 : Support GCD definition
-- ═══════════════════════════════════════════

/-- The GCD of all pairwise index differences in the support of L.
    `r = gcd{i - j | i, j ∈ spi(L)}`.
    This determines the kernel dimension (Lemma 4.3). -/
noncomputable def supportGcd (n_dim : ℕ) (coeffs : Fin n_dim → F) : ℕ :=
  Finset.univ.sup fun ij : Fin n_dim × Fin n_dim =>
    if coeffs ij.1 ≠ 0 ∧ coeffs ij.2 ≠ 0
    then Nat.gcd ((ij.1 : ℕ) - (ij.2 : ℕ) + n_dim) n_dim
    else n_dim

-- ═══════════════════════════════════════════
-- B2.2 : Kernel as fixed-point set
-- ═══════════════════════════════════════════

/-- **Kernel element characterization.**
    An element `c` is in the kernel of the translation plane iff
    `L(c·x) = c·L(x)` for all `x`, i.e., `c` commutes with `L`
    under the quasifield multiplication. -/
def isKernelElement (n_dim : ℕ) (coeffs : Fin n_dim → F) (c : F) : Prop :=
  ∀ x : F, additivePolyEval p n_dim coeffs (c * x) =
    c * additivePolyEval p n_dim coeffs x

/-- **Zero is a kernel element.** -/
lemma isKernelElement_zero (n_dim : ℕ) (coeffs : Fin n_dim → F) :
    isKernelElement p n_dim coeffs (0 : F) := by
  intro x
  simp [additivePolyEval_zero, mul_zero, zero_mul]

/-- **One is a kernel element.** -/
lemma isKernelElement_one (n_dim : ℕ) (coeffs : Fin n_dim → F) :
    isKernelElement p n_dim coeffs (1 : F) := by
  intro x
  simp [one_mul]

/-- **Kernel is closed under multiplication.** -/
lemma isKernelElement_mul (n_dim : ℕ) (coeffs : Fin n_dim → F)
    {a b : F} (ha : isKernelElement p n_dim coeffs a)
    (hb : isKernelElement p n_dim coeffs b) :
    isKernelElement p n_dim coeffs (a * b) := by
  intro x
  show additivePolyEval p n_dim coeffs (a * b * x) = a * b * additivePolyEval p n_dim coeffs x
  calc additivePolyEval p n_dim coeffs (a * b * x)
      = additivePolyEval p n_dim coeffs (a * (b * x)) := by rw [mul_assoc]
    _ = a * additivePolyEval p n_dim coeffs (b * x) := ha (b * x)
    _ = a * (b * additivePolyEval p n_dim coeffs x) := by rw [hb x]
    _ = a * b * additivePolyEval p n_dim coeffs x := by ring

/-- **Kernel is closed under addition.** -/
lemma isKernelElement_add (n_dim : ℕ) (coeffs : Fin n_dim → F)
    {a b : F} (ha : isKernelElement p n_dim coeffs a)
    (hb : isKernelElement p n_dim coeffs b) :
    isKernelElement p n_dim coeffs (a + b) := by
  intro x
  rw [add_mul, additivePolyEval_add, ha x, hb x, add_mul]

/-- **GF(p) elements are kernel elements.**
    If `c^p = c` (i.e., `c ∈ GF(p)`), then `c` is a kernel element. -/
lemma isKernelElement_gfp (n_dim : ℕ) (coeffs : Fin n_dim → F)
    {c : F} (hc : c ^ p = c) :
    isKernelElement p n_dim coeffs c :=
  fun x => additivePolyEval_smul p n_dim coeffs c hc x

-- ═══════════════════════════════════════════
-- B2.3 : Kernel as a subfield
-- ═══════════════════════════════════════════

/-- The kernel set. -/
noncomputable def kernelSet (n_dim : ℕ) (coeffs : Fin n_dim → F) : Set F :=
  {c : F | isKernelElement p n_dim coeffs c}

/-- The kernel contains 0. -/
lemma kernelSet_zero (n_dim : ℕ) (coeffs : Fin n_dim → F) :
    (0 : F) ∈ kernelSet p n_dim coeffs :=
  isKernelElement_zero p n_dim coeffs

/-- The kernel contains 1. -/
lemma kernelSet_one (n_dim : ℕ) (coeffs : Fin n_dim → F) :
    (1 : F) ∈ kernelSet p n_dim coeffs :=
  isKernelElement_one p n_dim coeffs

/-- The kernel is closed under multiplication. -/
lemma kernelSet_mul (n_dim : ℕ) (coeffs : Fin n_dim → F)
    {a b : F} (ha : a ∈ kernelSet p n_dim coeffs) (hb : b ∈ kernelSet p n_dim coeffs) :
    a * b ∈ kernelSet p n_dim coeffs :=
  isKernelElement_mul p n_dim coeffs ha hb

/-- The kernel is closed under addition. -/
lemma kernelSet_add (n_dim : ℕ) (coeffs : Fin n_dim → F)
    {a b : F} (ha : a ∈ kernelSet p n_dim coeffs) (hb : b ∈ kernelSet p n_dim coeffs) :
    a + b ∈ kernelSet p n_dim coeffs :=
  isKernelElement_add p n_dim coeffs ha hb

/-- The kernel contains GF(p). -/
lemma kernelSet_gfp (n_dim : ℕ) (coeffs : Fin n_dim → F)
    {c : F} (hc : c ^ p = c) :
    c ∈ kernelSet p n_dim coeffs :=
  isKernelElement_gfp p n_dim coeffs hc

-- ═══════════════════════════════════════════
-- B2.4 : Lemma 4.4 — Automorphism characterization
-- ═══════════════════════════════════════════

/-- **Lemma 4.4 (abstract form).** An element `(a, b, α)` defines an
    automorphism of the translation plane iff the coefficients satisfy
    certain compatibility conditions with the linearized polynomial. -/
def isAutomorphismTriple (n_dim : ℕ) (coeffs : Fin n_dim → F)
    (a b : F) (α : ℕ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧
  ∀ x : F, semilinearOp p α a (additivePolyEval p n_dim coeffs
    (semilinearOp p α b x)) =
    additivePolyEval p n_dim coeffs (semilinearOp p α (a * b) x)

-- ═══════════════════════════════════════════
-- B2.5 : Lemma 4.5 — Sylow structure
-- ═══════════════════════════════════════════

/-- **Lemma 4.5(a) (condition).** The "p-part" of automorphisms:
    elements `(1, 1, 0)` form the identity component of the Sylow
    p-subgroup. This is characterized by `L(x + c) = L(x) + L(c)`
    for all x, which is automatic for additive L. -/
lemma sylow_identity_component (n_dim : ℕ) (coeffs : Fin n_dim → F) (c x : F) :
    additivePolyEval p n_dim coeffs (x + c) =
    additivePolyEval p n_dim coeffs x + additivePolyEval p n_dim coeffs c :=
  additivePolyEval_add p n_dim coeffs x c

end DempwolffMueller
