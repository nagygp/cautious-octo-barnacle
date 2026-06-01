/-
# Bridge Pathway: Spectral / Fourier-Analytic Dual Bridge

## Key Insight: Duality Between Differential and Spectral Views

The APN property has two equivalent formulations:

1. **Differential (spatial)**: ∀ a ≠ 0, |{x : f(x+a)+f(x) = b}| ≤ 2.
2. **Spectral (Fourier)**: ∀ a ≠ 0, b, |W_f(a,b)|² ≤ 2^{n+1}.

where W_f(a,b) = Σ_x (-1)^{Tr(bx + f(x+a) + f(x))} is the Walsh transform.

This is a **duality bridge** in Caramello's sense:
- T₁ = "Theory of functions with bounded differentials"
- T₂ = "Theory of functions with bounded Walsh spectrum"
- The Morita equivalence is the Fourier/Walsh transform.

## Bridge Diagram

```
    Kasami APN (differential)
         |
    ←── Walsh/Fourier Bridge ──→
         |
    Kasami APN (spectral)
         |
    Walsh coefficient bound
         |
    Parseval identity + moment method
         |
    Power sum identities for x^d
```

## Why This Might Be Simpler

The spectral characterization replaces the combinatorial counting of
solutions with an ALGEBRAIC bound on Walsh coefficients. For power
functions x^d, the Walsh coefficients have algebraic structure that
can be exploited.

For power functions: W_{x^d}(a,b) = Σ_x (-1)^{Tr(bx^d + ax)}.
Setting y = bx^d: this becomes a Kloosterman-like sum.

## DAG Structure

```
Layer 0: Trace and character theory (Mathlib)
Layer 1: Walsh transform definition and properties
Layer 2: Parseval identity
Layer 3: APN ↔ Walsh bound equivalence
Layer 4: Walsh coefficients for power functions
Layer 5: Moment method for Kasami
```
-/
import Mathlib

set_option maxHeartbeats 800000

namespace SpectralDualBridge

open Finset Fintype

/-! ## Layer 0: Trace Function and Characters

The absolute trace Tr : GF(2^n) → GF(2) is the bridge between
additive and multiplicative structure.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L0.1** The absolute trace: Tr(x) = x + x^2 + x^4 + ... + x^{2^{n-1}}. -/
noncomputable def absTr (n : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range n, x ^ (2 ^ i)

/-- **L0.2** Trace is additive (F-linear over GF(2)). -/
theorem absTr_add (n : ℕ) (x y : F) :
    absTr n (x + y) = absTr n x + absTr n y := by
  simp only [absTr]
  rw [← Finset.sum_add_distrib]
  congr 1; ext i
  exact add_pow_expChar_pow x y 2 i

/-- **L0.3** Trace maps to GF(2): Tr(x)² = Tr(x). -/
theorem absTr_sq {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (x : F) :
    absTr n x ^ 2 = absTr n x := by
  sorry -- Uses Fermat: each term x^{2^i} maps to x^{2^{i+1}}, telescoping

/-- **L0.4** Trace takes values in {0, 1} (= GF(2)). -/
theorem absTr_values {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (x : F) :
    absTr n x = 0 ∨ absTr n x = 1 := by
  sorry -- From absTr_sq: t² = t ⟹ t(t-1) = 0 ⟹ t = 0 or t = 1

/-- **L0.5** Trace is surjective onto GF(2). -/
theorem absTr_surjective {n : ℕ} (hn : n ≥ 1) (hcard : Fintype.card F = 2 ^ n) :
    ∃ x : F, absTr n x = 1 := by
  sorry -- Standard result

/-! ## Layer 1: Walsh-Hadamard Transform

The Walsh transform is the Fourier transform over GF(2^n).
We define it using ℤ-valued characters since we don't need ℂ.
-/

/-- **L1.1** The additive character χ(x) = (-1)^{Tr(x)} ∈ {±1} ⊆ ℤ. -/
noncomputable def additiveChar (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (x : F) : ℤ :=
  if absTr n x = 0 then 1 else -1

/-- **L1.2** Character is multiplicative: χ(x+y) = χ(x) · χ(y). -/
theorem additiveChar_add (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (x y : F) :
    additiveChar n hcard (x + y) = additiveChar n hcard x * additiveChar n hcard y := by
  sorry -- From absTr_add and case analysis on Tr values

/-- **L1.3** Character values: χ(x)² = 1 (so χ(x) ∈ {±1}). -/
theorem additiveChar_sq (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (x : F) :
    additiveChar n hcard x ^ 2 = 1 := by
  simp only [additiveChar]; split <;> norm_num

/-- **L1.4** The Walsh-Hadamard transform of f at (a,b):
    W_f(a,b) = Σ_x χ(b·f(x) + a·x). -/
noncomputable def walshTransform (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, additiveChar n hcard (b * f x + a * x)

/-- **L1.5** Walsh of zero function: W_0(0, b) = |F| for b = 0. -/
theorem walsh_zero_at_origin (n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    walshTransform n hcard (fun _ => 0) 0 0 = (Fintype.card F : ℤ) := by
  simp [walshTransform, additiveChar, absTr, Finset.sum_const]

/-! ## Layer 2: Parseval Identity

The fundamental identity connecting spatial and spectral norms.
-/

/-- **L2.1** Orthogonality of characters: Σ_x χ(ax) = |F| if a = 0, else 0. -/
theorem character_orthogonality (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (a : F) :
    ∑ x : F, additiveChar n hcard (a * x) =
      if a = 0 then (Fintype.card F : ℤ) else 0 := by
  sorry

/-- **L2.2** Parseval identity: Σ_{a,b} W_f(a,b)² = |F|³. -/
theorem parseval_identity (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) :
    ∑ a : F, ∑ b : F, walshTransform n hcard f a b ^ 2 =
      (Fintype.card F : ℤ) ^ 3 := by
  sorry

/-- **L2.3** Parseval for the differential:
    Σ_b W_f(a,b)² = |F|² for each a ≠ 0 (if f is a permutation). -/
theorem parseval_per_a (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hperm : Function.Bijective f) (a : F) (ha : a ≠ 0) :
    ∑ b : F, walshTransform n hcard f a b ^ 2 =
      (Fintype.card F : ℤ) ^ 2 := by
  sorry

/-! ## Layer 3: APN ↔ Walsh Bound Equivalence

The spectral characterization of APN.
-/

/-- **L3.1** APN (differential definition). -/
def isAPN_diff (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    Fintype.card {x : F // f (x + a) + f x = b} ≤ 2

/-- **L3.2** APN (spectral definition). -/
def isAPN_spectral (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (f : F → F) : Prop :=
  ∀ a b : F, a ≠ 0 →
    walshTransform n hcard f a b ^ 2 ≤ 2 ^ (n + 1)

/-- **L3.3** **The Duality Bridge**: differential APN ↔ spectral APN.
    This is the core Morita equivalence between the two theories. -/
theorem apn_duality_bridge (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (f : F → F) :
    isAPN_diff f ↔ isAPN_spectral n hcard f := by
  sorry

/-! ## Layer 4: Walsh Coefficients for Power Functions

For f(x) = x^d, the Walsh transform has special algebraic structure.
-/

/-- **L4.1** For power functions, W_{x^d}(a,b) = W_{x^d}(1, b·a^{-d}).
    This reduces to a single-variable sum. -/
theorem walsh_power_reduction (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ) (a b : F) (ha : a ≠ 0) :
    walshTransform n hcard (fun x => x ^ d) a b =
    walshTransform n hcard (fun x => x ^ d) 1 (b * a⁻¹ ^ d) := by
  sorry

/-- **L4.2** The Kloosterman-like sum for power functions:
    K_d(c) = Σ_x χ(x^d + cx). -/
noncomputable def kloostermanSum (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ) (c : F) : ℤ :=
  ∑ x : F, additiveChar n hcard (c * x ^ d + x)

/-- **L4.3** W_{x^d}(1, b) = K_d(b). -/
theorem walsh_eq_kloosterman (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ) (b : F) :
    walshTransform n hcard (fun x => x ^ d) 1 b = kloostermanSum n hcard d b := by
  simp only [walshTransform, kloostermanSum, one_mul]

/-! ## Layer 5: Moment Method for Kasami

The fourth moment of Walsh coefficients determines APN.
-/

/-- **L5.1** The fourth moment: Σ_b W_f(a,b)⁴.
    APN ↔ fourth moment = 2^{2n+1} · |F| for all a ≠ 0. -/
noncomputable def fourthMoment (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (a : F) : ℤ :=
  ∑ b : F, walshTransform n hcard f a b ^ 4

/-- **L5.2** For APN functions, the fourth moment is bounded.
    Σ_b W(a,b)⁴ ≤ 2^{2(n+1)} · |F|. -/
theorem apn_fourth_moment_bound (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hapn : isAPN_diff f) (a : F) (ha : a ≠ 0) :
    fourthMoment n hcard f a ≤ 2 ^ (2 * (n + 1)) * Fintype.card F := by
  sorry

/-- **L5.3** For power functions, the fourth moment relates to
    the number of solutions of a system of equations. -/
theorem fourth_moment_counting (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ) (a : F) (ha : a ≠ 0) :
    fourthMoment n hcard (fun x => x ^ d) a =
      (Fintype.card F : ℤ) *
        Fintype.card {p : F × F × F //
          p.1 + p.2.1 + p.2.2 + (p.1 + p.2.1 + p.2.2) = 0 ∧
          p.1 ^ d + p.2.1 ^ d + p.2.2 ^ d + (p.1 + p.2.1 + p.2.2) ^ d = 0} := by
  sorry

/-! ## Summary: The Spectral Dual Bridge

```
    Kasami APN (differential)
         ↕   (Walsh/Fourier bridge — Layer 3)
    Kasami APN (spectral)
         |
    |W(a,b)|² ≤ 2^{n+1}
         |
    Kloosterman sum bound (Layer 4)
         |
    Fourth moment method (Layer 5)
         |
    Algebraic identity counting
```

### What Makes This Bridge Novel

1. **Duality**: Converts a combinatorial counting problem into an
   algebraic bound on exponential sums.

2. **Power function structure**: For x^d, the Walsh transform
   reduces to Kloosterman-like sums with known algebraic theory.

3. **Moment method**: The fourth moment connects APN to a system
   of equations that can be attacked directly.

### Connection to Other Bridges

- **Cyclotomic Bridge** (Layer 0-2): The Kloosterman sum for d = Φ₃(2^k)
  has extra structure from the cyclotomic factorization.

- **Hilbert 90 Bridge**: The vanishing of certain Galois cohomology
  groups translates to cancellation in the exponential sum.

- **Ω-Generalization**: In a non-Boolean topos, the Walsh transform
  takes values in a richer ring (not just ℤ), giving "graded" APN.
-/

end SpectralDualBridge
