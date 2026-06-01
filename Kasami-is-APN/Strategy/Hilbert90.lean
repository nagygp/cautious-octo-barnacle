/-
# Strategy B: Hilbert 90 DAG

## Attack on `lam_forced_trivial` via Galois Cohomology

### DAG Overview

```
lam_forced_trivial
├── cocycle_condition               -- The ratio P/s defines a 1-cocycle
│   ├── cross_as_coboundary_obs     -- cross = 0 ↔ cocycle is trivial
│   └── galois_action_on_ratio     -- Frob(P/s) related to P/s
├── cyclic_galois_structure         -- Gal(GF(2^n)/GF(2^{gcd(k,n)})) is cyclic
│   ├── galois_group_cyclic         -- cyclic of order n/gcd(k,n)
│   └── generator_is_frobenius     -- σ = Frob^k generates
├── hilbert90_for_cyclic            -- H¹(G, F*) = 0 for cyclic G
│   ├── norm_one_implies_cobdy     -- N(a) = 1 ⟹ a = σ(b)/b
│   └── galois_cohom_vanishing     -- standard Hilbert 90
├── ratio_is_cocycle                -- The collision makes P/s a 1-cocycle
│   ├── collision_symmetry          -- g(t) = g(t+c)
│   └── frobenius_of_ratio         -- Frob^k(P/s) computation
├── coboundary_forces_fixed_field  -- cocycle trivial ⟹ P/s ∈ GF(2^{gcd})
│   ├── hilbert90_for_cyclic
│   └── ratio_is_cocycle
└── linPolyL_zero_from_fixed_field -- P/s ∈ GF(2^{gcd}) ⟹ L_k(P/s) = 0
    ├── coboundary_forces_fixed_field
    └── fixed_field_is_kernel      -- GF(2^{gcd}) = ker(L_k)
```
-/

import Mathlib

set_option maxHeartbeats 800000

namespace Hilbert90DAG

open Finset Fintype

/-! ## Layer 0: Definitions -/

def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

def frob (k : ℕ) {F : Type*} [CommRing F] (x : F) : F := x ^ (2 ^ k)

def relNorm (k : ℕ) {F : Type*} [CommRing F] (x : F) : F := x ^ (2 ^ k + 1)

def linPolyL (k : ℕ) (F : Type*) [Field F] [CharP F 2] (x : F) : F :=
  x ^ (2 ^ k) + x

def crossForm (k : ℕ) {F : Type*} [CommRing F] (s P : F) : F :=
  s * P ^ (2 ^ k) + s ^ (2 ^ k) * P

/-! ## Layer 1: Galois Theory Foundations -/

section GaloisFoundations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L1.1** Frobenius preserves addition. Grounded: `add_pow_expChar_pow`. -/
theorem frob_is_additive (k : ℕ) (x y : F) :
    frob k (x + y) = frob k x + frob k y := by
  simp [frob]; exact add_pow_expChar_pow x y 2 k

/-- **L1.2** Frobenius is multiplicative. Grounded: `mul_pow`. -/
theorem frob_is_multiplicative (k : ℕ) (x y : F) :
    frob k (x * y) = frob k x * frob k y := by
  simp [frob, mul_pow]

/-- **L1.3** Frobenius fixes GF(2). -/
theorem frob_fixes_gf2 (k : ℕ) (x : F) (hx : x = 0 ∨ x = 1) :
    frob k x = x := by
  rcases hx with rfl | rfl <;> simp [frob]

/-
**L1.4** ker(L_k) = Fix(Frob^k).
-/
theorem kernel_iff_frob_fixed (k : ℕ) (x : F) :
    linPolyL k F x = 0 ↔ frob k x = x := by
  unfold frob; simp +decide [ ← eq_sub_iff_add_eq', linPolyL ] ;
  grind

-- x^{2^k} + x = 0 ↔ x^{2^k} = x (using char 2: -x = x)

/-- **L1.5** Fixed field of Frob^k = GF(2^{gcd(k,n)}). -/
theorem fixed_field_of_frob (k n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (x : F) :
    frob k x = x ↔ x ^ (2 ^ Nat.gcd k n) = x := by
  sorry

end GaloisFoundations

/-! ## Layer 2: 1-Cocycles and Coboundaries -/

section Cocycles

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L2.1** A 1-cocycle: norm-1 element. -/
def isNormOneCocycle (k : ℕ) (a : F) : Prop := relNorm k a = 1

/-- **L2.2** A coboundary: a = σ(b)/b. -/
def isCoboundary (k : ℕ) (a : F) : Prop :=
  ∃ b : F, b ≠ 0 ∧ a = frob k b / b

/-- **L2.3** Every coboundary has norm 1. -/
theorem coboundary_has_norm_one (k n : ℕ) (a : F)
    (hcard : Fintype.card F = 2 ^ n) (hcob : isCoboundary k a) :
    isNormOneCocycle k a := by sorry

/-- **L2.4** N_k(x) = x · Frob^k(x). -/
theorem relNorm_as_product (k : ℕ) (x : F) :
    relNorm k x = x * frob k x := by
  simp only [relNorm, frob]; ring

end Cocycles

/-! ## Layer 3: The Ratio P/s as a Cocycle -/

section RatioAsCocycle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L3.1** Frobenius of ratio related to ratio via cross form. -/
theorem frob_ratio_relation (k : ℕ) (s P : F) (hs : s ≠ 0) :
    frob k (P / s) = (P / s) + crossForm k s P / relNorm k s := by
  sorry

/-
**L3.2** Cross = 0 ⟹ Frob(P/s) = P/s.
-/
theorem cross_zero_implies_frob_fixed (k : ℕ) (s P : F) (hs : s ≠ 0)
    (hcross : crossForm k s P = 0) :
    frob k (P / s) = P / s := by
  -- Since crossForm k s P = 0, we have that P * s^(2^k) + s * P^(2^k) = 0.
  simp [crossForm] at hcross;
  convert kernel_iff_frob_fixed k ( P / s ) |>.1 _ using 1;
  convert congr_arg ( fun x => x / s ^ ( 2 ^ k + 1 ) ) hcross using 1 <;> ring;
  simp +decide [ linPolyL, mul_assoc, mul_comm, mul_left_comm, hs ] ; ring

/-- **L3.3** Collision makes P/s a twisted cocycle. -/
theorem ratio_twisted_cocycle (k : ℕ) (t₁ c : F)
    (heq : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k =
           (t₁ + c + 1) ^ kasamiExp k + (t₁ + c) ^ kasamiExp k)
    (hs : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k ≠ 0) :
    let s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
    let P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
    let lam := P / s
    frob k lam + lam = crossForm k s P / relNorm k s := by
  sorry

end RatioAsCocycle

/-! ## Layer 4: Hilbert's Theorem 90 -/

section Hilbert90

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L4.1** Additive Hilbert 90: Tr_k(a) = 0 ⟹ a = σ(b)+b.
    Grounded in: Mathlib.FieldTheory.Hilbert90 -/
theorem additive_hilbert90 (k n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime k n) (a : F) (htr : linPolyL k F a = 0) :
    ∃ b : F, a = frob k b + b := by sorry

/-- **L4.2** Multiplicative Hilbert 90: N_k(a) = 1 ⟹ a = σ(b)/b.
    H¹(Gal(L/K), L*) = 0 for cyclic extensions. -/
theorem multiplicative_hilbert90 (k n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime k n) (a : F) (ha : a ≠ 0) (hnorm : relNorm k a = 1) :
    isCoboundary k a := by sorry

/-- **L4.3** Image of L_k has 2^{n-gcd(k,n)} elements. -/
theorem linPolyL_image_card (k n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    Fintype.card { y : F // ∃ x : F, linPolyL k F x = y } =
      2 ^ n / 2 ^ Nat.gcd k n := by sorry

end Hilbert90

/-! ## Layer 5: The Cocycle-to-Fixed-Field Bridge -/

section CocycleBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **L5.1** ker(L_k) ⊆ {0, 1} when gcd(k,n) = 1. -/
theorem cocycle_forces_fixed_field (k n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime k n) (lam : F) (hker : linPolyL k F lam = 0) :
    lam = 0 ∨ lam = 1 := by sorry

/-- **L5.2** Hilbert 90 path forces L_k(P/s) = 0. -/
theorem hilbert90_forces_kernel (k n : ℕ) (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hcop : Nat.Coprime k n)
    (t₁ c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (heq : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k =
           (t₁ + c + 1) ^ kasamiExp k + (t₁ + c) ^ kasamiExp k)
    (hs : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k ≠ 0)
    (hP : t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k ≠ 0) :
    linPolyL k F (
      (t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k) /
      ((t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k)) = 0 := by
  sorry

end CocycleBridge

/-! ## Layer 6: Assembly — Hilbert 90 Path -/

section Assembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
Cross = 0 ↔ L_k(P/s) = 0.
-/
theorem cross_zero_iff_kernel (k : ℕ) (s P : F) (hs : s ≠ 0) :
    crossForm k s P = 0 ↔ linPolyL k F (P / s) = 0 := by
  rw [ show crossForm k s P = s * P ^ ( 2 ^ k ) + s ^ ( 2 ^ k ) * P from rfl, show linPolyL k F ( P / s ) = ( P / s ) ^ ( 2 ^ k ) + ( P / s ) from rfl ];
  field_simp;
  simp +decide [ hs, mul_add, mul_assoc, mul_left_comm, pow_add, mul_div_cancel₀, add_eq_zero_iff_eq_neg ];
  rw [ div_pow, mul_div, div_eq_iff ] <;> ring ; aesop

/-- **The Master Assembly via Hilbert 90** -/
theorem cross_nonzero_impossible_hilbert90
    (k n : ℕ) (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hcop : Nat.Coprime k n)
    (t₁ c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (heq : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k =
           (t₁ + c + 1) ^ kasamiExp k + (t₁ + c) ^ kasamiExp k)
    (hs : (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k ≠ 0)
    (hP : t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k ≠ 0)
    (hcross : crossForm k
      ((t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k)
      (t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k) ≠ 0) :
    False := by
  set s := (t₁ + 1) ^ kasamiExp k + t₁ ^ kasamiExp k
  set P := t₁ ^ kasamiExp k + (t₁ + c) ^ kasamiExp k
  -- Step 1: Hilbert 90 forces L_k(P/s) = 0
  have h_ker := hilbert90_forces_kernel k n hk hn hn0 hcard hcop t₁ c hc0 hc1 heq hs hP
  -- Step 2: L_k(P/s) = 0 ⟹ cross = 0
  have h_cross_zero : crossForm k s P = 0 :=
    (cross_zero_iff_kernel k s P hs).mpr h_ker
  -- Step 3: Contradiction
  exact hcross h_cross_zero

end Assembly

/-! ## DAG Dependency Summary — Hilbert 90 Path

```
Layer 0: Definitions
    ↑ Grounded in: Mathlib.FieldTheory.Finite

Layer 1: Galois foundations (frob_is_additive, kernel_iff_frob_fixed)
    ↑ Grounded in: add_pow_expChar_pow, CharP.cast_eq_zero

Layer 2: Cocycle formalism (isNormOneCocycle, isCoboundary)
    ↑ Grounded in: Lean type theory (∃, ∧)

Layer 3: Ratio as cocycle (frob_ratio_relation, ratio_twisted_cocycle)
    ↑ Uses: Layer 1 + Layer 2 + collision hypothesis

Layer 4: Hilbert 90 (additive_hilbert90, multiplicative_hilbert90)
    ↑ Grounded in: Mathlib.FieldTheory.Hilbert90

Layer 5: Cocycle → fixed field → ker(L_k)
    ↑ Uses: Layer 3 + Layer 4 + kernel_iff_frob_fixed

Layer 6: Assembly — contradiction (cross_zero_iff_kernel + hilbert90_forces_kernel)
    ↑ Uses: Layer 5 + cross_zero_iff_kernel
```
-/

end Hilbert90DAG