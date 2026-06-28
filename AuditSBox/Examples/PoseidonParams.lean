import Mathlib
import AuditSBox.PrimeFieldDiffUnif

/-!
# Poseidon S-Box — Concrete Parameter Instantiation

The module `PrimeFieldDiffUnif` proves, fully generally, that the power-map
S-box `x ↦ x^d` over `ZMod p` has differential uniformity `≤ d - 1` whenever
`d ≥ 2` and `p ∤ d` (`PrimeFieldAudit.power_map_bounded`), and in particular
that the Poseidon `x^5` S-box has δ ≤ 4 for any prime `p > 5`
(`PrimeFieldAudit.poseidon_sbox_bounded`).

This file *instantiates* that theory at the two field orders most relevant to
practice — the scalar fields of the BN254 and BLS12-381 elliptic curves, which
underlie the Poseidon hash used in Ethereum L2 / ZK systems (Polygon, Scroll,
Aztec, …).

## Why primality is taken as a hypothesis

`bn254Fr` and `bls12381Fr` below are the standard, well-documented prime orders
of these curves' scalar fields. Re-deriving their primality inside Lean (a
254/255-bit number) is a heavy computation orthogonal to the security property
being certified, so we take `Fact (Nat.Prime ·)` as an instance hypothesis.
Under that standard fact, the differential-uniformity bound is fully proved.

## What is certified

For each field order `p`:

  - `x^5` S-box: differential uniformity `δ ≤ 4`;
  - `x^3` S-box: differential uniformity `δ ≤ 2`;
  - maximum differential bias `≤ (d-1)/p`, which is `≈ 2^-252` (utterly
    negligible). The `#eval`s below print the numeric bias.
-/

namespace PoseidonParams

open PrimeFieldAudit

/-! ### Field orders -/

/-- The scalar field order (Fr) of the BN254 (alt-bn128) curve. -/
def bn254Fr : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The scalar field order (Fr) of the BLS12-381 curve. -/
def bls12381Fr : ℕ :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-! ### Basic numeric facts (no primality needed) -/

theorem bn254_gt_five : 5 < bn254Fr := by norm_num [bn254Fr]
theorem bn254_gt_three : 3 < bn254Fr := by norm_num [bn254Fr]
theorem bls12381_gt_five : 5 < bls12381Fr := by norm_num [bls12381Fr]
theorem bls12381_gt_three : 3 < bls12381Fr := by norm_num [bls12381Fr]

/-! ### BN254 certificates -/

/-- Poseidon `x^5` over the BN254 scalar field has differential uniformity ≤ 4. -/
theorem bn254_quintic_bounded [Fact (Nat.Prime bn254Fr)] :
    isDiffBounded 4 (powerMap (p := bn254Fr) 5) :=
  poseidon_sbox_bounded bn254_gt_five

/-- The `x^3` Poseidon variant over the BN254 scalar field has δ ≤ 2. -/
theorem bn254_cubic_bounded [Fact (Nat.Prime bn254Fr)] :
    isDiffBounded 2 (powerMap (p := bn254Fr) 3) :=
  cube_map_bounded bn254_gt_three

/-! ### BLS12-381 certificates -/

/-- Poseidon `x^5` over the BLS12-381 scalar field has differential uniformity ≤ 4. -/
theorem bls12381_quintic_bounded [Fact (Nat.Prime bls12381Fr)] :
    isDiffBounded 4 (powerMap (p := bls12381Fr) 5) :=
  poseidon_sbox_bounded bls12381_gt_five

/-- The `x^3` Poseidon variant over the BLS12-381 scalar field has δ ≤ 2. -/
theorem bls12381_cubic_bounded [Fact (Nat.Prime bls12381Fr)] :
    isDiffBounded 2 (powerMap (p := bls12381Fr) 3) :=
  cube_map_bounded bls12381_gt_three

/-! ### Differential bias (numeric)

The maximum differential bias of the `x^5` S-box is `4 / p`. The following
evaluate it numerically — both are about `2^-252`, i.e. cryptographically
negligible. -/

/-- BN254 `x^5` maximum differential bias `4 / p`. -/
def bn254QuinticBias : Float := (4 : Float) / bn254Fr.toFloat

/-- BLS12-381 `x^5` maximum differential bias `4 / p`. -/
def bls12381QuinticBias : Float := (4 : Float) / bls12381Fr.toFloat

#eval Float.log2 bn254QuinticBias      -- ≈ -252  (bias ≈ 2^-252)
#eval Float.log2 bls12381QuinticBias   -- ≈ -253  (bias ≈ 2^-253)
#eval bn254Fr                          -- the BN254 scalar field order
#eval bls12381Fr                       -- the BLS12-381 scalar field order

end PoseidonParams
