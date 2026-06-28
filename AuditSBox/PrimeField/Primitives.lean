import Mathlib
import AuditSBox.PrimeFieldDiffUnif
import AuditSBox.PrimeField.AbstractBridge
import AuditSBox.PrimeField.InverseDuality
import AuditSBox.PrimeField.AlgebraicDegree
import AuditSBox.Examples.PoseidonParams

/-!
# Certified S-box bounds for named arithmetization-friendly primitives

This module collects the verified differential and algebraic-degree certificates
for the nonlinear layers of several deployed / proposed ZK-friendly primitives,
all routed through the shared abstract framework (`APN.differentialUniformity`)
and the prime-field power-map theory.

| primitive | S-box            | certificate                                  |
|-----------|------------------|----------------------------------------------|
| MiMC      | `x^3`            | `mimc_sbox_diffUnif_le_two`                   |
| Poseidon  | `x^5`            | `poseidon_sbox_diffUnif_le_four`              |
| Rescue    | `x^5` & `x^(1/5)`| `rescue_forward…` / `rescue_inverse…`         |
| Griffin   | `x^5` (+ inv)    | shares the Poseidon/Rescue power-map bounds   |

For each, the *forward* algebraic degree is small (the source of arithmetization
efficiency), e.g. `algDegree (x^5) = 5`, while interpolation resistance of the map
is captured by `interpolation_resistance` (and grows under round iteration via
`powerMap_comp`).

Concrete instances are given at the BN254 and BLS12-381 scalar fields (the
parameters used by Poseidon in production).
-/

noncomputable section

namespace PrimeFieldAudit

/-! ### Generic per-primitive certificates (any suitable prime field) -/

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **MiMC** S-box `x^3`: differential uniformity `≤ 2` for `p > 3`. -/
theorem mimc_sbox_diffUnif_le_two (hp3 : 3 < p) :
    APN.differentialUniformity (powerMap (p := p) 3) ≤ 2 :=
  cube_diffUnif_le_two hp3

/-- **Poseidon** S-box `x^5`: differential uniformity `≤ 4` for `p > 5`. -/
theorem poseidon_sbox_diffUnif_le_four (hp5 : 5 < p) :
    APN.differentialUniformity (powerMap (p := p) 5) ≤ 4 :=
  poseidon_diffUnif_le_four hp5

/-- **Rescue / Griffin forward** S-box `x^5`: differential uniformity `≤ 4`. -/
theorem rescue_forward_sbox_diffUnif_le_four (hp5 : 5 < p) :
    APN.differentialUniformity (powerMap (p := p) 5) ≤ 4 :=
  poseidon_diffUnif_le_four hp5

/-- **Rescue / Griffin inverse** S-box `x^(1/5)` (any `e` with `5·e ≡ 1 mod p-1`):
differential uniformity `≤ 4`, matching the forward bound by inversion duality. -/
theorem rescue_griffin_inverse_sbox_diffUnif_le_four (e : ℕ) (hp5 : 5 < p)
    (hde1 : 1 ≤ 5 * e) (hdvd : (p - 1) ∣ (5 * e - 1)) :
    APN.differentialUniformity (powerMap (p := p) e) ≤ 4 :=
  rescue_inverse_sbox_bounded e hp5 hde1 hdvd

/-! ### Forward algebraic degree (low ⇒ arithmetization-friendly) -/

/-- The MiMC forward S-box `x^3` has algebraic degree exactly `3` (for `p > 3`). -/
theorem mimc_algDegree (hp3 : 3 < p) :
    algDegree (powerMap (p := p) 3) = 3 :=
  algDegree_powerMap 3 (by omega)

/-- The Poseidon forward S-box `x^5` has algebraic degree exactly `5` (for `p > 5`). -/
theorem poseidon_algDegree (hp5 : 5 < p) :
    algDegree (powerMap (p := p) 5) = 5 :=
  algDegree_powerMap 5 (by omega)

/-! ### Concrete instances at the BN254 scalar field -/

namespace BN254

open PoseidonParams

variable [Fact (Nat.Prime bn254Fr)]

/-- Poseidon `x^5` over BN254: abstract differential uniformity `≤ 4`. -/
theorem poseidon_diffUnif_le_four :
    APN.differentialUniformity (powerMap (p := bn254Fr) 5) ≤ 4 :=
  poseidon_sbox_diffUnif_le_four bn254_gt_five

/-- MiMC `x^3` over BN254: abstract differential uniformity `≤ 2`. -/
theorem mimc_diffUnif_le_two :
    APN.differentialUniformity (powerMap (p := bn254Fr) 3) ≤ 2 :=
  mimc_sbox_diffUnif_le_two bn254_gt_three

/-- Poseidon `x^5` over BN254 has algebraic degree exactly `5`. -/
theorem poseidon_algDegree_eq :
    algDegree (powerMap (p := bn254Fr) 5) = 5 :=
  poseidon_algDegree bn254_gt_five

end BN254

/-! ### Concrete instances at the BLS12-381 scalar field -/

namespace BLS12381

open PoseidonParams

variable [Fact (Nat.Prime bls12381Fr)]

/-- Poseidon `x^5` over BLS12-381: abstract differential uniformity `≤ 4`. -/
theorem poseidon_diffUnif_le_four :
    APN.differentialUniformity (powerMap (p := bls12381Fr) 5) ≤ 4 :=
  poseidon_sbox_diffUnif_le_four bls12381_gt_five

/-- MiMC `x^3` over BLS12-381: abstract differential uniformity `≤ 2`. -/
theorem mimc_diffUnif_le_two :
    APN.differentialUniformity (powerMap (p := bls12381Fr) 3) ≤ 2 :=
  mimc_sbox_diffUnif_le_two bls12381_gt_three

/-- Poseidon `x^5` over BLS12-381 has algebraic degree exactly `5`. -/
theorem poseidon_algDegree_eq :
    algDegree (powerMap (p := bls12381Fr) 5) = 5 :=
  poseidon_algDegree bls12381_gt_five

end BLS12381

end PrimeFieldAudit

end
