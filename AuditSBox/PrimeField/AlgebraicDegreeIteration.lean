import Mathlib
import AuditSBox.PrimeFieldDiffUnif
import AuditSBox.PrimeField.AlgebraicDegree

/-!
# Algebraic-degree growth under round iteration

`AuditSBox.PrimeField.AlgebraicDegree` proves the *per-S-box* algebraic degree of
a power map `x ↦ x^d` (with `d < p`) is exactly `d`.  For an arithmetization-
friendly permutation built by *iterating* a low-degree round map (MiMC, Poseidon,
Rescue, …), the security-relevant quantity is how the algebraic degree grows under
that iteration — this is what designers quote for interpolation / Gröbner
resistance (`RESEARCH_DIRECTIONS.md` item 5, `FUTURE_DIRECTIONS_FOUNDATIONS` §B).

Composing the power map `x ↦ x^d` with itself `r` times is the power map
`x ↦ x^{d^r}` (`powerMap_iterate`).  As a *function* on `ZMod p`, the exponent
only matters modulo `p − 1` (Fermat): for `m ≥ 1`,

  `x^m = x^{((m-1) mod (p-1)) + 1}`  for all `x : ZMod p`,

so the algebraic degree of `x ↦ x^m` is the **reduced exponent**
`redExp p m := ((m-1) mod (p-1)) + 1 ∈ {1, …, p-1}`.  Iteration multiplies the raw
exponent (`d^r`) but the algebraic degree is its reduction, which **saturates** at
`p − 1` (`algDegree_powerMap_iterate`, `redExp_le`).

## Main results

* `powerMap_reduce` — `powerMap m = powerMap (redExp p m)` as functions (`m ≥ 1`).
* `redExp_le` / `redExp_pos` — `1 ≤ redExp p m ≤ p − 1`.
* `algDegree_powerMap_reduce` — `algDegree (powerMap m) = redExp p m` for `m ≥ 1`.
* `powerMap_iterate` — `(powerMap d)^[r] = powerMap (d^r)`.
* `algDegree_powerMap_iterate` — `algDegree ((powerMap d)^[r]) = redExp p (d^r)`
  for `d ≥ 1`: the round-iterated algebraic degree, saturating at `p − 1`.
-/

open Polynomial

noncomputable section

namespace PrimeFieldAudit

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The **reduced exponent** of `m` modulo `p − 1`, normalised into `{1, …, p-1}`:
`redExp p m = ((m-1) mod (p-1)) + 1`.  It is the algebraic degree of the function
`x ↦ x^m` on `ZMod p` (for `m ≥ 1`). -/
def redExp (p m : ℕ) : ℕ := (m - 1) % (p - 1) + 1

omit hp in
/-- The reduced exponent is positive. -/
theorem redExp_pos (m : ℕ) : 1 ≤ redExp p m := Nat.le_add_left 1 _

/-- The reduced exponent saturates at `p − 1`. -/
theorem redExp_le (m : ℕ) : redExp p m ≤ p - 1 := by
  have hp2 : 2 ≤ p := hp.1.two_le
  have : (m - 1) % (p - 1) < p - 1 := Nat.mod_lt _ (by omega)
  unfold redExp; omega

/-
As a function on `ZMod p`, the exponent only matters via its reduction:
`x^m = x^{redExp p m}` for every `x`, when `m ≥ 1`.
-/
theorem powerMap_reduce (m : ℕ) (hm : 1 ≤ m) :
    powerMap (p := p) m = powerMap (p := p) (redExp p m) := by
  ext x; by_cases hx : x = 0 <;> simp +decide [ hx, powerMap ];
  · rw [ zero_pow ( by linarith ), zero_pow ( by exact Nat.succ_ne_zero _ ) ];
  · rw [ show m = ( m - 1 ) % ( p - 1 ) + 1 + ( p - 1 ) * ( ( m - 1 ) / ( p - 1 ) ) by linarith [ Nat.mod_add_div ( m - 1 ) ( p - 1 ), Nat.sub_add_cancel hm ], pow_add, pow_mul ] ; simp +decide [ hx, ZMod.pow_card_sub_one_eq_one ];
    unfold redExp; simp +decide [ Nat.add_mod, Nat.mod_eq_of_lt ( show ( m - 1 ) % ( p - 1 ) < p - 1 from Nat.mod_lt _ ( Nat.sub_pos_of_lt hp.1.one_lt ) ) ] ;

/-- **Algebraic degree of a general power map.**  For `m ≥ 1`, the function
`x ↦ x^m` over `ZMod p` has algebraic degree the reduced exponent `redExp p m`. -/
theorem algDegree_powerMap_reduce (m : ℕ) (hm : 1 ≤ m) :
    algDegree (powerMap (p := p) m) = redExp p m := by
  rw [algDegree, powerMap_reduce m hm,
    canonicalPoly_powerMap (redExp p m) (lt_of_le_of_lt (redExp_le m) (by have := hp.1.two_le; omega)),
    natDegree_X_pow]

/-- Iterating the power map `x ↦ x^d` `r` times is the power map `x ↦ x^{d^r}`. -/
theorem powerMap_iterate (d r : ℕ) :
    (powerMap (p := p) d)^[r] = powerMap (p := p) (d ^ r) := by
  induction r with
  | zero => funext x; simp [powerMap]
  | succ n ih =>
      rw [Function.iterate_succ', ih, powerMap_comp, pow_succ]

/-- **Round-iterated algebraic degree (saturating).**  For a low-degree round map
`x ↦ x^d` with `d ≥ 1`, the algebraic degree of the `r`-fold iterate is the
reduced exponent `redExp p (d^r)` — the raw exponent `d^r` reduced modulo `p − 1`,
saturating at `p − 1`. -/
theorem algDegree_powerMap_iterate (d r : ℕ) (hd : 1 ≤ d) :
    algDegree ((powerMap (p := p) d)^[r]) = redExp p (d ^ r) := by
  rw [powerMap_iterate]
  exact algDegree_powerMap_reduce (d ^ r) (Nat.one_le_pow _ _ hd)

end PrimeFieldAudit

end