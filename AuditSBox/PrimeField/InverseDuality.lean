import Mathlib
import RequestProject.DiffUniformity.DifferentialUniformityUpstream
import AuditSBox.PrimeFieldDiffUnif
import AuditSBox.PrimeField.AbstractBridge

/-!
# Differential uniformity is invariant under inversion

Several arithmetization-friendly primitives (Rescue, Griffin, …) use *inverse*
power maps `x ↦ x^(1/d)` as their nonlinear layer.  Over `ZMod p` the map
`x ↦ x^e` with `d·e ≡ 1 (mod p-1)` is exactly the functional inverse of the
permutation `x ↦ x^d`.

The differential uniformity of a permutation equals that of its inverse — this is
the classical "the DDT of `f⁻¹` is the transpose of the DDT of `f`" fact.  We
prove it abstractly in the `APN` framework and then specialize: the inverse power
map enjoys the *same* differential bound as the forward power map, so e.g. the
Rescue inverse S-box `x^(1/5)` has differential uniformity `≤ 4`.

## Main results

* `APN.fiberCard_inv_transpose` — for mutually inverse `f`, `g` on a finite
  additive group, `fiberCard g a b = fiberCard f b a`.
* `APN.differentialUniformity_inv` — `differentialUniformity g =
  differentialUniformity f` for mutually inverse `f`, `g`.
* `PrimeFieldAudit.powerMap_comp_eq_id` — `x^d` and `x^e` are mutually inverse
  over `ZMod p` when `d·e ≡ 1 (mod p-1)`.
* `PrimeFieldAudit.inversePowerMap_diffUnif_le` — the inverse power map shares the
  `≤ d-1` differential bound.
* `PrimeFieldAudit.rescue_inverse_sbox_bounded` — the Rescue inverse S-box
  `x^(1/5)` has `δ ≤ 4`.
-/

open scoped Classical

namespace APN

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-
For mutually inverse maps `f`, `g` on a finite additive group, the derivative
fibre counts are transposes of one another:
`fiberCard g a b = fiberCard f b a`.
-/
omit [Fintype G] in
theorem fiberCard_inv_transpose (f g : G → G)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f)
    (a b : G) :
    fiberCard g a b = fiberCard f b a := by
  convert Nat.card_congr _ using 1;
  refine' Equiv.ofBijective _ ⟨ fun x y h => _, fun y => _ ⟩;
  use fun x => ⟨ g x, by
    simp_all +decide [ Function.LeftInverse, Function.RightInverse, derivMap ];
    have := x.2; simp_all +decide [ derivMap ] ;
    simp +decide [ ← this, hfg ] ⟩
  all_goals generalize_proofs at *;
  · grind;
  · use ⟨ f y, by
      have := y.2; simp_all +decide [ derivMap ] ;
      grind ⟩
    generalize_proofs at *;
    aesop

/-
The differential uniformity of a permutation equals that of its inverse.
-/
theorem differentialUniformity_inv (f g : G → G)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) :
    differentialUniformity g = differentialUniformity f := by
  refine' le_antisymm ( diffUnif_le_iff g ( differentialUniformity f ) |>.2 _ ) ( diffUnif_le_iff f ( differentialUniformity g ) |>.2 _ );
  · intro a ha b;
    by_cases hb : b = 0;
    · rw [ fiberCard_inv_transpose f g hgf hfg a b, hb ];
      unfold fiberCard; simp +decide [ APN.derivMap ] ;
      simp +decide [ ha.symm ];
    · exact fiberCard_inv_transpose f g hgf hfg a b ▸ fiberCard_le_diffUnif f hb a;
  · intro a ha b
    have h_fiberCard : fiberCard f a b = fiberCard g b a := by
      rw [ APN.fiberCard_inv_transpose f g hgf hfg ];
    by_cases hb : b = 0;
    · simp_all +decide [ fiberCard ];
      simp_all +decide [ derivMap ];
      simp +decide [ ha, eq_comm ];
    · exact h_fiberCard.symm ▸ APN.fiberCard_le_diffUnif g hb a

end APN

namespace PrimeFieldAudit

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-
Over `ZMod p`, the power maps `x^d` and `x^e` are mutually inverse whenever
`d·e ≡ 1 (mod p-1)` and `1 ≤ d·e`.  (Fermat's little theorem reduces the exponent
mod `p-1` on nonzero inputs; the exponent positivity handles `x = 0`.)
-/
theorem powerMap_comp_eq_id (d e : ℕ) (hde1 : 1 ≤ d * e)
    (hdvd : (p - 1) ∣ (d * e - 1)) :
    Function.LeftInverse (powerMap (p := p) e) (powerMap (p := p) d) := by
  intro x
  by_cases hx : x = 0;
  · simp +decide [ hx, powerMap ];
    aesop;
  · obtain ⟨ k, hk ⟩ := hdvd;
    rw [ tsub_eq_iff_eq_add_of_le hde1 ] at hk;
    simp +decide [ ← pow_mul, hk, powerMap ];
    simp +decide [ pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx ]

/-- The inverse power map `x^e` (with `d·e ≡ 1 mod p-1`) has the same differential
uniformity bound `≤ d-1` as the forward power map `x^d`. -/
theorem inversePowerMap_diffUnif_le (d e : ℕ) (hd : 2 ≤ d) (hpd : ¬ (p ∣ d))
    (hde1 : 1 ≤ d * e) (hdvd : (p - 1) ∣ (d * e - 1)) :
    APN.differentialUniformity (powerMap (p := p) e) ≤ d - 1 := by
  have hinv := powerMap_comp_eq_id (p := p) d e hde1 hdvd
  have hinv' : Function.RightInverse (powerMap (p := p) e) (powerMap (p := p) d) := by
    have hsymm := powerMap_comp_eq_id (p := p) e d (by rwa [Nat.mul_comm])
      (by rwa [Nat.mul_comm])
    exact hsymm
  rw [APN.differentialUniformity_inv (powerMap (p := p) d) (powerMap (p := p) e) hinv hinv']
  exact powerMap_diffUnif_le d hd hpd

/-- **Rescue inverse S-box.**  Any inverse `x^e` of the Rescue forward S-box `x^5`
(i.e. `5·e ≡ 1 mod p-1`) has differential uniformity `≤ 4`, for `p > 5`. -/
theorem rescue_inverse_sbox_bounded (e : ℕ) (hp5 : 5 < p)
    (hde1 : 1 ≤ 5 * e) (hdvd : (p - 1) ∣ (5 * e - 1)) :
    APN.differentialUniformity (powerMap (p := p) e) ≤ 4 :=
  inversePowerMap_diffUnif_le 5 e (by norm_num)
    (Nat.not_dvd_of_pos_of_lt (by norm_num) hp5) hde1 hdvd

end PrimeFieldAudit