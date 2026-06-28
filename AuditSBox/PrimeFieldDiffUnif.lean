import Mathlib

/-!
# Prime Field Differential Uniformity — Verification Module

Formalizes the differential uniformity bound for power maps over prime fields,
providing a reusable framework for cryptographic S-box audit.

## Main Results

- `diffUniformity_power_le`: For the power map `x ^ d` over a finite field `F`,
  when char(F) does not divide d and d ≥ 2, the differential uniformity is `≤ d - 1`.
- `poseidon_sbox_bounded`: For `x ^ 5` over `ZMod p` with `p > 5` prime, uniformity `≤ 4`.
- `bias_bound`: The S-box contributes a maximum differential bias of `(d-1)/p`.

## Mathematical Argument

For `f(x) = x^d` over a finite field `F`, the differential equation `f(x+a) - f(x) = b`
becomes `(x+a)^d - x^d = b`. Expanding, the `x^d` terms cancel, yielding a
polynomial of degree `≤ d-1` in `x`. When the characteristic does not divide `d`,
the coefficient of `x^{d-1}` is `d·a ≠ 0`, ensuring the polynomial is nonzero.
By the fundamental theorem of algebra for finite fields, this polynomial has at
most `d-1` roots.

**Note**: The hypothesis `char(F) ∤ d` is necessary. In characteristic `p` with
`d = p`, we have `(x+a)^p - x^p = a^p` for all `x` (Frobenius), making every
element a solution when `b = a^p`.
-/

open Polynomial Finset Fintype BigOperators

noncomputable section

namespace PrimeFieldAudit

/-! ### §1. Core Definitions -/

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The power map `x ↦ x ^ d` over `ZMod p`. -/
def powerMap (d : ℕ) : ZMod p → ZMod p := fun x => x ^ d

/-- The derivative of `f` in direction `a`: `Df_a(x) = f(x+a) - f(x)`. -/
def diff (f : ZMod p → ZMod p) (a x : ZMod p) : ZMod p :=
  f (x + a) - f x

/-- The fiber: set of `x` such that `diff f a x = b`. -/
def fiber (f : ZMod p → ZMod p) (a b : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun x => diff f a x = b)

/-- The fiber cardinality. -/
def fiberCard (f : ZMod p → ZMod p) (a b : ZMod p) : ℕ :=
  (fiber f a b).card

/-- Differential uniformity bound: all fibers have cardinality `≤ δ`. -/
def isDiffBounded (δ : ℕ) (f : ZMod p → ZMod p) : Prop :=
  ∀ a : ZMod p, a ≠ 0 → ∀ b : ZMod p, fiberCard f a b ≤ δ

/-! ### §2. Polynomial Root Count -/

/-- Solutions to a polynomial equation over a field are bounded by the degree. -/
lemma card_solutions_le_natDegree {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (q : Polynomial F) (hq : q ≠ 0) :
    (Finset.univ.filter (fun x => q.eval x = 0)).card ≤ q.natDegree := by
  have : (Finset.univ.filter (fun x => eval x q = 0)).val.card ≤ (q.roots.toFinset).card := by
    refine Finset.card_le_card ?_
    intro x hx; aesop
  exact this.trans (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _))

/-! ### §3. The Differential Polynomial -/

/-- The differential polynomial: `(X + C a)^d - X^d - C b`. -/
def diffPoly (F : Type*) [CommRing F] (a b : F) (d : ℕ) : Polynomial F :=
  (Polynomial.X + Polynomial.C a) ^ d - Polynomial.X ^ d - Polynomial.C b

/-- The differential polynomial has degree ≤ d - 1 when `a ≠ 0` and `d ≥ 2`. -/
lemma diffPoly_natDegree_le {F : Type*} [Field F] (a b : F) (ha : a ≠ 0)
    (d : ℕ) (hd : 2 ≤ d) :
    (diffPoly F a b d).natDegree ≤ d - 1 := by
  have h_deg_sub : Polynomial.degree ((Polynomial.X + Polynomial.C a) ^ d -
      Polynomial.X ^ d : Polynomial F) < d := by
    convert Polynomial.degree_sub_lt _ _ _ <;> norm_num
    exact fun h => absurd h <| Polynomial.X_add_C_ne_zero a
  rw [diffPoly] at *
  rcases d with (_ | _ | d) <;>
    simp_all +decide [Polynomial.degree_add_eq_left_of_degree_lt]
  contrapose! h_deg_sub
  rw [Polynomial.degree_eq_natDegree] <;> norm_cast; aesop

/-- Evaluating the differential polynomial gives the differential of the power map. -/
lemma diffPoly_eval {F : Type*} [CommRing F] (a b : F) (d : ℕ) (x : F) :
    (diffPoly F a b d).eval x = (x + a) ^ d - x ^ d - b := by
  simp [diffPoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]

/-! ### §4. Nonvanishing of the Differential Polynomial

When `char(F) ∤ d`, the coefficient of `x^{d-1}` in `(X+a)^d - X^d` is `d·a ≠ 0`,
so the differential polynomial is nonzero for any `b`.
-/

/-
The differential polynomial `(X+a)^d - X^d - b` is nonzero when
    `a ≠ 0`, `d ≥ 2`, and `char(F) ∤ d`.
-/
lemma diffPoly_ne_zero {F : Type*} [Field F] (a b : F) (ha : a ≠ 0)
    (d : ℕ) (hd : 2 ≤ d) (hchar : (d : F) ≠ 0) :
    diffPoly F a b d ≠ 0 := by
      refine' ne_of_apply_ne ( fun p => p.coeff ( d - 1 ) ) _;
      unfold diffPoly; simp +decide [ Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow, Polynomial.coeff_C, Nat.sub_add_cancel ( by linarith : 1 ≤ d ) ] ;
      rcases d with ( _ | _ | d ) <;> simp_all +decide [ Nat.choose_succ_succ, pow_succ' ]

/-! ### §5. Main Differential Uniformity Bound -/

/-
**Key Theorem**: The power map `x^d` has differential uniformity `≤ d - 1`
    over any finite field, provided `d ≥ 2` and `char(F) ∤ d`.

    The hypothesis `char(F) ∤ d` is necessary: in characteristic `p` with `d = p`,
    the Frobenius endomorphism gives `(x+a)^p - x^p = a^p` for all `x`.
-/
theorem diffUniformity_power_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (hd : 2 ≤ d) (hchar : (d : F) ≠ 0) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      (Finset.univ.filter (fun x => (x + a) ^ d - x ^ d = b)).card ≤ d - 1 := by
        intro a ha b;
        convert card_solutions_le_natDegree ( diffPoly F a b d ) ( diffPoly_ne_zero a b ha d hd hchar ) |> le_trans <| diffPoly_natDegree_le a b ha d hd using 1;
        simp +decide [ diffPoly, sub_eq_iff_eq_add ]

/-! ### §6. Application to ZMod p -/

/-- The power map `x^d` over `ZMod p` has differential uniformity `≤ d - 1`,
    provided `d ≥ 2` and `p ∤ d`. -/
theorem power_map_bounded (d : ℕ) (hd : 2 ≤ d) (hpd : ¬ (p ∣ d)) :
    isDiffBounded (d - 1) (powerMap (p := p) d) := by
  intro a ha b
  simp only [fiberCard, fiber, diff, powerMap]
  have hchar : (d : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff d p]
  exact diffUniformity_power_le d hd hchar a ha b

/-! ### §7. Poseidon S-box: x^5 -/

/-- **Poseidon audit**: The `x^5` S-box over `ZMod p` has differential uniformity `≤ 4`,
    provided `p > 5` (so that `p ∤ 5`). -/
theorem poseidon_sbox_bounded (hp5 : 5 < p) :
    isDiffBounded 4 (powerMap (p := p) 5) := by
  apply power_map_bounded 5 (by norm_num)
  exact Nat.not_dvd_of_pos_of_lt (by omega) hp5

/-- The `x^3` cubing map has differential uniformity `≤ 2`, provided `p > 3`. -/
theorem cube_map_bounded (hp3 : 3 < p) :
    isDiffBounded 2 (powerMap (p := p) 3) := by
  apply power_map_bounded 3 (by norm_num)
  exact Nat.not_dvd_of_pos_of_lt (by omega) hp3

/-- The `x^7` map has differential uniformity `≤ 6`, provided `p > 7`. -/
theorem septic_map_bounded (hp7 : 7 < p) :
    isDiffBounded 6 (powerMap (p := p) 7) := by
  apply power_map_bounded 7 (by norm_num)
  exact Nat.not_dvd_of_pos_of_lt (by omega) hp7

/-! ### §8. Bias Bound

For a prime field `𝔽_p` with the `x^d` S-box, the maximum differential bias is
`(d-1)/p`. For Poseidon with BN254 (`p ≈ 2^254`), this gives `4/p ≈ 2^{-252}`,
which is cryptographically negligible.
-/

/-- The differential bias of the power map is at most `(d-1)/p`. -/
theorem bias_bound (d : ℕ) (hd : 2 ≤ d) (hpd : ¬ (p ∣ d))
    (a : ZMod p) (ha : a ≠ 0) (b : ZMod p) :
    (fiberCard (powerMap (p := p) d) a b : ℚ) / (Fintype.card (ZMod p) : ℚ) ≤
    ((d - 1 : ℕ) : ℚ) / (p : ℚ) := by
  rw [ZMod.card p]
  have hbound := power_map_bounded (p := p) d hd hpd a ha b
  exact div_le_div_of_nonneg_right (by exact_mod_cast hbound) (by positivity)

end PrimeFieldAudit

end