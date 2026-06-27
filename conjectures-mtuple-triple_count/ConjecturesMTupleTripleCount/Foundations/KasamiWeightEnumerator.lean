import ConjecturesMTupleTripleCount.Foundations.KasamiCrossCorrelationValueSet
import ConjecturesMTupleTripleCount.Foundations.ValueDistribution
import Mathlib

/-!
# Foundations, Layer A3 — the cyclic-code / weight-enumerator bridge

This module transcribes **Layer A3** of the value-set dependency chain in
`Docs/VanishFutureDirections.md` §6: the **Delsarte duality** between additive
characters and Hamming weights that identifies the cross-correlation spectrum
`{R(s)}_s` with the *weight distribution* of (the dual of) the two-zero
Kasami/BCH cyclic code.  It is the conceptual hinge that lets the
MacWilliams/Pless machinery (Layer A4) read the moments of `R` off code weights.

## The Delsarte bridge

To a frequency `s` we associate the **codeword**
`c_s : F → GF(2)`, `c_s(x) = Tr(s·Δf_a(x))`, a coordinate vector of the
trace/dual Kasami code.  Its **Hamming weight** is
`w(s) = #{x | c_s(x) ≠ 0} = #{x | χ(s·Δf_a x) = -1}` (`codeWeight`).

Since `χ = (-1)^{Tr}` is `±1`-valued, the character sum
`R(s) = ∑_x χ(s·Δf_a x)` counts the signed balance of the codeword, giving the
**affine duality**
```
  2·w(s) = q − R(s)            (two_mul_codeWeight_eq)
```
i.e. `w(s) = (q − R(s))/2`.  This is exactly the Delsarte relation
"weight = (length − character sum)/2" for a binary trace code; it turns the
*spectrum* `{R(s)}` into the *weight distribution* `{w(s)}` by an order-reversing
affine bijection.

## From the value set to the weight distribution

Feeding Layer 10's value set `R(s) ∈ {q, 0, ±A}` (with `A = 2^{(n+1)/2}`) through
the bridge yields the **three nonzero weights of the dual Kasami code**
```
  w(0) = 0 ,   and for s ≠ 0 :   w(s) ∈ { q/2, (q−A)/2, (q+A)/2 } .
```
(`kasami_codeWeight_value_set`).  Because the bridge is a bijection in `R`, the
multiplicities transfer verbatim from `kasami_crossCorr_value_table`, giving the
weight-distribution table `kasami_codeWeight_table`.

## Scope and the Mathlib gap

Mathlib has linear codes and Hamming distance but **not** cyclic codes as ideals
of `GF(2)[x]/(xᴺ−1)`, BCH bounds, or the additive-character description of their
weights.  This module supplies the substantive, fully self-contained part of the
bridge — the *additive-character description of the weights* (Delsarte duality)
and the resulting weight distribution — which is precisely what Layer A4 (the
MacWilliams identity / Pless power moments) consumes.  The packaging of the
codewords into an honest cyclic-code ideal, and the MacWilliams transform itself,
remain the documented Mathlib gap of Layers A3/A4.

## Sources

MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 5, 7–8
(Delsarte duality, Pless power moments, weight enumerators); Kasami (1971);
Carlet, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## A3 core — the sign-weight duality (upstreamable pearl)

For a `±1`-valued function `g`, twice the number of `-1`'s equals the length
minus the sum.  This is the function-agnostic algebra behind Delsarte duality. -/

/-- **Sign-weight duality.**  For `g : ι → ℤ` taking only the values `1` and
`-1`, `2·#{g = -1} = |ι| − ∑ g`.  (The weight `#{g = -1}` of the associated
binary codeword is `(length − character sum)/2`.) -/
theorem two_mul_negCard_eq_card_sub_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℤ) (hg : ∀ i, g i = 1 ∨ g i = -1) :
    2 * ((univ.filter (fun i => g i = -1)).card : ℤ)
      = (Fintype.card ι : ℤ) - ∑ i, g i := by
  have hsign : ∀ i, g i = -1 ∨ g i = 0 ∨ g i = 1 := fun i => by
    rcases hg i with h | h <;> simp [h]
  have h1 := sum_eq_posCard_sub_negCard g hsign
  have h2 := posCard_add_negCard_add_zeroCard g hsign
  have hzero : zeroCard g = 0 := by
    unfold zeroCard
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    rcases hg i with h | h <;> simp [h]
  unfold posCard negCard zeroCard at *
  rw [hzero] at h2
  have h2' : ((univ.filter (fun i => g i = 1)).card : ℤ)
      + ((univ.filter (fun i => g i = -1)).card : ℤ) = (Fintype.card ι : ℤ) := by
    rw [add_zero] at h2; exact_mod_cast h2
  linarith [h1, h2']

/-! ## The dual Kasami codeword and its Hamming weight -/

/-- The **codeword** of the (dual) trace code at frequency `s`:
`c_s(x) = Tr(s·Δf_a(x)) ∈ GF(2)`. -/
noncomputable def kasamiCodeword (f : F → F) (s a : F) : F → ZMod 2 :=
  fun x => WalshAB.Tr (s * MTuple.deriv f a x)

/-- The **Hamming weight** of the codeword `c_s`:
`w(s) = #{x | χ(s·Δf_a x) = -1}`. -/
noncomputable def codeWeight (f : F → F) (s a : F) : ℕ :=
  (univ.filter (fun x : F => WalshAB.χ (s * MTuple.deriv f a x) = -1)).card

omit [Fintype F] [DecidableEq F] in
/-- `χ z = -1` exactly when `Tr z ≠ 0`. -/
theorem chi_eq_neg_one_iff (z : F) : WalshAB.χ z = -1 ↔ WalshAB.Tr z ≠ 0 := by
  unfold WalshAB.χ; split <;> simp_all

omit [DecidableEq F] in
/-- The codeword's Hamming weight `codeWeight` is literally the number of
coordinates where the codeword `c_s` is nonzero. -/
theorem codeWeight_eq_support_card (f : F → F) (s a : F) :
    codeWeight f s a
      = (univ.filter (fun x : F => kasamiCodeword f s a x ≠ 0)).card := by
  unfold codeWeight kasamiCodeword
  refine congrArg Finset.card ?_
  refine Finset.filter_congr ?_
  intro x _
  simpa using chi_eq_neg_one_iff (s * MTuple.deriv f a x)

/-! ## The Delsarte bridge: `2·w(s) = q − R(s)` -/

/-- **Delsarte duality.**  Twice the codeword weight equals the length minus the
cross-correlation value: `2·w(s) = q − R(s)`.  Off the trivial frequency this is
the affine order-reversing bijection between the spectrum and the weight
distribution. -/
theorem two_mul_codeWeight_eq (f : F → F) (s a : F) :
    2 * (codeWeight f s a : ℤ) = (Fintype.card F : ℤ) - autocorrScaled f s a := by
  have hval : ∀ x : F, WalshAB.χ (s * MTuple.deriv f a x) = 1
      ∨ WalshAB.χ (s * MTuple.deriv f a x) = -1 :=
    fun x => WalshAB.χ_values _
  have hbridge := two_mul_negCard_eq_card_sub_sum
    (fun x : F => WalshAB.χ (s * MTuple.deriv f a x)) hval
  exact hbridge

/-- The codeword weight in closed form: `w(s) = (q − R(s))/2` (as integers). -/
theorem codeWeight_int_eq (f : F → F) (s a : F) :
    (codeWeight f s a : ℤ) = ((Fintype.card F : ℤ) - autocorrScaled f s a) / 2 := by
  have h := two_mul_codeWeight_eq f s a
  omega

/-- The codeword at the trivial frequency `s = 0` is the zero codeword:
`w(0) = 0`. -/
theorem codeWeight_zero (f : F → F) (a : F) : codeWeight f 0 a = 0 := by
  have h := two_mul_codeWeight_eq f 0 a
  rw [MTuple.autocorrScaled_zero] at h
  omega

/-! ## The Kasami dual-code weight distribution

Feeding Layer 10's value set `R(s) ∈ {q, 0, ±A}` through the Delsarte bridge
gives the three nonzero weights `{q/2, (q−A)/2, (q+A)/2}` of the dual Kasami
code, with `A = 2^{(n+1)/2}`. -/

/-- **The Kasami dual-code weight set.**  For the Kasami map `f = (·^{d k})` over
`GF(2ⁿ)` (`n` odd, `1 ≤ k < n`, `gcd(k,n)=1`) and `a ≠ 0`, given the two
classical scalar inputs **(A)** divisibility and **(B)** the fourth moment, twice
each codeword weight lies in `{0, q, q − A, q + A}` (`A = 2^{(n+1)/2}`); the
zero weight occurs only at the trivial frequency `s = 0`. -/
theorem kasami_codeWeight_value_set {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3)
    (s : F) :
    2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ) = 0
    ∨ 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ) = (Fintype.card F : ℤ)
    ∨ 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ)
        = (Fintype.card F : ℤ) - 2 ^ ((n + 1) / 2)
    ∨ 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ)
        = (Fintype.card F : ℤ) + 2 ^ ((n + 1) / 2) := by
  have hbridge := two_mul_codeWeight_eq (fun x : F => x ^ d k) s a
  rcases kasami_crossCorr_value_set hcard hk hkn hcop hnodd hn a ha hdiv hfourth s with
    h | h | h | h <;> rw [h] at hbridge
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; omega

/-! ## The weight-distribution multiplicity table

The Delsarte bridge `R ↦ (q − R)/2` is an affine bijection, so the codeword
weights `(q ∓ A)/2` occur with exactly the multiplicities of the spectrum values
`±A` from `kasami_crossCorr_value_table`. -/

/-- The set of frequencies of a given codeword weight equals the set of
frequencies of the corresponding cross-correlation value, via the Delsarte
bijection `2·w = q − R`. -/
theorem codeWeight_filter_eq (f : F → F) (a : F) (v : ℤ) :
    (univ.filter (fun s : F => 2 * (codeWeight f s a : ℤ) = (Fintype.card F : ℤ) - v))
      = (univ.filter (fun s : F => autocorrScaled f s a = v)) := by
  refine Finset.filter_congr ?_
  intro s _
  have h := two_mul_codeWeight_eq f s a
  constructor <;> intro hh <;> omega

/-- **The Kasami dual-code weight-distribution table.**  With the value set in
hand, the heavy weight `(q + A)/2` and the light weight `(q − A)/2`
(`A = 2^{(n+1)/2}`) occur with the multiplicities of the spectrum values `∓A`:
their signed excess is `A·(#{w = (q−A)/2} − #{w = (q+A)/2}) = −q` and their total
support is `A²·(#{w = (q−A)/2} + #{w = (q+A)/2}) = q²`. -/
theorem kasami_codeWeight_table {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (2 : ℤ) ^ ((n + 1) / 2)
        * (((univ.filter (fun s : F => 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ)
              = (Fintype.card F : ℤ) - 2 ^ ((n + 1) / 2))).card : ℤ)
          - ((univ.filter (fun s : F => 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ)
              = (Fintype.card F : ℤ) + 2 ^ ((n + 1) / 2))).card : ℤ))
        = -(Fintype.card F : ℤ)
    ∧ ((2 : ℤ) ^ ((n + 1) / 2)) ^ 2
        * (((univ.filter (fun s : F => 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ)
              = (Fintype.card F : ℤ) - 2 ^ ((n + 1) / 2))).card : ℤ)
          + ((univ.filter (fun s : F => 2 * (codeWeight (fun x : F => x ^ d k) s a : ℤ)
              = (Fintype.card F : ℤ) + 2 ^ ((n + 1) / 2))).card : ℤ))
        = (Fintype.card F : ℤ) ^ 2 := by
  have hpos := codeWeight_filter_eq (fun x : F => x ^ d k) a (2 ^ ((n + 1) / 2))
  have hneg := codeWeight_filter_eq (fun x : F => x ^ d k) a (-2 ^ ((n + 1) / 2))
  rw [show (Fintype.card F : ℤ) - -2 ^ ((n + 1) / 2)
        = (Fintype.card F : ℤ) + 2 ^ ((n + 1) / 2) from by ring] at hneg
  rw [hpos, hneg]
  exact kasami_crossCorr_value_table hcard hk hkn hcop hnodd hn a ha hdiv hfourth

end Vanish.Foundations
