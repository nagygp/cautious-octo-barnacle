import ConjecturesMTupleTripleCount.Foundations.KasamiAxKatzAK2
import Mathlib

/-!
# Foundations, Layer AK3 — the Stickelberger / Gauss-sum layer (preliminaries)

This module implements the **third layer of the Ax–Katz / McEliece sub-path for
input (A)** laid out in `Docs/VanishFutureDirections.md` §7.

Layer AK2 (`KasamiAxKatzAK2.lean`) built the *arithmetic* of the binary digit sum
`s₂` (= `binDigitSum`) that the Stickelberger congruence reads off.  This layer
supplies the two ingredients AK3 / AK4 consume:

1. **Digit-sum preliminaries (the remaining `s₂`-arithmetic, extending AK2).**
   The block-additivity law `s₂(2^k·m + r) = s₂(m) + s₂(r)` for `r < 2^k`
   (`binDigitSum_block_add`), and the bit-count bound `s₂(a) ≤ n` for `a < 2^n`
   (`binDigitSum_le_of_lt_two_pow`).  These are the elementary digit-sum facts
   the Canteaut–Charpin–Dobbertin / McEliece weight-divisibility bound (AK4)
   reads off the cyclotomic-coset leader.

2. **The Gauss-sum toolkit (the analytic side of Stickelberger).**  The
   elementary structural facts of the Gauss sum `g(χ, ψ) = ∑ₓ χ(x)·ψ(x)` over a
   finite field, all provable from Mathlib: the trivial-character value
   `g(1, ψ) = −1` for a nontrivial `ψ` (`gaussSum_one_eq_neg_one`); the absolute
   value / conjugate identity `g(χ,ψ)·g(χ⁻¹,ψ⁻¹) = q` for nontrivial `χ` and
   primitive `ψ` (`gaussSum_mul_inv_eq_card`); non-vanishing
   (`gaussSum_ne_zero'`); and the Frobenius / `p`-power law
   `g(χ,ψ)^p = g(χ^p, ψ^p)` over a target of characteristic `p`
   (`gaussSum_pow_char`).  These are the analytic inputs on which Stickelberger's
   `2`-adic congruence acts.

## Scope

This layer is sorry-free.  It transcribes the **provable preliminaries** of the
Stickelberger layer: the digit-sum arithmetic and the Gauss-sum structural
toolkit.  The *deep core* of AK3 — Stickelberger's congruence proper, expressing
the `2`-adic valuation `v₂(g(χ))` of a Gauss sum through the binary digit sum
`s₂` of the exponent of the multiplicative character `χ` — requires the `p`-adic
/ Teichmüller machinery (the prime above `2` in the cyclotomic field, the
Gross–Koblitz / Stickelberger factorization) that is **absent from Mathlib**; it
is deliberately neither axiomatized nor `sorry`-ed here, but documented as the
open frontier of the sub-path (as the deep cores of AK4 / BE3 are).

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5–6 (Gauss sums and their valuations);
Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 14
(Stickelberger's congruence); McEliece, *Weight congruences for p-ary cyclic
codes* (Discrete Math., 1972); Canteaut–Charpin–Dobbertin (SIAM J. Discrete
Math., 2000).
-/

namespace Vanish.Foundations

open Finset BigOperators MulChar AddChar

/-! ## 1. Digit-sum preliminaries (extending the AK2 engine) -/

/-
**Block additivity of the binary digit sum.**  If `r < 2^k` then the base-`2`
expansion of `2^k·m + r` is the expansion of `r` (the low `k` bits) followed by
the expansion of `m` (shifted up by `k`), with no carry between the blocks, so
`s₂(2^k·m + r) = s₂(m) + s₂(r)`.  This is the disjoint-block law the
cyclotomic-coset / CCD computation (AK4) reads off.
-/
theorem binDigitSum_block_add (k m r : ℕ) (hr : r < 2 ^ k) :
    binDigitSum (2 ^ k * m + r) = binDigitSum m + binDigitSum r := by
  induction' k with k ih generalizing m r <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
  rcases Nat.even_or_odd' r with ⟨ c, rfl | rfl ⟩;
  · convert ih m c ( by linarith ) using 1;
    · convert binDigitSum_two_mul ( 2 ^ k * m + c ) using 2 ; ring;
    · rw [ Vanish.Foundations.binDigitSum_two_mul ];
  · convert congr_arg ( · + 1 ) ( ih m c ( by linarith ) ) using 1;
    · convert Vanish.Foundations.binDigitSum_two_mul_add_one ( 2 ^ k * m + c ) using 2 ; ring;
    · rw [ add_assoc, Vanish.Foundations.binDigitSum_two_mul_add_one ]

/-
**Bit-count bound.**  If `a < 2^n` then `a` has at most `n` binary digits, so its
digit sum is at most `n`: `s₂(a) ≤ n`.
-/
theorem binDigitSum_le_of_lt_two_pow (n a : ℕ) (ha : a < 2 ^ n) :
    binDigitSum a ≤ n := by
  -- By definition of exponentiation, we know that $2^n > a$ implies that $a$ has at most $n$ digits in binary.
  have h_digits : (Nat.digits 2 a).length ≤ n := by
    have := @Nat.digits_len 2 a;
    exact if h : a = 0 then by simp +decide [ h ] else by rw [ this ( by decide ) h ] ; exact Nat.log_lt_of_lt_pow ( by positivity ) ha;
  exact le_trans ( List.sum_le_card_nsmul _ _ fun x hx => Nat.le_of_lt_succ <| Nat.digits_lt_base' hx ) <| by simpa using h_digits;

/-! ## 2. The Gauss-sum toolkit (the analytic side of Stickelberger) -/

variable {R : Type*} [Field R] [Fintype R]
  {R' : Type*} [CommRing R'] [IsDomain R']

/-
**Trivial-character Gauss sum.**  For a nontrivial additive character `ψ` of a
finite field, the Gauss sum of the *trivial* multiplicative character is `−1`:
`g(1, ψ) = ∑_{x≠0} ψ(x) = (∑ₓ ψ(x)) − ψ(0) = 0 − 1 = −1`.
-/
theorem gaussSum_one_eq_neg_one {ψ : AddChar R R'} (hψ : ψ ≠ 1) :
    gaussSum (1 : MulChar R R') ψ = -1 := by
  have := AddChar.sum_eq_zero_of_ne_one hψ;
  convert congr_arg ( fun x => x - 1 ) this using 1;
  · convert Finset.sum_eq_sum_diff_singleton_add ( Finset.mem_univ ( 0 : R ) ) ( fun a => ( 1 : MulChar R R' ) a * ψ a ) using 1;
    convert sub_eq_iff_eq_add.mpr rfl using 1;
    convert sub_eq_iff_eq_add.mpr rfl using 1;
    convert rfl;
    rotate_left;
    exact inferInstance;
    exact 0;
    exact Classical.decEq R;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ MulChar.one_apply ( IsUnit.mk0 x ( by aesop ) ) ] ] ; simp +decide;
  · norm_num

/--
**The conjugate / absolute-value identity.**  For a nontrivial multiplicative
character `χ` and a primitive additive character `ψ`, the product of the Gauss
sum and its conjugate is the field size: `g(χ, ψ)·g(χ⁻¹, ψ⁻¹) = q`.  (A direct
restatement of Mathlib's `gaussSum_mul_gaussSum_eq_card`, the analytic anchor of
the `|g(χ)|² = q` absolute-value bound that Stickelberger refines `2`-adically.)
-/
theorem gaussSum_mul_inv_eq_card {χ : MulChar R R'} (hχ : χ ≠ 1)
    {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card R : R') :=
  gaussSum_mul_gaussSum_eq_card hχ hψ

/--
**Non-vanishing of the Gauss sum.**  When the field size is invertible in the
target (`(q : R') ≠ 0`), the Gauss sum of a nontrivial multiplicative character
against a primitive additive character is nonzero.
-/
theorem gaussSum_ne_zero' (h : (Fintype.card R : R') ≠ 0) {χ : MulChar R R'}
    (hχ : χ ≠ 1) {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 :=
  gaussSum_ne_zero_of_nontrivial h hχ hψ

omit [IsDomain R'] in
/--
**The Frobenius / `p`-power law.**  When the target ring `R'` has prime
characteristic `p`, the `p`-th power of a Gauss sum of `χ` and `ψ` is the Gauss
sum of their `p`-th powers: `g(χ, ψ)^p = g(χ^p, ψ^p)`.  This is the algebraic
identity underlying the Galois descent used in Stickelberger's congruence.
-/
theorem gaussSum_pow_char (p : ℕ) [Fact p.Prime] [CharP R' p]
    (χ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ ^ p = gaussSum (χ ^ p) (ψ ^ p) :=
  gaussSum_frob p χ ψ

end Vanish.Foundations