import RequestProject.Weil.CharSum

/-!
# Hasse derivatives and high-order vanishing

Stepanov's method certifies that the auxiliary polynomial vanishes *to high order* at every curve
point.  Over a field of positive characteristic the ordinary derivative is useless for this (it
collapses on `p`-th powers), so one uses the **Hasse derivatives** `hasseDeriv k`, the
characteristic-free analogue of `f^{(k)}/k!`.  The decisive fact is the *vanishing criterion*:

> if all Hasse derivatives of order `< m` of a nonzero `g` vanish at `a`, then `a` is a root of `g`
> of multiplicity at least `m`,

and its converse.  This is what feeds the counting engine `card_le_of_rootMultiplicity` in
`Weil.Stepanov`.  This module isolates the Hasse-derivative API needed: the vanishing criterion, the
behaviour under products (Leibniz) and under `p`-th powers (the Frobenius interaction that makes the
high-order vanishing computable for the explicit Stepanov polynomial).

These statements are about `Mathlib`'s `Polynomial.hasseDeriv`; they are medium-difficulty and
self-contained.

## Main statements (skeletons)
* `Weil.Hasse.le_rootMultiplicity_of_hasseDeriv` — the vanishing criterion (`⇐`).
* `Weil.Hasse.hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity` — its converse (`⇒`).
* `Weil.Hasse.hasseDeriv_mul` — the Leibniz rule for Hasse derivatives.
* `Weil.Hasse.hasseDeriv_pow_char` — Hasse derivatives of a `p`-th power (Frobenius interaction).
* `Weil.Hasse.rootMultiplicity_prod_le` — multiplicities add: a tool to transfer vanishing across
  products in the construction.
-/

open scoped BigOperators
open Polynomial

namespace Weil
namespace Hasse

variable {F : Type*} [Field F]

/-
**Vanishing criterion (the direction used by Stepanov).**  If every Hasse derivative of order
strictly below `m` of a nonzero polynomial `g` vanishes at `a`, then `a` is a root of `g` of
multiplicity at least `m`.  Together with `card_le_of_rootMultiplicity` this turns high-order
vanishing at curve points into the point-count bound.
-/
lemma le_rootMultiplicity_of_hasseDeriv (g : F[X]) (hg : g ≠ 0) (a : F) (m : ℕ)
    (h : ∀ k < m, (Polynomial.hasseDeriv k g).eval a = 0) :
    m ≤ g.rootMultiplicity a := by
  rw [ Polynomial.le_rootMultiplicity_iff hg ];
  have h_taylor : ∀ k < m, Polynomial.coeff (Polynomial.comp g (Polynomial.X + Polynomial.C a)) k = 0 := by
    convert h using 2;
    rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
    simp +decide [ Polynomial.coeff_X_add_C_pow, hasseDeriv ];
    simp +decide [ Polynomial.eval_finset_sum, mul_assoc, mul_comm, mul_left_comm, Polynomial.sum_over_range ];
  have h_taylor_div : (Polynomial.X)^m ∣ Polynomial.comp g (Polynomial.X + Polynomial.C a) := by
    exact Polynomial.X_pow_dvd_iff.mpr fun k hk => h_taylor k hk;
  obtain ⟨ q, hq ⟩ := h_taylor_div; replace hq := congr_arg ( Polynomial.comp · ( Polynomial.X - Polynomial.C a ) ) hq; simp_all +decide [ Polynomial.comp_assoc ] ;

/-
**Converse vanishing criterion.**  If `a` is a root of multiplicity at least `m`, then all Hasse
derivatives of order `< m` vanish at `a`.
-/
lemma hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity (g : F[X]) (a : F) (m : ℕ)
    (hm : m ≤ g.rootMultiplicity a) (k : ℕ) (hk : k < m) :
    (Polynomial.hasseDeriv k g).eval a = 0 := by
  have h_coeff : (g.comp (Polynomial.X + Polynomial.C a)).coeff k = (Polynomial.hasseDeriv k g).eval a := by
    simp +decide [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
    simp +decide [ Polynomial.coeff_X_add_C_pow, Polynomial.hasseDeriv ];
    simp +decide [ Polynomial.eval_finset_sum, mul_assoc, mul_comm, mul_left_comm, Polynomial.sum_over_range ];
  rw [ ← h_coeff, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree ];
  convert hk.trans_le hm using 1;
  exact?

/-- **Leibniz rule** for Hasse derivatives: `Dₖ(g·h) = ∑_{i+j=k} Dᵢ g · Dⱼ h`.  Used to control the
order of vanishing of products appearing in the auxiliary-polynomial construction. -/
lemma hasseDeriv_mul (g h : F[X]) (k : ℕ) :
    Polynomial.hasseDeriv k (g * h)
      = ∑ ij ∈ Finset.antidiagonal k,
          Polynomial.hasseDeriv ij.1 g * Polynomial.hasseDeriv ij.2 h := by
  rw [Polynomial.hasseDeriv_mul]

/-- A natural-number cast is fixed by the Frobenius `x ↦ x^p` (it lies in the prime subfield). -/
lemma natCast_pow_char [Fintype F] (m : ℕ) : (m : F) ^ (ringChar F) = (m : F) := by
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.char_is_prime F (ringChar F)⟩
  induction m with
  | zero => simp [zero_pow (Nat.Prime.pos (Fact.out (p := (ringChar F).Prime))).ne']
  | succ n ih =>
      push_cast
      rw [add_pow_char, ih, one_pow]

/-- A natural-number cast is fixed by every power of the Frobenius `x ↦ x^(p^j)`. -/
lemma natCast_pow_char_pow [Fintype F] (m j : ℕ) : (m : F) ^ (ringChar F ^ j) = (m : F) := by
  induction j with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, ih, natCast_pow_char]

/-- **Coefficients of a `p^j`-th power in characteristic `p`.**  For any `h : F[X]`,
the `i`-th coefficient of `h ^ (p^j)` is `(h.coeff (i / p^j))^(p^j)` if `p^j ∣ i`, and `0`
otherwise.  This is the Frobenius/`expand` interaction at the level of coefficients. -/
lemma coeff_pow_char_pow [Fintype F] (h : F[X]) (j i : ℕ) :
    (h ^ (ringChar F ^ j)).coeff i
      = (if ringChar F ^ j ∣ i then (h.coeff (i / ringChar F ^ j)) ^ (ringChar F ^ j) else 0) := by
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.char_is_prime F (ringChar F)⟩
  haveI : ExpChar F (ringChar F) := ExpChar.prime (Fact.out (p := (ringChar F).Prime))
  have hpos : 0 < ringChar F ^ j := pow_pos (Nat.Prime.pos (Fact.out (p := (ringChar F).Prime))) _
  rw [← Polynomial.map_iterateFrobenius_expand (R := F) (p := ringChar F) h j,
      Polynomial.coeff_map, Polynomial.coeff_expand hpos, iterateFrobenius_def]
  split_ifs with hdvd
  · rfl
  · simp [zero_pow hpos.ne']

/-
**Frobenius interaction.**  In characteristic `p`, the Hasse derivative of a `p`-th power is a
`p`-th power of a Hasse derivative when `p ∣ k`, and vanishes otherwise.  This is the identity that
makes the high-order vanishing of the Stepanov polynomial (an `𝔽_q`-combination of `p`-th powers)
reducible to *linear* conditions on its coefficients.
-/
lemma hasseDeriv_pow_char [Fintype F] (g : F[X]) (j k : ℕ) :
    Polynomial.hasseDeriv k (g ^ (ringChar F ^ j))
      = (if ringChar F ^ j ∣ k
          then (Polynomial.hasseDeriv (k / ringChar F ^ j) g) ^ (ringChar F ^ j)
          else 0) := by
  split_ifs with h;
  · refine' Polynomial.ext fun n => _;
    obtain ⟨ m, rfl ⟩ := h;
    by_cases h : ringChar F ^ j ∣ n <;> simp_all +decide [ Polynomial.hasseDeriv_coeff ];
    · -- By Lucas's theorem, we know that $\binom{n + p^j m}{p^j m} \equiv \binom{n/p^j + m}{m} \pmod{p}$.
      have h_lucas : Nat.choose (n + ringChar F ^ j * m) (ringChar F ^ j * m) ≡ Nat.choose (n / ringChar F ^ j + m) m [MOD ringChar F] := by
        obtain ⟨ k, rfl ⟩ := h;
        have h_choose : Nat.choose (ringChar F ^ j * (k + m)) (ringChar F ^ j * m) ≡ Nat.choose (k + m) m [MOD ringChar F] := by
          have h_prime : Nat.Prime (ringChar F) := by
            exact CharP.char_is_prime F ( ringChar F )
          haveI := Fact.mk h_prime; simp +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
          -- Using the polynomial expansion, we can see that $(1 + X)^{p^j (k + m)} \equiv (1 + X^{p^j})^{k + m} \pmod{p}$.
          have h_poly_expand : (1 + Polynomial.X : Polynomial (ZMod (ringChar F))) ^ (ringChar F ^ j * (k + m)) = (1 + Polynomial.X ^ (ringChar F ^ j)) ^ (k + m) := by
            rw [ pow_mul ];
            simp +decide [ add_pow_char_pow ];
          replace h_poly_expand := congr_arg ( fun q => Polynomial.coeff q ( ringChar F ^ j * m ) ) h_poly_expand ; simp_all +decide [ Polynomial.coeff_one_add_X_pow ];
          rw [ add_comm, add_pow ];
          simp +decide [ ← pow_mul, Polynomial.coeff_X_pow ];
          rw [ Finset.sum_eq_single m ] <;> aesop;
        rwa [ Nat.mul_add, Nat.mul_div_cancel_left _ ( pow_pos ( Nat.Prime.pos ( CharP.char_is_prime F ( ringChar F ) ) ) _ ) ] at *;
      convert congr_arg ( fun x : ℕ => ( x : F ) * ( g ^ ringChar F ^ j |> Polynomial.coeff ) ( n + ringChar F ^ j * m ) ) h_lucas using 1;
      · rw [ ← Nat.mod_add_div ( Nat.choose ( n + ringChar F ^ j * m ) ( ringChar F ^ j * m ) ) ( ringChar F ) ] ; simp +decide [ pow_add, pow_mul, CharP.cast_eq_zero ] ;
      · rw [ Weil.Hasse.coeff_pow_char_pow ];
        rw [ Weil.Hasse.coeff_pow_char_pow ];
        simp +decide [ Nat.add_div, Nat.mul_div_cancel_left, h, pow_add, pow_mul, Nat.choose_succ_succ, Polynomial.hasseDeriv_coeff ];
        rw [ Nat.add_div ] <;> norm_num [ h, Nat.mul_div_cancel_left, Nat.pow_pos ];
        · split_ifs <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          rw [ mul_pow, Weil.Hasse.natCast_pow_char_pow ];
          rw [ ← Nat.mod_add_div ( Nat.choose ( n / ringChar F ^ j + m ) m ) ( ringChar F ) ] ; simp +decide [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
        · exact pow_pos ( Nat.pos_of_ne_zero ( by have := CharP.char_is_prime F ( ringChar F ) ; aesop ) ) _;
    · rw [ Weil.Hasse.coeff_pow_char_pow ];
      split_ifs <;> simp_all +decide [ Nat.dvd_add_left ];
      rw [ Weil.Hasse.coeff_pow_char_pow ] ; aesop;
  · ext n;
    simp +decide [ Polynomial.hasseDeriv_coeff, coeff_pow_char_pow ];
    intro h_div
    have h_binom : ringChar F ∣ Nat.choose (n + k) k := by
      have h_binom : Nat.choose (n + k) k * k = (n + k) * Nat.choose (n + k - 1) (k - 1) := by
        cases a : n + k <;> cases b : k <;> simp_all +decide [ Nat.add_one_mul_choose_eq ];
      contrapose! h;
      refine' Nat.Coprime.dvd_of_dvd_mul_left _ ( h_binom.symm ▸ dvd_mul_of_dvd_left h_div _ );
      exact Nat.Coprime.pow_left _ ( Nat.Prime.coprime_iff_not_dvd ( by have := CharP.char_is_prime F ( ringChar F ) ; aesop ) |>.2 h );
    exact Or.inl ( by rw [ CharP.cast_eq_zero_iff F ( ringChar F ) ] ; exact h_binom )

/-
A nonzero polynomial vanishing to order `≥ m` on a finite set `S` has `(∏_{a∈S}(X-a))^m ∣ g`;
this is the divisibility powering `card_le_of_rootMultiplicity`.
-/
lemma prod_pow_dvd_of_le_rootMultiplicity (g : F[X]) (S : Finset F) (m : ℕ)
    (hS : ∀ a ∈ S, m ≤ g.rootMultiplicity a) :
    (∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ m ∣ g := by
  convert Finset.prod_dvd_of_coprime _ _;
  rw [ ← Finset.prod_pow ];
  · intro a ha b hb hab; exact IsCoprime.pow ( Polynomial.irreducible_X_sub_C a |> fun h => h.coprime_iff_not_dvd.mpr fun h' => hab <| by simpa [ sub_eq_iff_eq_add ] using Polynomial.dvd_iff_isRoot.mp h' ) ;
  · exact fun a ha => dvd_trans ( pow_dvd_pow _ ( hS a ha ) ) ( Polynomial.pow_rootMultiplicity_dvd _ _ )

end Hasse
end Weil