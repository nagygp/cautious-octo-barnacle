import RequestProject.Foundations.KasamiCrossCorrelationTable

/-!
# Foundations, Layer 10 (value set) — the actual Kasami cross-correlation values

This module supplies **Layer 10's open input** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`): the *value set* of the scaled
cross-correlation
`R(s) = autocorrScaled f s a = ∑_x χ(s·Δf_a x)` of the Kasami map
`f = (·^{d k})`.  Layer 9 supplied the structural 2-to-1 reduction and the first
two power moments; Layer 10's table (`KasamiCrossCorrelationTable.lean`) supplied
the Pless/MacWilliams *solve* (multiplicities **from** a value set) and the fourth
power moment.  What was missing — and is filled in here — is the *actual set of
values* `R(s)` takes.

## The value set (from a computation over `GF(2ⁿ)`, `n` odd, `gcd(k,n)=1`)

```
R(0) = q = 2ⁿ ,   and for s ≠ 0 :   R(s) ∈ { 0, +2^{(n+1)/2}, -2^{(n+1)/2} } .
```

That is, off the trivial frequency the cross-correlation is **three-valued** with
`A = 2^{(n+1)/2}` — exactly the magnitude of the AB Walsh spectrum (Layer 5).
This is *not* a generic APN/AB phenomenon: for the quadratic Gold/cube maps
(`k = 1`) the derivative is `F₂`-affine and `R` collapses to the two-point set
`{0, ±q}` (`cube_crossCorr_three_valued`); the genuinely non-quadratic Kasami maps
(`k ≥ 2`) are what realize the spread-out three-valued spectrum.

## How the values are pinned down (the classical weight-divisibility computation)

The value set is reduced here to **two classical scalar inputs**, exactly the
Kasami-1971 / Canteaut–Charpin–Dobbertin weight-divisibility data named in the
roadmap, fed through the *same* integer-lattice argument that already deduces the
AB Walsh spectrum from its moments (`WalshAB.ab_from_moments`,
`WalshAB.eq_zero_or_one_of_sum_sq_eq_sum_fourth`):

* **(A) weight divisibility** — `2^{(n+1)/2} ∣ R(s)` for every `s`
  (`hdiv`).  This is the Kasami/CCD divisibility of the cross-correlation
  (equivalently of the dual Kasami/BCH code weights).
* **(B) the fourth moment** — `∑_{s≠0} R(s)⁴ = 2·q³`
  (`hfourth`), equivalently the derivative 4-collision count
  `#{x : Fin 4 → F | ∑ᵢ Δf_a(xᵢ) = 0} = q³ + 2q²`.

Writing `R(s) = 2^{(n+1)/2}·t(s)` (from (A)), the unconditional second moment
`∑_{s≠0} R(s)² = q²` (`crossCorr_second_moment_nonzero`, Layer 9) and (B) give
`∑_{s≠0} t(s)² = ∑_{s≠0} t(s)⁴ = 2^{n-1}`, whence `t(s)² ∈ {0,1}` and therefore
`R(s) ∈ {0, ±2^{(n+1)/2}}`.  The trivial frequency is `R(0) = q`
(`autocorrScaled_zero`).

Feeding the resulting value set to the Pless solve of the table module pins the
multiplicities: among the `q-1` nonzero frequencies, `R = ±A` occurs `q/2` times
with signed excess `#{R=A} − #{R=-A} = −2^{(n-1)/2}` (`crossCorr_value_table`).

Stating (A)/(B) as hypotheses isolates the remaining deep transcription to those
two scalar facts (a single divisibility and a single moment), rather than the
whole value set; everything downstream — the value set, the multiplicity table —
is derived here and is sorry-free.

## Sources

Kasami, *The weight enumerators for several classes of subcodes of the 2nd order
binary Reed–Muller codes* (Inform. Control, 1971); Canteaut–Charpin–Dobbertin,
*Weight divisibility of cyclic codes, …* (SIAM J. Discrete Math., 2000);
MacWilliams–Sloane (the Pless power moments); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The reduction: divisibility + fourth moment ⇒ three-valued (off `0`) -/

/-
**Three-valued cross-correlation from divisibility and the fourth moment.**  For
an APN `f` over `GF(2ⁿ)` (`n` odd) and `a ≠ 0`, if every cross-correlation value
is divisible by `2^{(n+1)/2}` (input **(A)**) and the nonzero-frequency fourth
moment is `2·q³` (input **(B)**), then off the trivial frequency the
cross-correlation is **three-valued**:
`R(s) ∈ {0, +2^{(n+1)/2}, -2^{(n+1)/2}}` for `s ≠ 0`.

This is the integer-lattice argument of `WalshAB.ab_from_moments`, applied to the
cross-correlation: write `R(s) = 2^{(n+1)/2}·t(s)`; then the unconditional second
moment `∑_{s≠0} R² = q²` (`crossCorr_second_moment_nonzero`) and **(B)** give
`∑_{s≠0} t² = ∑_{s≠0} t⁴ = 2^{n-1}`, so `t(s)² ∈ {0,1}`.
-/
theorem crossCorr_three_valued_of_div_fourth {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (f : F → F) (hf : WalshAB.IsAPN f) (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled f s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3)
    (s : F) (hs : s ≠ 0) :
    autocorrScaled f s a = 0
    ∨ autocorrScaled f s a = 2 ^ ((n + 1) / 2)
    ∨ autocorrScaled f s a = -2 ^ ((n + 1) / 2) := by
  -- Set exponent e = (n+1)/2 and rewrite cross-correlation as R(s) = 2^e * t(s).
  set e := (n + 1) / 2 with he
  have heq : ∀ s, ∃ t : ℤ, autocorrScaled f s a = 2 ^ e * t := by
    exact hdiv;
  choose t ht using heq;
  -- By `WalshAB.eq_zero_or_one_of_sum_sq_eq_sum_fourth`, it suffices to show `∑ s ∈ E, t s ^ 4 = ∑ s ∈ E, t s ^ 2`.
  have hsum_eq : ∑ s ∈ univ.erase 0, t s ^ 4 = ∑ s ∈ univ.erase 0, t s ^ 2 := by
    -- By `crossCorr_second_moment_nonzero`, `∑ s ∈ E, (autocorrScaled f s a)^2 = (Fintype.card F)^2`.
    have hsum_sq : ∑ s ∈ univ.erase 0, (autocorrScaled f s a) ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
      convert Vanish.Foundations.crossCorr_second_moment_nonzero f hf a ha using 1;
    simp_all +decide [ mul_pow, Finset.mul_sum _ _ _ ];
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ];
    · exact absurd hodd ( by simp +decide [ parity_simps ] );
    · exact mul_left_cancel₀ ( pow_ne_zero ( 4 * k + 4 ) two_ne_zero ) ( by linear_combination' hfourth - hsum_sq * 2 ^ ( 2 * k + 2 ) );
  have := WalshAB.eq_zero_or_one_of_sum_sq_eq_sum_fourth ( Finset.univ.erase ( 0 : F ) ) t hsum_eq s ( Finset.mem_erase_of_ne_of_mem hs ( Finset.mem_univ s ) );
  aesop

/-- **The Kasami cross-correlation value set.**  For the Kasami map
`f = (·^{d k})` over `GF(2ⁿ)` (`n` odd, `1 ≤ k < n`, `gcd(k,n)=1`) and `a ≠ 0`,
given the two classical scalar inputs **(A)** divisibility and **(B)** the fourth
moment, every cross-correlation value lies in the four-element set
`{q, 0, +2^{(n+1)/2}, -2^{(n+1)/2}}`, with the trivial frequency `R(0) = q` the
only occurrence of `q`. -/
theorem kasami_crossCorr_value_set {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3)
    (s : F) :
    autocorrScaled (fun x : F => x ^ d k) s a = (Fintype.card F : ℤ)
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = 0
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2)
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2) := by
  by_cases hs : s = 0
  · subst hs
    left; exact MTuple.autocorrScaled_zero _ a
  · rcases crossCorr_three_valued_of_div_fourth hcard hnodd _
      (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha hdiv hfourth s hs with
      h | h | h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; exact h

/-! ## The multiplicity table (Pless solve) over the nonzero frequencies -/

/-
**The closed-form Kasami cross-correlation table.**  With the value set in hand,
the Pless solve (`threeValued_moment_eqs`) fed the unconditional first and second
moments over the nonzero frequencies (`crossCorr_first_moment_nonzero`,
`crossCorr_second_moment_nonzero`, Layer 9) pins the multiplicities of the two
nonzero values `±A` (`A = 2^{(n+1)/2}`): the signed excess is `-q/A` and the
total support is `q²/A²`.
-/
theorem kasami_crossCorr_value_table {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (2 : ℤ) ^ ((n + 1) / 2)
        * (((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2))).card : ℤ)
          - ((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2))).card : ℤ))
        = -(Fintype.card F : ℤ)
    ∧ ((2 : ℤ) ^ ((n + 1) / 2)) ^ 2
        * (((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2))).card : ℤ)
          + ((univ.filter (fun s : F =>
              autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2))).card : ℤ))
        = (Fintype.card F : ℤ) ^ 2 := by
  have := @Vanish.Foundations.threeValued_moment_eqs;
  convert this ( fun s => if s = 0 then 0 else autocorrScaled ( fun x => x ^ d k ) s a ) ( 2 ^ ( ( n + 1 ) / 2 ) ) ( by positivity ) _ using 1;
  · simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ];
    rw [ show ( Finset.univ.filter fun s => autocorrScaled ( fun x => x ^ d k ) s a = 2 ^ ( ( n + 1 ) / 2 ) ) = Finset.univ.filter fun s => ( if s = 0 then 0 else autocorrScaled ( fun x => x ^ d k ) s a ) = 2 ^ ( ( n + 1 ) / 2 ) from ?_, show ( Finset.univ.filter fun s => autocorrScaled ( fun x => x ^ d k ) s a = -2 ^ ( ( n + 1 ) / 2 ) ) = Finset.univ.filter fun s => ( if s = 0 then 0 else autocorrScaled ( fun x => x ^ d k ) s a ) = -2 ^ ( ( n + 1 ) / 2 ) from ?_ ];
    · rw [ show ∑ x : F, autocorrScaled ( fun x => x ^ d k ) x a = 0 from ?_ ];
      · rw [ MTuple.autocorrScaled_zero ] ; aesop;
      · convert Vanish.Foundations.kasami_crossCorr_first_moment hcard hk hcop hnodd hn a ha using 1;
    · ext s; by_cases hs : s = 0 <;> simp +decide [ hs ] ;
      rw [ MTuple.autocorrScaled_zero ];
      linarith [ pow_pos ( zero_lt_two' ℤ ) ( ( n + 1 ) / 2 ) ];
    · ext s; by_cases hs : s = 0 <;> simp +decide [ hs ] ;
      rw [ MTuple.autocorrScaled_zero ];
      norm_cast ; simp +decide [ hcard ];
      exact iff_of_false ( by omega ) ( by positivity );
  · convert Iff.rfl using 2;
    · congr! 2;
      · congr! 2;
        ext s; by_cases hs : s = 0 <;> simp +decide [ hs ] ;
        rw [ MTuple.autocorrScaled_zero ];
        norm_cast ; simp +decide [ hcard ];
        exact iff_of_false ( by positivity ) ( by omega );
      · congr! 2;
        ext s; by_cases hs : s = 0 <;> simp +decide [ hs ] ;
        rw [ MTuple.autocorrScaled_zero ];
        linarith [ pow_pos ( zero_lt_two' ℤ ) ( ( n + 1 ) / 2 ) ];
    · convert Vanish.Foundations.crossCorr_second_moment_nonzero ( fun x => x ^ d k ) ( KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn ) a ha using 1;
      simp +decide [ Finset.sum_ite, Finset.filter_ne' ];
  · intro s; by_cases hs : s = 0 <;> simp +decide [ hs ] ;
    have := Vanish.Foundations.crossCorr_three_valued_of_div_fourth hcard hnodd ( fun x => x ^ d k ) ( KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn ) a ha hdiv hfourth s hs; aesop;

end Vanish.Foundations