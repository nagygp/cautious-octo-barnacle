import RequestProject.Foundations.KasamiAxKatzAK3d
import Mathlib

/-!
# Foundations, Layer AK3.3.1 — Frobenius preserves the prime-above-2 valuation

This module formalizes the **next first layer of the open deep core AK3.3** of
`Docs/VanishFutureDirections.md` §8.1: promoting the combinatorial digit-sum
orbit invariance (AK3.3.0, `KasamiAxKatzAK3d.lean`) to a genuine **valuation
invariance** at the level of the Dedekind height-one-prime API.

## The mathematical content

Stickelberger's valuation `v(g(ω^{-s}))` is constant along the Frobenius orbit
`s, 2s, 4s, …` because the Gauss-sum `p`-power law
`g(χ,ψ)^p = g(χ^p, ψ^p)` (`gaussSum_pow_char`, AK3) exhibits `g(ω^{-2s})` as a
Galois conjugate of `g(ω^{-s})`, and **Galois conjugation preserves the `2`-adic
valuation** of the prime above `2`.  AK3.3.0 proved the combinatorial shadow of
this — that the binary digit sum `s₂` is invariant under doubling modulo
`2ⁿ − 1`.  This module supplies the genuine valuation statement underlying it:

> An automorphism `e` of a Dedekind domain that **fixes** a height-one prime
> `𝔭` preserves the `𝔭`-adic valuation: `v_𝔭(e r) = v_𝔭(r)`.

This is exactly "`v(σ z) = v(z)` for `σ ∈ Gal` fixing the prime above `2`", the
upgrade of AK3.3.0 from `Nat` digit sums to the real height-one valuation.  The
proof is purely Dedekind-domain theory: `e` induces a multiplicative bijection on
ideals, so `𝔭ⁿ ∣ (r) ↔ 𝔭ⁿ ∣ (e r)` for every `n` (using `e 𝔭 = 𝔭`), and the
valuation is determined by these divisibilities
(`intValuation_le_pow_iff_dvd`).

## What is established (sorry-free)

* `map_dvd_map_ringEquiv_iff` — a ring automorphism preserves ideal
  divisibility: `Ideal.map e I ∣ Ideal.map e J ↔ I ∣ J`.
* `intValuation_eq_of_ringEquiv_fixes` — **the valuation invariance**: if `e`
  fixes the height-one prime (`Ideal.map e v.asIdeal = v.asIdeal`), then
  `v.intValuation (e r) = v.intValuation r`.
* `intValuation_eq_of_ringEquiv_fixes_iterate` — the **Frobenius-orbit form**:
  `v.intValuation (e^[j] r) = v.intValuation r`, the valuation analogue of
  `binDigitSum_two_pow_mul_mod` (AK3.3.0).

## Scope

This layer is sorry-free.  It is the genuine **valuation Frobenius-invariance**,
rooted entirely in Mathlib's Dedekind-domain / height-one-spectrum API
(`IsDedekindDomain.HeightOneSpectrum`), upgrading the combinatorial AK3.3.0.  The
remaining content of AK3.3 — identifying the Gauss-sum `p`-power law with the
action of this automorphism at the specific prime above `2` in the cyclotomic
field, and then the *value* `v(g(ω^{-s})) = s₂(s)` (Gross–Koblitz / `p`-adic
Gamma) — stays the open deep core, deliberately neither axiomatized nor
`sorry`-ed.

## Sources

Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 14
(Stickelberger's relation; the Galois action on Gauss sums); Washington,
*Introduction to Cyclotomic Fields*, Ch. 6; Neukirch, *Algebraic Number Theory*,
Ch. I (the decomposition group, Frobenius, and valuations of conjugates).
-/

namespace Vanish.Foundations

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-! ## 1. A ring automorphism preserves ideal divisibility -/

/-
**A ring automorphism preserves ideal divisibility.**  For a ring isomorphism
`e : R ≃+* R` and ideals `I J`, `Ideal.map e I ∣ Ideal.map e J ↔ I ∣ J`.  (`map`
is multiplicative and bijective, so it is a divisibility isomorphism on the ideal
monoid.)
-/
theorem map_dvd_map_ringEquiv_iff (e : R ≃+* R) (I J : Ideal R) :
    Ideal.map (e : R →+* R) I ∣ Ideal.map (e : R →+* R) J ↔ I ∣ J := by
  constructor <;> intro h;
  · rw [ Ideal.dvd_iff_le ] at *;
    rw [ Ideal.map_le_iff_le_comap ] at h;
    intro x hx; specialize h hx; simp_all +decide [ Ideal.mem_map_iff_of_surjective, e.surjective ] ;
  · obtain ⟨ K, rfl ⟩ := h;
    simp +decide [ Ideal.map_mul ]

/-! ## 2. A `WithZero (Multiplicative ℤ)` separation lemma -/

/-
Two elements `x, y ≤ 1` of `WithZero (Multiplicative ℤ)` that agree on every
threshold `· ≤ exp(-n)` (`n : ℕ`) are equal.  (The thresholds `exp(-n)` exactly
separate the values `≤ 1`, namely `0` and the `exp(-n)`.)  This is the final step
of the valuation invariance: a valuation value is determined by which prime-power
divisibilities hold.
-/
theorem withZero_eq_of_le_expNeg_iff {x y : WithZero (Multiplicative ℤ)}
    (hx : x ≤ 1) (hy : y ≤ 1)
    (h : ∀ n : ℕ, (x ≤ WithZero.exp (-(n : ℤ))) ↔ (y ≤ WithZero.exp (-(n : ℤ)))) :
    x = y := by
  by_cases hx0 : x = 0;
  · cases y <;> simp_all +decide [ WithZero.exp ];
    rename_i a; specialize h ( Int.toNat ( -a.toAdd ) + 1 ) ; simp_all +decide [ Int.toNat_of_nonneg ] ;
    cases max_cases ( -a.toAdd ) 0 <;> simp_all +decide [ WithZero.coe_le_coe ];
    exact absurd ‹_› ( not_and_of_not_left _ ( not_le_of_gt ( by simpa using hy.lt_of_ne ( by aesop ) ) ) );
  · by_cases hy0 : y = 0;
    · cases x using WithZero.recZeroCoe ; simp_all +decide;
      contrapose! h;
      cases ‹Multiplicative ℤ› using Multiplicative.rec ; simp_all +decide [ WithZero.exp ];
      rename_i k;
      exact ⟨ Int.toNat ( -k ) + 1, by exact_mod_cast ( by linarith [ Int.self_le_toNat ( -k ) ] : ( - ( Int.toNat ( -k ) + 1 ) : ℤ ) < k ) ⟩;
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, x = WithZero.exp a := by
        cases x ; aesop;
        exact ⟨ _, rfl ⟩
      obtain ⟨b, hb⟩ : ∃ b : ℤ, y = WithZero.exp b := by
        cases y ; aesop;
        rename_i k; use k.toAdd; aesop;
      have h_eq : a = b := by
        have h_eq : ∀ n : ℕ, a ≤ -(n : ℤ) ↔ b ≤ -(n : ℤ) := by
          simp_all +decide;
          convert h using 2;
          · rw [ ← WithZero.exp_neg ] ; exact WithZero.exp_le_exp.symm;
          · convert WithZero.exp_le_exp.symm using 1;
        have h_eq : a ≤ -(Int.toNat (-a)) ∧ b ≤ -(Int.toNat (-b)) := by
          grind +suggestions;
        grind
      exact ha.trans (h_eq ▸ hb.symm)

/-! ## 3. The valuation invariance -/

/-
**Frobenius preserves the prime-above-`p` valuation.**  If a ring automorphism
`e` fixes the height-one prime `v` (i.e. `Ideal.map e v.asIdeal = v.asIdeal`),
then it preserves the `v`-adic valuation:

  `v.intValuation (e r) = v.intValuation r`.

This is the valuation upgrade of the AK3.3.0 digit-sum doubling invariance.
-/
theorem intValuation_eq_of_ringEquiv_fixes (v : HeightOneSpectrum R) (e : R ≃+* R)
    (hfix : Ideal.map (e : R →+* R) v.asIdeal = v.asIdeal) (r : R) :
    v.intValuation (e r) = v.intValuation r := by
  apply withZero_eq_of_le_expNeg_iff; exact v.intValuation_le_one (e r); exact v.intValuation_le_one r; intro n;
  rw [ v.intValuation_le_pow_iff_dvd, v.intValuation_le_pow_iff_dvd ];
  convert map_dvd_map_ringEquiv_iff e ( v.asIdeal ^ n ) ( Ideal.span { r } ) using 1;
  rw [ Ideal.map_pow, hfix, Ideal.map_span, Set.image_singleton ];
  rfl

/-! ## 4. The Frobenius-orbit form -/

/--
**Orbit invariance of the valuation.**  Iterating `intValuation_eq_of_ringEquiv_fixes`:
the `v`-adic valuation is constant along the whole orbit `r, e r, e² r, …` of an
automorphism fixing `v`:

  `v.intValuation (e^[j] r) = v.intValuation r`.

This is the valuation analogue of `binDigitSum_two_pow_mul_mod` (AK3.3.0).
-/
theorem intValuation_eq_of_ringEquiv_fixes_iterate (v : HeightOneSpectrum R)
    (e : R ≃+* R) (hfix : Ideal.map (e : R →+* R) v.asIdeal = v.asIdeal) (j : ℕ)
    (r : R) :
    v.intValuation ((e : R → R)^[j] r) = v.intValuation r := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', intValuation_eq_of_ringEquiv_fixes v e hfix,
        ih]

end Vanish.Foundations