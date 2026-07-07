import RequestProject.Foundations.KasamiCrossCorrelationValueSet

/-!
# Foundations, Layer 10 (multiplicity table) — the explicit closed-form table

This module assembles the **green core** of the general-`k` Kasami
cross-correlation *value/multiplicity table*: the explicit closed-form
multiplicities of every value taken by the scaled cross-correlation
`R(s) = autocorrScaled (·^{d k}) s a = ∑_x χ(s·Δf_a x)`.

`KasamiCrossCorrelationValueSet.lean` supplied, sorry-free and *conditional on the
two classical scalar inputs*, both

* the **value set** `R(s) ∈ {q, 0, +2^{(n+1)/2}, -2^{(n+1)/2}}`
  (`kasami_crossCorr_value_set`), and
* the **moment equations** for the two nonzero-value counts
  (`kasami_crossCorr_value_table`).

Here we *solve* those moment equations to give the entire multiplicity table in
closed form.  Writing `q = 2ⁿ` and `A = 2^{(n+1)/2}`, for `n ≥ 3` odd and `a ≠ 0`:

| value `R(s)` | multiplicity |
| --- | --- |
| `q`               | `1`                          (only at `s = 0`) |
| `0`               | `2^{n-1} − 1`                                  |
| `+2^{(n+1)/2}`    | `2^{n-2} − 2^{(n-3)/2}`                        |
| `−2^{(n+1)/2}`    | `2^{n-2} + 2^{(n-3)/2}`                        |

The four multiplicities sum to `2ⁿ = q`, and the signed excess of the two
nonzero-magnitude values is `−2^{(n-1)/2}` — the classical Kasami/almost-bent
cross-correlation distribution (Kasami 1971; Canteaut–Charpin–Dobbertin).

## The bridge value

Everything in this module is **green (sorry-free)**, taking the two classical
scalar inputs as explicit hypotheses:

* **(A) weight divisibility** — `2^{(n+1)/2} ∣ R(s)` for every `s` (`hdiv`);
* **(B) the fourth moment** — `∑_{s≠0} R(s)⁴ = 2·q³` (`hfourth`).

Input **(B)** is the *fourth-moment / weight-divisibility "bridge" value*: the
single deep almost-bent datum (Chabaud–Vaudenay; Carlet Ch. 6) that the whole
value/multiplicity table rests on.  It is isolated exactly (its canonical
one-point-count form is `kasami_a1_preCount4` in `KasamiFourthMomentCanonical.lean`),
so this module is the green core *around* that bridge.

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM 2000); MacWilliams–Sloane (Pless
power moments); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

variable {n k : ℕ}

/-! ## The two nonzero-magnitude multiplicities (solving the moment equations) -/

/-
**Multiplicity of the value `+2^{(n+1)/2}`.**  Solving the two moment
equations `kasami_crossCorr_value_table` (signed excess `−q/A`, total `q²/A²`)
gives `#{R = +2^{(n+1)/2}} = 2^{n-2} − 2^{(n-3)/2}`.
-/
theorem kasami_crossCorr_card_pos
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn3 : 3 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2))).card
      = 2 ^ (n - 2) - 2 ^ ((n - 3) / 2) := by
  obtain ⟨ m, rfl ⟩ : ∃ m, n = 2 * m + 1 := hnodd;
  have := Vanish.Foundations.kasami_crossCorr_value_table hcard hk hkn hcop ( by simp ) ( by linarith ) a ha hdiv hfourth; simp_all +decide [ Nat.add_div ] ;
  rcases m with ( _ | m ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
  exact eq_tsub_of_add_eq ( by nlinarith [ pow_pos ( zero_lt_two' ℤ ) m, pow_mul' 2 2 m ] )

/-
**Multiplicity of the value `−2^{(n+1)/2}`.**  Solving the two moment
equations gives `#{R = −2^{(n+1)/2}} = 2^{n-2} + 2^{(n-3)/2}`.
-/
theorem kasami_crossCorr_card_neg
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn3 : 3 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2))).card
      = 2 ^ (n - 2) + 2 ^ ((n - 3) / 2) := by
  obtain ⟨ m, rfl ⟩ := hnodd;
  have := Vanish.Foundations.kasami_crossCorr_value_table hcard hk hkn hcop ( by simp +decide ) ( by linarith ) a ha hdiv hfourth;
  norm_num [ Nat.add_div ] at *;
  rcases m with ( _ | m ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
  norm_num [ pow_add, pow_mul' ] at *;
  exact_mod_cast ( by nlinarith [ pow_pos ( zero_lt_two' ℤ ) m ] : ( Finset.card ( Finset.filter ( fun s => autocorrScaled ( fun x => x ^ d k ) s a = - ( 2 * ( 2 * 2 ^ m ) ) ) Finset.univ ) : ℤ ) = 2 * ( 2 ^ m ) ^ 2 + 2 ^ m )

/-! ## The trivial-frequency and zero multiplicities -/

/-
**Multiplicity of the value `q`.**  `R(0) = q` (`autocorrScaled_zero`), and for
`s ≠ 0` the value set gives `R(s) ∈ {0, ±2^{(n+1)/2}}`, none of which equals
`q = 2ⁿ` for `n ≥ 3` (since `q > 2^{(n+1)/2} > 0`).  Hence `#{R = q} = 1`.
-/
theorem kasami_crossCorr_card_q
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn3 : 3 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = (Fintype.card F : ℤ))).card = 1 := by
  have h_n_gt_two_pow : (2 : ℤ) ^ ((n + 1) / 2) < (Fintype.card F : ℤ) := by
    exact_mod_cast hcard.symm ▸ pow_lt_pow_right₀ ( by decide ) ( Nat.div_lt_of_lt_mul <| by linarith );
  rw [ Finset.card_eq_one ];
  use 0; ext s; simp;
  constructor <;> intro hs;
  · contrapose! hs;
    have := Vanish.Foundations.crossCorr_three_valued_of_div_fourth hcard hnodd ( fun x => x ^ d k ) ( KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd ( by linarith ) ) a ha hdiv hfourth s hs;
    rcases this with ( h | h | h ) <;> linarith [ pow_pos ( zero_lt_two' ℤ ) ( ( n + 1 ) / 2 ) ];
  · rw [ hs, MTuple.autocorrScaled_zero ]

/-
**Multiplicity of the value `0`.**  The four value-classes partition `F`
(`kasami_crossCorr_value_set`), so their cards sum to `q = 2ⁿ`.  With
`#{R = q} = 1` and `#{R = A} + #{R = -A} = 2^{n-1}` (the total-count moment
equation), `#{R = 0} = 2ⁿ − 1 − 2^{n-1} = 2^{n-1} − 1`.
-/
theorem kasami_crossCorr_card_zero
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn3 : 3 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = 0)).card = 2 ^ (n - 1) - 1 := by
  have h_card : Fintype.card F = 1 + (2 ^ (n - 2) - 2 ^ ((n - 3) / 2)) + (2 ^ (n - 2) + 2 ^ ((n - 3) / 2)) + (Finset.univ.filter (fun s : F => autocorrScaled (fun x => x ^ d k) s a = 0)).card := by
    have h_card : (Finset.univ.filter (fun s : F => autocorrScaled (fun x => x ^ d k) s a = 0)).card + (Finset.univ.filter (fun s : F => autocorrScaled (fun x => x ^ d k) s a = (Fintype.card F : ℤ))).card + (Finset.univ.filter (fun s : F => autocorrScaled (fun x => x ^ d k) s a = 2 ^ ((n + 1) / 2))).card + (Finset.univ.filter (fun s : F => autocorrScaled (fun x => x ^ d k) s a = -2 ^ ((n + 1) / 2))).card = Fintype.card F := by
      rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
      · convert Finset.card_univ;
        grind +suggestions;
      · simp +contextual [ Finset.disjoint_left ];
        rintro s ( hs | hs | hs ) <;> linarith [ pow_pos ( zero_lt_two' ℤ ) ( ( n + 1 ) / 2 ), show ( Fintype.card F : ℤ ) > 0 by exact_mod_cast hcard.symm ▸ pow_pos ( zero_lt_two' ℕ ) _ ];
      · simp +contextual [ Finset.disjoint_left ];
        rintro s ( hs | hs ) <;> simp_all +decide [ pow_succ' ];
        · positivity;
        · omega;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith [ show ( Fintype.card F : ℤ ) > 0 from Nat.cast_pos.mpr ( Fintype.card_pos ) ] ;
    linarith [ Vanish.Foundations.kasami_crossCorr_card_q hcard hk hkn hcop hnodd hn3 a ha hdiv hfourth, Vanish.Foundations.kasami_crossCorr_card_pos hcard hk hkn hcop hnodd hn3 a ha hdiv hfourth, Vanish.Foundations.kasami_crossCorr_card_neg hcard hk hkn hcop hnodd hn3 a ha hdiv hfourth ];
  rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ Nat.pow_succ' ] at *;
  exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show 2 * 2 ^ n ≥ 2 ^ ( n / 2 ) from le_trans ( pow_le_pow_right₀ ( by decide ) ( Nat.div_le_self _ _ ) ) ( by linarith [ pow_pos ( by decide : 0 < 2 ) n ] ) ) ] )

/-! ## The full closed-form multiplicity table -/

/-- **The general-`k` Kasami cross-correlation multiplicity table.**  For the
Kasami map `x ↦ x^{d k}` over `GF(2ⁿ)` (`n ≥ 3` odd, `1 ≤ k < n`, `gcd(k,n)=1`)
and any shift `a ≠ 0`, given the two classical scalar inputs **(A)** divisibility
and **(B)** the fourth moment, the scaled cross-correlation takes:

* the value `q = 2ⁿ` exactly once (at `s = 0`);
* the value `0` on `2^{n-1} − 1` frequencies;
* the value `+2^{(n+1)/2}` on `2^{n-2} − 2^{(n-3)/2}` frequencies;
* the value `−2^{(n+1)/2}` on `2^{n-2} + 2^{(n-3)/2}` frequencies.

This is the complete classical Kasami/almost-bent cross-correlation distribution,
established green modulo the two named scalar inputs. -/
theorem kasami_crossCorr_multiplicity_table
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn3 : 3 ≤ n)
    (a : F) (ha : a ≠ 0)
    (hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
        ∣ autocorrScaled (fun x : F => x ^ d k) s a)
    (hfourth : ∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :
    (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = (Fintype.card F : ℤ))).card = 1
    ∧ (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = 0)).card = 2 ^ (n - 1) - 1
    ∧ (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2))).card
        = 2 ^ (n - 2) - 2 ^ ((n - 3) / 2)
    ∧ (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2))).card
        = 2 ^ (n - 2) + 2 ^ ((n - 3) / 2) :=
  ⟨kasami_crossCorr_card_q hcard hk hkn hcop hnodd hn3 a ha hdiv hfourth,
   kasami_crossCorr_card_zero hcard hk hkn hcop hnodd hn3 a ha hdiv hfourth,
   kasami_crossCorr_card_pos hcard hk hkn hcop hnodd hn3 a ha hdiv hfourth,
   kasami_crossCorr_card_neg hcard hk hkn hcop hnodd hn3 a ha hdiv hfourth⟩

end Vanish.Foundations