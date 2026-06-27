import ConjecturesMTupleTripleCount.Foundations.WalshTransform
import ConjecturesMTupleTripleCount.Foundations.ValueDistribution

/-!
# Foundations, Layer 5 — the three-valued spectrum of an AB function

This module realizes **Layer 5** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`): for an **almost bent (AB)** function `f` over
`GF(2ⁿ)` with `n` odd, the Walsh spectrum `b ↦ walsh f a b` (at a fixed nonzero
`a`) is **three-valued**, taking values in `{0, ±2^{(n+1)/2}}`, with a
*controlled distribution* read off from the first two moments.

It is the bridge from the project's already-proved `Kasami.Headlines.kasami_is_ab`
(`IsAB`) to a usable, explicitly distributed spectrum — the input Layer 6 needs.

## Results

* `walsh_three_valued` — from `IsAB`, `walsh f a b ∈ {0, 2^{(n+1)/2}, -2^{(n+1)/2}}`.
* `walsh_first_moment` — `∑_b walsh f a b = |F|` for a permutation fixing `0`.
* `walshSign` — the extracted `{-1, 0, 1}` sign function with
  `walsh f a b = 2^{(n+1)/2} · walshSign n f a b`.
* `walsh_zero_count` — `#{b : walsh f a b = 0} = 2^{n-1}`.
* `walsh_support_count` — `#{b : W = 2^{(n+1)/2}} + #{b : W = -2^{(n+1)/2}} = 2^{n-1}`.
* `walsh_signed_count` — `#{b : W = 2^{(n+1)/2}} − #{b : W = -2^{(n+1)/2}} = 2^{(n-1)/2}`.

The last two pin down the full distribution: `#{+} = 2^{n-2} + 2^{(n-3)/2}`,
`#{-} = 2^{n-2} − 2^{(n-3)/2}`, `#{0} = 2^{n-1}` (the classical AB cross-correlation
distribution).

## Sources

Chabaud–Vaudenay §3 (the moment method: `∑ W² = q²`, `∑ W⁴ = 2q³`); Carlet Ch. 6;
Canteaut–Charpin–Dobbertin (SIAM 2000).

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): the genuinely reusable, crypto-free
facts (three-valued-from-square, sign-distribution from moments) are factored into
`ValueDistribution.lean` and *reused* here (DRY); this file only supplies the AB
specialization and the single-responsibility bridge lemmas.
-/

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The three-valued spectrum -/

omit [DecidableEq F] in
/-- **Three-valued Walsh spectrum of an AB function.**  If `f` is AB on `GF(2ⁿ)`
with `n` odd, then for every nonzero `a` and every `b`,
`walsh f a b ∈ {0, 2^{(n+1)/2}, -2^{(n+1)/2}}`.  This is the elementary
consequence of `IsAB` (`W² ∈ {0, 2^{n+1}}`) together with
`2^{n+1} = (2^{(n+1)/2})²` for `n` odd, via the pearl
`eq_zero_or_eq_or_eq_neg_of_sq_eq_zero_or_sq`. -/
theorem walsh_three_valued {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    {f : F → F} (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) (b : F) :
    walsh f a b = 0 ∨ walsh f a b = 2 ^ ((n + 1) / 2)
      ∨ walsh f a b = -2 ^ ((n + 1) / 2) := by
  have hpow : (2 : ℤ) ^ (n + 1) = (2 ^ ((n + 1) / 2)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    obtain ⟨m, rfl⟩ := hodd
    omega
  have h := hAB a ha b
  rw [hpow] at h
  exact eq_zero_or_eq_or_eq_neg_of_sq_eq_zero_or_sq h

/-! ## The first moment -/

/-
**First moment of the Walsh spectrum.**  For a permutation `f` fixing `0`,
`∑_b walsh f a b = |F|` for every `a`.  (Swapping the order of summation, the
inner sum `∑_b χ(b·f x)` vanishes unless `f x = 0`, i.e. `x = 0`, where it is
`|F|` and `χ(a·0) = 1`.)
-/
theorem walsh_first_moment (f : F → F) (hf : Function.Bijective f) (hf0 : f 0 = 0)
    (a : F) :
    ∑ b : F, walsh f a b = (Fintype.card F : ℤ) := by
  -- Use the fact that `χ` is a multiplicative character to split the sum.
  have h_split : ∑ b : F, walsh f a b = ∑ x : F, WalshAB.χ (a * x) * ∑ b : F, WalshAB.χ (b * f x) := by
    unfold walsh;
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; rw [ ← WalshAB.χ_mul ] ;
  rw [ h_split, Finset.sum_eq_single 0 ];
  · simp +decide [ hf0, WalshAB.χ_zero ];
  · intro b _ hb; rw [ WalshAB.χ_sum_dual ] ; simp +decide;
    exact fun h => False.elim ( hb ( hf.injective ( h.trans hf0.symm ) ) );
  · exact fun h => False.elim ( h ( Finset.mem_univ 0 ) )

/-! ## The extracted sign function and its distribution -/

/-- The `{-1, 0, 1}` **sign function** of the AB Walsh spectrum: `1`, `-1`, `0`
according to whether `walsh f a b` equals `2^{(n+1)/2}`, `-2^{(n+1)/2}`, or `0`. -/
noncomputable def walshSign (n : ℕ) (f : F → F) (a b : F) : ℤ :=
  if walsh f a b = 2 ^ ((n + 1) / 2) then 1
  else if walsh f a b = -2 ^ ((n + 1) / 2) then -1 else 0

omit [DecidableEq F] in
/-- The sign function takes only the values `-1, 0, 1`. -/
theorem walshSign_mem (n : ℕ) (f : F → F) (a b : F) :
    walshSign n f a b = -1 ∨ walshSign n f a b = 0 ∨ walshSign n f a b = 1 := by
  unfold walshSign
  split_ifs <;> simp

omit [DecidableEq F] in
/-- The defining relation `walsh = 2^{(n+1)/2} · walshSign`, valid on the
three-valued AB spectrum. -/
theorem walsh_eq_walshSign {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    {f : F → F} (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) (b : F) :
    walsh f a b = 2 ^ ((n + 1) / 2) * walshSign n f a b := by
  have h2 : (2 : ℤ) ^ ((n + 1) / 2) ≠ 0 := by positivity
  rcases walsh_three_valued hcard hodd hAB a ha b with h0 | hp | hm <;>
    unfold walshSign <;> simp_all

omit [DecidableEq F] in
/-- `#{b : walshSign = 1} = #{b : walsh f a b = 2^{(n+1)/2}}`. -/
theorem posCard_walshSign (n : ℕ) (f : F → F) (a : F) :
    posCard (walshSign n f a)
      = (univ.filter (fun b : F => walsh f a b = 2 ^ ((n + 1) / 2))).card := by
  refine' congr_arg Finset.card ( Finset.filter_congr fun b _ => _ );
  unfold walshSign; split_ifs <;> simp_all +decide ;

omit [DecidableEq F] in
/-- `#{b : walshSign = -1} = #{b : walsh f a b = -2^{(n+1)/2}}`. -/
theorem negCard_walshSign (n : ℕ) (f : F → F) (a : F) :
    negCard (walshSign n f a)
      = (univ.filter (fun b : F => walsh f a b = -2 ^ ((n + 1) / 2))).card := by
  unfold negCard walshSign;
  congr with x ; split_ifs <;> simp_all +decide;
  rw [ eq_neg_iff_add_eq_zero ] ; norm_cast ; norm_num

omit [DecidableEq F] in
/-- `#{b : walshSign = 0} = #{b : walsh f a b = 0}` (on the three-valued AB
spectrum). -/
theorem zeroCard_walshSign {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    {f : F → F} (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) :
    zeroCard (walshSign n f a)
      = (univ.filter (fun b : F => walsh f a b = 0)).card := by
  refine' congr_arg Finset.card ( Finset.ext fun x => _ );
  simp +decide [ walshSign ];
  split_ifs <;> simp_all +decide [ ne_of_gt ];
  have := walsh_three_valued hcard hodd hAB a ha x; aesop;

/-
**Support count.**  For an AB permutation on `GF(2ⁿ)` (`n ≥ 1` odd), the
number of nonzero Walsh values at a fixed nonzero `a` is `2^{n-1}`:
`#{W = 2^{(n+1)/2}} + #{W = -2^{(n+1)/2}} = 2^{n-1}`.  (From Parseval
`∑ W² = q²` and the three-valued spectrum.)
-/
theorem walsh_support_count {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (hn : 1 ≤ n) {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f)
    (a : F) (ha : a ≠ 0) :
    ((univ.filter (fun b : F => walsh f a b = 2 ^ ((n + 1) / 2))).card : ℤ)
      + ((univ.filter (fun b : F => walsh f a b = -2 ^ ((n + 1) / 2))).card : ℤ)
      = 2 ^ (n - 1) := by
  have h_sum_sq : ∑ b : F, (walsh f a b : ℤ) ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
    convert Vanish.Foundations.walsh_sq_sum_via_foundation f hf a using 1;
  -- By definition of $walshSign$, we know that $(walsh f a b)^2 = 2^{n+1} * (walshSign n f a b)^2$.
  have h_walsh_sq : ∀ b : F, (walsh f a b : ℤ) ^ 2 = 2 ^ (n + 1) * (walshSign n f a b : ℤ) ^ 2 := by
    intro b
    rw [walsh_eq_walshSign hcard hodd hAB a ha b, mul_pow, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.mp (by simpa [parity_simps] using hodd))]
  -- By definition of $walshSign$, we know that $\sum_{b} (walshSign n f a b)^2 = posCard (walshSign n f a) + negCard (walshSign n f a)$.
  have h_sum_walshSign_sq : ∑ b : F, (walshSign n f a b : ℤ) ^ 2 = (posCard (walshSign n f a) : ℤ) + (negCard (walshSign n f a) : ℤ) := by
    convert Vanish.Foundations.sum_sq_eq_posCard_add_negCard ( fun b => walshSign n f a b ) ( fun b => Vanish.Foundations.walshSign_mem n f a b ) using 1;
  simp_all +decide [ ← Finset.mul_sum _ _ _ ];
  convert congr_arg ( fun x : ℤ => x / 2 ^ ( n + 1 ) ) h_sum_sq using 1;
  · rw [ Int.mul_ediv_cancel_left _ ( by positivity ) ];
    rw [ Vanish.Foundations.posCard_walshSign, Vanish.Foundations.negCard_walshSign ];
  · exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by cases n <;> simp_all +decide [ pow_succ' ] ; ring ) )

/-
**Zero count.**  For an AB permutation on `GF(2ⁿ)` (`n ≥ 1` odd), the number
of vanishing Walsh values at a fixed nonzero `a` is `2^{n-1}`.
-/
theorem walsh_zero_count {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (hn : 1 ≤ n) {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f)
    (a : F) (ha : a ≠ 0) :
    ((univ.filter (fun b : F => walsh f a b = 0)).card : ℤ) = 2 ^ (n - 1) := by
  have := @Vanish.Foundations.walsh_support_count F;
  specialize @this ( inferInstance ) ( inferInstance ) ( inferInstance ) ( inferInstance ) n hcard hodd hn f hf hAB a ha;
  have h_card : (Finset.card (Finset.filter (fun b => walsh f a b = 2 ^ ((n + 1) / 2)) Finset.univ)) + (Finset.card (Finset.filter (fun b => walsh f a b = -2 ^ ((n + 1) / 2)) Finset.univ)) + (Finset.card (Finset.filter (fun b => walsh f a b = 0) Finset.univ)) = 2 ^ n := by
    rw [ ← hcard, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
    · convert Finset.card_univ;
      ext b; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_univ, iff_true];
      have := walsh_three_valued hcard hodd hAB a ha b; tauto;
    · simp +contextual [ Finset.disjoint_left ];
      rintro b ( hb | hb ) <;> linarith [ pow_pos ( zero_lt_two' ℤ ) ( ( n + 1 ) / 2 ) ];
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith [ pow_pos ( zero_lt_two' ℤ ) ( ( n + 1 ) / 2 ) ] ;
  cases n <;> simp_all +decide [ pow_succ' ] ; linarith

/-
**Signed count.**  For an AB permutation fixing `0` on `GF(2ⁿ)` (`n ≥ 1`
odd), the signed difference of nonzero Walsh values at a fixed nonzero `a` is
`2^{(n-1)/2}`: `#{W = 2^{(n+1)/2}} − #{W = -2^{(n+1)/2}} = 2^{(n-1)/2}`.  (From
the first moment `∑ W = q` and the three-valued spectrum.)
-/
theorem walsh_signed_count {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    {f : F → F} (hf : Function.Bijective f) (hf0 : f 0 = 0)
    (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) :
    ((univ.filter (fun b : F => walsh f a b = 2 ^ ((n + 1) / 2))).card : ℤ)
      - ((univ.filter (fun b : F => walsh f a b = -2 ^ ((n + 1) / 2))).card : ℤ)
      = 2 ^ ((n - 1) / 2) := by
  convert congr_arg ( fun x : ℤ => x / 2 ^ ( ( n + 1 ) / 2 ) ) ( Vanish.Foundations.walsh_first_moment f hf hf0 a ) using 1;
  · rw [ Int.ediv_eq_of_eq_mul_left ];
    · positivity;
    · convert congr_arg ( fun x : ℤ => x * 2 ^ ( ( n + 1 ) / 2 ) ) ( Vanish.Foundations.sum_eq_posCard_sub_negCard ( fun b => Vanish.Foundations.walshSign n f a b ) ( fun b => ?_ ) ) using 1;
      · rw [ Finset.sum_mul _ _ _ ];
        exact Finset.sum_congr rfl fun x _ => by rw [ Vanish.Foundations.walsh_eq_walshSign hcard hodd hAB a ha x ] ; ring;
      · rw [ Vanish.Foundations.posCard_walshSign, Vanish.Foundations.negCard_walshSign ];
      · grind +suggestions;
  · cases hodd ; simp_all +decide [ Nat.add_div ];
    exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by ring ) )

end Vanish.Foundations