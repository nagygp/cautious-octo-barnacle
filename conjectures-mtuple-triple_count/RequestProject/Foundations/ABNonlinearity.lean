import RequestProject.Foundations.ABSpectrum

/-!
# Foundations — general almost-bent theory: optimal linearity / nonlinearity

This module records the second defining feature of almost-bent functions (beyond
being APN, cf. `ABImpliesAPN.lean`): they achieve the **optimal linearity /
nonlinearity** bound for `n` odd.

For a function `f` on `GF(2ⁿ)` the *linearity* at a nonzero frequency `a` is
`max_b |W(a,b)|`; the *nonlinearity* is `2^{n-1} − ½·max_{a≠0,b}|W(a,b)|`.  For
`n` odd the minimum possible linearity over all functions is `2^{(n+1)/2}`
(Sidelnikov–Chabaud–Vaudenay), attained exactly by the almost-bent functions.
This module supplies the two spectral facts that together *pin the linearity to
that optimum* for an AB permutation:

* `walsh_abs_le_of_ab` — the upper bound `|W(a,b)| ≤ 2^{(n+1)/2}` for every
  `a ≠ 0` and `b` (from the three-valued spectrum);
* `walsh_extreme_attained` — the extreme value `2^{(n+1)/2}` is *attained*
  (for an AB permutation fixing `0`), from the signed count
  `#{W = +} − #{W = −} = 2^{(n-1)/2} ≥ 1`.

Hence `max_b |W(a,b)| = 2^{(n+1)/2}` for an AB permutation fixing `0`, i.e. the
nonlinearity is exactly `2^{n-1} − 2^{(n-1)/2}` — the optimal value.

## Sources

Chabaud–Vaudenay §3; Carlet Ch. 6; Canteaut–Charpin–Dobbertin (SIAM 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open WalshAB Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**Linearity upper bound.**  For an AB function on `GF(2ⁿ)` (`n` odd), every
Walsh coefficient at a nonzero frequency has absolute value `≤ 2^{(n+1)/2}`.
-/
omit [DecidableEq F] in
theorem walsh_abs_le_of_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    {f : F → F} (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) (b : F) :
    |walsh f a b| ≤ 2 ^ ((n + 1) / 2) := by
  obtain h | h | h := Vanish.Foundations.walsh_three_valued hcard hodd hAB a ha b <;> simp +decide [ h ]

/-
**The optimal Walsh value is attained.**  For an AB permutation fixing `0`
on `GF(2ⁿ)` (`n` odd), at every nonzero frequency `a` some Walsh coefficient
equals `2^{(n+1)/2}`.  (From the signed count
`#{W = +} − #{W = −} = 2^{(n-1)/2} ≥ 1`.)
-/
theorem walsh_extreme_attained {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) {f : F → F} (hf : Function.Bijective f) (hf0 : f 0 = 0)
    (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) :
    ∃ b : F, walsh f a b = 2 ^ ((n + 1) / 2) := by
  -- By `Vanish.Foundations.walsh_signed_count`, we have `(P.card : ℤ) - (N.card : ℤ) = 2 ^ ((n - 1) / 2)`.
  set P := (Finset.filter (fun b : F => walsh f a b = 2 ^ ((n + 1) / 2)) Finset.univ)
  set N := (Finset.filter (fun b : F => walsh f a b = -2 ^ ((n + 1) / 2)) Finset.univ)
  have h_diff : (P.card : ℤ) - (N.card : ℤ) = 2 ^ ((n - 1) / 2) := by
    convert Vanish.Foundations.walsh_signed_count hcard hodd hf hf0 hAB a ha using 1;
  exact Exists.elim ( Finset.card_pos.mp ( by linarith [ show ( 2 : ℤ ) ^ ( ( n - 1 ) / 2 ) > 0 by positivity ] ) ) fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.2 ⟩

/-- **Optimal linearity.**  For an AB permutation fixing `0` on `GF(2ⁿ)` (`n`
odd), the linearity at each nonzero frequency is exactly `2^{(n+1)/2}`: it is an
upper bound on every `|W(a,b)|` and is attained. -/
theorem walsh_linearity_eq_of_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) {f : F → F} (hf : Function.Bijective f) (hf0 : f 0 = 0)
    (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) :
    (∀ b : F, |walsh f a b| ≤ 2 ^ ((n + 1) / 2))
      ∧ ∃ b : F, walsh f a b = 2 ^ ((n + 1) / 2) :=
  ⟨fun b => walsh_abs_le_of_ab hcard hodd hAB a ha b,
    walsh_extreme_attained hcard hodd hf hf0 hAB a ha⟩

end Vanish.Foundations