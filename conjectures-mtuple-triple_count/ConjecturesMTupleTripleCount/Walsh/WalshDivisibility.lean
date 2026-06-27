import Mathlib
import ConjecturesMTupleTripleCount.Walsh.WalshAB
import ConjecturesMTupleTripleCount.APN.Defs

/-!
# Reusable Walsh-divisibility infrastructure for the Kasami AB Theorem

This module collects the *characteristic-free, function-agnostic* building blocks
that the Kasami Walsh-divisibility step
(`KasamiWalshDiv.kasami_walsh_div`) is assembled from:

* **2-adic divisibility algebra.** `sq_dvd_of_dvd`, `dvd_of_sq_dvd`, `sq_bridge`,
  `exponent_align`, `walsh_div_iff_sq`, `extract_sqrt_div`: the squaring bridge
  `2^k ∣ m ↔ 2^{2k} ∣ m²`, so for `n` odd `2^{(n+1)/2} ∣ W ↔ 2^{n+1} ∣ W²`.
* **Degenerate Walsh cases.** `walsh_pow_zero_zero`, `walsh_pow_a_ne_zero`,
  `walsh_pow_b_ne_zero`: the `a = 0` / `b = 0` corners for power functions.
* **Character-sum divisibility.** `additive_char_sum_dvd`,
  `dvd_of_sq_dvd_pow_two_odd`, `quadratic_gauss_sum_div`: a quadratic-form
  character sum over `GF(2ⁿ)` is divisible by `2^{(n+1)/2}` (the Gauss-sum core).

The Kasami specialization (squaring the Walsh coefficient into a quadratic Gauss
sum) is carried out in `ConjecturesMTupleTripleCount/Core/KasamiWalshDiv.lean`.
-/

set_option maxHeartbeats 1600000

namespace WalshDivisibility

open Finset Fintype BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Layer S0: Integer Squaring Bridge -/

/-- `2^k ∣ m → 2^{2k} ∣ m²` -/
theorem sq_dvd_of_dvd (m : ℤ) (k : ℕ) (h : (2 : ℤ) ^ k ∣ m) :
    (2 : ℤ) ^ (2 * k) ∣ m ^ 2 := by
  obtain ⟨c, rfl⟩ := h; exact ⟨c ^ 2, by ring⟩

/-- `2^{2k} ∣ m² → 2^k ∣ m` -/
theorem dvd_of_sq_dvd (m : ℤ) (k : ℕ) (h : (2 : ℤ) ^ (2 * k) ∣ m ^ 2) :
    (2 : ℤ) ^ k ∣ m := by
  rw [← Int.pow_dvd_pow_iff (show (2 : ℕ) ≠ 0 from by norm_num)]
  rwa [show ((2 : ℤ) ^ k) ^ 2 = (2 : ℤ) ^ (2 * k) from by ring]

/-- **Squaring bridge**: `2^k ∣ m ↔ 2^{2k} ∣ m²`. -/
theorem sq_bridge (m : ℤ) (k : ℕ) :
    (2 : ℤ) ^ k ∣ m ↔ (2 : ℤ) ^ (2 * k) ∣ m ^ 2 :=
  ⟨sq_dvd_of_dvd m k, dvd_of_sq_dvd m k⟩

/-- For odd n, `2 * ((n+1)/2) = n + 1`. -/
theorem exponent_align {n : ℕ} (hodd : Odd n) : 2 * ((n + 1) / 2) = n + 1 := by
  obtain ⟨k, rfl⟩ := hodd; omega

/-- Walsh divisibility ↔ Walsh² divisibility for odd n. -/
theorem walsh_div_iff_sq {n : ℕ} (hodd : Odd n) (W : ℤ) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ W ↔ (2 : ℤ) ^ (n + 1) ∣ W ^ 2 := by
  constructor
  · intro h; rw [← exponent_align hodd]; exact sq_dvd_of_dvd W _ h
  · intro h; rw [← exponent_align hodd] at h; exact dvd_of_sq_dvd W _ h

/-- Extract W divisibility from W² divisibility. -/
theorem extract_sqrt_div {n : ℕ} (hodd : Odd n) (W : ℤ)
    (h : (2 : ℤ) ^ (n + 1) ∣ W ^ 2) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ W :=
  (walsh_div_iff_sq hodd W).mpr h

/-! ## Layer S1: Trivial Cases -/

/-- W(0, 0) = 2^n, divisible by 2^{(n+1)/2}. -/
theorem walsh_pow_zero_zero {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ) (hn : n ≥ 1) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh (· ^ d : F → F) 0 0 := by
  rw [walsh_zero_zero, hcard, Int.natCast_pow, Nat.cast_ofNat]
  exact ⟨2 ^ (n - (n + 1) / 2), by rw [← pow_add]; congr 1; omega⟩

/-- W(a, 0) = 0 for a ≠ 0. -/
theorem walsh_pow_a_ne_zero (d : ℕ) (a : F) (ha : a ≠ 0) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh (· ^ d : F → F) a 0 := by
  rw [walsh_b_zero _ a ha]; exact dvd_zero _

/-- W(0, b) = 0 for b ≠ 0 when f is a bijection. -/
theorem walsh_pow_b_ne_zero (d : ℕ)
    (b : F) (hb : b ≠ 0) (hbij : Function.Bijective (· ^ d : F → F)) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh (· ^ d : F → F) 0 b := by
  rw [walsh_a_zero_perm _ hbij b hb]; exact dvd_zero _

/-! ## Layer S1.5: Integer valuation helpers -/

/-
If `2^n ∣ S²` and `n` is odd, then `2^{(n+1)/2} ∣ S`.
    Proof: v₂(S²) = 2·v₂(S) is even. If S ≠ 0, then 2·v₂(S) ≥ n,
    so v₂(S) ≥ n/2. Since v₂(S) is a natural number and n is odd,
    v₂(S) ≥ ⌈n/2⌉ = (n+1)/2.
-/
theorem dvd_of_sq_dvd_pow_two_odd (S : ℤ) {n : ℕ} (hodd : Odd n)
    (h : (2 : ℤ) ^ n ∣ S ^ 2) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ S := by
  contrapose! h;
  rw [ ← Int.natAbs_dvd_natAbs, ← Nat.factorization_le_iff_dvd ] <;> norm_num;
  · exact lt_of_not_ge fun hn => h <| dvd_trans ( pow_dvd_pow _ <| by omega ) <| Int.natCast_pow 2 _ ▸ Int.natCast_dvd.mpr ( Nat.ordProj_dvd _ _ );
  · aesop

/-! ## Layer S1.7: Additive character sums -/

/-
For an additive function `g : F → F` (satisfying `g(x+y) = g(x) + g(y)`),
    the character sum `∑ y, χ(g(y))` is divisible by `Fintype.card F`.
    (It equals either 0 or `Fintype.card F`.)
-/
theorem additive_char_sum_dvd (g : F → F)
    (hg_add : ∀ x y : F, g (x + y) = g x + g y) :
    (Fintype.card F : ℤ) ∣ ∑ y : F, χ (g y) := by
  by_cases h : ∀ y : F, Tr ( g y ) = 0 <;> simp_all +decide [ χ ];
  obtain ⟨ a, ha ⟩ := h
  have h_sum_zero : ∑ x : F, χ (g x) = ∑ x : F, χ (g (x + a)) := by
    rw [ ← Equiv.sum_comp ( Equiv.addRight a ) ] ; aesop;
  have h_sum_neg : ∑ x : F, χ (g (x + a)) = -∑ x : F, χ (g x) := by
    simp +decide [ ← Finset.sum_neg_distrib, hg_add, χ_mul, ha ];
    exact Finset.sum_congr rfl fun x _ => by rw [ show χ ( g a ) = -1 by exact if_neg ha ] ; ring;
  have h_sum_zero_final : ∑ x : F, χ (g x) = 0 := by
    grind +ring
  exact h_sum_zero_final.symm ▸ dvd_zero _

/-! ## Layer S2: Quadratic Gauss Sum Divisibility

The proof uses the **S² factorization trick**:
1. Expand S² = Σ_{u,y} χ(Q(u+y) + Q(y)) by substituting x = u + y.
2. For fixed u, use hQ_add3 to show B(u,·) = Q(u+·) + Q(u) + Q(·) + Q(0) is additive.
3. Factor: Σ_y χ(Q(u+y)+Q(y)) = χ(Q(u)+Q(0)) · Σ_y χ(B(u,y)).
4. Since B(u,·) is additive, Σ_y χ(B(u,y)) is divisible by |F| = 2^n.
5. Therefore 2^n ∣ S².
6. Since n is odd, the 2-adic valuation parity argument gives 2^{(n+1)/2} ∣ S.
-/

/-
**Quadratic Gauss sum divisibility**: For a "quadratic" function
    `Q : F → F` (whose third discrete derivative vanishes: `hQ_add3`)
    over `GF(2^n)` with `n` odd, `∑_x χ(Q(x))` is divisible by `2^{(n+1)/2}`.
-/
theorem quadratic_gauss_sum_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (Q : F → F)
    (hQ_add3 : ∀ x y z : F,
      Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z)
      + Q x + Q y + Q z + Q 0 = 0) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ ∑ x : F, χ (Q x) := by
  convert dvd_of_sq_dvd_pow_two_odd _ hodd _;
  -- By expanding the square and using the properties of the character χ, we can show that the sum is divisible by |F|.
  have h_expand : (∑ x : F, χ (Q x)) ^ 2 = ∑ u : F, ∑ y : F, χ (Q (u + y) + Q y) := by
    rw [ sq, ← Finset.sum_comm ];
    simp +decide only [Finset.mul_sum _ _ _, mul_comm, χ_mul];
    exact Finset.sum_congr rfl fun x _ => by rw [ ← Equiv.sum_comp ( Equiv.addRight x ) ] ; simp +decide ;
  -- For fixed u, show Q(u+y) + Q(y) = Q(u) + Q(0) + B(u,y) where B(u,y) = Q(u+y) + Q(u) + Q(y) + Q(0).
  have h_factor : ∀ u : F, ∑ y : F, χ (Q (u + y) + Q y) = χ (Q u + Q 0) * ∑ y : F, χ (Q (u + y) + Q u + Q y + Q 0) := by
    intro u; rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun y _ => _ ; simp +decide [ χ_mul ] ; ring;
    simp +decide [ χ_sq ];
  -- By additive_char_sum_dvd, (Fintype.card F : ℤ) ∣ ∑ y, χ(B(u,y)).
  have h_div : ∀ u : F, (Fintype.card F : ℤ) ∣ ∑ y : F, χ (Q (u + y) + Q u + Q y + Q 0) := by
    intro u
    apply additive_char_sum_dvd
    intro x y
    have := hQ_add3 u x y
    simp_all +decide [ add_assoc ];
    grind +ring;
  simp_all +decide [ Finset.sum_mul _ _ _ ];
  exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right ( h_div x ) _

end WalshDivisibility