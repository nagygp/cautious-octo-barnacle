import Mathlib
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg
import RequestProject.AdjointBij

/-!
# Theorem 3.2 — Dempwolff & Müller

Formalization of Theorem 3.2 from "Permutation polynomials and
translation planes of even order" by U. Dempwolff and P. Müller (Adv. Geom. 2013).

**Setting.** Let `F = GF(2ⁿ)` with `n` odd. Let `m` be odd with `1 < m < n`
and `gcd(m, n) = 1`. Let `L(X) = ∑_{i=0}^{m-1} X^{2^i}` be a truncated trace map.
Set `k = 2^{n-1} - 2^{m-1} - 1`, and choose `1 ≤ k' ≤ 2ⁿ - 1` with
`k · k' ≡ 2^{m-1} (mod 2ⁿ - 1)`.

**Theorem 3.2.** `L(X) · X^k` and `L(X) · X^{k'}` are permutation polynomials on `F`.

The proof decomposes into:
1. The truncated trace is additive (Layer 1).
2. A key telescoping identity `L(x)² + L(x) = x^{2^m} + x` (Layer 2).
3. The kernel of `L` restricted to `F` is trivial when `gcd(m,n) = 1` (Layer 3).
4. A Dickson-like polynomial `f_m` and its recursion (Layer 4).
5. The Dickson functional equation `f_m(z + z⁻¹) = z^{2^m-1} + z^{-(2^m-1)}` (Layer 5).
6. An arithmetic identity `2k + (2^m + 1) = 2ⁿ - 1` (Layer 6).
7. Coprimality: `gcd(2^m - 1, 2^{2n} - 1) = 1` when `m` odd, `gcd(m,n) = 1` (Layer 7).
8. Injectivity of the power map from coprimality (Layer 8).
9. Injectivity of the Dickson-like polynomial on `F*` (Layer 9).
10. Reduction from `L(X)·X^k` to the Dickson polynomial (Layer 10).
11. Main theorem: `L(X)·X^k` is a permutation polynomial (Layer 11).
12. The `k'` part via Frobenius composition (Layer 12).
-/

namespace DempwolffMueller

open Finset BigOperators

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- The truncated trace map `L(x) = ∑_{i=0}^{m-1} x^{2^i}` on a field of characteristic 2. -/
def truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

/-- The Dickson-like polynomial `f_m(x) = ∑_{i=1}^{m} x^{2^m + 1 - 2^i}`.
    Indexed as `∑_{j=0}^{m-1} x^{2^m + 1 - 2^{j+1}}` where `j = i - 1`. -/
def dicksonF {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ j ∈ Finset.range m, x ^ (2 ^ m + 1 - 2 ^ (j + 1))

-- ═══════════════════════════════════════════
-- Layer 1 : Additivity of truncated trace
-- ═══════════════════════════════════════════

/-- In characteristic 2, each Frobenius power preserves addition:
    `(x + y)^{2^i} = x^{2^i} + y^{2^i}`. -/
lemma add_pow_two_pow {F : Type*} [CommSemiring F] [CharP F 2]
    (x y : F) (i : ℕ) :
    (x + y) ^ (2 ^ i) = x ^ (2 ^ i) + y ^ (2 ^ i) := by
  haveI : Fact (Nat.Prime 2) := Fact.mk (by norm_num)
  exact add_pow_char_pow x y 2 i

/-- The truncated trace is additive: `L(x + y) = L(x) + L(y)`. -/
lemma truncTrace_add {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (x y : F) :
    truncTrace m (x + y) = truncTrace m x + truncTrace m y := by
  simp only [truncTrace, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_two_pow x y i

/-- `L(0) = 0`. -/
lemma truncTrace_zero {F : Type*} [CommSemiring F] (m : ℕ) :
    truncTrace m (0 : F) = 0 := by
  simp [truncTrace]

/-- `L(1) = m` (as an element of `F`).
    In a field of characteristic 2, `L(1) = m mod 2 = 1` when `m` is odd. -/
lemma truncTrace_one {F : Type*} [CommSemiring F] (m : ℕ) :
    truncTrace m (1 : F) = (m : F) := by
  simp [truncTrace]

/-
When `m` is odd in characteristic 2, `L(1) = 1`.
-/
lemma truncTrace_one_eq_one {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (hm : Odd m) :
    truncTrace m (1 : F) = 1 := by
      obtain ⟨ k, rfl ⟩ := hm; simp +decide [ truncTrace ] ; ring;
      simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ]

/-
═══════════════════════════════════════════
Layer 2 : Telescoping identity
═══════════════════════════════════════════

**Telescoping identity.** In characteristic 2,
    `L(x)² + L(x) = x^{2^m} + x`.

    Proof: `L(x)² = ∑_{i=0}^{m-1} x^{2^{i+1}} = ∑_{i=1}^{m} x^{2^i}`,
    so `L(x)² + L(x) = x^{2^m} + x` (intermediate terms cancel in pairs mod 2).
-/
lemma truncTrace_sq_add_self {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (x : F) :
    truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x := by
      induction' m with m ih <;> simp_all +decide [ Finset.sum_range_succ, pow_succ, pow_mul ];
      · simp +decide [ truncTrace ];
        rw [ ← two_smul F x, CharTwo.two_eq_zero, zero_smul ];
      · simp_all +decide [ ← sq, add_mul, mul_add, Finset.sum_range_succ ];
        convert congr_arg ( · + x ^ 2 ^ m * x ^ 2 ^ m + x ^ 2 ^ m ) ih using 1 <;> ring;
        · unfold truncTrace; simp +decide [ Finset.sum_range_succ, pow_succ, pow_mul ] ; ring;
          rw [ add_comm 1 m, Finset.sum_range_succ ] ; ring;
          simp +decide [ ← add_assoc, ← two_mul, CharTwo.two_eq_zero ];
        · simp +decide [ ← two_mul, CharTwo.two_eq_zero ]

/-
═══════════════════════════════════════════
Layer 3 : Kernel of truncated trace
═══════════════════════════════════════════

If `L(x) = 0`, then `x^{2^m} = x`.
    Immediate from the telescoping identity: `0 + 0 = x^{2^m} + x`,
    so `x^{2^m} = x` (using `a + a = 0` in characteristic 2).
-/
lemma frob_fixed_of_truncTrace_zero {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) {x : F} (hLx : truncTrace m x = 0) :
    x ^ (2 ^ m) = x := by
      have h_telescope : truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x := by
        exact?;
      rw [ eq_comm ] at h_telescope;
      have h_cancel : ∀ a b : F, a + b = 0 → a = b := by
        intro a b hab
        have h_eq : a + b + b = 0 + b := by
          rw [hab];
        convert h_eq using 1 <;> simp +decide [ add_assoc ];
        simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
      exact h_cancel _ _ ( by simpa [ hLx ] using h_telescope )

/-
`x² = x` implies `x = 0 ∨ x = 1` in any integral domain.
-/
lemma sq_eq_self_imp {F : Type*} [Field F] {x : F} (h : x ^ 2 = x) :
    x = 0 ∨ x = 1 := by
      exact or_iff_not_imp_left.mpr fun hx => mul_left_cancel₀ hx <| by linear_combination h;

/-
**Coprime Frobenius fixed-point lemma.**
    If `x^{2^m} = x` and `x^{2^n} = x` in `F` with `gcd(m, n) = 1`,
    then `x² = x`.

    The set `{x | x^{2^a} = x}` is a subfield of size `2^a`.
    The intersection of `{x | x^{2^m} = x}` and `{x | x^{2^n} = x}`
    is `{x | x^{2^{gcd(m,n)}} = x}`, by the formula
    `gcd(2^m - 1, 2^n - 1) = 2^{gcd(m,n)} - 1`
    applied to the multiplicative group.
-/
lemma frob_coprime_fixed {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {m' n' : ℕ} (hcop : Nat.Coprime m' n')
    {x : F} (hm : x ^ (2 ^ m') = x) (hn : x ^ (2 ^ n') = x) :
    x ^ 2 = x := by
      -- By induction on $k$, we can show that $x^{2^k} = x$ for any $k$ that is a linear combination of $m'$ and $n'$.
      have h_ind : ∀ k : ℕ, x ^ (2 ^ k) = x → ∀ l : ℕ, x ^ (2 ^ (l + k)) = x := by
        intro k hk l; induction l <;> simp_all +decide [ pow_add, pow_mul ] ;
        simp_all +decide [ pow_right_comm ];
        rw [ ← pow_mul, mul_comm, pow_mul, hk, sq ];
        by_cases hx : x = 0 <;> simp_all +decide [ sq ];
        have h_order : orderOf x ∣ 2 ^ m' - 1 ∧ orderOf x ∣ 2 ^ n' - 1 := by
          exact ⟨ orderOf_dvd_iff_pow_eq_one.mpr ( by rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow m' 2 zero_lt_two ), pow_add, pow_one ] at hm; aesop ), orderOf_dvd_iff_pow_eq_one.mpr ( by rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow n' 2 zero_lt_two ), pow_add, pow_one ] at hn; aesop ) ⟩;
        have h_order_one : Nat.gcd (2 ^ m' - 1) (2 ^ n' - 1) = 1 := by
          simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ];
        have := Nat.dvd_gcd h_order.1 h_order.2; aesop;
      -- Since $m'$ and $n'$ are coprime, by Bezout's identity, there exist integers $a$ and $b$ such that $am' - bn' = 1$.
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a * m' = b * n' + 1 ∨ b * n' = a * m' + 1 := by
        have := Nat.exists_mul_mod_eq_one_of_coprime hcop;
        rcases n' with ( _ | _ | n' ) <;> simp_all +decide;
        obtain ⟨ a, ha₁, ha₂ ⟩ := this; exact ⟨ a, m' * a / ( n' + 1 + 1 ), Or.inl <| by linarith [ Nat.mod_add_div ( m' * a ) ( n' + 1 + 1 ) ] ⟩ ;
      -- By applying the induction hypothesis repeatedly, we can show that $x^{2^{am'}} = x$ and $x^{2^{bn'}} = x$.
      have h_am : x ^ (2 ^ (a * m')) = x := by
        refine' Nat.recOn a _ _ <;> simp_all +decide [ Nat.succ_mul, pow_add ]
      have h_bn : x ^ (2 ^ (b * n')) = x := by
        refine' Nat.recOn b _ _ <;> simp_all +decide [ Nat.succ_mul, pow_add ];
      cases' hab with hab hab <;> simp_all +decide [ pow_add, pow_mul ]

/-
In `GF(2ⁿ)`, every element satisfies `x^{2^n} = x`.
-/
lemma pow_card_eq_self {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ n) = x := by
      rw [ ← hn, FiniteField.pow_card ]

/-
**Kernel triviality.** If `m` is odd, `gcd(m,n) = 1`, and `Fintype.card F = 2ⁿ`,
    then `L(x) = 0` implies `x = 0` for all `x ∈ F`.

    Proof: `L(x) = 0` ⟹ `x^{2^m} = x` (Layer 2), and `x^{2^n} = x` (finite field),
    so `x² = x` (coprime Frobenius), giving `x ∈ {0, 1}`.
    Since `L(1) = 1 ≠ 0`, we get `x = 0`.
-/
lemma truncTrace_ker_trivial {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_odd : Odd m) (hm_pos : 1 < m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) {x : F} (hLx : truncTrace m x = 0) :
    x = 0 := by
      -- From `truncTrace_sq_add_self` and `L(x)=0`, we get `x^{2^m} = x` via `frob_fixed_of_truncTrace_zero`.
      have hx2m : x ^ (2 ^ m) = x := by
        exact?
      have hx2n : x ^ (2 ^ n) = x := by
        rw [ ← hn, FiniteField.pow_card ]
      have hx2 : x ^ 2 = x := by
        exact?
      have hx01 : x = 0 ∨ x = 1 := (sq_eq_self_imp hx2)
      cases hx01 <;> simp_all +decide;
      exact absurd hLx ( by rw [ truncTrace_one_eq_one m hm_odd ] ; exact one_ne_zero )

/-
═══════════════════════════════════════════
Layer 4 : Dickson polynomial recursion
═══════════════════════════════════════════

Base case: `f₁(x) = x`.
-/
lemma dicksonF_one {F : Type*} [CommSemiring F] (x : F) :
    dicksonF 1 x = x := by
      unfold dicksonF; simp +decide ;

/-
**Dickson recursion.** `x · f_m(x) = f_{m-1}(x)² + x^{2^m}`.
    In characteristic 2, squaring distributes over sums,
    so `f_{m-1}(x)² = ∑ x^{2·(2^{m-1}+1-2^{j+1})}`.
    The recursion follows by reindexing.
-/
lemma dicksonF_recursion {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) (hm : 1 ≤ m) (x : F) (hx : x ≠ 0) :
    dicksonF (m + 1) x = (dicksonF m x ^ 2 + x ^ (2 ^ (m + 1))) / x := by
      rw [ eq_div_iff hx ];
      -- By definition of $dicksonF$, we can expand both sides.
      unfold dicksonF;
      -- Expand the right-hand side using the definition of `dicksonF`.
      have h_rhs : (∑ j ∈ Finset.range m, x ^ (2 ^ m + 1 - 2 ^ (j + 1))) ^ 2 = ∑ j ∈ Finset.range m, x ^ (2 ^ (m + 1) + 2 - 2 ^ (j + 2)) := by
        have h_rhs : ∀ (s : Finset ℕ) (f : ℕ → F), (∑ j ∈ s, f j) ^ 2 = ∑ j ∈ s, f j ^ 2 := by
          induction' ( Finset.range m ) using Finset.induction <;> simp_all +decide [ pow_succ, mul_assoc, Finset.sum_range_succ ];
          intro s f; induction s using Finset.induction <;> simp_all +decide [ pow_succ, mul_assoc, Finset.sum_range_succ ] ;
          grind +ring;
        convert h_rhs _ _ using 2 ; ring;
        grind;
      simp_all +decide [ Finset.sum_range_succ', pow_succ' ];
      simp +decide [ add_mul, mul_add, Finset.sum_mul _ _ _, pow_succ, mul_assoc, mul_comm, mul_left_comm, hx ];
      congr! 1;
      · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ ← pow_succ' ] ; rw [ Nat.sub_add_comm ] ; ring;
        · rw [ ← pow_add, Nat.add_sub_assoc ];
          rw [ show ( 4 : ℕ ) = 2 ^ 2 by norm_num, mul_comm ];
          rw [ ← pow_add ];
          exact le_trans ( pow_le_pow_right₀ ( by decide ) ( show 2 + i ≤ m + 1 by linarith [ Finset.mem_range.mp hi ] ) ) ( by ring_nf; norm_num );
        · rw [ ← pow_succ' ] ; exact Nat.mul_le_mul_left _ ( pow_le_pow_right₀ ( by decide ) ( Finset.mem_range.mp hi ) ) ;
      · rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr ( by positivity ) ) ]

/-
Equivalent form: `x · f_{m+1}(x) = f_m(x)² + x^{2^{m+1}}`.
-/
lemma dicksonF_recursion_mul {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) (x : F) :
    x * dicksonF (m + 1) x = dicksonF m x ^ 2 + x ^ (2 ^ (m + 1)) := by
      by_cases hx : x = 0;
      · simp +decide [ hx, dicksonF ];
        rw [ Finset.sum_eq_zero ] <;> simp +decide [ Nat.sub_eq_zero_iff_le, pow_add ];
        exact fun x hx => by rw [ ← pow_succ ] ; exact pow_le_pow_right₀ ( by decide ) hx;
      · cases le_or_gt 1 m <;> simp_all +decide [ dicksonF_recursion ];
        · rw [ mul_div_cancel₀ _ hx ];
        · simp +decide [ dicksonF ];
          ring

/-
═══════════════════════════════════════════
Layer 5 : Dickson functional equation
═══════════════════════════════════════════

**Dickson functional equation.**
    `f_m(z + z⁻¹) = z^{2^m - 1} + z^{-(2^m - 1)}` for `z ≠ 0`.

    Proved by induction on `m` using the recursion
    `x · f_m(x) = f_{m-1}(x)² + x^{2^m}`
    and the char-2 identities `(a + b)² = a² + b²`, `(z + z⁻¹)^{2^m} = z^{2^m} + z^{-2^m}`.
-/
lemma dicksonF_functional {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) (hm : 0 < m) {z : F} (hz : z ≠ 0) :
    dicksonF m (z + z⁻¹) = z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) := by
      induction' m with m ih generalizing z;
      · grind;
      · rcases eq_or_ne m 0 with rfl | hm' <;> simp_all +decide [ Nat.pow_succ' ];
        · exact?;
        · have h_ind : (z + z⁻¹) * dicksonF (m + 1) (z + z⁻¹) = (z + z⁻¹) * (z ^ (2 * 2 ^ m - 1) + (z ^ (2 * 2 ^ m - 1))⁻¹) := by
            convert dicksonF_recursion_mul m ( z + z⁻¹ ) using 1;
            rw [ ih ( Nat.pos_of_ne_zero hm' ) hz ] ; ring;
            rw [ show ( 2 ^ m * 2 - 1 : ℕ ) = ( 2 ^ m - 1 ) * 2 + 1 by zify ; norm_num ; ring ] ; simp +decide [ pow_add, pow_mul, hz ] ; ring;
            simp +decide [ hz, pow_mul', add_pow_char_pow ] ; ring;
            simp +decide [ hz, pow_mul', add_pow_char_pow ] ; ring;
            simp +decide [ show z ^ ( 2 ^ m * 2 ) = z ^ 2 * z ^ ( ( 2 ^ m - 1 ) * 2 ) by rw [ ← pow_add, show 2 ^ m * 2 = 2 + ( 2 ^ m - 1 ) * 2 by nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow m 2 zero_lt_two ) ] ], show z⁻¹ ^ ( 2 ^ m * 2 ) = z⁻¹ ^ 2 * z⁻¹ ^ ( ( 2 ^ m - 1 ) * 2 ) by rw [ ← pow_add, show 2 ^ m * 2 = 2 + ( 2 ^ m - 1 ) * 2 by nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow m 2 zero_lt_two ) ] ] ] ; ring;
            rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;
          by_cases h : z + z⁻¹ = 0 <;> simp_all +decide;
          -- In characteristic 2, $z + z⁻¹ = 0$ implies $z = 1$.
          have hz_one : z = 1 := by
            grind;
          simp_all +decide [ dicksonF ];
          rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ Nat.pow_succ' ];
          exact Nat.sub_ne_zero_of_lt ( by linarith [ pow_pos ( zero_lt_two' ℕ ) m, pow_le_pow_right₀ ( show 1 ≤ 2 by decide ) ‹_› ] )

/-
═══════════════════════════════════════════
Layer 6 : Arithmetic identity for k
═══════════════════════════════════════════

`2k + (2^m + 1) = 2ⁿ - 1` where `k = 2^{n-1} - 2^{m-1} - 1`.

    Proof: `2(2^{n-1} - 2^{m-1} - 1) + 2^m + 1 = 2ⁿ - 2^m - 2 + 2^m + 1 = 2ⁿ - 1`.
-/
lemma two_k_add_eq {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m < n) :
    2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) = 2 ^ n - 1 := by
      zify;
      rcases n with ( _ | n ) <;> rcases m with ( _ | m ) <;> norm_num [ pow_succ' ] at *;
      rw [ Nat.sub_sub, Nat.cast_sub ] <;> push_cast <;> linarith [ pow_lt_pow_right₀ ( by decide : 1 < 2 ) hmn, pow_pos ( by decide : 0 < 2 ) m ]

/-
═══════════════════════════════════════════
Layer 7 : Coprimality of Mersenne-like numbers
═══════════════════════════════════════════

**Mersenne coprimality.** `gcd(2^m - 1, 2^n - 1) = 2^{gcd(m,n)} - 1`.
    In particular, if `gcd(m, n) = 1`, then `gcd(2^m - 1, 2^n - 1) = 1`.
-/
lemma Nat.coprime_mersenne_of_coprime {m' n' : ℕ}
    (hcop : Nat.Coprime m' n') :
    Nat.Coprime (2 ^ m' - 1) (2 ^ n' - 1) := by
      -- By definition of coprimality, we need to show that gcd(2^m' - 1, 2^n' - 1) = 1.
      have h_gcd : Nat.gcd (2 ^ m' - 1) (2 ^ n' - 1) = 1 := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      convert h_gcd using 1

/-
When `m` is odd and `gcd(m, n) = 1`, we have `gcd(m, 2n) = 1`,
    and therefore `gcd(2^m - 1, 2^{2n} - 1) = 1`.
-/
lemma coprime_mersenne_double {m' n' : ℕ}
    (hm_odd : Odd m') (hcop : Nat.Coprime m' n') :
    Nat.Coprime (2 ^ m' - 1) (2 ^ (2 * n') - 1) := by
      convert Nat.coprime_mersenne_of_coprime _ using 1;
      exact Nat.Coprime.mul_right ( by obtain ⟨ k, rfl ⟩ := hm_odd; norm_num ) hcop

-- ═══════════════════════════════════════════
-- Layer 8 : Coprime power map is injective
-- ═══════════════════════════════════════════

/-- If `gcd(e, |G|) = 1` and `x^e = 1` in a finite group, then `x = 1`. -/
lemma eq_one_of_pow_eq_one_of_coprime {G : Type*} [Group G] [Fintype G]
    {e : ℕ} (hcop : Nat.Coprime e (Fintype.card G)) {x : G}
    (hxe : x ^ e = 1) : x = 1 := by
  have h1 : orderOf x ∣ e := orderOf_dvd_of_pow_eq_one hxe
  have h2 : orderOf x ∣ Fintype.card G := orderOf_dvd_card
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rwa [orderOf_eq_one_iff] at h3

/-
If `gcd(e, |G|) = 1`, then `x ↦ x^e` is injective on `G`.
-/
lemma pow_left_injective_of_coprime {G : Type*} [Group G] [Fintype G]
    {e : ℕ} (hcop : Nat.Coprime e (Fintype.card G)) :
    Function.Injective (fun x : G => x ^ e) := by
      refine' Finite.injective_iff_surjective.2 _;
      intro y
      obtain ⟨k, hk⟩ : ∃ k : ℕ, e * k ≡ 1 [MOD (Fintype.card G)] := by
        have := Nat.exists_mul_mod_eq_one_of_coprime hcop;
        rcases n : Fintype.card G with ( _ | _ | n ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
        exact ⟨ _, this.choose_spec.2 ⟩;
      use y ^ k; simp_all +decide [ ← pow_mul, ← ZMod.natCast_eq_natCast_iff ] ;
      rw [ mul_comm, ← Nat.mod_add_div ( e * k ) ( Fintype.card G ), show e * k % Fintype.card G = 1 % Fintype.card G from by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using hk ] ; simp +decide [ pow_add, pow_mul, pow_one, pow_zero, Nat.mod_eq_of_lt ] ;

/-
═══════════════════════════════════════════
Layer 9 : Injectivity of Dickson polynomial
═══════════════════════════════════════════

**Key equivalence for Dickson injectivity.**
    If `f_m(x) = f_m(y)` with `x, y ∈ F*`, pick `u, v` in a (possibly quadratic)
    extension with `x = u + u⁻¹`, `y = v + v⁻¹`. Then from
    `u^{2^m-1} + u^{-(2^m-1)} = v^{2^m-1} + v^{-(2^m-1)}`,
    we deduce `u^{2^m-1} = v^{2^m-1}` or `u^{2^m-1} = v^{-(2^m-1)}`.
    Since `gcd(2^m-1, |ext*|) = 1`, either `u = v` or `u = v⁻¹`,
    giving `x = y` in both cases.

    We encapsulate the core algebraic step: if `a + a⁻¹ = b + b⁻¹`
    in a field, then `a = b` or `a = b⁻¹`.
-/
lemma eq_or_eq_inv_of_add_inv_eq {F : Type*} [Field F] [CharP F 2]
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + a⁻¹ = b + b⁻¹) :
    a = b ∨ a = b⁻¹ := by
      grind +suggestions

/-
`dicksonF` commutes with ring homomorphisms (in particular `algebraMap`).
-/
lemma dicksonF_map_ringHom {F K : Type*} [CommSemiring F] [CommSemiring K]
    (f : F →+* K) (m : ℕ) (x : F) :
    dicksonF m (f x) = f (dicksonF m x) := by
      simp +decide only [dicksonF, map_sum, map_pow]

/-
In an algebraically closed field of characteristic 2, the polynomial
    `t² + a·t + 1` always has a root (and the root is nonzero since the
    constant term is 1).
-/
lemma exists_quad_root_char2 {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2]
    (a : K) : ∃ z : K, z ≠ 0 ∧ z ^ 2 + a * z + 1 = 0 := by
      obtain ⟨ z, hz ⟩ := IsAlgClosed.exists_root ( Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C 1 ) ( by
        rw [ Polynomial.degree_add_C ] <;> rw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ] );
      exact ⟨ z, by rintro rfl; norm_num at hz, by simpa using hz ⟩

/-
For `x ∈ F*`, there exists `z` in `AlgebraicClosure F` with `z ≠ 0`
    and `z + z⁻¹ = algebraMap F _ x`.
-/
lemma exists_add_inv_rep {F : Type*} [Field F] [CharP F 2]
    {x : F} (hx : x ≠ 0) :
    ∃ z : AlgebraicClosure F, z ≠ 0 ∧
      z + z⁻¹ = algebraMap F (AlgebraicClosure F) x := by
        -- By existence of roots in the algebraic closure (exists_quad_root_char2), there exists a root $z$ of $t^2 + (algebraMap F _ x) * t + 1 = 0$. This root is nonzero since $x \neq 0$.
        obtain ⟨z, hz_nonzero, hz_eq⟩ : ∃ z : AlgebraicClosure F, z ≠ 0 ∧ z ^ 2 + (algebraMap F (AlgebraicClosure F) x) * z + 1 = 0 := by
          have h_alg_closed : ∀ (a : AlgebraicClosure F), ∃ z : AlgebraicClosure F, z ^ 2 + a * z + 1 = 0 := by
            intro a
            have h_alg_closed : IsAlgClosed (AlgebraicClosure F) := by
              infer_instance
            exact (by
            have := h_alg_closed.exists_root ( Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 ) ?_ <;> simp_all +decide [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ];
            rw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> rw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ]);
          exact Exists.elim ( h_alg_closed ( algebraMap F ( AlgebraicClosure F ) x ) ) fun z hz => ⟨ z, by rintro rfl; simp +decide at hz, hz ⟩;
        grind +qlia

/-
If `z` is a root of `t² + a·t + 1 = 0` with `a^{2^n} = a` (i.e. `a ∈ GF(2ⁿ)`),
    then `z^{2^{2n}} = z`.

    Proof: `z^{2^n}` is also a root of the same quadratic (since
    `(z^{2^n})² + a·z^{2^n} + 1 = (z² + a·z + 1)^{2^n} = 0`).
    Applying Frobenius^n again gives `z^{2^{2n}} = z`.
-/
lemma frob_2n_eq_self_of_quad_root {K : Type*} [Field K] [CharP K 2]
    {n : ℕ} {a z : K} (hz : z ^ 2 + a * z + 1 = 0) (ha : a ^ (2 ^ n) = a) :
    z ^ (2 ^ (2 * n)) = z := by
      -- By raising both sides of the equation $z^2 + a*z + 1 = 0$ to the $2^n$ power, we get $(z^{2^n})^2 + a^{2^n}*(z^{2^n}) + 1 = 0$.
      have h_exp : (z ^ (2 ^ n)) ^ 2 + a ^ (2 ^ n) * (z ^ (2 ^ n)) + 1 = 0 := by
        have h_root_pow : (z ^ 2 + a * z + 1) ^ (2 ^ n) = 0 := by
          rw [ hz, zero_pow ( by positivity ) ];
        convert h_root_pow using 1 ; ring;
        simp +decide [ add_pow_char_pow, mul_pow ] ; ring;
      by_cases h_cases : z ^ (2 ^ n) = z <;> simp_all +decide [ pow_mul' ];
      · rw [ pow_two, pow_mul, h_cases ];
        exact h_cases;
      · -- Since $z^{2^n} \neq z$, we have $z^{2^n} = a + z$.
        have h_z_pow : z ^ (2 ^ n) = a + z := by
          grind +ring;
        simp_all +decide [ pow_succ, pow_mul ];
        simp_all +decide [ add_pow_char_pow ];
        grind

/-
If `z^{2^{2n}} = z`, `w^{2^{2n}} = w`, `z ≠ 0`, `w ≠ 0`,
    `gcd(d, 2^{2n} - 1) = 1`, and `z^d = w^d`, then `z = w`.
-/
lemma eq_of_pow_eq_of_frob_fixed {K : Type*} [Field K] [CharP K 2]
    {n d : ℕ} (hcop : Nat.Coprime d (2 ^ (2 * n) - 1))
    {z w : K} (hz : z ≠ 0) (hw : w ≠ 0)
    (hz_fix : z ^ (2 ^ (2 * n)) = z)
    (hw_fix : w ^ (2 ^ (2 * n)) = w)
    (hpow : z ^ d = w ^ d) :
    z = w := by
      have h_order : (z / w) ^ d = 1 ∧ (z / w) ^ (2 ^ (2 * n) - 1) = 1 := by
        cases k : 2 ^ ( 2 * n ) <;> simp_all +decide [ pow_succ, mul_assoc, div_eq_iff ];
        simp_all +decide [ div_pow, pow_eq_one_iff ];
      have h_order_div : (z / w) ^ Nat.gcd d (2 ^ (2 * n) - 1) = 1 := by
        rw [ pow_gcd_eq_one ] ; aesop;
      simp_all +decide [ div_eq_iff ]

/-
**Dickson injectivity on units.**
    The Dickson-like polynomial `f_m` is injective on `F* = F \ {0}`
    when `m` is odd, `gcd(m, n) = 1`, and `|F| = 2ⁿ`.

    The proof uses the functional equation and coprimality of `2^m - 1`
    with `2^{2n} - 1` (the order of the multiplicative group of a
    quadratic extension of `F`).
-/
lemma dicksonF_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (m : ℕ) (hm_pos : 0 < m) (hm_odd : Odd m) (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hf : dicksonF m x = dicksonF m y) :
    x = y := by
      obtain ⟨z, hz⟩ : ∃ z : AlgebraicClosure F, z ≠ 0 ∧ z + z⁻¹ = algebraMap F (AlgebraicClosure F) x := by
        exact?
      obtain ⟨w, hw⟩ : ∃ w : AlgebraicClosure F, w ≠ 0 ∧ w + w⁻¹ = algebraMap F (AlgebraicClosure F) y := by
        convert exists_add_inv_rep hy using 1
      have hz_eq_w : z = w ∨ z = w⁻¹ := by
        have hz_eq_w : z ^ (2 ^ m - 1) = w ^ (2 ^ m - 1) ∨ z ^ (2 ^ m - 1) = w⁻¹ ^ (2 ^ m - 1) := by
          have h_eq : dicksonF m (z + z⁻¹) = z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) ∧ dicksonF m (w + w⁻¹) = w ^ (2 ^ m - 1) + w⁻¹ ^ (2 ^ m - 1) := by
            exact ⟨ dicksonF_functional m hm_pos hz.1, dicksonF_functional m hm_pos hw.1 ⟩
          generalize_proofs at *; (
          have h_eq : dicksonF m (z + z⁻¹) = dicksonF m (w + w⁻¹) := by
            convert congr_arg ( algebraMap F ( AlgebraicClosure F ) ) hf using 1 <;> simp +decide [ hz.2, hw.2, dicksonF_map_ringHom ]
          generalize_proofs at *; (
          have := eq_or_eq_inv_of_add_inv_eq ( show z ^ ( 2 ^ m - 1 ) ≠ 0 from pow_ne_zero _ hz.1 ) ( show w ^ ( 2 ^ m - 1 ) ≠ 0 from pow_ne_zero _ hw.1 ) ?_ <;> simp_all +decide [ add_comm ] ;))
        generalize_proofs at *; (
        have hz_eq_w : z ^ (2 ^ (2 * n)) = z ∧ w ^ (2 ^ (2 * n)) = w := by
          have hz_frob : (algebraMap F (AlgebraicClosure F) x) ^ (2 ^ n) = algebraMap F (AlgebraicClosure F) x ∧ (algebraMap F (AlgebraicClosure F) y) ^ (2 ^ n) = algebraMap F (AlgebraicClosure F) y := by
            have hz_frob : ∀ x : F, x ^ (2 ^ n) = x := by
              exact fun x => by rw [ ← hn, FiniteField.pow_card ] ;
            generalize_proofs at *; (
            exact ⟨ by rw [ ← map_pow, hz_frob ], by rw [ ← map_pow, hz_frob ] ⟩)
          generalize_proofs at *; (
          grind +suggestions)
        generalize_proofs at *; (
        have hz_eq_w : Nat.Coprime (2 ^ m - 1) (2 ^ (2 * n) - 1) := by
          nontriviality;
          exact?
        generalize_proofs at *; (
        cases' ‹z ^ ( 2 ^ m - 1 ) = w ^ ( 2 ^ m - 1 ) ∨ z ^ ( 2 ^ m - 1 ) = w⁻¹ ^ ( 2 ^ m - 1 ) › with h h <;> [ left; right ] <;> apply eq_of_pow_eq_of_frob_fixed hz_eq_w <;> aesop ( simp_config := { singlePass := true } ) ;)))
      generalize_proofs at *; (
      rcases hz_eq_w with ( rfl | rfl ) <;> simp_all +decide [ add_comm ])

/-
═══════════════════════════════════════════
Layer 10 : Reduction from L(x)·x^k to Dickson
═══════════════════════════════════════════

**Squaring is bijective** in a field of characteristic 2
    (the Frobenius endomorphism is an automorphism of a finite field).
-/
lemma sq_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2] :
    Function.Bijective (fun x : F => x ^ 2) := by
      convert Finite.injective_iff_bijective.mp _;
      · infer_instance;
      · intro x y hxy;
        grind

/-
**Inversion is bijective** on `F*` (trivially, since `(·⁻¹)⁻¹ = ·`).
-/
lemma inv_bijective_units {F : Type*} [Field F] :
    Function.Bijective (fun x : F => x⁻¹) := by
      exact Function.bijective_iff_has_inverse.mpr ⟨ fun x => x⁻¹, fun x => by simp +decide, fun x => by simp +decide ⟩

/-
**On `F*`, `x^{2k} = x^{-(2^m+1)}`** when `2k + (2^m + 1) = 2ⁿ - 1 = |F*|`.
    That is, `x^{2k} · x^{2^m+1} = 1` for `x ∈ F*`.
-/
lemma pow_2k_eq_pow_neg {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n m : ℕ} (hn : Fintype.card F = 2 ^ n) (hn1 : 1 ≤ n)
    (hm1 : 1 ≤ m) (hmn : m < n)
    {x : F} (hx : x ≠ 0) :
    x ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) = x⁻¹ ^ (2 ^ m + 1) := by
      -- By two_k_add_eq, we have $2k + (2^m + 1) = 2^n - 1$.
      have h_eq : 2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) = 2 ^ n - 1 := by
        convert two_k_add_eq hn1 hm1 hmn using 1;
      -- By FiniteField.pow_card_sub_one_eq_one, we have $x^{2^n - 1} = 1$ for $x \neq 0$.
      have h_pow_card : x ^ (2 ^ n - 1) = 1 := by
        rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx ];
      simp +decide [ ← h_eq, pow_add, hx ] at h_pow_card ⊢;
      grind +splitImp

/-
**Identity connecting g and f.** For `x ∈ F*`:
    `(L(x) · x^k)² = L(x)² · x^{-(2^m+1)}`
    and `L(x⁻¹)² · x^{2^m+1} = f_m(x)`.
    Therefore injectivity of `f_m` on `F*` implies injectivity of `L(·) · (·)^k` on `F*`.
-/
lemma truncTrace_sq_mul_inv_eq_dicksonF {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) {x : F} (hx : x ≠ 0) :
    truncTrace m x⁻¹ ^ 2 * x ^ (2 ^ m + 1) = dicksonF m x := by
      convert congr_arg ( fun y => y ^ 2 * x ^ ( 2 ^ m + 1 ) ) ( show ( ∑ i ∈ Finset.range m, x⁻¹ ^ ( 2 ^ i ) ) = ( ∑ i ∈ Finset.range m, ( x⁻¹ ) ^ ( 2 ^ i ) ) from rfl ) using 1;
      convert ( Finset.sum_mul _ _ _ ) |> Eq.symm using 1;
      convert rfl;
      convert Finset.sum_congr rfl fun i hi => ?_;
      convert mul_div_cancel₀ _ ( pow_ne_zero ( 2 ^ ( i + 1 ) ) hx ) using 1;
      rw [ mul_div_cancel₀ _ ( pow_ne_zero _ hx ) ];
      rotate_left;
      congr! 1;
      rotate_left;
      use fun i => x⁻¹ ^ ( 2 ^ ( i + 1 ) );
      · rw [ inv_pow, inv_mul_eq_div, div_eq_iff ( pow_ne_zero _ hx ) ];
        rw [ ← pow_add, Nat.sub_add_cancel ( show 2 ^ ( i + 1 ) ≤ 2 ^ m + 1 from Nat.le_succ_of_le ( pow_le_pow_right₀ ( by decide ) ( by linarith [ Finset.mem_range.mp hi ] ) ) ) ];
      · induction' m with m ih <;> simp_all +decide [ Finset.sum_range_succ, pow_succ, pow_mul ];
        grobner

/-
═══════════════════════════════════════════
Layer 11 : Main injectivity of L(x)·x^k
═══════════════════════════════════════════

**L(x)·x^k is injective on `F*`.** Combines:
    - `(L(x)·x^k)²` agrees with `g(x)` on `F*` (Layer 10),
    - `g(1/x) = f_m(x)` on `F*` (Layer 10),
    - `f_m` is injective on `F*` (Layer 9),
    - squaring and inversion are bijective (Layer 10).
-/
lemma LxXk_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (m : ℕ) (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1) =
           truncTrace m y * y ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :
    x = y := by
      -- By squaring both sides of the equation, we get $(L(x) \cdot x^k)^2 = (L(y) \cdot y^k)^2$, which simplifies to $L(x)^2 \cdot x^{-2^m-1} = L(y)^2 \cdot y^{-2^m-1}$.
      have h_sq : truncTrace m x ^ 2 * x⁻¹ ^ (2 ^ m + 1) = truncTrace m y ^ 2 * y⁻¹ ^ (2 ^ m + 1) := by
        convert congr_arg ( · ^ 2 ) heq using 1 <;> ring;
        · have := pow_2k_eq_pow_neg ( hn := hn ) ( hn1 := Nat.one_le_iff_ne_zero.mpr ( by aesop_cat ) ) ( hm1 := hm_pos.le ) ( hmn := hm_lt ) ( hx := hx ) ; simp_all +decide [ pow_mul', mul_assoc, mul_comm, mul_left_comm ] ;
          simp +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm, hx ];
        · have := pow_2k_eq_pow_neg ( hn := hn ) ( show 1 ≤ n from Nat.one_le_of_lt hm_lt ) ( show 1 ≤ m from Nat.one_le_of_lt hm_pos ) ( show m < n from hm_lt ) hy; simp_all +decide [ pow_succ', pow_mul', mul_assoc ] ;
          exact Or.inl ( by rw [ ← this ] ; ring );
      -- By Layer 10, we know that $L(x^{-1})^2 \cdot x^{2^m+1} = f_m(x)$ and $L(y^{-1})^2 \cdot y^{2^m+1} = f_m(y)$.
      have h_f_m : dicksonF m x⁻¹ = dicksonF m y⁻¹ := by
        have := truncTrace_sq_mul_inv_eq_dicksonF m ( show x⁻¹ ≠ 0 from inv_ne_zero hx ) ; have := truncTrace_sq_mul_inv_eq_dicksonF m ( show y⁻¹ ≠ 0 from inv_ne_zero hy ) ; simp_all +decide [ pow_add, pow_mul ] ;
      have := dicksonF_injective_on_units hn m ( by linarith ) hm_odd hcop ( inv_ne_zero hx ) ( inv_ne_zero hy ) h_f_m; aesop;

/-
**L(x)·x^k is a bijection on `F`.**
    By Layer 3 (kernel triviality), `L(x)·x^k = 0` iff `x = 0`.
    By Layer 11, `L(x)·x^k` is injective on `F*`.
    Together, `L(x)·x^k` is injective on `F`, hence bijective (finite).
-/
lemma LxXk_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (m : ℕ) (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
      have h_inj : Function.Injective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
        intro x y hxy; by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide ;
        · simp_all +decide [ truncTrace_zero ];
          exact absurd ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy ) hy;
        · simp_all +decide [ truncTrace_zero ];
          exact hx ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy );
        · apply LxXk_injective_on_units hn m hm_pos hm_odd hm_lt hn_odd hcop hx hy hxy;
      exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

/-
═══════════════════════════════════════════
Layer 12 : The k' part via Frobenius
═══════════════════════════════════════════

**Frobenius composition preserves bijectivity.**
    If `g : F → F` is bijective and `j : ℕ`, then `x ↦ (g x)^{2^j}` is bijective,
    since the Frobenius `x ↦ x^{2^j}` is an automorphism of `F` in characteristic 2.
-/
lemma frob_comp_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (g : F → F) (hg : Function.Bijective g) (j : ℕ) :
    Function.Bijective (fun x => g x ^ (2 ^ j)) := by
      have h_frobenius_bijective : Function.Bijective (fun x : F => x ^ (2 ^ j)) := by
        have h_frob_j_bijective : Function.Bijective (fun x : F => x ^ 2) := by
          exact?;
        induction' j with j ih;
        · simp +decide [ Function.bijective_id ];
        · convert ih.comp h_frob_j_bijective using 1 ; ext ; ring;
          simp +decide [ pow_mul ];
          ring;
      exact h_frobenius_bijective.comp hg

/-
**Adjoint relation.** `L*(x)^{2^{m-1}} = L(x)`, where
    `L*(x) = ∑_{i=n-m+1}^{n} x^{2^i}` is the trace adjoint of `L`.
    In characteristic 2, `(∑ a_i)^{2^j} = ∑ a_i^{2^j}`, so
    `L*(x)^{2^{m-1}} = ∑_{i=n-m+1}^{n} x^{2^{i+m-1}}`.
    Since `x^{2^n} = x` in `GF(2ⁿ)`, reindexing gives `L(x)`.
-/
lemma truncTrace_adj_frob {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ) (hm : m ≤ n) (x : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) ^ (2 ^ (m - 1)) =
    truncTrace m x := by
      -- Now consider the expression $\sum_{i=n-m+1}^{n} x^{2^i}$. We can rewrite this as $\sum_{k=0}^{m-1} x^{2^{n+1-m+j}}$.
      have h_sum_rewrite : (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) = ∑ j ∈ Finset.range m, x ^ (2 ^ (n - m + 1 + j)) := by
        rw [ Finset.sum_Ico_eq_sum_range ];
        rw [ show n + 1 - ( n - m + 1 ) = m by omega ];
      -- In characteristic 2, $(∑ a_i)^{2^j} = ∑ a_i^{2^j}$, so we can simplify the expression.
      have h_char2 : (∑ j ∈ Finset.range m, x ^ (2 ^ (n - m + 1 + j))) ^ (2 ^ (m - 1)) = ∑ j ∈ Finset.range m, x ^ (2 ^ (n - m + 1 + j + (m - 1))) := by
        induction' ( Finset.range m ) using Finset.induction <;> simp_all +decide [ pow_add, pow_mul ];
        simp_all +decide [ add_pow_char_pow ];
      -- Simplify the exponent using the fact that $x^{2^n} = x$ in $GF(2^n)$.
      have h_exp_simplify : ∀ j ∈ Finset.range m, x ^ (2 ^ (n - m + 1 + j + (m - 1))) = x ^ (2 ^ (j)) := by
        intro j hj
        have h_exp_simplify_step : x ^ (2 ^ n) = x := by
          rw [ ← hn, FiniteField.pow_card ];
        rw [ show n - m + 1 + j + ( m - 1 ) = n + j by linarith [ Nat.sub_add_cancel hm, Nat.sub_add_cancel ( show 1 ≤ m from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] ];
        rw [ pow_add, pow_mul, h_exp_simplify_step ];
      exact h_sum_rewrite.symm ▸ h_char2.symm ▸ Finset.sum_congr rfl h_exp_simplify

/-
**L(X)·X^{k'} is a permutation polynomial.**
    Since `L(X)·X^k` is bijective, so is `(L(X)·X^k)^{2^{m-1}}`.
    By the Frobenius ring-homomorphism property in characteristic 2,
    `(L(x)·x^k)^{2^{m-1}} = L(x)^{2^{m-1}} · x^{k·2^{m-1}}`.
    The adjoint relation shows `L*(x)^{2^{m-1}} = L(x)`, and Lemma 3.1
    relates `L*` to `L`, establishing the bijectivity of `L(X)·X^{k'}`.
-/
lemma LxXk'_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (m : ℕ) (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n)
    (k' : ℕ) (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) = 2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by
      have h_adj_bij : Function.Bijective (fun x : F => (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) * x ^ ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1))) := by
        have h_adj_bij : Function.Bijective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
          exact LxXk_bijective hn m hm_pos hm_odd hm_lt hn_odd hcop;
        have h_adj_bij : Function.Bijective (fun x : F => (truncTrace m x) ^ (2 ^ (n - m + 1)) * x ^ ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1))) := by
          have h_adj_bij : Function.Bijective (fun x : F => (truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ (2 ^ (n - m + 1))) := by
            convert frob_comp_bijective_right _ h_adj_bij _ using 1;
          convert h_adj_bij using 2 ; ring;
        convert h_adj_bij using 2;
        rw [ ← truncTrace_adj_frob hn m ( by linarith ) ];
        simp +decide [ ← pow_mul, mul_comm ];
        rw [ ← pow_add, show n - m + 1 + ( m - 1 ) = n by omega ];
        grind +suggestions;
      have h_adj_swap : ∀ w z : F, frobSum 2 n ((∑ i ∈ Finset.Ico (n - m + 1) (n + 1), w ^ (2 ^ i)) * z) = frobSum 2 n (w * (truncTrace m z)) := by
        have h_adj_swap : ∀ w z : F, frobSum 2 n (frobSum 2 m w * z) = frobSum 2 n (w * (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (2 ^ i))) := by
          apply frobSum_adjoint_Ico;
          · exact hn;
          · lia;
        have h_adj_swap : ∀ w z : F, frobSum 2 n ((truncTrace m w) * z) = frobSum 2 n (w * (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (2 ^ i))) := by
          convert h_adj_swap using 1;
        intro w z; have := h_adj_swap w z; have := h_adj_swap z w; simp_all +decide [ mul_comm ] ;
      apply adjoint_swap_bij 2 hn (by linarith) (fun x => (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i))) (fun x => truncTrace m x) (by
      simp +decide [ ← Finset.sum_add_distrib, add_pow_two_pow ]) (by
      exact?) h_adj_swap (by
      intro x hx_nonzero
      have h_trace_nonzero : ∃ y : F, frobSum 2 n (x * y) ≠ 0 := by
        apply trace_nondegenerate;
        · exact hn;
        · linarith;
        · exact hx_nonzero
      exact h_trace_nonzero) ((2 ^ (n - 1) - 2 ^ (m - 1) - 1) * 2 ^ (n - m + 1)) k' (by
      have h_mod_chain : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' * 2 ^ (n - m + 1) % (2 ^ n - 1) = 2 ^ (m - 1) * 2 ^ (n - m + 1) % (2 ^ n - 1) := by
        exact Nat.ModEq.mul_right _ hk';
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← pow_add, show n - m + 1 + ( m - 1 ) = n by omega ];
      exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] )) h_adj_bij

-- ═══════════════════════════════════════════
-- Layer 13 : Main theorem — Theorem 3.2
-- ═══════════════════════════════════════════

/-- **Theorem 3.2.** Let `F = GF(2ⁿ)` with `n` odd. Let `m` be odd with
    `1 < m < n` and `gcd(m, n) = 1`. Let `L(X) = ∑_{i=0}^{m-1} X^{2^i}`
    be a truncated trace map. Set `k = 2^{n-1} - 2^{m-1} - 1`.
    Then `L(X)·X^k` is a permutation polynomial on `F`.

    Moreover, if `k'` satisfies `k·k' ≡ 2^{m-1} (mod 2ⁿ-1)`,
    then `L(X)·X^{k'}` is also a permutation polynomial. -/
theorem theorem_3_2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (m : ℕ) (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :=
  LxXk_bijective hn m hm_pos hm_odd hm_lt hn_odd hcop

end DempwolffMueller