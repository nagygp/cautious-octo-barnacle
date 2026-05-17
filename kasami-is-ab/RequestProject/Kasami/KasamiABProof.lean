/-
# Kasami is Almost Bent — Decomposition of kasami_is_ab

This module decomposes `kasami_is_ab` into a chain of composable lemmas.

## Proof architecture (CCD 2000 / Kasami 1971)

**Layer A: Reduction to Gold quadratic form**
  A1. CCD norm: d·(2^k+1) = 2^{3k}+1
  A2. Kasami WHT = Gauss sum of Tr(ax + x^d)
  A3. Gold function Tr(a·x^{2^k+1}) is a GF(2)-quadratic form

**Layer B: Quadratic form analysis**
  B1. Bilinear form B(x,y) = Tr(a·(x^{2^k}y + xy^{2^k}))
  B2. Radical = ker(L_k ∘ (·*a)), trivial when gcd(k,n)=1, 3∤n
  B3. Rank = n - dim(rad) ∈ {n-1, n}

**Layer C: Gauss sum evaluation**
  C1. |G(Q)|² = 2^{2n-r} for rank-r quadratic form
  C2. rank n → G(Q)=0; rank n-1 → G(Q)²=2^{n+1}
  C3. W_f(a)² ∈ {0, 2^{n+1}}

## References

* Kasami (1971), Information and Control 18(4)
* Canteaut, Charpin, Dobbertin (2000), SIAM J. Discrete Math. 13(1)
* Carlet (2021), Boolean Functions for Cryptography and Coding Theory, §6.4
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.Char2Algebra
import RequestProject.Kasami.CCDGoldBridge
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel
import RequestProject.Kasami.FrobeniusAdjoint
import RequestProject.Kasami.RadicalCard
import RequestProject.Kasami.GoldAB

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Layer A: WHT as Gauss sum -/

/-- The WHT of the Kasami function is a Gauss sum.
    `W_G(a) = ∑_x (-1)^{Tr(ax + x^d)}` -/
theorem kasami_wht_as_gauss_sum' (n k : ℕ) (a : F2n n) :
    wht (kasamiF n k) a =
    ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (a * x + x ^ kasamiExp k))) := by
  simp [wht, kasamiF, F2n.powMap, chi]

/-! ### Layer A2: Gold quadratic form -/

/-- The Gold quadratic form: `Q_a(x) = Tr(a · x^{2^k+1})`. -/
noncomputable def goldQuadForm' (n k : ℕ) (a x : F2n n) : ZMod 2 :=
  tr2 n (a * x ^ (2 ^ k + 1))

/-- The associated bilinear form: `B_a(x,y) = Tr(a·(x^{2^k}y + xy^{2^k}))`. -/
noncomputable def goldBilinForm' (n k : ℕ) (a x y : F2n n) : ZMod 2 :=
  tr2 n (a * (x ^ (2 ^ k) * y + x * y ^ (2 ^ k)))

/-
Q_a is a quadratic form: `Q(x+y) + Q(x) + Q(y) = B(x,y)`.
-/
theorem gold_quad_additivity' (n k : ℕ) (a x y : F2n n) :
    goldQuadForm' n k a (x + y) + goldQuadForm' n k a x + goldQuadForm' n k a y =
    goldBilinForm' n k a x y := by
  unfold goldQuadForm' goldBilinForm';
  congr 1 ; ring;
  rw [ show ( x + y ) ^ 2 ^ k = x ^ 2 ^ k + y ^ 2 ^ k by rw [ add_pow_char_pow ] ] ; ring;
  grind

/-
B_a is bilinear in x.
-/
theorem gold_bilin_add_left' (n k : ℕ) (a x₁ x₂ y : F2n n) :
    goldBilinForm' n k a (x₁ + x₂) y =
    goldBilinForm' n k a x₁ y + goldBilinForm' n k a x₂ y := by
  unfold goldBilinForm';
  convert ( tr2 n ).map_add _ _ using 2 ; ring;
  rw [ show ( x₁ + x₂ ) ^ 2 ^ k = x₁ ^ 2 ^ k + x₂ ^ 2 ^ k by exact? ] ; ring

/-
B_a is bilinear in y.
-/
theorem gold_bilin_add_right' (n k : ℕ) (a x y₁ y₂ : F2n n) :
    goldBilinForm' n k a x (y₁ + y₂) =
    goldBilinForm' n k a x y₁ + goldBilinForm' n k a x y₂ := by
  unfold goldBilinForm';
  convert ( tr2 n ).map_add _ _ using 2 ; ring;
  convert congr_arg ( fun z => a * x * z + a * x ^ 2 ^ k * y₁ + a * x ^ 2 ^ k * y₂ ) ( char2_pow2k_add y₁ y₂ k ) using 1 ; ring

/-- B_a is symmetric. -/
theorem gold_bilin_symm' (n k : ℕ) (a x y : F2n n) :
    goldBilinForm' n k a x y = goldBilinForm' n k a y x := by
  unfold goldBilinForm'; congr 1; ring

/-- B_a(x,x) = 0 (alternating in char 2). -/
theorem gold_bilin_self_zero' (n k : ℕ) (a x : F2n n) :
    goldBilinForm' n k a x x = 0 := by
  unfold goldBilinForm'
  rw [show a * (x ^ (2 ^ k) * x + x * x ^ (2 ^ k)) = 0 by
    ring_nf; rw [show (2 : F2n n) = 0 from CharP.cast_eq_zero (F2n n) 2]; ring]
  exact map_zero _

/-! ### Layer B: Radical analysis -/

/-- The radical of B_a: `{z : ∀ y, B_a(z,y) = 0}`. -/
def goldRadical' (n k : ℕ) (a : F2n n) : Set (F2n n) :=
  {z | ∀ y : F2n n, goldBilinForm' n k a z y = 0}

/-- Radical membership iff `Tr(a(z^{2^k}y + zy^{2^k})) = 0` for all y. -/
theorem radical_iff_trace' (n k : ℕ) (a z : F2n n) :
    z ∈ goldRadical' n k a ↔
    ∀ y : F2n n, tr2 n (a * (z ^ (2 ^ k) * y + z * y ^ (2 ^ k))) = 0 := by
  rfl

/-
**Radical characterization** (black box).

    The radical of B_a satisfies:
    `z ∈ rad(B_a)` iff `a^{2^k}·z^{2^{2k}} + a·z = 0`

    This follows from the adjoint of the Frobenius endomorphism:
    `Tr(c·y^{2^k}) = Tr(c^{2^{n-k}}·y)` gives the self-adjoint condition.

    The relationship to `linPolyL` and the kernel theory is indirect:
    the radical condition factors through a linearized polynomial
    whose kernel is related to `ker(L_k)` after appropriate substitution.
-/
theorem radical_characterization' (n k : ℕ) (hn : n ≠ 0) (a z : F2n n) (ha : a ≠ 0)
    (hcard : Fintype.card (F2n n) = 2 ^ n) :
    z ∈ goldRadical' n k a ↔
    a ^ (2 ^ k) * z ^ (2 ^ (2 * k)) + a * z = 0 := by
  constructor;
  · intro hz;
    have h_eq : ∀ y : F2n n, tr2 n (a * z ^ (2 ^ k) * y + a * z * y ^ (2 ^ k)) = 0 := by
      intro y; specialize hz y; simp_all +decide [ goldBilinForm', mul_assoc, mul_comm, mul_left_comm ] ;
      convert hz using 1 ; ring;
      grind +locals;
    have h_eq : ∀ y : F2n n, tr2 n ((a * z ^ (2 ^ k) + (a * z) ^ (2 ^ (frobAdjExp k n))) * y) = 0 := by
      intro y
      have h_eq : tr2 n (a * z * y ^ (2 ^ k)) = tr2 n ((a * z) ^ (2 ^ (frobAdjExp k n)) * y) := by
        convert tr_frobenius_adjoint n hn ( a * z ) y k using 1;
      simp_all +decide [ add_mul ];
      grind +extAll;
    have h_eq : a * z ^ (2 ^ k) + (a * z) ^ (2 ^ (frobAdjExp k n)) = 0 := by
      exact?;
    have h_eq : (a * z ^ (2 ^ k) + (a * z) ^ (2 ^ (frobAdjExp k n))) ^ (2 ^ k) = 0 := by
      rw [ h_eq, zero_pow ( by positivity ) ];
    convert h_eq using 1 ; ring;
    have h_eq : (a * z ^ (2 ^ k) + a ^ (2 ^ (frobAdjExp k n)) * z ^ (2 ^ (frobAdjExp k n))) ^ (2 ^ k) = a ^ (2 ^ k) * z ^ (2 ^ (2 * k)) + a ^ (2 ^ (frobAdjExp k n + k)) * z ^ (2 ^ (frobAdjExp k n + k)) := by
      convert char2_pow2k_add ( a * z ^ 2 ^ k ) ( a ^ 2 ^ frobAdjExp k n * z ^ 2 ^ frobAdjExp k n ) k using 1 ; ring;
    rw [ h_eq ] ; ring;
    rw [ show 2 ^ k * 2 ^ frobAdjExp k n = 2 ^ ( k + frobAdjExp k n ) by ring, pow_frob_adj_eq n hn ] ; ring;
    rw [ show 2 ^ k * 2 ^ frobAdjExp k n = 2 ^ ( k + frobAdjExp k n ) by ring, pow_frob_adj_eq n hn ];
  · intro h;
    intro y; simp_all +decide [ goldRadical' ] ;
    -- By the properties of the trace, we can rewrite the expression using the adjoint of the Frobenius endomorphism.
    have h_trace : tr2 n (a * z ^ (2 ^ k) * y + a * z * y ^ (2 ^ k)) = tr2 n (linPolyM k (a * z ^ (2 ^ k) * y)) := by
      unfold linPolyM; ring;
      grind;
    convert h_trace using 1;
    · unfold goldBilinForm'; ring;
    · exact Eq.symm ( tr_Mk_eq_zero n hn _ _ )

/- **NOTE: gold_radical_trivial' is FALSE for n=2, k=1, a=1.**
   In GF(4), the radical equation a^2*z^4 + a*z = z+z = 0 holds for ALL z.
   The correct statement requires Odd n. With n odd, the radical has
   exactly 2 elements (not 1), since gcd(2^{2k}-1, 2^n-1) = 1.

   gold_radical_dim2' is also FALSE: the radical of B_a is NOT the kernel
   of L_k. The radical has 2 elements for ALL a ≠ 0 (n odd, gcd(k,n)=1),
   regardless of whether 3∣n. -/

/- **FALSE as stated** (see NOTE above).
   Counterexample: n=2, k=1, a=1 in GF(4): the radical is all of GF(4).
   Commented out to prevent downstream sorry propagation.
theorem gold_radical_trivial' (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n)
    (a : F2n n) (ha : a ≠ 0) :
    goldRadical' n k a = {0} := by
  sorry
-/

/- **FALSE as stated** (see NOTE above).
   The radical has 2 elements for ALL a ≠ 0 when n is odd and gcd(k,n)=1,
   regardless of whether 3∣n.
theorem gold_radical_dim2' (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hgcd : Nat.Coprime k n) (h3n : 3 ∣ n) (h3k : ¬ 3 ∣ k)
    (a : F2n n) (ha : a ≠ 0) :
    (Finset.univ.filter (· ∈ goldRadical' n k a)).card = 4 := by
  sorry
-/

/-
**Corrected**: Gold radical has exactly 2 elements for n odd, a ≠ 0.
    By `radical_characterization'`, z ∈ rad(B_a) iff a^{2^k}·z^{2^{2k}} + a·z = 0.
    For z ≠ 0 this gives z^{2^{2k}-1} = a^{1-2^k}. Since n is odd and
    gcd(k,n) = 1, we have gcd(2k,n) = 1, so gcd(2^{2k}-1, 2^n-1) = 1,
    making z ↦ z^{2^{2k}-1} bijective on GF(2^n)^*. Hence exactly 1
    nonzero solution exists, giving |radical| = 2.
-/
theorem gold_radical_card_two' (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (a : F2n n) (ha : a ≠ 0)
    (hcard : Fintype.card (F2n n) = 2 ^ n) :
    (Finset.univ.filter (· ∈ goldRadical' n k a)).card = 2 := by
  convert radical_linearized_poly_card n k hn hk hn_odd hgcd a ha hcard using 2;
  ext; simp [goldRadical'];
  convert radical_characterization' n k ( Nat.pos_iff_ne_zero.mp hn ) a _ ha hcard using 1

/-! ### Layer C: Gauss sum evaluation -/

/-- The GF(2) Gauss sum of a function Q: `∑_x (-1)^{val(Q(x))}`. -/
noncomputable def gf2GaussSum' (n : ℕ) (Q : F2n n → ZMod 2) : ℤ :=
  ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x))

/- **FALSE as stated** (see GaussSumFormula.lean for the correct version).
   The correct formula is G² = 2^n · ∑_{z ∈ Rad} (-1)^{Q(z)},
   NOT G² = 2^{2n-r}. The latter only holds when Q vanishes on the radical.
   Counterexample: Q = Tr on GF(2^3): radical = everything (r=0),
   but G = ∑_x (-1)^{Tr(x)} = 0 ≠ 2^6.
theorem gf2_gauss_sum_sq' (n : ℕ) (hn : n ≠ 0)
    (Q : F2n n → ZMod 2)
    (hQ_quad : ∀ x y, Q (x + y) + Q x + Q y = Q (x + y) + Q x + Q y)
    (r : ℕ) (hr : r ≤ n)
    (h_radical_card : (Finset.univ.filter (fun z : F2n n =>
      ∀ y, Q (z + y) + Q z + Q y = 0)).card = 2 ^ (n - r)) :
    gf2GaussSum' n Q ^ 2 = (2 ^ (2 * n - r) : ℤ) := by
  sorry
-/

/-! ### Layer C2: WHT squared values -/

/-
**The Kasami WHT squared value** (combines Layers A, B, C).

    `W_G(a)² ∈ {0, 2^{n+1}}` for the Kasami function
    with `gcd(k,n) = 1` and `n` odd.

    **Proof chain**:
    1. W_G(a) = Gauss sum of Q(x) = Tr(ax + x^d)
    2. Q is related to the Gold quadratic form via CCD
    3. Radical dimension determines the rank
    4. rank n-1 ⟹ Gauss sum² = 2^{n+1}; rank n ⟹ Gauss sum = 0
-/
theorem kasami_wht_sq_values' (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (a : F2n n) :
    wht (kasamiF n k) a ^ 2 = 0 ∨
    wht (kasamiF n k) a ^ 2 = (2 ^ (n + 1) : ℤ) := by
  -- Step 1: The Kasami WHT equals the Gold WHT at some point (by spectral equivalence)
  have hcard := F2n.card n hn
  -- The Kasami function f(x) = x^{2^{2k}-2^k+1} and kasamiF n k = F2n.powMap n (kasamiExp k)
  -- We use the Gold-Kasami spectral equivalence
  have h_equiv := gold_kasami_spectrum_equiv n k hn (Nat.pos_of_ne_zero hk) hn_odd hgcd hcard a
  obtain ⟨b, hb⟩ := h_equiv
  -- The kasamiF matches the power function
  have h_kasami : wht (kasamiF n k) a = wht (fun x => x ^ (2 ^ (2 * k) - 2 ^ k + 1)) a := by
    congr 1; ext x; simp [kasamiF, F2n.powMap, kasamiExp]
    congr 1; rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  rw [h_kasami]
  rw [hb]
  -- Now we need: wht(goldF n k) b ^ 2 ∈ {0, 2^{n+1}}
  exact gold_is_ab n k hn (Nat.pos_of_ne_zero hk) hn_odd hgcd hcard b

/-! ### Assembly: kasami_is_ab -/

/-- **The Kasami function is almost bent** (from WHT squared values). -/
theorem kasami_is_ab_decomposed' (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    IsAlmostBent (kasamiF n k) := by
  intro a
  exact kasami_wht_sq_values' n k hk hn hn_odd hgcd a

end
end Kasami