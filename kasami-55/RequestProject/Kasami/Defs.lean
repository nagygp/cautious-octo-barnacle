/-
  Kasami Definitions
  ==================
  Core arithmetic definitions and properties for the Kasami exponent and
  related objects. This file is the "source of truth" for the mathematical
  objects used throughout the Kasami spectrum proof.
-/
import Mathlib

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000

/-! ## Kasami Exponent -/

/-- The Kasami exponent: d = 2^(2k) - 2^k + 1 -/
noncomputable def kasamiExponent (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Kasami exponent equals 2^(2k) - 2^k + 1.
    We need k ≥ 1 to ensure 2^(2k) ≥ 2^k. -/
lemma kasamiExponent_eq (k : ℕ) (hk : k ≥ 1) :
    kasamiExponent k = 2 ^ (2 * k) - 2 ^ k + 1 := by
  rfl

/-
2^(2k) ≥ 2^k for all k
-/
lemma pow_two_2k_ge_pow_two_k (k : ℕ) : 2 ^ (2 * k) ≥ 2 ^ k := by
  exact pow_le_pow_right₀ ( by decide ) ( by linarith )

/-
The Kasami exponent is positive for k ≥ 1
-/
lemma kasamiExponent_pos (k : ℕ) (hk : k ≥ 1) : kasamiExponent k > 0 := by
  exact Nat.succ_pos _

/-! ## Kasami Exponent Factoring

The key identity: x^d - 1 factors in a specific way related to the
linearized polynomial L_k. Specifically, for d = 2^(2k) - 2^k + 1:

  x^(2^(2k)) + x^(2^k) + x = x * (x^(2^(2k)-1) + x^(2^k - 1) + 1)

This connects x^d to the linearized polynomial L_k(x) = x^(2^(2k)) + x^(2^k) + x.
-/

/-! ## Frobenius Iterates in Characteristic 2

In a field F of characteristic 2, the k-th Frobenius iterate sends x ↦ x^(2^k).
Key properties:
- It is a field automorphism (ring homomorphism).
- frob^n = id when |F| = 2^n.
- Composition: frob^a ∘ frob^b = frob^(a+b).
-/

section FrobeniusProperties

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The k-th Frobenius iterate: x ↦ x^(2^k) -/
noncomputable def frobIter (k : ℕ) : F →+* F :=
  (frobenius F 2) ^ k

lemma frobIter_apply (k : ℕ) (x : F) :
    frobIter k x = x ^ (2 ^ k) := by
  induction' k with k ih;
  · simp +decide [ frobIter ];
  · convert congr_arg ( fun y => y ^ 2 ) ih using 1 <;> ring;
    unfold frobIter ;
    simp +decide [ pow_add, frobenius_def ]

/-
Frobenius composition: frob^a ∘ frob^b = frob^(a+b)
-/
lemma frobIter_comp (a b : ℕ) :
    (frobIter (a + b) : F →+* F) = (frobIter a).comp (frobIter b) := by
  unfold frobIter;
  simp +decide [ pow_add, RingHom.ext_iff ]

/-
The n-th Frobenius iterate is identity when |F| = 2^n
-/
lemma frobIter_card_eq_id (n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    (frobIter n : F →+* F) = RingHom.id F := by
  ext x;
  -- By definition of $frobIter$, we know that $(frobIter n) x = x^{2^n}$.
  have h_frobIter : (frobIter n) x = x ^ (2 ^ n) := by
    exact?;
  rw [ h_frobIter, ← hcard, FiniteField.pow_card ];
  rfl

end FrobeniusProperties

/-! ## Linearized Polynomial L_k

  L_k(z) = z^(2^(2k)) + z^(2^k) + z

This is a linearized polynomial over F_{2^n}, meaning L_k(x + y) = L_k(x) + L_k(y).
Its kernel plays a central role: rad(Q_a) = ker(L_a) where L_a(z) = a·L_k(z/a)
appropriately defined.
-/

section LinearizedPoly

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The linearized polynomial L_k(z) = z^(2^(2k)) + z^(2^k) + z -/
noncomputable def linPolyL (k : ℕ) (z : F) : F :=
  z ^ (2 ^ (2 * k)) + z ^ (2 ^ k) + z

/-
L_k is additive (linearized polynomial property in char 2)
-/
lemma linPolyL_add (k : ℕ) (x y : F) :
    linPolyL k (x + y) = linPolyL k x + linPolyL k y := by
  unfold linPolyL;
  simp +decide [ add_pow_char_pow, add_assoc, add_left_comm ]

/-
L_k(0) = 0
-/
lemma linPolyL_zero (k : ℕ) : linPolyL k (0 : F) = 0 := by
  unfold linPolyL; norm_num;

/-! ## The "a-twisted" linearized map

For a ∈ F*, we define L_a(z) = a^(2^(2k)) · z^(2^(2k)) + a^(2^k) · z^(2^k) + a · z.
This arises from expanding the polar form of Q_a(x) = Tr(a · x^d).
-/

/-- The a-twisted linearized polynomial -/
noncomputable def linPolyLA (k : ℕ) (a z : F) : F :=
  a ^ (2 ^ (2 * k)) * z ^ (2 ^ (2 * k)) +
  a ^ (2 ^ k) * z ^ (2 ^ k) +
  a * z

/-
L_a is additive in z (for fixed a)
-/
lemma linPolyLA_add (k : ℕ) (a x y : F) :
    linPolyLA k a (x + y) = linPolyLA k a x + linPolyLA k a y := by
  unfold linPolyLA;
  simp +decide [ add_pow_char_pow, mul_add, add_assoc, add_left_comm, add_comm ]

/-
L_a(0) = 0
-/
lemma linPolyLA_zero (k : ℕ) (a : F) : linPolyLA k a (0 : F) = 0 := by
  unfold linPolyLA; ring;

end LinearizedPoly

/-! ## Trace and Quadratic Form

The quadratic form Q_a(x) = Tr(a · x^d) where Tr is the absolute trace
from F_{2^n} to F_2, and d is the Kasami exponent.

The associated bilinear (polar) form is:
  B_a(x, y) = Q_a(x + y) + Q_a(x) + Q_a(y) = Tr(a · ((x+y)^d + x^d + y^d))

In characteristic 2, this is a symmetric bilinear form (since + = −).
-/

section QuadraticForm

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The absolute trace Tr : F → F_2, viewed as landing in F.
    Tr(x) = x + x^2 + x^(2^2) + ... + x^(2^(n-1)) where |F| = 2^n -/
noncomputable def absoluteTrace (n : ℕ) (x : F) : F :=
  ∑ i ∈ range n, x ^ (2 ^ i)

/-
The trace is additive
-/
lemma absoluteTrace_add (n : ℕ) (x y : F) :
    absoluteTrace n (x + y) = absoluteTrace n x + absoluteTrace n y := by
  unfold absoluteTrace;
  simp +decide [ add_pow_char_pow, Finset.sum_add_distrib ]

/-
Trace is Frobenius-invariant: Tr(x^2) = Tr(x) (char 2)
-/
lemma trace_frobenius_invariant (n : ℕ) (x : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) :
    absoluteTrace n (x ^ 2) = absoluteTrace n x := by
  unfold absoluteTrace;
  conv_rhs => rw [ ← Nat.sub_add_cancel hn, Finset.sum_range_succ' ] ;
  cases n <;> simp_all +decide [ pow_succ', pow_mul, Finset.sum_range_succ ];
  have := FiniteField.pow_card x; simp_all +decide [ pow_succ', pow_mul ] ;

/-
More generally, Tr(x^(2^k)) = Tr(x)
-/
lemma trace_frobIter_invariant (n k : ℕ) (x : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) :
    absoluteTrace n (x ^ (2 ^ k)) = absoluteTrace n x := by
  induction' k with k ih;
  · lia;
  · have := trace_frobenius_invariant n ( x ^ 2 ^ k ) hcard hn; simp_all +decide [ pow_succ, pow_mul ] ;

/-
The trace takes values in {0, 1} (the prime field F_2)
-/
lemma trace_sq_eq_trace (n : ℕ) (x : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) :
    absoluteTrace n x ^ 2 = absoluteTrace n x := by
  -- By definition of absolute trace, we have:
  have h_trace_def : absoluteTrace n x ^ 2 = ∑ i ∈ Finset.range n, x ^ (2 ^ (i + 1)) := by
    unfold absoluteTrace; simp +decide [ pow_succ, pow_mul, Finset.sum_mul _ _ _ ] ;
    simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, pow_mul ];
    exact?;
  have := trace_frobIter_invariant n 1 x hcard hn; simp_all +decide [ pow_succ, pow_mul ] ;
  convert this using 1;
  exact Finset.sum_congr rfl fun _ _ => by ring;

/-
Non-degeneracy of trace: if Tr(x·y) = 0 for all y, then x = 0
-/
lemma trace_nondegenerate (n : ℕ) (x : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) :
    (∀ y : F, absoluteTrace n (x * y) = 0) → x = 0 := by
  contrapose!;
  intro hx_nonzero
  obtain ⟨z, hz⟩ : ∃ z : F, absoluteTrace n z ≠ 0 := by
    by_contra h_contra
    push_neg at h_contra
    have h_trivial : ∀ z : F, absoluteTrace n z = 0 := by
      exact h_contra;
    have h_trivial : ∏ z : F, (Polynomial.X - Polynomial.C z) ∣ ∑ i ∈ Finset.range n, Polynomial.X ^ (2 ^ i) := by
      refine' Finset.prod_dvd_of_coprime _ _;
      · intros z hz w hw hzw; exact Polynomial.irreducible_X_sub_C _ |> fun h => h.coprime_iff_not_dvd.mpr fun h' => hzw <| by simpa [ sub_eq_iff_eq_add ] using Polynomial.dvd_iff_isRoot.mp h';
      · exact fun z _ => Polynomial.dvd_iff_isRoot.mpr ( by simpa [ Polynomial.eval_finset_sum ] using h_trivial z );
    have := Polynomial.natDegree_le_of_dvd h_trivial;
    rw [ Polynomial.natDegree_sum_eq_of_disjoint ] at this <;> simp_all +decide [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
    · exact absurd ( this ( by exact ne_of_apply_ne ( fun p => p.coeff ( 2 ^ ( n - 1 ) ) ) ( by cases n <;> simp_all +decide [ Polynomial.coeff_X_pow ] ) ) ) ( by rintro ⟨ b, hb, hb' ⟩ ; exact not_le_of_gt ( pow_lt_pow_right₀ ( by decide ) hb ) hb' );
    · simp +decide [ Set.Pairwise ];
  exact ⟨ z / x, by simpa [ mul_div_cancel₀ _ hx_nonzero ] using hz ⟩

end QuadraticForm