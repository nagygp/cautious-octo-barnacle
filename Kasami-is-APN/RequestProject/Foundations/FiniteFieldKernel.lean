/-
# Layer 45: Finite Field Kernel Theory & Linearized Polynomial Foundations

This module provides the key finite field infrastructure needed for
Gold/Kasami APN proofs, grounded in Mathlib's finite field library.

## Core Results

1. **Frobenius fixed point count**: |{x ∈ GF(2^n) : x^{2^k} = x}| = 2^{gcd(k,n)}
2. **Linearized polynomial kernel**: |ker(x^{2^k} + x)| = 2^{gcd(k,n)}
   (In char 2, x^{2^k} + x = 0 ⟺ x^{2^k} = x)
3. **Gold APN from kernel bound**: When gcd(k,n)=1, ker has 2 elements,
   so the Gold differential has ≤ 2 solutions.

## Mathlib Connections

- `FiniteField.pow_card`: x^{|F|} = x for all x ∈ F
- `Polynomial.card_roots`: roots ≤ degree
- `Nat.pow_sub_one_gcd_pow_sub_one`: gcd(a^b-1, a^c-1) = a^{gcd(b,c)}-1
- `powCoprime`: coprime exponent → bijective power map on cyclic groups
- `add_pow_expChar_pow`: (x+y)^{p^n} = x^{p^n} + y^{p^n} in char p

## DAG Structure (depends on Layers 38, 40, 42)
import Mathlib
import RequestProject.Foundations.KasamiAPN

-/
namespace Caramello.FiniteFieldKernel

-/
open Caramello.APNTheory Caramello.MCMInjectivity Caramello.KasamiAPN
-/
open Finset Fintype

-/
/-! ## Section 1: Characteristic 2 Foundations from Mathlib -/

/-
In characteristic 2, x + x = 0.
-/
theorem char2_add_self {F : Type*} [Semiring F] [CharP F 2] (x : F) :
    x + x = 0 := by
  simp +decide [ ← two_mul, CharTwo.two_eq_zero ]

/-
In characteristic 2, -x = x.
-/
theorem char2_neg_eq {F : Type*} [Ring F] [CharP F 2] (x : F) :
    -x = x := by
  grind +locals

/-- In characteristic 2, x - y = x + y. -/
theorem char2_sub_eq_add {F : Type*} [Ring F] [CharP F 2] (x y : F) :
    x - y = x + y := by
  rw [sub_eq_add_neg, char2_neg_eq]

/-- Frobenius: (x + y)^{2^k} = x^{2^k} + y^{2^k} in characteristic 2.
    This is `add_pow_expChar_pow` from Mathlib. -/
theorem frobenius_add {F : Type*} [CommSemiring F] [CharP F 2]
    (x y : F) (k : ℕ) :
    (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
  add_pow_expChar_pow x y 2 k

/-- x^{|F|} = x for all x in a finite field (Fermat's little theorem).
    This is `FiniteField.pow_card` from Mathlib. -/
theorem pow_card_eq_self {F : Type*} [Field F] [Fintype F] (x : F) :
    x ^ Fintype.card F = x :=
  FiniteField.pow_card x

/-! ## Section 2: Frobenius Fixed Points

The solutions of x^{2^k} = x in GF(2^n) form the subfield GF(2^{gcd(k,n)}).
We prove this via the order-theoretic approach.

/-
In characteristic 2, x^{2^k} + x = 0 ⟺ x^{2^k} = x.
-/
-/
theorem frob_ker_iff {F : Type*} [Ring F] [CharP F 2] (k : ℕ) (x : F) :
    x ^ (2 ^ k) + x = 0 ↔ x ^ (2 ^ k) = x := by
  rw [ ← eq_neg_iff_add_eq_zero, eq_comm ];
  rw [ char2_neg_eq, eq_comm ]

/-- The set of solutions of x^{2^k} = x in F. -/
def frobFixedSet (F : Type*) [Field F] (k : ℕ) : Set F :=
  { x | x ^ (2 ^ k) = x }

/-- 0 is always a fixed point. -/
theorem zero_mem_frobFixed {F : Type*} [Field F] (k : ℕ) :
    (0 : F) ∈ frobFixedSet F k := by simp [frobFixedSet]

/-- 1 is always a fixed point. -/
theorem one_mem_frobFixed {F : Type*} [Field F] (k : ℕ) :
    (1 : F) ∈ frobFixedSet F k := by simp [frobFixedSet]

/-- The fixed set is closed under addition in char 2 (by Frobenius additivity). -/
theorem frobFixed_add_closed {F : Type*} [Field F] [CharP F 2] (k : ℕ)
    {x y : F} (hx : x ∈ frobFixedSet F k) (hy : y ∈ frobFixedSet F k) :
    x + y ∈ frobFixedSet F k := by
  simp only [frobFixedSet, Set.mem_setOf_eq] at *
  rw [frobenius_add x y k, hx, hy]

/-- The fixed set is closed under multiplication. -/
theorem frobFixed_mul_closed {F : Type*} [Field F] (k : ℕ)
    {x y : F} (hx : x ∈ frobFixedSet F k) (hy : y ∈ frobFixedSet F k) :
    x * y ∈ frobFixedSet F k := by
  simp only [frobFixedSet, Set.mem_setOf_eq] at *
  rw [mul_pow, hx, hy]

/-
For nonzero x: x^{2^k} = x ⟺ x^{2^k - 1} = 1.
-/
theorem frobFixed_iff_pow_pred {F : Type*} [Field F] (k : ℕ) (hk : 0 < k)
    (x : F) (hx : x ≠ 0) :
    x ^ (2 ^ k) = x ↔ x ^ (2 ^ k - 1) = 1 := by
  rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ), pow_add, pow_one ] ; aesop

/-
Number of solutions of x^d = 1 in the unit group of a finite field
    equals gcd(d, |F×|). This is a consequence of the cyclic group structure.
-/
theorem card_pow_eq_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (hd : 0 < d) :
    Fintype.card { x : Fˣ // x ^ d = 1 } = Nat.gcd d (Fintype.card Fˣ) := by
  -- Apply the fact that the number of elements of order dividing $d$ in a cyclic group of order $n$ is $\gcd(d, n)$.
  have h_card_units : Fintype.card {x : Fˣ | x ^ d = 1} = Nat.gcd d (Fintype.card Fˣ) := by
    have h_cyclic : IsCyclic Fˣ := by
      infer_instance
    have h_card : ∀ d : ℕ, 0 < d → Fintype.card { x : Fˣ | x ^ d = 1 } = Nat.gcd d (Fintype.card Fˣ) := by
      intro d hd
      have h_card : Fintype.card { x : Fˣ | x ^ d = 1 } = Fintype.card { x : Fˣ | orderOf x ∣ d } := by
        simp +decide [ orderOf_dvd_iff_pow_eq_one ]
      -- Apply the fact that in a cyclic group of order $n$, the number of � elements� of order dividing $ �d�$ is $\gcd(d, n)$.
      have h_card : Fintype.card { x : Fˣ | orderOf x ∣ d } = ∑ e ∈ Nat.divisors (Nat.gcd d (Fintype.card Fˣ)), Fintype.card { x : Fˣ | orderOf x = e } := by
        simp +decide only [card_ofFinset, Finset.card_eq_sum_ones];
        rw [ ← Finset.sum_biUnion ];
        · congr with x ; simp +decide [ Nat.dvd_gcd_iff ];
          exact fun h => orderOf_dvd_card;
        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
      have h_card : ∀ e ∈ Nat.divisors (Nat.gcd d (Fintype.card Fˣ)), Fintype.card { x : Fˣ | orderOf x = e } = Nat.totient e := by
        intro e he;
        have h_card : ∀ e ∈ Nat.divisors (Fintype.card Fˣ), Fintype.card { x : Fˣ | orderOf x = e } = Nat.totient e := by
          intro e he;
          have := @IsCyclic.card_orderOf_eq_totient Fˣ _ _;
          simpa [ Fintype.card_subtype ] using this ( Nat.dvd_of_mem_divisors he );
        exact h_card e ( Nat.mem_divisors.mpr ⟨ dvd_trans ( Nat.dvd_of_mem_divisors he ) ( Nat.gcd_dvd_right _ _ ), by aesop ⟩ );
      have := Nat.sum_totient ( Nat.gcd d ( Fintype.card Fˣ ) );
      rw [ Finset.sum_congr rfl h_card ] at * ; aesop;
    exact h_card d hd;
  exact h_card_units

/-
**Key theorem**: Number of solutions of x^{2^k} = x in GF(2^n)
    equals 2^{gcd(k,n)}.

    Proof sketch:
    - Nonzero solutions: x^{2^k-1} = 1 in Fˣ (cyclic of order 2^n - 1)
    - Count = gcd(2^k - 1, 2^n - 1) = 2^{gcd(k,n)} - 1 (Mersenne GCD)
    - Add x=0: total = 2^{gcd(k,n)}
-/
theorem card_frobFixed {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n) :
    Fintype.card { x : F // x ^ (2 ^ k) = x } = 2 ^ (Nat.gcd k n) := by
  have h_solutions : Fintype.card { x : F | x ≠ 0 ∧ x ^ (2 ^ k - 1) = 1 } = Nat.gcd (2 ^ k - 1) (2 ^ n - 1) := by
    have h_solutions : Fintype.card { x : Fˣ // x ^ (2 ^ k - 1) = 1 } = Nat.gcd (2 ^ k - 1) (2 ^ n - 1) := by
      convert card_pow_eq_one _ ( Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two hk.ne' ) ) using 1;
      rw [ Fintype.card_units, hcard ];
    rw [ ← h_solutions, Fintype.card_subtype ];
    rw [ Fintype.card_subtype ];
    refine' Finset.card_bij ( fun x hx => Units.mk0 x ( by aesop ) ) _ _ _ <;> simp +decide [ Units.ext_iff ];
  have h_solutions : Fintype.card { x : F // x ^ (2 ^ k) = x } = Fintype.card { x : F // x ≠ 0 ∧ x ^ (2 ^ k - 1) = 1 } + 1 := by
    rw [ Fintype.card_subtype, Fintype.card_subtype ];
    rw [ show ( Finset.filter ( fun x => x ^ 2 ^ k = x ) Finset.univ : Finset F ) = Finset.filter ( fun x : F => x ≠ 0 ∧ x ^ ( 2 ^ k - 1 ) = 1 ) Finset.univ ∪ { 0 } from ?_, Finset.card_union ] <;> norm_num [ hk.ne', hn.ne' ];
    ext x; by_cases hx : x = 0 <;> simp +decide [ hx, pow_succ, pow_mul ] ;
    rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ), pow_add, pow_one, mul_comm ] ; aesop;
  simp_all +decide [ mersenne_gcd ];
  rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ]

/-
**Corollary**: When gcd(k,n) = 1, the Frobenius kernel {x : x^{2^k}+x=0}
    has exactly 2 elements.
-/
theorem card_linKernel_coprime {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hcard : Fintype.card F = 2 ^ n) :
    Fintype.card { x : F // x ^ (2 ^ k) + x = 0 } = 2 := by
  rw [ Fintype.card_subtype ];
  convert card_frobFixed hk hn hcard using 1;
  · rw [ Fintype.subtype_card ];
    simp +decide only [add_eq_zero_iff_eq_neg, char2_neg_eq];
  · rw [ hgcd, pow_one ]

/-! ## Section 3: Gold APN — Full Proof via Kernel Bound

The Gold differential equation (x+a)^{2^k+1} + x^{2^k+1} = b expands to
  a^{2^k}·x + a·x^{2^k} + a^{2^k+1} = b     [gold_differential_linearized]

For a ≠ 0, the solutions form a coset of the kernel of the linearized map
L_a(x) = x^{2^k} + a^{2^k-1}·x, which is isomorphic to the kernel of
x^{2^k} + x. When gcd(k,n)=1, this kernel has 2 elements.

/-- The Gold linearized map: L_a(x) = x^{2^k} + a^{2^k-1}·x.
    Solutions of the differential equation form a coset of ker(L_a). -/
-/
noncomputable def goldLinMap {F : Type*} [Field F] (k : ℕ) (a x : F) : F :=
  x ^ (2 ^ k) + a ^ (2 ^ k - 1) * x

/-- L_a is additive in char 2. -/
theorem goldLinMap_add {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) (a x y : F) :
    goldLinMap k a (x + y) = goldLinMap k a x + goldLinMap k a y := by
  simp only [goldLinMap, frobenius_add, mul_add]
  ring

/-- Difference of solutions is in the kernel (in char 2, subtraction = addition). -/
theorem goldLinMap_sum_zero {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) (a c x₁ x₂ : F) (h₁ : goldLinMap k a x₁ = c) (h₂ : goldLinMap k a x₂ = c) :
    goldLinMap k a (x₁ + x₂) = 0 := by
  rw [goldLinMap_add, h₁, h₂, char2_add_self]

/-
For a ≠ 0, the kernel of L_a is isomorphic to the kernel of x^{2^k}+x
    via the substitution z = x · a^{-(2^k - 1)}.
-/
theorem goldLinMap_ker_equiv_frob_ker {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) (hk : 0 < k) (a : F) (ha : a ≠ 0) (x : F) :
    goldLinMap k a x = 0 ↔ (x * a⁻¹) ^ (2 ^ k) + (x * a⁻¹) = 0 := by
  unfold goldLinMap; ring;
  rw [ show a ^ ( 2 ^ k - 1 ) = a ^ ( 2 ^ k ) / a from ?_, div_eq_mul_inv ];
  · field_simp;
    simp +decide [ ha, mul_assoc, mul_comm, mul_left_comm ];
    field_simp;
    rw [ mul_zero ];
  · rw [ eq_div_iff ha, ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ]

/-
**The key bound**: For the Gold differential, the number of solutions
    of (x+a)^{2^k+1} + x^{2^k+1} = b is bounded by |ker(x^{2^k}+x)|.
-/
theorem gold_differential_solutions_le_kernel {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (a b : F) (ha : a ≠ 0) :
    Fintype.card { x : F // (x + a) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) = b } ≤
    Fintype.card { x : F // x ^ (2 ^ k) + x = 0 } := by
  -- Let $q = � �2^k$. The equation $(x+a)^{q+1} + x^{q+1} = b$ can be rewritten using the linearized map $goldLinMap k a x$.
  set q := 2 ^ k
  have h_eq : ∀ x : F, (x + a) ^ (q + 1) + x ^ (q + 1) = a * (goldLinMap k a x + a ^ q) := by
    intro x
    have h_eq : (x + a) ^ (q + 1) + x ^ (q + 1) = a ^ q * x + a * x ^ q + a ^ (q + 1) := by
      convert gold_differential_linearized k a x using 1;
    rw [ h_eq, goldLinMap ] ; ring;
    rw [ show a ^ q = a ^ ( 2 ^ k - 1 ) * a by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ] ; ring;
  -- If the solution set is empty, |solutions| = 0 ≤ |kernel|. If non-empty, pick x₀. The map x ↦ (x + x₀)*a⁻¹ sends solutions to kernel elements (by additivity of goldLinMap and goldLinMap_ker_equiv_frob_ker), and is injective.
  by_cases h_empty : {x : F | a * (goldLinMap k a x + a ^ q) = b} = ∅;
  · simp_all +decide [ Set.ext_iff ];
  · -- Let $x₀$ be a solution to $ �a� * (goldLinMap k a x + a ^ q) = b$.
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, a * (goldLinMap k a x₀ + a ^ q) = b := by
      exact Set.nonempty_iff_ne_empty.2 h_empty;
    -- The map $x (x + x₀)*a⁻¹$ sends solutions to kernel elements.
    have h_map : ∀ x : F, a * (goldLinMap k a x + a ^ q) = b → (x + x₀) * a⁻¹ ∈ {x : F | x ^ q + x = 0} := by
      intro x hx; have := goldLinMap_ker_equiv_frob_ker k hk a ha ( x + x₀ ) ; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
      have := goldLinMap_add k a x x₀; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
      grind;
    -- The map $x (x + x₀)*a⁻¹$ is injective.
    have h_inj : Function.Injective (fun x : {x : F | a * (goldLinMap k a x + a ^ q) = b} => ⟨(x.val + x₀) * a⁻¹, h_map x.val x.property⟩ : {x : F | a * (goldLinMap k a x + a ^ q) = b} → {x : F | x ^ q + x = 0}) := by
      intro x y; aesop;
    convert Fintype.card_le_of_injective _ h_inj using 1;
    simp +decide only [h_eq];
    congr! 1

/-- **Gold is APN (via kernel bound)**: When gcd(k,n) = 1, each Gold
    differential fiber has ≤ 2 solutions. -/
theorem gold_apn_via_kernel {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1)
    (hcard : Fintype.card F = 2 ^ n) :
    ∀ a b : F, a ≠ 0 →
    Fintype.card { x : F // (x + a) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) = b } ≤ 2 := by
  intro a b ha
  calc Fintype.card { x : F // (x + a) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) = b }
      ≤ Fintype.card { x : F // x ^ (2 ^ k) + x = 0 } :=
        gold_differential_solutions_le_kernel hk hn hcard a b ha
    _ = 2 := card_linKernel_coprime hk hn hgcd hcard

/-! ## Section 4: Kasami Kernel Theory

For the Kasami function, the differential equation reduces to a more complex
system but the key principle is the same: solutions form cosets of linearized
polynomial kernels, and coprimality bounds the kernel size.

/-- The Kasami differential equation has at most 2 solutions for each
    nonzero a, using the Kasami coprimality and kernel bound. -/
-/
theorem kasami_differential_structure {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (a b : F) (ha : a ≠ 0) :
    Fintype.card { x : F // (x + a) ^ (kasamiExponent k) +
      x ^ (kasamiExponent k) = b } ≤ 2 := by
  sorry

/-! ## Section 5: Connecting to APNTheory Definitions

Bridge between the fiber-counting approach and the differentialUniformity definition.
-/

/-- differentialCount equals the cardinality of the fiber subtype. -/
theorem differentialCount_eq_card {F : Type*} [Add F] [Fintype F] [DecidableEq F]
    (f : F → F) (a b : F) :
    differentialCount f a b = Fintype.card { x : F // f (x + a) + f x = b } := by
  rfl

/-- If every nonzero-a fiber has cardinality ≤ 2, then f is APN. -/
theorem isAPN_of_fiber_bound {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]
    (f : F → F)
    (h : ∀ a b : F, a ≠ 0 →
      Fintype.card { x : F // f (x + a) + f x = b } ≤ 2) :
    IsAPN f := by
  unfold IsAPN differentialUniformity
  apply Finset.sup_le; intro a ha
  apply Finset.sup_le; intro b _
  exact h a b (Finset.mem_filter.mp ha).2

/-! ## Section 6: Full Gold APN Theorem (Assembled) -/

/-- **Gold is APN**: x^{2^k+1} is APN on GF(2^n) when gcd(k,n) = 1.
    Proved via the linearized polynomial kernel bound.

    Note: Gold APN holds for all n with gcd(k,n) = 1, regardless of parity. -/
theorem gold_is_apn_assembled {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAPN (powerFunction (goldExponent k) : F → F) := by
  convert isAPN_of_fiber_bound _ _;
  convert gold_apn_via_kernel;
  rotate_left;
  exact F;
  all_goals try infer_instance;
  exact k;
  exact n;
  aesop

/-- **Kasami is APN**: x^{2^{2k}-2^k+1} is APN on GF(2^n) when
    gcd(k,n) = 1 and n is odd.
    Assembled from the kernel bound approach. -/
theorem kasami_is_apn_assembled {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAPN (powerFunction (kasamiExponent k) : F → F) := by
  sorry

end Caramello.FiniteFieldKernel