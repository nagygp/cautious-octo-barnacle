import Mathlib
import RequestProject.KasamiDefs

/-!
# Kasami AB — Phase 1: Linearized Polynomial Foundations

## Main Results

* `linearized_kernel_subset_cube` — ker(L_k) ⊆ ker(frob_{3k} − id),
  i.e., if L_k(z) = 0 then z^{2^{3k}} = z.
* `mk_ker_eq_F2` — Under gcd(3k, n) = 1, ker(L_k) ⊆ {0, 1}.
-/

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-! ### Key identity: applying Frobenius to L_k equation -/

section KerLSubset

variable {F : Type*} [CommRing F] [CharP F 2]

/-- If L_k(z) = 0, then z^{2^{2k}} = z^{2^k} + z. -/
private lemma kerL_rearrange {k : ℕ} {z : F} (hz : z ∈ kerL k) :
    frobIter (2 * k) z = frobIter k z + z := by
  unfold kerL at hz;
  unfold frobIter at *; have := hz; simp_all +decide [ linPolyL ] ;
  grind

/-- **Phase 1, Lemma 1.** If L_k(z) = 0 then z^{2^{3k}} = z. -/
lemma linearized_kernel_subset_cube {k : ℕ} {z : F} (hz : z ∈ kerL k) :
    z ∈ frobFixedPts (3 * k) := by
  have h1 : frobIter k (frobIter (2*k) z) = frobIter k (frobIter k z + z) := by
    rw [ kerL_rearrange hz ]
  have h2 : frobIter k (frobIter (2*k) z) = frobIter (k + 2*k) z ∧ frobIter k (frobIter k z + z) = frobIter (k+k) z + frobIter k z := by
    exact ⟨ frobIter_comp _ _ _, by rw [ frobIter_add, frobIter_comp ] ⟩
  simp_all +decide [ show 3 * k = k + 2 * k by ring ]
  have h3 : frobIter (k + k) z = frobIter k z + z := by
    convert kerL_rearrange hz using 1
    rw [ two_mul ]
  simp_all +decide [ frobFixedPts ]
  grind

/-- `kerL k ⊆ frobFixedPts (3 * k)` as a set inclusion. -/
lemma kerL_subset_frobFixed (k : ℕ) : (kerL k : Set F) ⊆ frobFixedPts (3 * k) :=
  fun _ hz => linearized_kernel_subset_cube hz

end KerLSubset

/-! ### Helper lemmas for bounding the kernel -/

section FieldHelpers

variable {F : Type*} [Field F] [CharP F 2]

/-
In any field, z² = z implies z = 0 or z = 1.
-/
private lemma sq_eq_self_imp (z : F) (h : z * z = z) :
    z = 0 ∨ z = 1 := by
  by_cases hz : z = 0 <;> simp_all +decide

/-
z^{2^m} = z implies z^{2^{a*m}} = z for all a (by iterating the Frobenius).
-/
omit [CharP F 2] in
private lemma pow_iterate_of_fixed
    {m : ℕ} {z : F} (hz : z ^ (2 ^ m) = z) (a : ℕ) :
    z ^ (2 ^ (a * m)) = z := by
  induction a <;> simp_all +decide [ Nat.succ_mul, pow_add ];
  rw [ pow_mul, ‹z ^ 2 ^ ( _ * m ) = z›, hz ]

/-
In a finite field of char 2 with |F| = 2^n, every element satisfies z^{2^n} = z.
-/
omit [CharP F 2] in
private lemma pow_card_fixed [Fintype F]
    {n : ℕ} (_hn : n ≠ 0) (hcard : Nat.card F = 2 ^ n) (z : F) :
    z ^ (2 ^ n) = z := by
  convert FiniteField.pow_card z;
  rw [ ← hcard, Nat.card_eq_fintype_card ]

/-
If z^{2^m} = z and z^{2^n} = z in a field of char 2,
    then z^{2^{gcd(m,n)}} = z.
-/
omit [CharP F 2] in
private lemma pow_gcd_fixed
    {m n : ℕ} {z : F} (hm : z ^ (2 ^ m) = z) (hn : z ^ (2 ^ n) = z) :
    z ^ (2 ^ (Nat.gcd m n)) = z := by
  have h_ind : ∀ (m n : ℕ), z ^ 2 ^ m = z → z ^ 2 ^ n = z → z ^ 2 ^ (Nat.gcd m n) = z := by
    intros m n hm hn
    induction' n using Nat.strong_induction_on with n ih generalizing m;
    rcases lt_trichotomy n 0 with hn' | rfl | hn' <;> simp_all +decide [ Nat.gcd_comm ];
    rw [ ← Nat.mod_add_div m n ] at *; simp_all +decide [ pow_add, pow_mul ] ;
    rw [ Nat.gcd_comm, ih _ ( Nat.mod_lt _ hn' ) _ hn ];
    have h_ind : ∀ k : ℕ, (z ^ 2 ^ (m % n)) ^ (2 ^ n) ^ k = z ^ 2 ^ (m % n) := by
      intro k; induction k <;> simp_all +decide [ pow_succ, pow_mul ] ;
      rw [ pow_right_comm, hn ];
    rw [ ← h_ind ( m / n ), hm ];
  exact h_ind m n hm hn

end FieldHelpers

/-! ### Bounding the kernel size -/

section KerBound

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- In a finite field of order 2^n, if z^{2^m} = z and gcd(m,n) = 1,
    then z ∈ {0, 1}. -/
lemma frobFixed_subset_gf2 {n : ℕ} (hn : n ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    {m : ℕ} (_hm : m ≠ 0) (hgcd : Nat.gcd m n = 1) :
    frobFixedPts (F := F) m ⊆ gf2Set := by
  intro z hz
  simp only [frobFixedPts, Set.mem_setOf_eq, frobIter] at hz
  have hzn : z ^ (2 ^ n) = z := pow_card_fixed hn hcard z
  have hgcd_fixed : z ^ (2 ^ (Nat.gcd m n)) = z := pow_gcd_fixed hz hzn
  rw [hgcd] at hgcd_fixed
  simp only [pow_one] at hgcd_fixed
  have : z = 0 ∨ z = 1 := sq_eq_self_imp z (by rw [← sq]; exact hgcd_fixed)
  simp only [gf2Set, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact this

/-- **Phase 1, Lemma 2.** Under the hypothesis gcd(3k, n) = 1,
    the kernel of L_k is contained in {0, 1}. -/
theorem mk_ker_eq_F2 {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1) :
    (kerL (F := F) k) ⊆ gf2Set :=
  Set.Subset.trans (kerL_subset_frobFixed k) (frobFixed_subset_gf2 hn hcard (by omega) hgcd)

end KerBound
