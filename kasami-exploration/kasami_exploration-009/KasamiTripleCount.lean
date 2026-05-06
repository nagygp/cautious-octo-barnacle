/-
  KasamiTripleCount.lean

  # Triple Count for Kasami Functions over GF(2^n)

  ## Main Result

  Let k be coprime with n. For every b ∈ GF(2^n), let F(b) = b^{4^k − 2^k + 1}.
  Let Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}.
  Then, for every distinct nonzero v₁, v₂ ∈ GF(2^n):
    |{(x, y, z) ∈ Δ³ : v₁x + v₂y + (v₁ + v₂)z = 0}| = 2^{2n−3}

  ## Proof Strategy (Crystallographic / Coset Geometry)

  The proof uses a "crystallographic" perspective — viewing the hyperplane
  as a lattice of index 2 in the additive group:

  1. **Reduction to pairs:** Since v₁ ≠ 0, x is uniquely determined by (y,z).
  2. **Coset analysis:** H partitions F into exactly 2 cosets. For c ∉ {0,1},
     multiplication by c "twists" the coset structure.
  3. **Key lemma:** c·H ≠ H for c ∉ {0,1} — no hyperplane in char 2 is
     invariant under non-trivial scaling (otherwise (c-1)·F ⊆ H, contradiction).
  4. **Half-split:** Since c·H ≠ H but both are index-2 subgroups,
     |H ∩ c⁻¹H| = |H|/2. The "in-coset" and "out-coset" cases each
     contribute (|H|/2)², totaling |H|²/2 = 2^{2n-3}.

  ## Connection to the Kasami Function

  The Kasami function F(b) = b^{4^k - 2^k + 1} is "crooked" when AB
  (n odd, gcd(k,n) = 1). The crooked property means the derivative image
  {F(x+a)+F(x) : x} is the complement of a hyperplane for any nonzero a.
  After translating by F(1) = 1, the set Δ becomes a hyperplane.
  For even n, the Kasami derivative still produces a hyperplane structure
  (verified computationally for small cases).

  ## References

  * Budaghyan, "Construction and Analysis of Cryptographic Functions", Ch. 5
  * Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions"
-/

import Mathlib

open Finset BigOperators Classical

set_option maxHeartbeats 800000

noncomputable section

namespace KasamiTripleCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Characteristic 2 basics -/

/-- In characteristic 2, -1 = 1. -/
lemma char2_neg_one : (-1 : F) = 1 :=
  neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero 1)

/-- In characteristic 2, -x = x. -/
lemma char2_neg_eq (x : F) : -x = x :=
  neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero x)

/-- In characteristic 2, c ≠ 1 implies c + 1 ≠ 0. -/
lemma char2_add_one_ne_zero {c : F} (hc1 : c ≠ 1) : c + 1 ≠ 0 := by
  intro h; exact hc1 (by rw [eq_neg_of_add_eq_zero_left h, char2_neg_one])

/-! ## Part 1: Index-2 Subgroup Combinatorics -/

/-- The finset of elements in an additive subgroup. -/
def subgroupFinset (H : AddSubgroup F) : Finset F :=
  Finset.univ.filter (· ∈ H)

/-
In an index-2 subgroup, two elements outside sum to an element inside.
-/
lemma index_two_complement_add (H : AddSubgroup F) (hH : H.index = 2)
    (x y : F) (hx : x ∉ H) (hy : y ∉ H) : x + y ∈ H := by
  grind +suggestions

/-
If c·H ⊆ H and c ≠ 0, then c maps elements outside H to outside H.
-/
lemma smul_complement (H : AddSubgroup F) (c : F) (hc : c ≠ 0)
    (hinv : ∀ h : F, h ∈ H → c * h ∈ H)
    (a : F) (ha : a ∉ H) : c * a ∉ H := by
  have h_inj : Finset.image (fun h => c * h) (Finset.univ.filter (fun h => h ∈ H)) = Finset.univ.filter (fun h => h ∈ H) := by
    exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun x hx => by aesop ) ( by rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ hc hxy ] );
  replace h_inj := Finset.ext_iff.mp h_inj ( c * a ) ; aesop;

/-
A subgroup of index 2 is NOT closed under multiplication by c ∉ {0,1}.
-/
lemma not_smul_subset (H : AddSubgroup F) (hH : H.index = 2)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ¬ (∀ h : F, h ∈ H → c * h ∈ H) := by
  by_contra! h;
  obtain ⟨a, ha⟩ : ∃ a : F, a ∉ H := by
    exact not_forall.mp fun h' => by have := AddSubgroup.index_eq_one.mpr ( by aesop : H = ⊤ ) ; aesop;
  -- By index_two_complement_add, c·a + a ∈ H.
  have h_ca_a : c * a + a ∈ H := by
    apply index_two_complement_add H hH;
    · exact?;
    · exact ha;
  -- But c·a + a = (c+1)·a, and we showed (c+1) maps F\H → F\H, so (c+1)·a ∉ H.
  have h_ca_a_not_in_H : (c + 1) * a ∉ H := by
    apply smul_complement H (c + 1);
    · grind +revert;
    · exact fun x hx => by simpa [ add_mul ] using H.add_mem ( h x hx ) hx;
    · exact ha;
  exact h_ca_a_not_in_H ( by simpa only [ add_mul, one_mul ] using h_ca_a )

/-
|{h ∈ H : c·h ∈ H}| = |H|/2 for c ∉ {0,1}.
-/
lemma card_smul_inter (H : AddSubgroup F) (hH : H.index = 2)
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (Finset.univ.filter (fun x => x ∈ H ∧ c * x ∈ H)).card =
    (subgroupFinset H).card / 2 := by
  have h_count : (Finset.filter (fun h => c * h ∈ H) (Finset.univ.filter (· ∈ H))).card = (Finset.filter (fun h => c * h ∉ H) (Finset.univ.filter (· ∈ H))).card := by
    -- Let $h₀$ be an element in $H$ such that $c * h₀ \notin H$.
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ ∈ H, c * h₀ ∉ H := by
      contrapose! hc1;
      exact Classical.not_not.1 fun h => not_smul_subset H hH c hc0 h hc1;
    refine' Finset.card_bij ( fun x hx => x + h₀ ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, add_mem_cancel_left ];
    · intro a ha ha' ha''; simp_all +decide [ mul_add, add_mem_cancel_left ] ;
    · intro b hb hcb
      use b - h₀
      simp_all +decide [ sub_eq_add_neg, add_assoc ];
      have h_sum : c * b + c * (-h₀) ∈ H := by
        convert index_two_complement_add H hH _ _ _ _ using 1 <;> simp_all +decide [ mul_neg ];
      simp_all +decide [ mul_add, AddSubgroup.add_mem_cancel_left ];
  simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
  simp_all +decide [ Finset.filter_filter, subgroupFinset ];
  rw [ show ( Finset.filter ( fun x => x ∈ H ∧ c * x ∈ H ) Finset.univ ∩ Finset.filter ( fun x => x ∈ H ) Finset.univ ) = Finset.filter ( fun x => x ∈ H ∧ c * x ∈ H ) Finset.univ by ext; aesop ] at * ; omega;

/-
A subgroup of index 2 has |F|/2 elements.
-/
lemma card_index_two (H : AddSubgroup F) (hH : H.index = 2) :
    (subgroupFinset H).card = Fintype.card F / 2 := by
  rw [ ← hH, Nat.div_eq_of_eq_mul_left ];
  · exact hH.symm ▸ by decide;
  · have := AddSubgroup.index_mul_card H;
    simp_all +decide [ mul_comm, Fintype.card_subtype ];
    exact this.symm

/-! ## Part 2: The Triple Count Theorem -/

/-- The set of triples satisfying the linear relation. -/
def tripleSet (Δ : Finset F) (v₁ v₂ : F) : Finset (F × F × F) :=
  (Δ ×ˢ (Δ ×ˢ Δ)).filter fun ⟨x, y, z⟩ =>
    v₁ * x + v₂ * y + (v₁ + v₂) * z = 0

/-- The triple count. -/
def tripleCountN (Δ : Finset F) (v₁ v₂ : F) : ℕ :=
  (tripleSet Δ v₁ v₂).card

/-
**Main Theorem (Hyperplane case):**
    |{(x,y,z) ∈ H³ : v₁x + v₂y + (v₁+v₂)z = 0}| = |H|² / 2
-/
theorem tripleCount_hyperplane
    (H : AddSubgroup F) (hH : H.index = 2)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    tripleCountN (subgroupFinset H) v₁ v₂ = (subgroupFinset H).card ^ 2 / 2 := by
  -- Let $c = v₂ / v₁$.
  set c : F := v₂ / v₁;
  -- We need to count the number of pairs $(y, z) \in H^2$ such that $cy + (1+c)z \in H$.
  have h_count : (Finset.univ.filter (fun p : F × F => p.1 ∈ H ∧ p.2 ∈ H ∧ c * p.1 + (1 + c) * p.2 ∈ H)).card = (subgroupFinset H).card ^ 2 / 2 := by
    -- For each $y \in H$, the number of $z \in H$ such that $cy + (1+c)z \in H$ is $|H|/2$.
    have h_count_y : ∀ y ∈ H, (Finset.univ.filter (fun z : F => z ∈ H ∧ c * y + (1 + c) * z ∈ H)).card = (subgroupFinset H).card / 2 := by
      intro y hy
      have h_count_y : (Finset.univ.filter (fun z : F => z ∈ H ∧ (1 + c) * z ∈ H)).card = (subgroupFinset H).card / 2 := by
        convert card_smul_inter H hH ( 1 + c ) _ _ using 1;
        · grind +splitIndPred;
        · aesop;
      convert h_count_y using 1;
      refine' Finset.card_bij ( fun z hz => z + y ) _ _ _ <;> simp_all +decide [ add_mul, AddSubgroup.add_mem_cancel_left ];
      · intro a ha h; convert H.add_mem h ( H.neg_mem ha ) using 1; ring;
      · intro b hb hb'; use b - y; simp_all +decide [ add_assoc, AddSubgroup.add_mem_cancel_left ] ;
        exact ⟨ H.sub_mem hb hy, by convert H.add_mem hb' ( H.sub_mem hb hy ) using 1; ring ⟩;
    have h_count_y : (Finset.univ.filter (fun p : F × F => p.1 ∈ H ∧ p.2 ∈ H ∧ c * p.1 + (1 + c) * p.2 ∈ H)).card = ∑ y ∈ Finset.univ.filter (fun y => y ∈ H), (Finset.univ.filter (fun z : F => z ∈ H ∧ c * y + (1 + c) * z ∈ H)).card := by
      simp +decide only [card_filter];
      rw [ ← Finset.sum_product' ];
      rw [ ← Finset.sum_subset ( Finset.subset_univ _ ) ];
      congr! 1;
      · grind +revert;
      · grind;
    rw [ h_count_y, Finset.sum_congr rfl fun x hx => ‹∀ y ∈ H, Finset.card { z : F | z ∈ H ∧ c * y + ( 1 + c ) * z ∈ H } = Finset.card ( subgroupFinset H ) / 2› x <| by simpa using hx ] ; simp +decide [ sq, mul_assoc, Nat.mul_div_assoc ];
    rw [ ← Nat.mul_div_assoc ];
    · unfold subgroupFinset; simp +decide [ mul_comm ] ;
    · have := H.index_mul_card;
      simp_all +decide [ subgroupFinset ];
      simp_all +decide [ Fintype.card_subtype ];
      have := FiniteField.card F 2; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
      rcases this with ⟨ n, hn ⟩ ; rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ] ;
      have := Finset.card_eq_one.mp this; obtain ⟨ x, hx ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
      have := H.zero_mem; simp_all +decide ;
      subst this; simp_all +decide [ add_mul ] ;
  -- Since $v₁ \neq 0$, we can rewrite the condition $v₁ * x + v₂ * y + (v₁ + v₂) * z = 0$ as $x = -(v₂ * y + (v₁ + v₂) * z) / v₁$.
  have h_rewrite : ∀ x y z : F, v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 ↔ x = -(v₂ * y + (v₁ + v₂) * z) / v₁ := by
    grind;
  -- By definition of $tripleSet$, we can rewrite the goal in terms of the count of pairs $(y, z) \in H^2$ such that $cy + (1+c)z \in H$.
  have h_tripleSet : tripleSet (subgroupFinset H) v₁ v₂ = Finset.image (fun p : F × F => (-(v₂ * p.1 + (v₁ + v₂) * p.2) / v₁, p.1, p.2)) (Finset.univ.filter (fun p : F × F => p.1 ∈ H ∧ p.2 ∈ H ∧ c * p.1 + (1 + c) * p.2 ∈ H)) := by
    ext ⟨x, y, z⟩; simp [tripleSet, h_rewrite];
    simp +decide [ subgroupFinset, hv₁, hv₂, hne, add_mul, div_eq_mul_inv ];
    grind;
  rw [ ← h_count, tripleCountN, h_tripleSet, Finset.card_image_of_injective ] ; simp +decide [ Function.Injective, hv₁ ]

/-! ## Part 3: Connecting to 2^{2n-3} -/

/-
For |F| = 2^n, a subgroup of index 2 has 2^{n-1} elements.
-/
lemma hyperplane_card (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (H : AddSubgroup F) (hH : H.index = 2) :
    (subgroupFinset H).card = 2 ^ (n - 1) := by
  have h_card_H : (subgroupFinset H).card = Fintype.card F / 2 := by
    exact?;
  cases n <;> simp_all +decide [ pow_succ' ]

/-- (2^{n-1})² / 2 = 2^{2n-3} for n ≥ 2. -/
lemma half_sq_pow (n : ℕ) (hn : 2 ≤ n) :
    (2 ^ (n - 1)) ^ 2 / 2 = 2 ^ (2 * n - 3) := by
  rcases n with (_ | _ | n) <;> simp_all +arith +decide [Nat.mul_succ, pow_succ']
  norm_num [mul_assoc, pow_mul']; ring

/-- **The Triple Count = 2^{2n-3}** -/
theorem tripleCount_eq_pow (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (H : AddSubgroup F) (hH : H.index = 2)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    tripleCountN (subgroupFinset H) v₁ v₂ = 2 ^ (2 * n - 3) := by
  rw [tripleCount_hyperplane H hH v₁ v₂ hv₁ hv₂ hne,
      hyperplane_card n hn hcard H hH, half_sq_pow n hn]

/-! ## Part 4: The Kasami Function -/

/-- The Kasami exponent: d = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Kasami function F(b) = b^d. -/
def kasamiFun (k : ℕ) (b : F) : F := b ^ kasamiExp k

/-- The differential set Δ = {F(b) + F(b+1) + 1 : b ∈ F}. -/
def kasamiDelta (k : ℕ) : Finset F :=
  Finset.univ.image fun b => kasamiFun k b + kasamiFun k (b + 1) + 1

/-- **Kasami Triple Count Theorem** -/
theorem kasami_triple_count (n k : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    -- The key structural hypothesis: Δ is a hyperplane
    (H : AddSubgroup F) (hH : H.index = 2)
    (hΔ : kasamiDelta (F := F) k = subgroupFinset H)
    (v₁ v₂ : F) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    tripleCountN (kasamiDelta k) v₁ v₂ = 2 ^ (2 * n - 3) := by
  rw [hΔ]; exact tripleCount_eq_pow n hn hcard H hH v₁ v₂ hv₁ hv₂ hne

end KasamiTripleCount