/-
  Theorem3/Factorization.lean

  Bracken–McGuire factorization of the linearized polynomial arising from
  the derivative of a Gold-type APN function.

  The normalized operator `Lnorm(y) = y^(2^k) + y + 1` can be related to
  the composition of two Gold-type (Frobenius-linear) operators.  In
  particular, the additive polynomial `y ↦ y^(2^k) + y` factors through
  the Frobenius endomorphism, and its kernel has size at most `2^k` (being
  a polynomial of degree `2^k` over a field).

  This file:
  1. Defines two intermediate linearized (additive) operators L₁, L₂.
  2. Proves that `y^(2^k) + y` is their composition (up to additive structure).
  3. Deduces the root-count bound from the degree bound on each factor.

  Reference: Bracken–Byrne–Markin–McGuire, Theorem 3 (Factorization step).
-/
import Mathlib

noncomputable section

open Polynomial Finset Classical

variable (k : ℕ)
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Frobenius properties in characteristic 2 -/

/-- The Frobenius endomorphism `φ(x) = x^2` is a ring homomorphism in char 2. -/
def frob2 : F →+* F := frobenius F 2

/-- The iterated Frobenius `φ^k(x) = x^(2^k)`. -/
def frobIter : F →+* F := (frobenius F 2) ^ k

/-- `frobIter k x = x ^ (2^k)` -/
lemma frobIter_apply (x : F) : frobIter k F x = x ^ (2 ^ k) := by
  induction' k with k ih
  · aesop
  · convert congr_arg (fun y => y ^ 2) ih using 1 <;> ring
    unfold frobIter; rw [pow_add, pow_one]; norm_cast

/-! ### The linearized operator and its factorization -/

/-- The linearized (additive) operator `L₀(y) = y^(2^k) + y`. -/
def L₀ (y : F) : F := y ^ (2 ^ k) + y

/-- `L₀` is additive (𝔽₂-linear): `L₀(a + b) = L₀(a) + L₀(b)`. -/
lemma L₀_add (a b : F) : L₀ k F (a + b) = L₀ k F a + L₀ k F b := by
  unfold L₀
  induction' k with k ih <;> simp_all +decide [pow_succ, pow_mul]
  · ring
  · grind

/-- **First Gold-type operator.** `L₁(y) = y^2 + y` (the Artin–Schreier map). -/
def L₁ (y : F) : F := y ^ 2 + y

/-- **Second Gold-type operator.**
  `L₂(y) = ∑_{i=0}^{k-1} y^(2^i)` — the partial Frobenius trace. -/
def L₂ (y : F) : F :=
  ∑ i ∈ range k, y ^ (2 ^ i)

/-- **Factorization identity:** `L₁(L₂(y)) = L₀(y) = y^(2^k) + y`. -/
lemma L₁_comp_L₂ (y : F) : L₁ F (L₂ k F y) = L₀ k F y := by
  unfold L₁ L₂ L₀
  induction' k with k ih <;> simp_all +decide [pow_succ, pow_mul, Finset.sum_range_succ]
  · grind
  · grind

/-! ### Kernel bounds from the factorization -/

/-- The kernel of `L₁` has at most 2 elements. -/
lemma card_ker_L₁ :
    (univ.filter fun y : F => L₁ F y = 0).card ≤ 2 := by
  have h_roots_bound : ∀ y : F, y ^ 2 + y = 0 → y = 0 ∨ y = 1 := by grind
  exact le_trans (Finset.card_le_card
    (show Finset.filter (fun y => y ^ 2 + y = 0) Finset.univ ⊆ {0, 1} by aesop_cat))
    (Finset.card_insert_le _ _)

/-
The kernel of `L₂` has at most `2^(k-1)` elements (requires `k ≥ 1`).
-/
lemma card_ker_L₂ (hk : 0 < k) :
    (univ.filter fun y : F => L₂ k F y = 0).card ≤ 2 ^ (k - 1) := by
  -- Consider the polynomial $p := \sum_{i=0}^{k-1} X^{2^i}$.
  set p : Polynomial F := ∑ i ∈ Finset.range k, Polynomial.X ^ (2 ^ i);
  -- The set of roots of $p$ is exactly the set of elements in $F$ that satisfy $L₂(y) = 0$.
  have h_roots : Finset.filter (fun y : F => L₂ k F y = 0) (Finset.univ : Finset F) ⊆ p.roots.toFinset := by
    intro y hy; simp_all +decide [ Polynomial.eval_finset_sum ] ;
    refine' ⟨ _, _ ⟩;
    · simp +zetaDelta at *;
      exact ne_of_apply_ne ( fun p => p.coeff ( 2 ^ ( k - 1 ) ) ) ( by cases k <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] );
    · rw [ Polynomial.eval_finset_sum, show L₂ k F y = ∑ i ∈ Finset.range k, y ^ ( 2 ^ i ) from rfl ] at * ; aesop;
  refine' le_trans ( Finset.card_le_card h_roots ) ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
  rw [ Polynomial.natDegree_sum_eq_of_disjoint ];
  · simp +zetaDelta at *;
    exact fun i hi => pow_le_pow_right₀ ( by decide ) ( Nat.le_pred_of_lt hi );
  · intro i hi j hj hij; contrapose hij; aesop;

/-
**Root count for `L₀`:**  `|{y ∈ F : y^(2^k) + y = 0}| ≤ 2^k`.

  For `k ≥ 1`, the polynomial `X^(2^k) + X` has degree `2^k` and is nonzero,
  so it has at most `2^k` roots.
-/
lemma card_roots_L₀_le (hk : 0 < k) :
    (univ.filter fun y : F => L₀ k F y = 0).card ≤ 2 ^ k := by
  -- Consider the polynomial $p(x) = x^{2^k} + x$.
  set p : Polynomial F := Polynomial.X ^ (2 ^ k) + Polynomial.X;
  -- Since $p(x)$ is a polynomial of degree $2^k$, it has at most $2^k$ roots in $\mathbb{F}$.
  have h_roots_bound : (p.roots.toFinset).card ≤ 2 ^ k := by
    refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
    rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num [ hk ];
    grind +splitImp;
  refine' le_trans ( Finset.card_le_card _ ) h_roots_bound;
  intro y hy; simp_all +decide [ L₀ ] ;
  exact ⟨ ne_of_apply_ne Polynomial.natDegree ( by erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num ; linarith [ Nat.pow_le_pow_right two_pos hk ] ), by aesop ⟩

/-
**Root count for the shifted operator:**
  `|{y ∈ F : y^(2^k) + y + 1 = 0}| ≤ 2^k`.
-/
lemma card_roots_shifted_le (hk : 0 < k) :
    (univ.filter fun y : F => y ^ (2 ^ k) + y + 1 = 0).card ≤ 2 ^ k := by
  -- By the Fundamental Theorem of Algebra, the number of roots of $x^{2^k} + x + 1$ in $F$ is at most $2^k$.
  have h_roots : (Finset.filter (fun y : F => y ^ 2 ^ k + y + 1 = 0) Finset.univ).card ≤ (Polynomial.X ^ 2 ^ k + Polynomial.X + 1 : Polynomial F).roots.toFinset.card := by
    refine Finset.card_le_card ?_;
    simp +decide [ Finset.subset_iff ];
    exact fun x hx => ⟨ by exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide [ hx ] ), hx ⟩;
  refine' le_trans h_roots ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
  rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num;
  · linarith;
  · linarith

end