/-
  Task 1: Gold APN Base Case
  Prove that for g(x) = x^(2^k+1), the equation Δ_u g(x) = 0
  simplifies to u^(2^k) · x + u · x^(2^k) = 0.

  Reference: Bracken-McGuire arXiv:0803.3781, and kasami-67 formalization.
-/
import Mathlib
import Theorem3.Defs

set_option maxHeartbeats 1600000

open Polynomial Finset

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

instance : ExpChar F 2 := expChar_of_injective_ringHom (RingHom.injective (RingHom.id F)) 2

/-- In characteristic 2, (x + u)^(2^k) = x^(2^k) + u^(2^k). -/
lemma add_pow_two_pow (x u : F) (k : ℕ) :
    (x + u) ^ (2 ^ k) = x ^ (2 ^ k) + u ^ (2 ^ k) :=
  add_pow_expChar_pow x u 2 k

/-- Rewrite x^(2^k+1) as x^(2^k) * x. -/
lemma gold_as_mul (x : F) (k : ℕ) :
    x ^ (2 ^ k + 1) = x ^ (2 ^ k) * x := by
  rw [pow_succ]

/-
**Gold APN Base Case**: The linearized derivative of the Gold function
    g(x) = x^(2^k+1) satisfies:
    Δ_u g(x) = u^(2^k) · x + u · x^(2^k)

    This is the fundamental identity used in all APN proofs for Gold-type functions.
-/
theorem gold_apn (x u : F) (k : ℕ) :
    deltaDerivative (goldFunction k) u x = u ^ (2 ^ k) * x + u * x ^ (2 ^ k) := by
  unfold deltaDerivative goldFunction;
  simp +decide [ pow_add, add_pow_two_pow, mul_assoc, mul_comm, mul_left_comm ];
  grind

/-
If gcd(k,n) = 1, the equation u^(2^k)·x + u·x^(2^k) = 0 with u ≠ 0
    factors as u^(2^k+1) · (y^(2^k) + y) = 0 where y = x/u,
    so y^(2^k) = y, meaning y ∈ GF(2^k) ∩ GF(2^n) = GF(2).
    Hence y ∈ {0, 1}, giving x ∈ {0, u}.
-/
theorem gold_kernel_le_two (u : F) (k n : ℕ) (hu : u ≠ 0)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) :
    ∀ (S : Finset F), (↑S : Set F) ⊆ deltaKernel (goldFunction k) u → S.card ≤ 2 := by
  unfold deltaKernel at *; simp_all +decide [ goldFunction, deltaDerivative ] ;
  -- When gcd(k,n)=1, the equation y^(2^k) = y has exactly 2 solutions in F_{2^n}, namely y=0 and y=1.
  have h_solutions : ∀ y : F, y ^ (2 ^ k) = y → y = 0 ∨ y = 1 := by
    -- Since $k$ and $n$ are coprime, the order of any element in $F_{2^n}$ divides $2^n - 1$.
    have h_order_div : ∀ y : F, y ≠ 0 → y ^ (2 ^ n - 1) = 1 := by
      exact fun y hy => by rw [ ← hcard, FiniteField.pow_card_sub_one_eq_one y hy ] ;
    -- Since $k$ and $n$ are coprime, the order of any element in $F_{2^n}$ divides $2^k - 1$.
    have h_order_div_k : ∀ y : F, y ≠ 0 → y ^ (2 ^ k - 1) = 1 → y ^ (Nat.gcd (2 ^ n - 1) (2 ^ k - 1)) = 1 := by
      exact fun y hy hy' => by rw [ pow_gcd_eq_one ] ; aesop;
    -- Since $k$ and $n$ are coprime, $\gcd(2^n - 1, 2^k - 1) = 2^{\gcd(n, k)} - 1 = 2^1 - 1 = 1$.
    have h_gcd : Nat.gcd (2 ^ n - 1) (2 ^ k - 1) = 1 := by
      simp_all +decide [ Nat.Coprime, Nat.Coprime.symm ];
    intro y hy; by_cases hy' : y = 0 <;> simp_all +decide [ pow_succ' ] ;
    exact h_order_div_k y hy' ( mul_left_cancel₀ hy' <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ; aesop );
  -- Therefore, the set $\{x \in F \mid u^{2^k} \cdot x + u \cdot x^{2^k} = 0\}$ contains at most two elements.
  have h_set : {x : F | u ^ (2 ^ k) * x + u * x ^ (2 ^ k) = 0} ⊆ {0, u} := by
    intro x hx; specialize h_solutions ( x / u ) ; simp_all +decide [ div_pow, mul_pow, add_eq_zero_iff_eq_neg ] ;
    simp_all +decide [ div_eq_iff, mul_comm ];
    grind;
  intro S hS;
  have h_card : S.card ≤ ({0, u} : Set F).ncard := by
    convert Set.ncard_le_ncard ( show ( S : Set F ) ⊆ { 0, u } from ?_ ) using 1;
    · rw [ Set.ncard_coe_finset ];
    · refine' Set.Subset.trans hS _;
      convert h_set using 1;
      ext x; simp +decide [ add_pow_two_pow, mul_add, add_mul, pow_succ' ] ; ring;
      grind;
  exact h_card.trans ( Set.ncard_insert_le _ _ ) |> le_trans <| by simp +decide [ hu ] ;

end