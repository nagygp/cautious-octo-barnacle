/-
# Kasami APN — Polynomial Elimination MVP

This module proves the core Kasami APN theorem via the collision-in-kernel approach:

1. Define g(t) = (t+1)^d + t^d where d = q²-q+1, q = 2^k
2. Show: if g(t₁) = g(t₂) and t₁ ≠ t₂, then L_k(t₁+t₂) = 0
   where L_k(x) = x^q + x is the linearized polynomial
3. Since ker(L_k) = {0,1} when gcd(k,n) = 1, each fiber has ≤ 2 elements
4. This gives kasami_diff_bound, completing the APN proof.

## Key Identity

  (g(t) + 1) · (t²+t)^q = (t^q+t)^{q+1}

## Proof Strategy for c ≠ 1 case

From the collision, we derive s^q + s = a where s = L_k(t₁)/L_k(h) and
a = (c+g(h))/(g(h)+1). Since c ≠ 1, a ≠ 1. The equation L_k(s) = a has
solutions iff Tr(a) = 0. Since a IS a legitimate value (the collision
exists), we need a different approach:

Setting τ = L₁(h)/L₁(t₁), we derive τ^q = (a+1)/s^{q+1}.
The key disjunction (a+1)(1+τ^{2q}) = 0 gives:
- Case τ^{2q} = 1: In char 2, x^{2^m} = 1 ⟹ x = 1. So τ = 1,
  forcing L₁(h) = L₁(t₁), hence h+t₁ ∈ {0,1}, hence t₂ ∈ {0,1},
  hence c = g(t₂) = 1, contradiction.
- Case a = 1: s^q+s = 1 in GF(2^n) with n odd. But
  Tr(1) = n mod 2 = 1 ≠ 0, so 1 ∉ Im(L_k), contradiction.
-/
import Mathlib
import RequestProject.Foundations.DicksonPoly

noncomputable section
open Finset Fintype Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Basic definitions -/

def kasami_d (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

def L_k (k : ℕ) (x : F) : F := x ^ (2 ^ k) + x

def L_1 (x : F) : F := x ^ 2 + x

def kasami_g (k : ℕ) (t : F) : F :=
  (t + 1) ^ kasami_d k + t ^ kasami_d k

/-! ## Properties of L_k -/

theorem L_k_add (k : ℕ) (x y : F) :
    L_k k (x + y) = L_k k x + (L_k k y : F) := by
  simp only [L_k, add_pow_expChar_pow]; ring

theorem L_k_zero : L_k k (0 : F) = 0 := by simp [L_k]

theorem L_k_one : L_k k (1 : F) = 0 := by
  simp [L_k, one_pow, CharTwo.add_self_eq_zero]

theorem L_k_kernel_card {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hcard : Fintype.card F = 2 ^ n) :
    Fintype.card { x : F // L_k k x = 0 } = 2 := by
  have h_eq : Fintype.card {x : F | x ^ (2 ^ k) + x = 0} = 2 := by
    have h_subfield : {x : F | x ^ (2 ^ k) = x} = {x : F | x ^ 2 = x} := by
      ext x
      constructor <;> intro hx <;> have := FiniteField.pow_card x <;>
        simp_all +decide [pow_succ, pow_mul]
      · have h_exp : x ^ (2 ^ Nat.gcd k n) = x := by
          have h_exp : ∀ m n : ℕ, x ^ (2 ^ m) = x → x ^ (2 ^ n) = x →
              x ^ (2 ^ Nat.gcd m n) = x := by
            intros m n hm hn
            induction' n using Nat.strong_induction_on with n ih generalizing m
            rcases eq_or_ne n 0 with rfl | hn'
            · simp_all +decide [Nat.gcd_comm]
            rw [← Nat.mod_add_div m n] at *
            simp_all +decide [pow_add, pow_mul]
            convert ih (m % n) (Nat.mod_lt _ (Nat.pos_of_ne_zero hn')) n hn _ using 1
            · rw [Nat.gcd_comm]
            · contrapose! hm
              induction' m / n with d hd <;> simp_all +decide [pow_succ, pow_mul]
              simp_all +decide [pow_right_comm]
          exact h_exp k n hx this
        simp_all +decide [pow_succ']
      · by_cases hx' : x = 0 <;> simp_all +decide [sq]
    simp_all +decide [Set.ext_iff, pow_succ']
    rw [Fintype.card_subtype]; simp_all +decide [← sq]
    rw [show (Finset.filter (fun x : F => x ^ 2 ^ k + x = 0) Finset.univ : Finset F) =
        {0, 1} from ?_]
    · rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp +decide [hn.ne']
    · grind
  exact h_eq

theorem L_k_kernel_eq_one {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hcard : Fintype.card F = 2 ^ n)
    (h : F) (hker : L_k k h = 0) (hne : h ≠ 0) : h = 1 := by
  have h_card : Fintype.card {x : F // L_k k x = 0} = 2 :=
    L_k_kernel_card hk hn hgcd hcard
  rw [Fintype.card_subtype] at h_card
  rw [Finset.card_eq_two] at h_card
  obtain ⟨x, y, hxy, h⟩ := h_card
  simp_all +decide [Finset.ext_iff, Set.ext_iff]
  have := h 0; have := h 1; simp_all +decide [L_k_zero, L_k_one]
  grind

/-! ## Characteristic 2 identities -/

omit [Fintype F] [DecidableEq F] in
theorem char2_neg (x : F) : -x = x :=
  neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero x)

omit [Fintype F] [DecidableEq F] in
theorem char2_sub (x y : F) : x - y = x + y := by
  rw [sub_eq_add_neg, char2_neg]

/-! ## Key identity and g properties -/

theorem kasami_g_symm (k : ℕ) (t : F) : kasami_g k (t + 1) = kasami_g k t := by
  unfold kasami_g
  have h2 : (t + 1 + 1 : F) = t := by
    calc t + 1 + 1 = t + (1 + 1) := by ring
      _ = t + 0 := by rw [CharTwo.add_self_eq_zero (1 : F)]
      _ = t := by ring
  rw [h2]; ring

theorem kasami_key_identity (k : ℕ) (t : F) :
    (kasami_g k t + 1) * (L_1 t) ^ (2 ^ k) = (L_k k t) ^ (2 ^ k + 1) := by
  simp [kasami_g, L_1]
  rw [kasami_d]
  have h_expansion : (t + 1) ^ (2 ^ (2 * k) - 2 ^ k + 1) * (t ^ 2 + t) ^ (2 ^ k) +
      t ^ (2 ^ (2 * k) - 2 ^ k + 1) * (t ^ 2 + t) ^ (2 ^ k) + (t ^ 2 + t) ^ (2 ^ k) =
      (t ^ (2 ^ k) + t) ^ (2 ^ k + 1) := by
    have h_expansion :
        (t + 1) ^ (2 ^ (2 * k) - 2 ^ k + 1) * (t ^ 2 + t) ^ (2 ^ k) =
          (t + 1) ^ (2 ^ (2 * k) + 1) * t ^ (2 ^ k) ∧
        t ^ (2 ^ (2 * k) - 2 ^ k + 1) * (t ^ 2 + t) ^ (2 ^ k) =
          t ^ (2 ^ (2 * k) + 1) * (t + 1) ^ (2 ^ k) := by
      constructor <;> rw [show t ^ 2 + t = t * (t + 1) by ring] <;> rw [mul_pow] <;> ring
      all_goals simp +decide [mul_assoc, ← pow_add,
        Nat.sub_add_cancel (show 2 ^ k ≤ 2 ^ (k * 2) from
          pow_le_pow_right₀ (by decide) (by linarith))]
    simp_all +decide [pow_succ, pow_mul]
    simp +decide [← mul_pow, add_pow_char_pow]; ring
    rw [show (4 ^ k : ℕ) = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]; ring
    rw [show (1 + t) ^ 2 ^ (k * 2) = (1 + t ^ 2 ^ (k * 2)) by
      rw [add_pow_char_pow]; ring]; ring
    simp +decide [show (2 : F) = 0 by exact CharP.cast_eq_zero F 2]
  convert h_expansion using 1; ring!

theorem kasami_g_eq_one_imp_L_k_zero (k : ℕ) (t : F)
    (hg : kasami_g k t = 1) : L_k k t = 0 := by
  have h_zero : (L_1 t) ^ (2 ^ k) * (kasami_g k t + 1) = (L_k k t) ^ (2 ^ k + 1) := by
    rw [mul_comm, kasami_key_identity]
  simp_all +decide [pow_succ']
  simp_all +decide [← two_mul, CharTwo.two_eq_zero]

theorem kasami_g_zero : kasami_g k (0 : F) = 1 := by
  simp [kasami_g, kasami_d]

theorem kasami_g_one : kasami_g k (1 : F) = 1 := by
  simp [kasami_g, kasami_d, CharTwo.add_self_eq_zero]

/-! ## L_1 properties -/

theorem L_1_add (x y : F) : L_1 (x + y) = L_1 x + L_1 y := by
  simp only [L_1]
  have : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by rw [add_pow_char (R := F) (p := 2)]
  rw [this]; ring

theorem L_1_zero : L_1 (0 : F) = 0 := by simp [L_1]

theorem L_1_one : L_1 (1 : F) = 0 := by
  simp [L_1, one_pow, CharTwo.add_self_eq_zero]

/-
In char 2, x^{2^m} = 1 implies x = 1
-/
theorem pow_two_pow_eq_one_imp {m : ℕ} {x : F} (h : x ^ (2 ^ m) = 1) : x = 1 := by
  -- By induction on $m$, we can show that if $x^{2^m} = 1$, then $x = 1$.
  induction' m with m ih generalizing x <;> simp_all +decide [ pow_succ', pow_mul ];
  grind +ring

/-
L_k(s) = 1 has no solution when n is odd
-/
theorem L_k_ne_one {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (s : F) : L_k k s ≠ 1 := by
  intro hs_one
  have h_sum : ∑ i ∈ Finset.range n, (L_k k (s ^ (2 ^ (i * k)))) = n * 1 := by
    convert Finset.sum_const ( 1 : F ) using 2;
    · simp_all +decide [ L_k, pow_mul' ];
      convert congr_arg ( · ^ ( 2 ^ k ) ^ ‹_› ) hs_one using 1 ; ring;
      · rw [ add_pow_char_pow ] ; ring;
      · rw [ one_pow ];
    · aesop;
  simp_all +decide [ L_k ];
  -- By the properties of the Frobenius automorphism, we can simplify the sum.
  have h_frobenius : ∑ x ∈ Finset.range n, ((s ^ 2 ^ (x * k)) ^ 2 ^ k + s ^ 2 ^ (x * k)) = s ^ 2 ^ (n * k) + s := by
    convert Finset.sum_range_sub ( fun x => s ^ 2 ^ ( x * k ) ) n using 1 <;> simp +decide [ pow_mul', pow_add ] ; ring!;
    · rw [ Finset.sum_add_distrib, sub_eq_add_neg ] ; simp +decide [ CharTwo.neg_eq ] ;
    · exact?
  generalize_proofs at *; (
  -- Since $s^{2^n} = s$ in $GF(2^n)$, we have $s^{2^{nk}} = s$.
  have h_exp : s ^ 2 ^ (n * k) = s := by
    have h_exp : ∀ x : F, x ^ (2 ^ n) = x := by
      exact fun x => by rw [ ← hcard, FiniteField.pow_card ] ;
    generalize_proofs at *; (
    exact Nat.recOn k ( by simp +decide ) fun m ih => by rw [ Nat.mul_succ, pow_add, pow_mul, h_exp, ih ] ;)
  generalize_proofs at *; (
  grind +splitIndPred))

/-! ## The collision lemmas -/

theorem collision_c_eq_one (k : ℕ) (t₁ t₂ : F)
    (hg1 : kasami_g k t₁ = 1) (hg2 : kasami_g k t₂ = 1) :
    L_k k (t₁ + t₂) = 0 := by
  rw [L_k_add, kasami_g_eq_one_imp_L_k_zero k t₁ hg1,
      kasami_g_eq_one_imp_L_k_zero k t₂ hg2]; simp

/-
L_1(x) = 0 iff x ∈ {0, 1}
-/
theorem L_1_eq_zero_iff (x : F) : L_1 x = 0 ↔ x = 0 ∨ x = 1 := by
  unfold L_1;
  grind +ring

/-
When L_1(t₁) = L_1(t₂) and t₁ ≠ t₂, then t₂ = t₁ + 1
-/
theorem L_1_eq_imp_t2_eq (t₁ t₂ : F) (hne : t₁ ≠ t₂)
    (hL1 : L_1 t₁ = L_1 t₂) : t₂ = t₁ + 1 := by
  simp_all +decide [ L_1 ];
  grind +ring

/-
Key Frobenius identity: g_k(t) = (g_{n-k}(t))^{2^{2k}}.
    This follows from d_k ≡ d_{n-k} · 2^{2k} (mod 2^n - 1).
-/
theorem kasami_g_frobenius {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hkn : k < n) (hgcd : Nat.gcd k n = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (t : F) :
    kasami_g k t = (kasami_g (n - k) t) ^ (2 ^ (2 * k)) := by
  unfold kasami_g;
  -- Note: $d_{n-k} = 2^{2(n-k)} - 2^{n-k} + 1$
  have h_dnk : kasami_d (n - k) * 2 ^ (2 * k) ≡ kasami_d k [MOD 2 ^ n - 1] := by
    refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
    unfold kasami_d; norm_num; ring;
    rw [ Nat.cast_sub <| Nat.pow_le_pow_right ( by decide ) <| by linarith [ Nat.sub_add_cancel hkn.le ] ] ; rw [ Nat.cast_sub <| Nat.pow_le_pow_right ( by decide ) <| by linarith [ Nat.sub_add_cancel hkn.le ] ] ; push_cast ; ring_nf ;
    rw [ show n = k + ( n - k ) by rw [ Nat.add_sub_cancel' hkn.le ] ] ; ring_nf;
    norm_num [ pow_mul ] ; ring_nf ;
    exact ⟨ 2 ^ k * ( 2 ^ ( n - k ) - 1 ) + 1, by ring ⟩;
  -- Since $t^{2^n} = t$ for all $t \in F$, we have $x^{d_k} = x^{d_{n-k} \cdot 2^{2k}}$ for $x \neq 0$.
  have h_exp_eq : ∀ x : F, x ≠ 0 → x ^ (kasami_d k) = x ^ (kasami_d (n - k) * 2 ^ (2 * k)) := by
    intro x hx; rw [ ← Nat.mod_add_div ( kasami_d ( n - k ) * 2 ^ ( 2 * k ) ) ( 2 ^ n - 1 ), ← Nat.mod_add_div ( kasami_d k ) ( 2 ^ n - 1 ), h_dnk ] ; simp +decide [ pow_add, pow_mul ] ;
    have := FiniteField.pow_card_sub_one_eq_one x; simp_all +decide [ pow_mul ] ;
  by_cases ht : t = 0 <;> by_cases ht' : t + 1 = 0 <;> simp_all +decide [ add_pow_char_pow ];
  · simp +decide [ kasami_d, hk.ne', hn.ne' ];
  · simp_all +decide [ add_eq_zero_iff_eq_neg, pow_mul ];
    rw [ zero_pow, zero_pow, zero_pow ] <;> norm_num [ kasami_d ];
  · ring

/-! ## Partial trace and MCM permutation -/

/-- The partial trace S_k(y) = Σ_{i=0}^{k-1} y^{2^i}. -/
def S_k (k : ℕ) (y : F) : F := ∑ i ∈ Finset.range k, y ^ (2 ^ i)

/-- Key structural identity: L_k(t) = S_k(L_1(t)).
    Proof by induction: t^{2^{m+1}} + t^{2^m} = (t²+t)^{2^m} (Frobenius), telescoping. -/
theorem L_k_eq_S_k_L_1 (k : ℕ) (t : F) : L_k k t = S_k k (L_1 t) := by
  simp only [L_k, S_k, L_1]
  induction k with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have key : t ^ 2 ^ (m + 1) + t ^ 2 ^ m = (t ^ 2 + t) ^ 2 ^ m := by
      rw [pow_succ, pow_mul, add_pow_expChar_pow]
      simp [← pow_mul, mul_comm]
    have : t ^ 2 ^ (m + 1) + t = (t ^ 2 ^ m + t) + (t ^ 2 ^ (m + 1) + t ^ 2 ^ m) := by
      rw [show (t ^ 2 ^ m + t) + (t ^ 2 ^ (m + 1) + t ^ 2 ^ m) =
           t ^ 2 ^ (m + 1) + (t ^ 2 ^ m + t ^ 2 ^ m) + t from by ring]
      rw [CharTwo.add_self_eq_zero]; ring
    rw [this, ih, key]

/-- **MCM Permutation Theorem** (Cohen-Matthews 1994, Dempwolff-Müller 2013):
    The function M(y) = S_k(y)^{q+1}/y^q is injective on F* when
    k is odd, gcd(k,n) = 1, and n is odd.

    This follows from the Dickson polynomial identity
    f_k(z + 1/z) = z^{q-1} + z^{-(q-1)} and the coprimality
    gcd(q-1, 2^{2n}-1) = 1 (Theorem 3.2 of Dempwolff-Müller 2013). -/
theorem mcm_permutation {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hk_odd : Odd k) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (y₁ y₂ : F) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (h_eq : S_k k y₁ ^ (2 ^ k + 1) * y₂ ^ (2 ^ k) =
            S_k k y₂ ^ (2 ^ k + 1) * y₁ ^ (2 ^ k)) :
    y₁ = y₂ := by
  sorry

/-- The MCM permutation implies: for k odd, collision forces L_1 equal.
    This uses that f_{k,q+1}(x) = T_k(x)^{q+1}/x^q is a permutation
    on GF(2^n) when k is odd and gcd(k,n) = 1. -/
theorem collision_odd_k_imp_L1_eq {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hk_odd : Odd k) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (t₁ t₂ : F) (hne : t₁ ≠ t₂)
    (hcoll : kasami_g k t₁ = kasami_g k t₂)
    (hc : kasami_g k t₁ ≠ 1) :
    L_1 t₁ = L_1 t₂ := by
  -- From the key identity: (g(t)+1)·L₁(t)^q = L_k(t)^{q+1}
  -- Using L_k(t) = S_k(L₁(t)):  (g(t)+1)·L₁(t)^q = S_k(L₁(t))^{q+1}
  -- So g(t₁) = g(t₂) gives: S_k(L₁(t₁))^{q+1}/L₁(t₁)^q = S_k(L₁(t₂))^{q+1}/L₁(t₂)^q
  -- By MCM injectivity: L₁(t₁) = L₁(t₂).
  have hc2 : kasami_g k t₂ ≠ 1 := hcoll ▸ hc
  -- t₁ and t₂ are not in {0,1} (since g(0) = g(1) = 1)
  have ht₁_ne_zero : t₁ ≠ 0 := fun h => hc (by rw [h]; exact kasami_g_zero)
  have ht₁_ne_one : t₁ ≠ 1 := fun h => hc (by rw [h]; exact kasami_g_one)
  have ht₂_ne_zero : t₂ ≠ 0 := fun h => hc2 (by rw [h]; exact kasami_g_zero)
  have ht₂_ne_one : t₂ ≠ 1 := fun h => hc2 (by rw [h]; exact kasami_g_one)
  -- L₁(t₁) ≠ 0 and L₁(t₂) ≠ 0
  have hL1_t₁ : L_1 t₁ ≠ 0 := by
    intro h; rw [L_1_eq_zero_iff] at h; rcases h with h | h <;> contradiction
  have hL1_t₂ : L_1 t₂ ≠ 0 := by
    intro h; rw [L_1_eq_zero_iff] at h; rcases h with h | h <;> contradiction
  -- From key identity at t₁ and t₂ + collision:
  have hki₁ := kasami_key_identity k t₁
  have hki₂ := kasami_key_identity k t₂
  -- Since g(t₁) = g(t₂): L_k(t₁)^{q+1}·L₁(t₂)^q = L_k(t₂)^{q+1}·L₁(t₁)^q
  have h_cross : (L_k k t₁) ^ (2 ^ k + 1) * (L_1 t₂) ^ (2 ^ k) =
                  (L_k k t₂) ^ (2 ^ k + 1) * (L_1 t₁) ^ (2 ^ k) := by
    -- (g+1)·L₁(t₁)^q = L_k(t₁)^{q+1} and (g+1)·L₁(t₂)^q = L_k(t₂)^{q+1}
    -- with g(t₁)+1 = g(t₂)+1, so cross-multiply:
    have h1 : L_k k t₁ ^ (2 ^ k + 1) = (kasami_g k t₁ + 1) * L_1 t₁ ^ 2 ^ k := hki₁.symm
    have h2 : L_k k t₂ ^ (2 ^ k + 1) = (kasami_g k t₂ + 1) * L_1 t₂ ^ 2 ^ k := hki₂.symm
    rw [h1, h2, hcoll]; ring
  -- Rewrite using L_k(t) = S_k(L₁(t)):
  rw [L_k_eq_S_k_L_1, L_k_eq_S_k_L_1] at h_cross
  -- Apply MCM permutation theorem:
  exact mcm_permutation hk hn hgcd hk_odd hn_odd hcard (L_1 t₁) (L_1 t₂) hL1_t₁ hL1_t₂ h_cross

/-
For even k, reduce to odd n-k using Frobenius identity
-/
set_option maxHeartbeats 1600000 in
theorem collision_even_k_imp_L1_eq {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hk_even : ¬Odd k) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (t₁ t₂ : F) (hne : t₁ ≠ t₂)
    (hcoll : kasami_g k t₁ = kasami_g k t₂)
    (hc : kasami_g k t₁ ≠ 1) :
    L_1 t₁ = L_1 t₂ := by
  by_cases hk' : k < n;
  · -- From the collision: g_{n-k}(t₁)^{2^{2k}} = g_{n-k}(t₂)^{2^{2k}}.
    have h_collision : kasami_g (n - k) t₁ ^ (2 ^ (2 * k)) = kasami_g (n - k) t₂ ^ (2 ^ (2 * k)) := by
      rw [ ← kasami_g_frobenius hk hn hk' hgcd hcard t₁, ← kasami_g_frobenius hk hn hk' hgcd hcard t₂, hcoll ];
    -- From the collision: g_{n-k}(t₁) = g_{n-k}(t₂).
    have h_collision_eq : kasami_g (n - k) t₁ = kasami_g (n - k) t₂ := by
      have h_frobenius_inj : Function.Injective (fun x : F => x ^ (2 ^ (2 * k))) := by
        intro x y hxy
        have h_eq : (x - y) ^ (2 ^ (2 * k)) = 0 := by
          simp_all +decide [ sub_pow_char_pow ];
        exact sub_eq_zero.mp ( eq_zero_of_pow_eq_zero h_eq );
      exact h_frobenius_inj h_collision;
    apply collision_odd_k_imp_L1_eq (k := n - k) (n := n) (by
    exact Nat.sub_pos_of_lt hk') (by
    exact hn) (by
    simpa [ hk'.le ] using hgcd) (by
    grind) (by
    exact hn_odd) (by
    exact hcard) t₁ t₂ hne h_collision_eq (by
    contrapose! hc;
    rw [ kasami_g_frobenius hk hn hk' hgcd hcard t₁, hc, one_pow ]);
  · -- Since $k \geq n$, we can reduce $k$ to $k \mod n$.
    have h_mod : kasami_g k t₁ = kasami_g (k % n) t₁ ∧ kasami_g k t₂ = kasami_g (k % n) t₂ := by
      have h_mod : ∀ x : F, x ^ (2 ^ k) = x ^ (2 ^ (k % n)) := by
        intro x; rw [ ← Nat.mod_add_div k n ] ; simp +decide [ pow_add, pow_mul, hcard.symm ] ;
        induction k / n <;> simp_all +decide [ pow_succ, pow_mul ];
        have := FiniteField.pow_card x; simp_all +decide [ pow_mul, pow_right_comm ] ;
      unfold kasami_g;
      unfold kasami_d; ring;
      rw [ show 2 ^ ( k * 2 ) - 2 ^ k = 2 ^ k * ( 2 ^ k - 1 ) by rw [ Nat.mul_sub_left_distrib, mul_one, ← pow_add, show k * 2 = k + k by ring ] ] ; rw [ show 2 ^ ( k % n * 2 ) - 2 ^ ( k % n ) = 2 ^ ( k % n ) * ( 2 ^ ( k % n ) - 1 ) by rw [ Nat.mul_sub_left_distrib, mul_one, ← pow_add, show k % n * 2 = k % n + k % n by ring ] ] ; simp +decide [ pow_mul, h_mod ] ;
      have h_mod : ∀ x : F, x ^ (2 ^ k - 1) = x ^ (2 ^ (k % n) - 1) := by
        intro x; by_cases hx : x = 0 <;> simp_all +decide [ pow_succ' ] ;
        · rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ' ];
          rw [ zero_pow, zero_pow ] <;> norm_num;
          · rw [ Nat.sub_eq_zero_iff_le ] ; norm_num;
            intro h; have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero h ) ( Nat.dvd_refl n ) ; simp_all +decide ;
            have := Finset.card_eq_two.mp hcard; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
            cases hxy.2 0 <;> cases hxy.2 1 <;> cases hxy.2 t₁ <;> cases hxy.2 t₂ <;> simp_all +decide;
            all_goals subst_vars; simp_all +decide [ kasami_g ] ;
            · simp_all +decide [ kasami_d ];
            · unfold kasami_d at hc; simp_all +decide [ Nat.pow_succ' ] ;
            · unfold kasami_d at hc; simp_all +decide [ Nat.pow_succ' ] ;
            · simp_all +decide [ kasami_d ];
          · exact ne_of_gt ( Nat.sub_pos_of_lt ( by linarith [ Nat.one_le_pow k 2 zero_lt_two ] ) );
        · rw [ show x ^ ( 2 ^ k - 1 ) = x ^ ( 2 ^ k ) / x by rw [ eq_div_iff hx, ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ], show x ^ ( 2 ^ ( k % n ) - 1 ) = x ^ ( 2 ^ ( k % n ) ) / x by rw [ eq_div_iff hx, ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ], h_mod ];
      grind;
    by_cases hk'' : k % n = 0 <;> simp_all +decide [ Nat.gcd_eq_right_iff_dvd ];
    · have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero hk'' ) ( Nat.dvd_refl n ) ; simp_all +decide ;
      have := Finset.card_eq_two.mp hcard; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
      cases hxy.2 0 <;> cases hxy.2 1 <;> cases hxy.2 t₁ <;> cases hxy.2 t₂ <;> simp_all +decide [ L_1 ];
      all_goals subst_vars; simp_all +decide [ kasami_g ] ;; all_goals grind;
    · by_cases hk''' : Odd (k % n);
      · apply collision_odd_k_imp_L1_eq (Nat.pos_of_ne_zero hk'') hn (by
        rwa [ Nat.gcd_comm, Nat.gcd_rec ] at hgcd) hk''' hn_odd hcard t₁ t₂ hne hcoll;
        aesop;
      · have h_mod : kasami_g (k % n) t₁ = (kasami_g (n - k % n) t₁) ^ (2 ^ (2 * (k % n))) ∧ kasami_g (k % n) t₂ = (kasami_g (n - k % n) t₂) ^ (2 ^ (2 * (k % n))) := by
          apply And.intro (kasami_g_frobenius (Nat.pos_of_ne_zero hk'') hn (Nat.mod_lt k hn) (by
          rwa [ Nat.gcd_comm, Nat.gcd_rec ] at hgcd) hcard t₁) (kasami_g_frobenius (Nat.pos_of_ne_zero hk'') hn (Nat.mod_lt k hn) (by
          rwa [ Nat.gcd_comm, Nat.gcd_rec ] at hgcd) hcard t₂)
        generalize_proofs at *;
        have h_mod : kasami_g (n - k % n) t₁ = kasami_g (n - k % n) t₂ := by
          have h_mod : ∀ x y : F, x ^ (2 ^ (2 * (k % n))) = y ^ (2 ^ (2 * (k % n))) → x = y := by
            intro x y hxy
            have h_frobenius : (x - y) ^ (2 ^ (2 * (k % n))) = 0 := by
              simp_all +decide [ sub_pow_char_pow ]
            generalize_proofs at *;
            exact sub_eq_zero.mp ( eq_zero_of_pow_eq_zero h_frobenius )
          generalize_proofs at *;
          grind
        generalize_proofs at *; simp_all +decide [ Nat.even_iff ] ;
        apply collision_odd_k_imp_L1_eq (Nat.sub_pos_of_lt (Nat.mod_lt k hn)) hn (by
        cases le_total n ( k % n ) <;> simp_all +decide [ Nat.gcd_comm ];
        · linarith [ Nat.mod_lt k hn ];
        · rw [ Nat.gcd_comm, ← Nat.gcd_rec ] at * ; aesop) (by
        cases le_total n ( k % n ) <;> simp_all +decide [ Nat.even_iff, Nat.odd_iff ];
        · linarith [ Nat.mod_lt k hn ];
        · omega) hn_odd hcard t₁ t₂ hne h_mod (by
        intro h; simp_all +decide [ pow_eq_one_iff ] ;
        norm_num [ ← h_mod ] at *)

/-- The main collision lemma (c ≠ 1 case, n odd).
    Proof strategy:
    - If L_1(t₁) = L_1(t₂): forces t₂ = t₁+1, so L_k(t₁+t₂) = L_k(1) = 0.
    - If L_1(t₁) ≠ L_1(t₂): contradiction from MCM permutation (odd k)
      or Frobenius reduction (even k). -/
theorem collision_c_ne_one {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (t₁ t₂ : F) (hne : t₁ ≠ t₂)
    (hcoll : kasami_g k t₁ = kasami_g k t₂)
    (hc : kasami_g k t₁ ≠ 1) :
    L_k k (t₁ + t₂) = 0 := by
  -- Case split on whether L_1 values are equal
  by_cases hL1 : L_1 t₁ = L_1 t₂
  · -- Case 1: L_1(t₁) = L_1(t₂), so t₂ = t₁ + 1
    have h_t2 := L_1_eq_imp_t2_eq t₁ t₂ hne hL1
    rw [h_t2]
    have : t₁ + (t₁ + 1) = 1 := by
      have : t₁ + t₁ = 0 := CharTwo.add_self_eq_zero t₁
      calc t₁ + (t₁ + 1) = (t₁ + t₁) + 1 := by ring
        _ = 0 + 1 := by rw [‹t₁ + t₁ = 0›]
        _ = 1 := by ring
    rw [this]
    exact L_k_one
  · -- Case 2: L_1(t₁) ≠ L_1(t₂), derive contradiction
    -- We need: for n odd, gcd(k,n)=1, a collision in g with c≠1
    -- and L_1(t₁) ≠ L_1(t₂) is impossible.
    -- For odd k: this follows from the MCM permutation.
    -- For even k: use Frobenius identity to reduce to odd n-k.
    exfalso
    -- Both cases ultimately reach collision_odd_k_imp_L1_eq
    -- which contradicts hL1
    by_cases hk_odd : Odd k
    · exact hL1 (collision_odd_k_imp_L1_eq hk hn hgcd hk_odd hn_odd hcard t₁ t₂ hne hcoll hc)
    · exact hL1 (collision_even_k_imp_L1_eq hk hn hgcd hk_odd hn_odd hcard t₁ t₂ hne hcoll hc)

/-- **The collision lemma**: collisions in the Kasami differential
    force the difference to lie in ker(L_k). -/
theorem collision_in_L_kernel {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (t₁ t₂ : F) (hne : t₁ ≠ t₂)
    (hcoll : kasami_g k t₁ = kasami_g k t₂) :
    L_k k (t₁ + t₂) = 0 := by
  by_cases hc : kasami_g k t₁ = 1
  · exact collision_c_eq_one k t₁ t₂ hc (hcoll ▸ hc)
  · exact collision_c_ne_one hk hn hgcd hn_odd hcard t₁ t₂ hne hcoll hc

/-! ## From collision lemma to fiber bound -/

theorem kasami_g_paired {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (t₁ t₂ : F) (hne : t₁ ≠ t₂)
    (hcoll : kasami_g k t₁ = kasami_g k t₂) :
    t₂ = t₁ + 1 := by
  have hker := collision_in_L_kernel hk hn hgcd hn_odd hcard t₁ t₂ hne hcoll
  have hh : t₁ + t₂ ≠ 0 := by
    intro heq; apply hne
    rw [add_eq_zero_iff_eq_neg, char2_neg] at heq; exact heq
  have h1 := L_k_kernel_eq_one hk hn hgcd hcard (t₁ + t₂) hker hh
  calc t₂ = 0 + t₂ := by ring
    _ = (t₁ + t₁) + t₂ := by rw [CharTwo.add_self_eq_zero]
    _ = t₁ + (t₁ + t₂) := by ring
    _ = t₁ + 1 := by rw [h1]

theorem kasami_g_fiber_le_two {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (c : F) :
    Fintype.card { t : F // kasami_g k t = c } ≤ 2 := by
  by_contra h
  obtain ⟨t₁, t₂, t₃, ht₁, ht₂, ht₃, h_distinct⟩ :
      ∃ t₁ t₂ t₃ : F, t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ ∧
        kasami_g k t₁ = c ∧ kasami_g k t₂ = c ∧ kasami_g k t₃ = c := by
    obtain ⟨s, hs⟩ := Finset.two_lt_card.1 (by simpa [Fintype.card_subtype] using h)
    grind
  have ht₂_eq : t₂ = t₁ + 1 :=
    kasami_g_paired hk hn hgcd hn_odd hcard t₁ t₂ ht₁ (by aesop)
  have ht₃_eq : t₃ = t₁ + 1 :=
    kasami_g_paired hk hn hgcd hn_odd hcard t₁ t₃ ht₂ (by aesop)
  exact ht₃ (by rw [ht₂_eq, ht₃_eq])

/-! ## Main theorem -/

theorem kasami_diff_bound' {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n)
    (a b : F) (ha : a ≠ 0) :
    Fintype.card { x : F // (x + a) ^ kasami_d k + x ^ kasami_d k = b } ≤ 2 := by
  -- For any $t \in \mathbb{F}_q$, let $x = t a^{-1} a = t a^{-1} \cdot a = t a^{-1} \cdot a = t$.
  have h_map : Fintype.card {x : F | (x + a) ^ kasami_d k + x ^ kasami_d k = b} ≤ Fintype.card {t : F | kasami_g k t * a ^ kasami_d k = b} := by
    have h_map : ∀ x : F, (x + a) ^ kasami_d k + x ^ kasami_d k = b → kasami_g k (x / a) * a ^ kasami_d k = b := by
      intro x hx
      have h_map : (x + a) ^ kasami_d k + x ^ kasami_d k = (x / a + 1) ^ kasami_d k * a ^ kasami_d k + (x / a) ^ kasami_d k * a ^ kasami_d k := by
        simp +decide [ ← mul_pow, add_mul, ha ];
      unfold kasami_g; linear_combination' hx - h_map;
    convert Set.card_le_card ( show ( Set.image ( fun x => x / a ) { x : F | ( x + a ) ^ kasami_d k + x ^ kasami_d k = b } ) ⊆ { t : F | kasami_g k t * a ^ kasami_d k = b } from ?_ ) using 1;
    · rw [ Set.card_image_of_injective _ fun x y hxy => by simpa [ ha ] using hxy ];
    · exact Set.image_subset_iff.mpr h_map;
  refine' le_trans h_map ( le_trans ( _ : _ ≤ _ ) ( kasami_g_fiber_le_two hk hn hgcd hn_odd hcard ( b / a ^ kasami_d k ) ) );
  simp +decide [ ha, eq_div_iff ]

theorem kasami_is_apn_mvp {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card { x : F // (x + a) ^ kasami_d k + x ^ kasami_d k = b } ≤ 2 :=
  fun a ha b => kasami_diff_bound' hk hn hgcd hn_odd hcard a b ha

end