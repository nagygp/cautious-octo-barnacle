/-
# Five Foundational MVPs for `kasami_ax_factorization`

All five exploit the same algebraic backbone:
1. **Universal Identity**: S(t)^{q+1} = L_{3k}(t) + 1 + Cross_k(t^d, (t+1)^d)
2. **KEY Identity**: For Δ(c) = 0, Cross_k(β, P(c)) = L_{3k}(c)
3. **Bridge**: Cross_k(β, P) = N_k(β)·L_k(P/β) (proved as bridge_2_4)
4. **Injection**: c ↦ P(c)/β is injective (x ↦ x^d is permutation when n odd)
5. **Kernel Landing**: L_{3k}(c) = 0 for collisions, so P(c)/β ∈ ker(L_k)
-/
import Mathlib
import Strategy.Bridges.EquivalentContexts

set_option maxHeartbeats 800000

namespace KasamiFive

open Finset Fintype EquivalentContexts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ═══════════════════════════════════════════════════════════════════
    SHARED INFRASTRUCTURE
    ═══════════════════════════════════════════════════════════════════ -/

/-- L_k as AddMonoidHom. -/
noncomputable def L_hom (k : ℕ) : F →+ F where
  toFun x := x ^ (2 ^ k) + x
  map_zero' := by simp
  map_add' x y := by simp [add_pow_expChar_pow x y 2 k]; ring

/-- P(c) = t₀^d + (t₀+c)^d: the partial differential. -/
noncomputable def P_val (k : ℕ) (t₀ c : F) : F :=
  t₀ ^ d k + (t₀ + c) ^ d k

theorem P_zero (k : ℕ) (t₀ : F) : P_val k t₀ 0 = 0 := by
  unfold P_val; simp; exact CharTwo.add_self_eq_zero _

/-- Fibers of an AddMonoidHom have card ≤ kernel card. -/
theorem addHom_fiber_le (f : F →+ F) (γ : F) :
    Fintype.card {x : F // f x = γ} ≤ Fintype.card {x : F // f x = 0} := by
  by_cases hne : ∃ x₀, f x₀ = γ
  · obtain ⟨x₀, h₀⟩ := hne
    apply le_of_eq
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨x, hx⟩ => ⟨x + x₀, by
        show f (x + x₀) = 0; rw [f.map_add, hx, h₀, CharTwo.add_self_eq_zero]⟩
      invFun := fun ⟨x, hx⟩ => ⟨x + x₀, by
        show f (x + x₀) = γ; rw [f.map_add, hx, h₀, zero_add]⟩
      left_inv := fun ⟨x, _⟩ => Subtype.ext (by
        show x + x₀ + x₀ = x; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])
      right_inv := fun ⟨x, _⟩ => Subtype.ext (by
        show x + x₀ + x₀ = x; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])
    }
  · push_neg at hne
    have h0 : Fintype.card {x : F // f x = γ} = 0 := by
      rw [Fintype.card_eq_zero_iff]; exact ⟨fun ⟨x, hx⟩ => (hne x hx).elim⟩
    omega

/-! ═══════════════════════════════════════════════════════════════════
    MVP F1 — Cross Identity Approach
    ═══════════════════════════════════════════════════════════════════

    Prove the universal polynomial identity, derive the KEY identity
    for collisions, show P(c)/β ∈ ker(L_k), get injection.
-/

namespace MVP_F1

/-
**Universal Identity**: S(t)^{q+1} = L_{3k}(t) + 1 + Cross_k(t^d, (t+1)^d).
-/
theorem universal_identity (k : ℕ) (t : F) :
    ((t + 1) ^ d k + t ^ d k) ^ (2 ^ k + 1) =
    (t ^ (2 ^ (3 * k)) + t) + 1 +
    (t ^ d k * ((t + 1) ^ d k) ^ (2 ^ k) +
     (t ^ d k) ^ (2 ^ k) * (t + 1) ^ d k) := by
  have h_identity : ((t + 1) ^ d k) ^ (2 ^ k + 1) + (t ^ d k) ^ (2 ^ k + 1) = t ^ (2 ^ (3 * k)) + t + 1 := by
    rw [ ← pow_mul, ← pow_mul ];
    rw [ show d k * ( 2 ^ k + 1 ) = 2 ^ ( 3 * k ) + 1 by
          rw [ d ] ; ring;
          zify ; ring;
          rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring ];
    convert gold_diff_expand ( 3 * k ) t 1 using 1 ; ring;
  rw [ ← h_identity ] ; ring;
  rw [ add_pow_char_pow, pow_mul, pow_mul ] ; ring

/-
**KEY Identity**: For Δ(c) = 0, Cross_k(β, P(c)) = L_{3k}(c).
-/
theorem key_identity (k : ℕ) (t₀ c β : F)
    (hβ : (t₀ + 1) ^ d k + t₀ ^ d k = β)
    (hΔ : (t₀ + c + 1) ^ d k + (t₀ + c) ^ d k = β) :
    β * (P_val k t₀ c) ^ (2 ^ k) + β ^ (2 ^ k) * P_val k t₀ c =
    c ^ (2 ^ (3 * k)) + c := by
  have hL3kadDED : ((t₀ + 1) ^ d k + t₀ ^ d k) ^ (2 ^ k + 1) = (t₀ ^ (2 ^ (3 * k)) + t₀) + 1 + Cross k (t₀ ^ d k) ((t₀ + 1) ^ d k) := by
    convert universal_identity k t₀ using 1;
  have hL3kadDEDc : β ^ (2 ^ k + 1) = (t₀ + c) ^ (2 ^ (3 * k)) + (t₀ + c) + 1 + Cross k ((t₀ + c) ^ d k) ((t₀ + c + 1) ^ d k) := by
    rw [ ← hΔ ];
    convert universal_identity k ( t₀ + c ) using 1;
  -- Substitute hβ and hΔ into hL3kadDED and hL3kadDEDc.
  have hL3kadDED_subst : β ^ (2 ^ k + 1) = t₀ ^ (2 ^ (3 * k)) + t₀ + 1 + Cross k (t₀ ^ d k) (β + t₀ ^ d k) := by
    grind
  have hL3kadDEDc_subst : β ^ (2 ^ k + 1) = (t₀ + c) ^ (2 ^ (3 * k)) + (t₀ + c) + 1 + Cross k ((t₀ + c) ^ d k) (β + (t₀ + c) ^ d k) := by
    grind +qlia;
  simp_all +decide [ Cross ];
  simp_all +decide [ P_val, add_pow_expChar_pow ];
  grind +ring

/-- **Kernel Landing**: For collisions, P(c)/β ∈ ker(L_k). -/
theorem kernel_landing (k : ℕ) (t₀ β : F) (hβ : β ≠ 0)
    (hβ_eq : (t₀ + 1) ^ d k + t₀ ^ d k = β)
    (c : F) (hΔ : (t₀ + c + 1) ^ d k + (t₀ + c) ^ d k = β) :
    L k (P_val k t₀ c / β) = 0 := by
  sorry

/-- **MVP F1 Main** -/
theorem main {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (hk : k ≥ 1) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤
        Fintype.card {x : F // L k x = 0} := by
  sorry

end MVP_F1

/-! ═══════════════════════════════════════════════════════════════════
    MVP F2 — Polynomial Root Bound
    ═══════════════════════════════════════════════════════════════════

    Use Cross_k(β, ·) as additive map. Fiber bound from kernel size.
-/

namespace MVP_F2

/-- Cross_k(β, ·) as an AddMonoidHom. -/
noncomputable def cross_hom (k : ℕ) (β : F) : F →+ F where
  toFun P := β * P ^ (2 ^ k) + β ^ (2 ^ k) * P
  map_zero' := by simp
  map_add' P₁ P₂ := by rw [add_pow_expChar_pow]; ring

/-
The kernel of Cross_k(β, ·) has the same size as ker(L_k).
-/
theorem cross_ker_card (k : ℕ) (β : F) (hβ : β ≠ 0) :
    Fintype.card {P : F // cross_hom k β P = 0} =
    Fintype.card {x : F // L k x = 0} := by
  -- The map P P/β is a bijection between the two sets.
  have h_bij : {P : F | cross_hom k β P = 0} = (fun x => β * x) '' {x : F | L k x = 0} := by
    have h_bij : ∀ P : F, cross_hom k β P = 0 ↔ L k (P / β) = 0 := by
      convert cross_zero_iff_kernel k β using 1;
      aesop;
    ext P; simp [h_bij];
    exact ⟨ fun h => ⟨ P / β, h, mul_div_cancel₀ _ hβ ⟩, by rintro ⟨ x, hx, rfl ⟩ ; simpa [ mul_div_cancel_left₀ _ hβ ] using hx ⟩;
  rw [ Set.ext_iff ] at h_bij;
  rw [ Fintype.card_subtype, Fintype.card_subtype ];
  rw [ show ( Finset.filter ( fun x => ( cross_hom k β ) x = 0 ) Finset.univ ) = Finset.image ( fun x => β * x ) ( Finset.filter ( fun x => L k x = 0 ) Finset.univ ) from Finset.ext fun x => by aesop ] ; rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ hβ hxy ] ;

/-- **MVP F2 Main** -/
theorem main {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (hk : k ≥ 1) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤
        Fintype.card {x : F // L k x = 0} := by
  sorry

end MVP_F2

/-! ═══════════════════════════════════════════════════════════════════
    MVP F3 — Permutation Injection
    ═══════════════════════════════════════════════════════════════════

    Since x^d is a permutation, collision map c ↦ (t₀+c)^d is injective.
    Combined with Cross-kernel factorization → injection into ker(L_k).
-/

namespace MVP_F3

/-
When n is odd, x ↦ x^d is a permutation.
-/
theorem kasami_power_bijective {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (hk : k ≥ 1) :
    Function.Bijective (fun (x : F) => x ^ d k) := by
  have h_perm : Nat.Coprime (d k) (2 ^ n - 1) := by
    -- Since $2^n - 1$ is odd and $d_k$ is odd, their greatest common divisor must be 1.
    have h_odd_gcd : Nat.gcd (2 ^ n - 1) (2 ^ (3 * k) + 1) = 1 := by
      refine' Nat.Coprime.symm _;
      refine' Nat.Coprime.symm ( Nat.coprime_of_dvd' _ );
      intro p pp dk dk'; haveI := Fact.mk pp; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Nat.pow_mod ] ;
      -- Since $p$ divides $2^n - 1$, we have $2^n \equiv 1 \pmod{p}$.
      have h_order : orderOf (2 : ZMod p) ∣ n ∧ orderOf (2 : ZMod p) ∣ 6 * k := by
        simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
        exact ⟨ sub_eq_zero.mp dk, by linear_combination' dk' * ( 2 ^ ( 3 * k ) - 1 ) ⟩;
      -- Since $p$ divides $2^{3k} + 1$, we have $2^{3k} \equiv -1 \pmod{p}$.
      have h_order_3k : orderOf (2 : ZMod p) ∣ 6 * k ∧ ¬(orderOf (2 : ZMod p) ∣ 3 * k) := by
        simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ]; all_goals grind;
      -- Since $orderOf (2 : ZMod p)$ divides $6k$ but not $3k$, it must be that $orderOf (2 : ZMod p)$ is even.
      have h_order_even : Even (orderOf (2 : ZMod p)) := by
        contrapose! h_order_3k;
        exact fun h => Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime ( orderOf ( 2 : ZMod p ) ) 2 from Nat.Coprime.symm ( Nat.prime_two.coprime_iff_not_dvd.mpr fun h => h_order_3k <| even_iff_two_dvd.mpr h ) ) <| by convert h using 1; ring;
      exact absurd ( hn.of_dvd_nat h_order.1 ) ( by simp +decide [ h_order_even ] );
    refine' Nat.Coprime.symm ( Nat.Coprime.coprime_dvd_right _ h_odd_gcd );
    convert Nat.dvd_mul_right ( d k ) ( 2 ^ k + 1 ) using 1 ; zify ; norm_num [ d ] ; ring;
    rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
  convert bridge_6_to_7 k n hcard _;
  · exact ⟨ fun h => fun _ => h, fun h => h h_perm ⟩;
  · exact hn.pos

/-
Injection from collisions to ker(L_k).
-/
theorem collision_to_ker (k : ℕ) (hk : k ≥ 1) {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hn : Odd n)
    (t₀ β : F) (hβ : β ≠ 0)
    (hβ_eq : (t₀ + 1) ^ d k + t₀ ^ d k = β) :
    ∃ (f : {c : F // (t₀ + c + 1) ^ d k + (t₀ + c) ^ d k = β} →
            {x : F // L k x = 0}),
      Function.Injective f := by
  by_contra h_contra;
  -- By the properties of the Kasami function and the fact that $n$ is odd, we know that $β$ is non-zero.
  have hβ_ne_zero : β ≠ 0 := by
    exact hβ;
  exact h_contra ⟨ fun x => ⟨ P_val k t₀ x / β, by
    apply MVP_F1.kernel_landing k t₀ β hβ_ne_zero hβ_eq x.val x.2 ⟩, fun x y hxy => by
    have h_inj : Function.Injective (fun x : F => x ^ d k) := by
      exact ( kasami_power_bijective hcard hn k hk ).injective;
    simp_all +decide [ div_eq_iff, P_val ];
    exact Subtype.ext ( by simpa using h_inj hxy ) ⟩

/-- **MVP F3 Main** -/
theorem main {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (hk : k ≥ 1) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤
        Fintype.card {x : F // L k x = 0} := by
  sorry

end MVP_F3

/-! ═══════════════════════════════════════════════════════════════════
    MVP F4 — Direct Cross Fiber Bound
    ═══════════════════════════════════════════════════════════════════

    View the collision set as mapping into a fiber of Cross_k(β,·).
    The fiber has size |ker(L_k)| (since Cross is an AddMonoidHom).
-/

namespace MVP_F4

/-- Cross_k(β, ·) as an AddMonoidHom. -/
noncomputable def cross_hom (k : ℕ) (β : F) : F →+ F where
  toFun P := β * P ^ (2 ^ k) + β ^ (2 ^ k) * P
  map_zero' := by simp
  map_add' P₁ P₂ := by rw [add_pow_expChar_pow]; ring

/-
The collision set injects into a Cross fiber.
-/
theorem collision_bound (k : ℕ) (hk : k ≥ 1) {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hn : Odd n)
    (t₀ β : F) (hβ_eq : (t₀ + 1) ^ d k + t₀ ^ d k = β) :
    Fintype.card {c : F // (t₀ + c + 1) ^ d k + (t₀ + c) ^ d k = β} ≤
      Fintype.card {x : F // L k x = 0} := by
  have := @MVP_F3.main F;
  convert this hcard hn k hk 1 one_ne_zero β using 1;
  rw [ Fintype.card_subtype, Fintype.card_subtype ];
  rw [ Finset.card_filter, Finset.card_filter ];
  rw [ ← Equiv.sum_comp ( Equiv.addLeft t₀ ) ] ; simp +decide [ add_assoc ];
  simp +decide [ ← add_assoc, CharTwo.add_self_eq_zero ]

/-
**MVP F4 Main**
-/
theorem main {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (hk : k ≥ 1) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤
        Fintype.card {x : F // L k x = 0} := by
  convert MVP_F3.main hcard hn k hk using 1

end MVP_F4

/-! ═══════════════════════════════════════════════════════════════════
    MVP F5 — Gold Transfer via Raising
    ═══════════════════════════════════════════════════════════════════

    Raise the Kasami equation to the (q+1)-th power.
    Using d·(q+1) = q³+1, convert to Gold at parameter 3k.
    Transfer the Gold bound (already proved in gold_ax_factorization).
-/

namespace MVP_F5

/-- **MVP F5 Main**: via Gold transfer. -/
theorem main {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (hk : k ≥ 1) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤
        Fintype.card {x : F // L k x = 0} := by
  sorry

end MVP_F5

end KasamiFive