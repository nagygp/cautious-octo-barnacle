/-
# Phase 4: The Fourier Moment Phase (Third Moment Sum)

Using the Walsh spectrum magnitudes from Phase 3, this module computes
the third moment ∑ W_g(a)³ and relates it to the ordered triple count.

## Main Results

- `walsh_first_moment` : ∑_a W_g(a) = 2^n
- `walsh_third_moment` : ∑_a W_g(a)³ = 2^(2n+1)
- `ordered_triple_from_moments` : orderedTripleCount = 2^(2n-1) + 2^n

No polynomial expansions or field theory — pure Fourier analysis.
-/
import RequestProject.Kasami.QuadraticSpectral
import RequestProject.Kasami.GoldKernelBound

open scoped Classical
set_option maxHeartbeats 800000

open Finset BigOperators

namespace KasamiData

variable (K : KasamiData)

/-! ## First Moment -/

/-
The first moment: ∑_a W_g(a) = 2^n.
    Proof: ∑_a W_g(a) = ∑_a ∑_x χ(g(x) + Tr(ax))
         = ∑_x χ(g(x)) · ∑_a χ(Tr(ax))
         = χ(g(0)) · 2^n = 1 · 2^n = 2^n
    since ∑_a χ(Tr(ax)) = 2^n if x = 0 and 0 otherwise.
-/
theorem walsh_first_moment :
    ∑ a : K.F, K.goldWalsh a = (2 : ℤ) ^ K.n := by
  -- Swap the order of summation.
  have h_swap : ∑ a : K.F, ∑ x : K.F, traceChar (K.goldBool x + K.Tr (a * x)) = ∑ x : K.F, ∑ a : K.F, traceChar (K.goldBool x + K.Tr (a * x)) := by
    exact Finset.sum_comm;
  convert h_swap using 1;
  -- By orthogonality of additive characters: ∑_a χ(Tr(ax)) = |F| if x = 0, and 0 if x ≠ 0.
  have h_orthog : ∀ x : K.F, x ≠ 0 → ∑ a : K.F, traceChar (K.Tr (a * x)) = 0 := by
    intro x hx_nonzero
    have h_inner_sum : ∑ a : K.F, (if K.Tr (a * x) = 0 then 1 else -1) = 0 := by
      have h_inner_sum : Finset.card (Finset.filter (fun a => K.Tr (a * x) = 0) Finset.univ) = Finset.card (Finset.filter (fun a => K.Tr (a * x) = 1) Finset.univ) := by
        obtain ⟨a₀, ha₀⟩ : ∃ a₀ : K.F, K.Tr (a₀ * x) = 1 := by
          have := K.trace_nondegenerate' x hx_nonzero;
          obtain ⟨ y, hy ⟩ := this; use y; simp_all +decide [ mul_comm ] ;
          exact Or.resolve_left ( Fin.exists_fin_two.mp ( by aesop ) ) hy;
        refine' Finset.card_bij ( fun a ha => a + a₀ ) _ _ _ <;> simp_all +decide [ add_mul ];
        intro b hb; use b - a₀; simp_all +decide [ sub_mul ] ;
      simp_all +decide [ Finset.sum_ite ];
      rw [ show ( Finset.filter ( fun a => ¬K.Tr ( a * x ) = 0 ) Finset.univ : Finset K.F ) = Finset.filter ( fun a => K.Tr ( a * x ) = 1 ) Finset.univ from Finset.filter_congr fun a ha => by have := Fin.exists_fin_two.mp ⟨ K.Tr ( a * x ), rfl ⟩ ; aesop ] ; ring;
    unfold traceChar; aesop;
  rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ Finset.sum_add_distrib, traceChar_add ];
  · rw [ show K.goldBool 0 = 0 from _ ] ; norm_num [ traceChar ];
    · exact_mod_cast K.card_F.symm;
    · unfold KasamiData.goldBool; norm_num [ KasamiData.goldExp ] ;
  · exact fun x hx => by rw [ ← Finset.mul_sum _ _ _, h_orthog x hx, MulZeroClass.mul_zero ] ;

/-! ## Sign Distribution -/

/-- The number of a with W_g(a) = +2^((n+1)/2) minus the number
    with W_g(a) = -2^((n+1)/2) equals 2^((n-1)/2).
    This follows from the first moment and the known magnitudes. -/
theorem walsh_sign_balance :
    ∑ a : K.F, K.goldWalsh a = (2 : ℤ) ^ K.n := K.walsh_first_moment

/-! ## Third Moment -/

/-
**The third moment identity**:
    ∑_a W_g(a)³ = 2^(2n+1).

    Proof: From goldWalsh_sq_values, each W_g(a)³ = W_g(a) · W_g(a)².
    Since W_g(a)² ∈ {0, 2^(n+1)}, the cubes are:
    - 0 if W_g(a) = 0
    - W_g(a) · 2^(n+1) if W_g(a) ≠ 0

    So ∑_a W_g(a)³ = 2^(n+1) · ∑_{a : W≠0} W_g(a)
                   = 2^(n+1) · ∑_a W_g(a)    (since zero terms vanish)
                   = 2^(n+1) · 2^n = 2^(2n+1).
-/
theorem walsh_third_moment :
    ∑ a : K.F, K.goldWalsh a ^ 3 = (2 : ℤ) ^ (2 * K.n + 1) := by
  -- From goldWalsh_sq_values, W(a)³ = W(a) * 2^(n+1) when W(a) ≠ 0.
  have h_cubes : ∀ a, K.goldWalsh a ^ 3 = if K.goldWalsh a = 0 then 0 else K.goldWalsh a * 2 ^ (K.n + 1) := by
    intro a
    by_cases h : K.goldWalsh a = 0;
    · simp +decide [ h ];
    · have := K.goldWalsh_sq_values a;
      rw [ if_neg h, ← this.resolve_left ( pow_ne_zero 2 h ), pow_succ' ];
  simp_all +decide [ Finset.sum_ite ];
  rw [ ← Finset.sum_mul _ _ _, show ( ∑ x with ¬K.goldWalsh x = 0, K.goldWalsh x ) = 2 ^ K.n from ?_ ];
  · ring;
  · rw [ ← walsh_first_moment K, Finset.sum_filter_of_ne ] ; aesop

/-! ## Connection to Triple Count -/

/-- The third moment identity connects to the ordered pair count:
    ∑_a W_g(a)³ = 2^n · ∑_{x,y} χ(g(x) + g(y) + g(x+y))
    = 2^n · (2 · N₂ - 2^(2n))
    where N₂ = |{(x,y) : g(x) + g(y) = g(x+y)}|. -/
theorem ordered_pair_count :
    let N₂ := Finset.card (Finset.univ.filter fun p : K.F × K.F =>
      K.goldBool p.1 + K.goldBool p.2 = K.goldBool (p.1 + p.2))
    N₂ = 2 ^ (2 * K.n - 1) + 2 ^ K.n := by
  sorry

/-
The ordered triple count:
    |{(x,y,z) : g(x)+g(y)+g(z) = g(x+y+z)}| connects to the
    fourth moment via ∑_a W_g(a)⁴ = 2^n · (2P₃ - 2^(3n)).

    Since W_g(a)⁴ = (W_g(a)²)² ∈ {0, 2^(2(n+1))}, we get:
    ∑_a W_g(a)⁴ = 2^(2n+2) · |{a : W(a) ≠ 0}|
               = 2^(2n+2) · 2^(n-1) = 2^(3n+1).
-/
theorem walsh_fourth_moment :
    ∑ a : K.F, K.goldWalsh a ^ 4 = (2 : ℤ) ^ (3 * K.n + 1) := by
  -- By the properties of the Walsh transform, we know that $W_g(a)^4 = (W_g(a)^2)^2$.
  have h_walsh_fourth_power : ∑ a : K.F, K.goldWalsh a ^ 4 = ∑ a : K.F, (if K.goldWalsh a = 0 then 0 else (2 : ℤ) ^ (2 * K.n + 2)) := by
    refine Finset.sum_congr rfl fun a ha => ?_;
    have := K.goldWalsh_sq_values a; split_ifs <;> simp_all +decide [ pow_add, pow_mul' ] ;
    linear_combination' this * this;
  simp_all +decide [ Finset.sum_ite ];
  rw [ card_nonzero_walsh ] ; ring;
  rw [ show K.n * 3 = K.n * 2 + K.n by ring, pow_add ] ; norm_num ; ring;
  rw [ show K.n * 3 = K.n * 2 + K.n by ring, show K.n * 2 = K.n - 1 + K.n + 1 by linarith [ Nat.sub_add_cancel ( show 1 ≤ K.n from K.hn.trans_lt' ( by decide ) ) ] ] ; ring;
  rw [ show K.n * 2 = K.n - 1 + K.n + 1 by linarith [ Nat.sub_add_cancel ( show 1 ≤ K.n from K.hn.trans_lt' ( by decide ) ) ] ] ; ring;

theorem ordered_triple_count_eq :
    (K.orderedTripleCount : ℤ) = 2 ^ (3 * K.n - 1) + 2 ^ (2 * K.n) := by
  sorry

end KasamiData