import Mathlib
import RequestProject.KasamiPolarExpansion

/-!
# Gold Linearized Operator — Kernel Bound

For the Gold linearized operator L_a(y) = a·y^(2^k) + a^(2^(k+1))·y^(2^(k+1))
over GF(2^n) with n = 2k+1, we prove |ker(L_a)| ≤ 2 for a ≠ 0.

## Key Insight

When n = 2k+1, the operator L_a factors through the substitution w = y^(2^k):

  L_a(y) = w · (a + a^(2^(k+1)) · w)

This is a quadratic in w, giving at most 2 roots for w.
Since the Frobenius y ↦ y^(2^k) is a bijection, each root w
determines at most one y, so |ker(L_a)| ≤ 2.
-/

open scoped BigOperators

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

noncomputable section GoldKernelBound

variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [FiniteDimensional (ZMod 2) F] [Algebra.IsSeparable (ZMod 2) F]

instance gkbCharP : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

/-- The key factoring: when n - k = k + 1, the Gold operator factors as
    w · (a + a^(2^(k+1)) · w) where w = y^(2^k). -/
lemma goldLinearizedOp_factor (k : ℕ) (a y : F)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    goldLinearizedOp k a y =
    y ^ (2 ^ k) * (a + a ^ (2 ^ (k + 1)) * y ^ (2 ^ k)) := by
  unfold goldLinearizedOp
  rw [show Module.finrank (ZMod 2) F - k = k + 1 from by omega]
  have : y ^ (2 ^ (k + 1)) = (y ^ (2 ^ k)) ^ 2 := by
    rw [pow_succ 2 k, pow_mul]
  rw [this]
  ring

/-- The Frobenius y ↦ y^(2^k) is injective. -/
lemma frobenius_injective (k : ℕ) :
    Function.Injective (fun y : F => y ^ (2 ^ k)) := by
  intro x y hxy
  have : Function.Injective (fun z : F => z ^ 2) := by
    intro a b hab
    simp [sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq] at hab
    exact hab
  have h_inj_pow : ∀ m : ℕ, Function.Injective (fun z : F => z ^ (2 ^ m)) := by
    intro m
    induction m with
    | zero => simp [Function.Injective]
    | succ m ih =>
      intro a b hab
      have : (a ^ (2 ^ m)) ^ 2 = (b ^ (2 ^ m)) ^ 2 := by
        simp only [show (2 : ℕ) ^ (m + 1) = 2 ^ m * 2 from by ring] at hab
        rwa [pow_mul, pow_mul] at hab
      exact ih (‹Function.Injective (fun z : F => z ^ 2)› this)
  exact h_inj_pow k hxy

/-
**Gold kernel bound for n = 2k + 1.**
    The kernel of L_a has at most 2 elements when a ≠ 0.

    Proof: L_a(y) = w · (a + a^(2^(k+1)) · w) where w = y^(2^k).
    So L_a(y) = 0 iff w = 0 or w = -a · a^(-2^(k+1)).
    Each value of w determines at most one y (Frobenius injectivity).
    The case w = 0 gives y = 0.
    The second case gives at most one additional y₀.
-/
theorem gold_ker_le_two_kasami (k : ℕ) (a : F) (ha : a ≠ 0)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    Finset.card (Finset.filter (fun y => goldLinearizedOp k a y = 0) Finset.univ) ≤ 2 := by
  -- The polynomial $w * (a + a^{2^{k+1}} * w)$ has at most 2 roots in $w$.
  have h_poly_roots : {w : F | w * (a + a ^ (2 ^ (k + 1)) * w) = 0}.ncard ≤ 2 := by
    rw [ show { w : F | w * ( a + a ^ 2 ^ ( k + 1 ) * w ) = 0 } = ( { 0 } ∪ { -a / a ^ 2 ^ ( k + 1 ) } : Set F ) from ?_ ];
    · exact le_trans ( Set.ncard_union_le _ _ ) ( by norm_num );
    · grind;
  rw [ ← Set.ncard_coe_finset ];
  refine' le_trans _ h_poly_roots;
  rw [ ← Set.ncard_image_of_injective _ ( frobenius_injective k ) ];
  refine' Set.ncard_le_ncard _;
  simp +decide [ goldLinearizedOp_factor k a _ hn ]

end GoldKernelBound