import Mathlib
import RequestProject.KasamiPolarExpansion
import RequestProject.CCDCounting
import RequestProject.GoldKernelBound

/-!
# Walsh Transform via Radical Factorization

Proves the AB property (Walsh spectrum {0, ±2^((n+1)/2)}) for the Gold function
f(x) = Tr(x^{2^k+1}) over GF(2^n) with n = 2k+1 odd.

## Key Identity

W(a)² = |F| · (1 + chiInt(1 + a))

where chiInt(w) = (-1)^{Tr(w)}. This gives:
- W(a)² = 2^{n+1} when Tr(a) = 1  (since Tr(1) = 1 for n odd)
- W(a)² = 0 when Tr(a) = 0
-/

open scoped BigOperators

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

noncomputable section WalshRadical

variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [FiniteDimensional (ZMod 2) F] [Algebra.IsSeparable (ZMod 2) F]

instance wrCharP : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

/-! ## chiInt -/

/-- chiInt(w) = (-1)^{Tr(w)} as an integer. -/
def chiInt' (w : F) : ℤ :=
  if (fieldTrace w : ZMod 2).val = 0 then 1 else -1

/-- chiInt is multiplicative: chiInt(u) · chiInt(v) = chiInt(u + v). -/
lemma chiInt'_mul (u v : F) : chiInt' u * chiInt' v = chiInt' (u + v) := by
  unfold chiInt'
  simp only [map_add]
  rcases Fin.exists_fin_two.mp ⟨fieldTrace u, rfl⟩ with hu | hu <;>
  rcases Fin.exists_fin_two.mp ⟨fieldTrace v, rfl⟩ with hv | hv <;>
  simp +decide [hu, hv]

/-- chiInt(0) = 1. -/
@[simp] lemma chiInt'_zero : chiInt' (0 : F) = 1 := by
  simp [chiInt', map_zero]

/-! ## Trace lemmas -/

/-- Tr(y^{2^k}) = Tr(y) for all y (Frobenius invariance). -/
lemma trace_frob (k : ℕ) (y : F) :
    fieldTrace (y ^ (2 ^ k)) = fieldTrace y :=
  trace_frobenius_inv y k

/-- Tr(y^{2^k} + y) = 0 for all y. -/
lemma trace_frob_plus_id (k : ℕ) (y : F) :
    fieldTrace (y ^ (2 ^ k) + y) = 0 := by
  simp [map_add, trace_frob k y, CharTwo.add_self_eq_zero]

/-- Tr(1) = [F : GF(2)] as an element of ZMod 2. -/
lemma trace_one_eq_finrank :
    fieldTrace (1 : F) = (Module.finrank (ZMod 2) F : ZMod 2) := by
  have : (Algebra.lmul (ZMod 2) F) 1 = LinearMap.id := by ext; simp
  rw [fieldTrace, Algebra.trace_apply, this, LinearMap.trace_id]

/-- Tr(1) = 1 when n is odd. -/
lemma trace_one_odd (hn_odd : ¬ 2 ∣ Module.finrank (ZMod 2) F) :
    (fieldTrace (1 : F) : ZMod 2) = 1 := by
  rw [trace_one_eq_finrank]
  have h1 : Module.finrank (ZMod 2) F % 2 = 1 := by omega
  exact (ZMod.val_eq_one (by omega) (a := (Module.finrank (ZMod 2) F : ZMod 2))).mp
    (by rw [ZMod.val_natCast]; exact h1)

/-! ## Unweighted linearized polynomial -/

/-- L(y) = y^{2^k} + y^{2^{n-k}}. -/
def unweightedLinOp (k : ℕ) (y : F) : F :=
  y ^ (2 ^ k) + y ^ (2 ^ (Module.finrank (ZMod 2) F - k))

/-- When n = 2k+1: L(y) = y^{2^k} + y^{2^{k+1}}. -/
lemma unweightedLinOp_eq (k : ℕ) (y : F)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    unweightedLinOp k y = y ^ (2 ^ k) + y ^ (2 ^ (k + 1)) := by
  unfold unweightedLinOp; congr 2; congr 1; omega

/-- L(0) = 0. -/
@[simp] lemma unweightedLinOp_zero (k : ℕ) : unweightedLinOp k (0 : F) = 0 := by
  simp [unweightedLinOp]

/-- L(1) = 0. -/
@[simp] lemma unweightedLinOp_one (k : ℕ) : unweightedLinOp k (1 : F) = 0 := by
  simp [unweightedLinOp, CharTwo.add_self_eq_zero]

/-
The kernel of L has at most 2 elements when n = 2k+1.
-/
theorem unweighted_ker_le_two (k : ℕ)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    (Finset.filter (fun y : F => unweightedLinOp k y = 0) Finset.univ).card ≤ 2 := by
  -- When n = 2k+1, L(y) = y^{2^k} + y^{2^{k+1}} = w + w^2 where w = y^{2^k}. So L(y) = 0 iff w(1+w) = 0 iff w ∈ {0,1}.
  have h_w : ∀ y : F, unweightedLinOp k y = 0 ↔ y ^ (2 ^ k) = 0 ∨ y ^ (2 ^ k) = 1 := by
    intro y; simp [unweightedLinOp_eq k y hn]; (
    have h_frobenius : ∀ y : F, y ^ 2 = y ↔ y = 0 ∨ y = 1 := by
      exact fun x => ⟨ fun hx => or_iff_not_imp_left.mpr fun hx' => mul_left_cancel₀ hx' <| by linear_combination hx, fun hx => hx.elim ( fun hx => by simp +decide [ hx ] ) fun hx => by simp +decide [ hx ] ⟩;
    specialize h_frobenius ( y ^ 2 ^ k ) ; simp_all +decide [ pow_succ, pow_mul ] ;
    grind);
  -- Since $y^{2^k} = 0$ or $y^{2^k} = 1$ implies $y = 0$ or $y = 1$, the set of such $y$ has cardinality at most 2.
  have h_card : {y : F | y ^ (2 ^ k) = 0 ∨ y ^ (2 ^ k) = 1}.ncard ≤ 2 := by
    have h_card : {y : F | y ^ (2 ^ k) = 0 ∨ y ^ (2 ^ k) = 1} ⊆ {0, 1} := by
      intro y hy; cases hy <;> simp_all +decide [ pow_eq_zero_iff' ] ;
      have := @frobenius_injective F _ _ _ _ _ k; have := @this y 1; aesop;
    exact le_trans ( Set.ncard_le_ncard h_card ) ( Set.ncard_insert_le _ _ ) |> le_trans <| by norm_num;
  simpa [ ← Set.ncard_coe_finset, h_w ] using h_card

/-
The kernel of L is exactly {y : y = 0 ∨ y = 1}.
-/
theorem unweighted_kernel_char (k : ℕ)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    ∀ y : F, unweightedLinOp k y = 0 ↔ y = 0 ∨ y = 1 := by
  intro y
  constructor
  intro hy
  have hy_eq : y ^ (2 ^ k) * (y ^ (2 ^ k) + 1) = 0 := by
    unfold unweightedLinOp at hy;
    rw [ show Module.finrank ( ZMod 2 ) F - k = k + 1 by omega ] at hy; linear_combination' hy;
  have hy_cases : y ^ (2 ^ k) = 0 ∨ y ^ (2 ^ k) = 1 := by
    grind
  have hy_cases' : y = 0 ∨ y = 1 := by
    exact Or.imp ( fun h => by simpa using h ) ( fun h => by simpa using ( frobenius_injective k ) ( by aesop ) ) hy_cases
  exact hy_cases';
  rintro ( rfl | rfl ) <;> simp +decide [ unweightedLinOp ];
  grind

/-! ## Polar form identity -/

/-
The polar form Tr(z·y^{2^k} + z^{2^k}·y) equals Tr(y · L(z)).
-/
lemma polar_trace_eq (k : ℕ) (z y : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    fieldTrace (z * y ^ (2 ^ k) + z ^ (2 ^ k) * y) =
    fieldTrace (y * unweightedLinOp k z) := by
  convert gold_bridge k 1 y z hk hcard using 1;
  · ring;
  · unfold goldLinearizedOp unweightedLinOp; ring;

/-! ## Inner sum lemmas -/

/-
For z with L(z) ≠ 0, the inner sum vanishes.
-/
lemma inner_sum_off_radical (k : ℕ) (z : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (hz : unweightedLinOp k z ≠ 0) :
    ∑ y : F, chiInt' (z * y ^ (2 ^ k) + z ^ (2 ^ k) * y) = 0 := by
  -- By the polar trace identity, we can rewrite the sum as $\sum_{y \in F} \chi'(y \cdot L(z))$.
  have h_sum_rewrite : ∑ y : F, chiInt' (z * y ^ (2 ^ k) + z ^ (2 ^ k) * y) = ∑ y : F, chiInt' (y * unweightedLinOp k z) := by
    apply Finset.sum_congr rfl;
    intro y hy; rw [ chiInt', chiInt' ] ; simp +decide [ polar_trace_eq k z y hk hcard ] ;
  have h_sum_zero : ∑ y : F, chiInt' y = 0 := by
    -- Since the trace is surjective, there exists some $b \in F$ such that $\text{Tr}(b) = 1$.
    obtain ⟨b, hb⟩ : ∃ b : F, (fieldTrace b : ZMod 2) = 1 := by
      exact ( Algebra.trace_surjective ( ZMod 2 ) F ) 1 |> fun ⟨ b, hb ⟩ => ⟨ b, hb ⟩;
    -- By pairing each $y$ with $y + b$, we can show that the sum is zero.
    have h_pair : ∀ y : F, chiInt' (y + b) = -chiInt' y := by
      intro y
      simp [chiInt', hb];
      cases' Fin.exists_fin_two.mp ⟨ fieldTrace y, rfl ⟩ with h h <;> simp +decide [ h ];
    have h_sum_zero : ∑ y : F, chiInt' y = ∑ y : F, chiInt' (y + b) := by
      rw [ ← Equiv.sum_comp ( Equiv.addRight b ) ] ; simp +decide;
    norm_num [ h_pair ] at h_sum_zero; linarith;
  rw [ h_sum_rewrite, ← h_sum_zero ];
  exact Equiv.sum_comp ( Equiv.mulRight₀ _ hz ) fun y => chiInt' y

/-
For z = 1, the inner sum equals |F|.
-/
lemma inner_sum_one (k : ℕ) :
    ∑ y : F, chiInt' ((1 : F) * y ^ (2 ^ k) + (1 : F) ^ (2 ^ k) * y) =
    (Fintype.card F : ℤ) := by
  simp +decide [ chiInt' ];
  simp_all +decide [ ← two_mul, trace_frob ]

/-! ## Main Walsh² identity -/

/-
**Key identity**: W(a)² = |F| · (1 + chiInt(1 + a)).
-/
theorem walsh_sq_eq (k : ℕ) (a : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    (∑ x : F, chiInt' (x ^ (2 ^ k + 1) + a * x)) ^ 2 =
    (Fintype.card F : ℤ) * (1 + chiInt' (1 + a)) := by
  have h_subst : (∑ x : F, chiInt' (x ^ (2 ^ k + 1) + a * x)) ^ 2 = ∑ z : F, ∑ y : F, chiInt' ((z + y) ^ (2 ^ k + 1) + a * (z + y)) * chiInt' (y ^ (2 ^ k + 1) + a * y) := by
    rw [ sq, Finset.sum_comm ];
    rw [ Finset.sum_mul ];
    simp +decide only [Finset.mul_sum _ _ _];
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun y hy => by rw [ ← Equiv.sum_comp ( Equiv.addRight y ) ] ; simp +decide ;
  have h_factor : (∑ z : F, ∑ y : F, chiInt' ((z + y) ^ (2 ^ k + 1) + a * (z + y)) * chiInt' (y ^ (2 ^ k + 1) + a * y)) = (∑ z : F, chiInt' (z ^ (2 ^ k + 1) + a * z) * (∑ y : F, chiInt' (z * y ^ (2 ^ k) + z ^ (2 ^ k) * y))) := by
    have h_factor : ∀ z y : F, chiInt' ((z + y) ^ (2 ^ k + 1) + a * (z + y)) * chiInt' (y ^ (2 ^ k + 1) + a * y) = chiInt' (z ^ (2 ^ k + 1) + a * z) * chiInt' (z * y ^ (2 ^ k) + z ^ (2 ^ k) * y) := by
      intro z y
      have h_expand : (z + y) ^ (2 ^ k + 1) + a * (z + y) = z ^ (2 ^ k + 1) + a * z + (z * y ^ (2 ^ k) + z ^ (2 ^ k) * y) + y ^ (2 ^ k + 1) + a * y := by
        have h_expand : (z + y) ^ (2 ^ k) = z ^ (2 ^ k) + y ^ (2 ^ k) := by
          have h_frobenius : ∀ (x y : F), (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
            grind;
          refine' Nat.recOn k _ _ <;> simp_all +decide [ pow_succ, pow_mul ];
        rw [ pow_succ, h_expand ] ; ring;
      rw [ h_expand, chiInt'_mul, chiInt'_mul ];
      grind +splitImp;
    simp +decide only [h_factor, Finset.mul_sum _ _ _];
  -- For z ∉ {0,1}, the inner sum vanishes by inner_sum_off_radical.
  have h_inner_zero : ∀ z : F, z ≠ 0 ∧ z ≠ 1 → ∑ y : F, chiInt' (z * y ^ (2 ^ k) + z ^ (2 ^ k) * y) = 0 := by
    intro z hz
    have h_inner_zero : unweightedLinOp k z ≠ 0 := by
      exact fun h => hz.2 <| by have := unweighted_kernel_char k hn z; aesop;
    convert inner_sum_off_radical k z hk hcard h_inner_zero using 1;
  rw [ h_subst, h_factor, Finset.sum_eq_add ( 0 : F ) ( 1 : F ) ] <;> simp +decide [ h_inner_zero ];
  · rw [ show ( ∑ x : F, chiInt' ( x ^ 2 ^ k + x ) ) = Fintype.card F from ?_ ] ; ring;
    convert inner_sum_one k using 1;
    all_goals try infer_instance;
    simp +decide [ one_mul ];
  · exact fun z hz₁ hz₂ => Or.inr ( h_inner_zero z ⟨ hz₁, hz₂ ⟩ )

/-- **Gold Walsh spectrum (AB property).** W(a)² ∈ {0, 2^{n+1}}. -/
theorem gold_walsh_sq_AB (k : ℕ) (a : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    (∑ x : F, chiInt' (x ^ (2 ^ k + 1) + a * x)) ^ 2 = 0 ∨
    (∑ x : F, chiInt' (x ^ (2 ^ k + 1) + a * x)) ^ 2 =
      (2 : ℤ) ^ (Module.finrank (ZMod 2) F + 1) := by
  have hn_odd : ¬ 2 ∣ Module.finrank (ZMod 2) F := by omega
  have hws := walsh_sq_eq k a hk hcard hn
  have h1 := trace_one_odd hn_odd
  rw [hws]
  -- chiInt'(1 + a) depends on Tr(1 + a) = 1 + Tr(a)
  have : chiInt' (1 + a) =
    if (fieldTrace (1 + a) : ZMod 2).val = 0 then 1 else -1 := rfl
  simp only [map_add, h1] at this
  rcases Fin.exists_fin_two.mp ⟨fieldTrace a, rfl⟩ with ha | ha
  · -- Tr(a) = 0, Tr(1+a) = 1, chiInt = -1
    rw [ha] at this; simp +decide at this
    rw [this]; left; ring
  · -- Tr(a) = 1, Tr(1+a) = 0, chiInt = 1
    rw [ha] at this; simp +decide at this
    rw [this]; right
    rw [Nat.card_eq_fintype_card] at hcard
    rw [hcard, hn]; push_cast; ring

/-- **Gold function is balanced: W(0) = 0.** -/
theorem gold_walsh_zero (k : ℕ)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    ∑ x : F, chiInt' (x ^ (2 ^ k + 1)) = 0 := by
  have hn_odd : ¬ 2 ∣ Module.finrank (ZMod 2) F := by omega
  have h1 := trace_one_odd hn_odd
  -- Use AB to get W(0)² ∈ {0, 2^{n+1}}
  -- But more directly: W(0)² = |F| · (1 + chiInt(1))
  -- chiInt(1) = -1 since Tr(1) = 1
  -- So W(0)² = 0, hence W(0) = 0
  have hchi1 : chiInt' (1 : F) = -1 := by
    unfold chiInt'; rw [h1]; simp +decide
  -- Get the identity for a = 0
  have hws := walsh_sq_eq k (0 : F) hk hcard hn
  -- Simplify: x^{2^k+1} + 0*x = x^{2^k+1}
  conv at hws => lhs; arg 1; arg 2; ext x; rw [show x ^ (2 ^ k + 1) + 0 * x = x ^ (2 ^ k + 1) from by ring]
  -- Also: 1 + (0 : F) = 1
  rw [show (1 : F) + 0 = 1 from by ring] at hws
  rw [hchi1] at hws
  simp only [add_neg_cancel, mul_zero] at hws
  exact sq_eq_zero_iff.mp hws

end WalshRadical