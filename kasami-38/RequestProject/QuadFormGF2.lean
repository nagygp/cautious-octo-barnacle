/-
# Quadratic Form Theory over GF(2)

This file develops the basic theory of quadratic forms over GF(2),
which is needed for the WHT trichotomy proof.

A quadratic form Q : V → GF(2) satisfies:
  Q(0) = 0
  B(x,y) := Q(x+y) + Q(x) + Q(y) is bilinear (the "polar form")

The radical of Q is rad(Q) = {x : ∀ y, B(x,y) = 0}.
On rad(Q), Q restricts to a linear map.

Key theorem: S(Q)² = |V| · |rad(Q)| when Q vanishes on the radical,
where S(Q) = ∑_x (-1)^{Q(x)}.
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## Quadratic Form Structure -/

/-- A quadratic form over GF(2) on a finite-dimensional F₂-vector space. -/
structure QuadFormF2 (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] where
  /-- The quadratic form Q : V → ZMod 2. -/
  Q : V → ZMod 2
  /-- Q(0) = 0. -/
  Q_zero : Q 0 = 0
  /-- The polar form B(x,y) = Q(x+y) + Q(x) + Q(y) is additive in y. -/
  polar_add_right : ∀ x y₁ y₂ : V, Q (x + (y₁ + y₂)) + Q x + Q (y₁ + y₂) =
    (Q (x + y₁) + Q x + Q y₁) + (Q (x + y₂) + Q x + Q y₂)

/-- The polar form B(x,y) = Q(x+y) + Q(x) + Q(y). -/
def QuadFormF2.polar {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (qf : QuadFormF2 V) (x y : V) : ZMod 2 :=
  qf.Q (x + y) + qf.Q x + qf.Q y

/-- The radical of Q: elements x such that B(x,y) = 0 for all y. -/
def QuadFormF2.radical {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (qf : QuadFormF2 V) : Set V :=
  {x | ∀ y, qf.polar x y = 0}

/-! ## Sign Function and Exponential Sum -/

/-- The sign function: `(-1)^a` for `a ∈ ZMod 2`, as an integer. -/
def signZ (a : ZMod 2) : ℤ :=
  if a = 0 then 1 else -1

theorem signZ_zero : signZ 0 = 1 := by simp [signZ]
theorem signZ_one : signZ 1 = -1 := by simp [signZ]

theorem signZ_add (a b : ZMod 2) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> simp [signZ] <;> decide

theorem signZ_sq (a : ZMod 2) : signZ a ^ 2 = 1 := by
  fin_cases a <;> simp [signZ]

/-- The exponential sum `S(Q) = ∑_x (-1)^{Q(x)}`. -/
def QuadFormF2.expSum {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (qf : QuadFormF2 V) : ℤ :=
  ∑ x : V, signZ (qf.Q x)

/-! ## Key Theorem: S(Q)² = |V| · |rad(Q)| -/

/-
**Gauss Sum Square Formula** (for quadratic forms over GF(2)):

When Q vanishes on the radical (i.e., Q(w) = 0 for all w ∈ rad(Q)),
we have: `S(Q)² = |V| · |rad(Q)|`.

This is the fundamental result connecting the exponential sum to the
radical structure.
-/
theorem expSum_sq_eq_card_mul_radical_card
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
    (qf : QuadFormF2 V)
    (hrad : ∀ x ∈ qf.radical, qf.Q x = 0)
    (hfin : Set.Finite qf.radical) :
    qf.expSum ^ 2 = (Fintype.card V : ℤ) * (hfin.toFinset.card : ℤ) := by
  -- Let's rewrite the sum using the fact that $Q(x)$ is quadratic.
  have h_sum : (∑ x : V, signZ (qf.Q x))^2 = ∑ t : V, signZ (qf.Q t) * (∑ x : V, signZ (qf.polar x t)) := by
    -- By definition of polar form, we have $Q(x) + Q(x+t) = Q(t) + B(x,t)$.
    have h_polar : ∀ x t : V, signZ (qf.Q x) * signZ (qf.Q (x + t)) = signZ (qf.Q t) * signZ (qf.polar x t) := by
      intro x t;
      unfold QuadFormF2.polar;
      cases Fin.exists_fin_two.mp ⟨ qf.Q x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ qf.Q ( x + t ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ qf.Q t, rfl ⟩ <;> simp +decide [ * ];
    simp +decide only [sq, Finset.mul_sum _ _ _];
    rw [ Finset.sum_comm ];
    simp +decide only [Finset.sum_mul, ← h_polar];
    exact Finset.sum_congr rfl fun x _ => by rw [ ← Equiv.sum_comp ( Equiv.addLeft x ) ] ; simp +decide [ mul_comm ] ;
  -- For $t \notin \text{rad}(Q)$, $\sum_{x \in V} \text{signZ}(B(x,t)) = 0$.
  have h_inner_zero : ∀ t : V, t ∉ qf.radical → ∑ x : V, signZ (qf.polar x t) = 0 := by
    intro t ht_not_radical
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : V, qf.polar x₀ t = 1 := by
      contrapose! ht_not_radical;
      intro x; specialize ht_not_radical x; rcases Fin.exists_fin_two.mp ⟨ qf.polar x t, rfl ⟩ with h | h <;> simp_all +decide ;
      convert h using 1;
      unfold QuadFormF2.polar; simp +decide [ add_comm ] ;
      abel1;
    -- Since $B(x₀, t) = 1$, we have $B(x₀ + x, t) = B(x₀, t) + B(x, t) = 1 + B(x, t)$.
    have h_polar_add : ∀ x : V, qf.polar (x₀ + x) t = 1 + qf.polar x t := by
      intro x
      have h_polar_add : qf.polar (x₀ + x) t = qf.polar x₀ t + qf.polar x t := by
        convert qf.polar_add_right t x₀ x using 1 ; abel_nf;
        · unfold QuadFormF2.polar; abel_nf;
        · unfold QuadFormF2.polar; abel_nf;
      rw [h_polar_add, hx₀];
    -- Since $B(x₀, t) = 1$, we have $\sum_{x \in V} \text{signZ}(B(x, t)) = \sum_{x \in V} \text{signZ}(1 + B(x, t))$.
    have h_sum_signZ : ∑ x : V, signZ (qf.polar x t) = ∑ x : V, signZ (1 + qf.polar x t) := by
      rw [ ← Equiv.sum_comp ( Equiv.addLeft x₀ ) ] ; aesop;
    -- Since $\text{signZ}(1 + a) = -\text{signZ}(a)$ for any $a \in \mathbb{Z}/2\mathbb{Z}$, we have $\sum_{x \in V} \text{signZ}(1 + B(x, t)) = -\sum_{x \in V} \text{signZ}(B(x, t))$.
    have h_signZ_neg : ∀ x : V, signZ (1 + qf.polar x t) = -signZ (qf.polar x t) := by
      intro x; rcases qf.polar x t with ( _ | _ | n ) <;> norm_cast;
    norm_num [ h_signZ_neg ] at h_sum_signZ; linarith;
  -- For $t \in \text{rad}(Q)$, $\sum_{x \in V} \text{signZ}(B(x,t)) = |V|$.
  have h_inner_radical : ∀ t : V, t ∈ qf.radical → ∑ x : V, signZ (qf.polar x t) = (Fintype.card V : ℤ) := by
    intro t ht
    have h_inner_radical_step : ∀ x : V, qf.polar x t = 0 := by
      intro x
      have h_symm : qf.polar x t = qf.polar t x := by
        grind +locals
      rw [h_symm]
      exact ht x;
    simp +decide [ h_inner_radical_step, signZ ];
  -- Therefore, $\sum_{t \in V} \text{signZ}(Q(t)) \sum_{x \in V} \text{signZ}(B(x,t)) = \sum_{t \in \text{rad}(Q)} \text{signZ}(Q(t)) |V|$.
  have h_sum_radical : ∑ t : V, signZ (qf.Q t) * (∑ x : V, signZ (qf.polar x t)) = ∑ t ∈ hfin.toFinset, signZ (qf.Q t) * (Fintype.card V : ℤ) := by
    rw [ ← Finset.sum_subset ( Finset.subset_univ hfin.toFinset ) ];
    · exact Finset.sum_congr rfl fun x hx => by rw [ h_inner_radical x ( hfin.mem_toFinset.mp hx ) ] ;
    · grind +suggestions;
  convert h_sum_radical using 1;
  rw [ Finset.sum_congr rfl fun x hx => by rw [ hrad x ( hfin.mem_toFinset.mp hx ) ] ] ; simp +decide [ mul_comm ]

/-! ## S(Q) = 0 when Q is nonzero on radical -/

/-
When Q does not vanish on the radical, S(Q) = 0.
-/
theorem expSum_zero_of_radical_nonvanishing
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
    (qf : QuadFormF2 V)
    (hnonvanish : ∃ x ∈ qf.radical, qf.Q x ≠ 0) :
    qf.expSum = 0 := by
  obtain ⟨ w, hw, hw' ⟩ := hnonvanish;
  have h_sum_zero : ∑ x : V, signZ (qf.Q x) = ∑ x : V, -signZ (qf.Q x) := by
    apply Finset.sum_bij (fun x _ => x + w);
    · simp +decide;
    · aesop;
    · exact fun b _ => ⟨ b - w, Finset.mem_univ _, sub_add_cancel _ _ ⟩;
    · intro x _; have := hw x; simp_all +decide [ QuadFormF2.polar ] ;
      cases Fin.exists_fin_two.mp ⟨ qf.Q w, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ qf.Q x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ qf.Q ( x + w ), rfl ⟩ <;> simp_all +decide [ add_comm ];
  rw [ Finset.sum_neg_distrib ] at h_sum_zero ; linarith!

end