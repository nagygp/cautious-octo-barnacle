/-
# Gauss Sums and Exponential Sums for Quadratic Forms over F₂

This file establishes the connection between quadratic forms over F₂-vector spaces
and their associated exponential (Gauss) sums.

## Main Definitions

- `QuadFormF2.expSum`: The exponential sum S(Q) = ∑_{x ∈ V} (-1)^{Q(x)} ∈ ℤ
- `QuadFormF2.zeroCount`: The number of zeros #{x : Q(x) = 0}
- `QuadFormF2.oneCount`: The number of ones #{x : Q(x) = 1}

## Main Results

- `QuadFormF2.expSum_eq_sub`: S(Q) = #{Q=0} - #{Q=1}
- `QuadFormF2.expSum_eq_two_zeroCount_sub`: S(Q) = 2·#{Q=0} - |V|
- `QuadFormF2.expSum_sq_eq_card_mul_radical_sum`: S(Q)² = |V| · ∑_{u ∈ rad} (-1)^{Q(u)}
- `QuadFormF2.expSum_zero_of_radical_nonvanishing`: S(Q) = 0 when Q|_rad ≠ 0
- `QuadFormF2.expSum_sq_eq_card_mul_radical_card`: S(Q)² = |V|·|rad| when Q|_rad = 0

## Mathematical Context

For a quadratic form Q : F_{2^n} → F_2 with associated symplectic bilinear form B
of rank 2k:
- If Q|_{rad(B)} ≡ 0: S(Q) = ε · 2^{n-k} where ε = ±1 (Arf invariant)
- If Q|_{rad(B)} ≢ 0: S(Q) = 0

This trichotomy is the fundamental link between quadratic forms and the Walsh/Hadamard
spectrum of Boolean functions, central to the analysis of Kasami codes.
-/

import Mathlib
import RequestProject.QuadFormGF2.Defs

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical in
noncomputable section

namespace QuadFormF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]

/-! ## Sign function: (-1)^a for a ∈ ZMod 2 -/

/-- The sign function: maps 0 ↦ 1, 1 ↦ -1.
    This is (-1)^a viewed as an integer. -/
def signZ (a : ZMod 2) : ℤ :=
  if a = 0 then 1 else -1

@[simp] lemma signZ_zero : signZ 0 = 1 := by simp [signZ]
@[simp] lemma signZ_one : signZ 1 = -1 := by simp [signZ]

lemma signZ_mul (a b : ZMod 2) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> simp [signZ] <;> decide

lemma signZ_sq (a : ZMod 2) : signZ a ^ 2 = 1 := by
  fin_cases a <;> simp [signZ]

lemma signZ_ne_zero (a : ZMod 2) : signZ a ≠ 0 := by
  fin_cases a <;> simp [signZ]

lemma signZ_values (a : ZMod 2) : signZ a = 1 ∨ signZ a = -1 := by
  fin_cases a <;> simp [signZ]

lemma signZ_self_mul (a : ZMod 2) : signZ a * signZ a = 1 := by
  fin_cases a <;> simp [signZ]

/-! ## Exponential Sum -/

/-- The exponential sum (Gauss sum) of a quadratic form Q:
    S(Q) = ∑_{x ∈ V} (-1)^{Q(x)} ∈ ℤ -/
def expSum (Q : QuadFormF2 V) : ℤ :=
  ∑ x : V, signZ (Q x)

/-- The number of elements where Q vanishes -/
def zeroCount (Q : QuadFormF2 V) : ℕ :=
  (Finset.univ.filter (fun x : V => Q x = 0)).card

/-- The number of elements where Q equals 1 -/
def oneCount (Q : QuadFormF2 V) : ℕ :=
  (Finset.univ.filter (fun x : V => Q x = 1)).card

/-
V is partitioned into {Q=0} and {Q=1}
-/
lemma zero_one_partition (Q : QuadFormF2 V) :
    Q.zeroCount + Q.oneCount = Fintype.card V := by
  convert Finset.card_add_card_compl ( Finset.filter ( fun x => Q x = 0 ) Finset.univ );
  exact congr_arg Finset.card ( Finset.ext fun x => by have := Fin.exists_fin_two.mp ⟨ Q x, rfl ⟩ ; aesop )

/-
The exponential sum equals #{Q=0} - #{Q=1}
-/
lemma expSum_eq_sub (Q : QuadFormF2 V) :
    Q.expSum = (Q.zeroCount : ℤ) - (Q.oneCount : ℤ) := by
  convert Finset.sum_congr rfl fun x _refine => show ( if Q x = 0 then 1 else -1 ) = if Q x = 0 then 1 else -1 from rfl using 1;
  simp +decide [ Finset.sum_ite, Finset.filter_not, Finset.card_sdiff ];
  rw [ Nat.cast_sub ];
  · linarith! [ zero_one_partition Q ];
  · exact Finset.card_le_univ _

/-
The exponential sum equals 2·#{Q=0} - |V|
-/
lemma expSum_eq_two_zeroCount_sub (Q : QuadFormF2 V) :
    Q.expSum = 2 * (Q.zeroCount : ℤ) - (Fintype.card V : ℤ) := by
  linarith [ expSum_eq_sub Q, zero_one_partition Q ]

/-! ## S(Q)² via the bilinear form -/

/-
S(Q)² = |V| · ∑_{u ∈ rad(Q)} (-1)^{Q(u)}.

    Proof sketch:
    S(Q)² = (∑_x (-1)^{Q(x)})²
    = ∑_{x,y} (-1)^{Q(x)} · (-1)^{Q(y)}
    = ∑_{x,y} (-1)^{Q(x) + Q(y)}

    Substituting u = x + y (bijection for fixed y in char 2):
    = ∑_{u,y} (-1)^{Q(u+y) + Q(y)}
    = ∑_{u,y} (-1)^{Q(u) + polar(u,y)}  [since Q(u+y) = Q(u) + Q(y) + polar(u,y)]
    = ∑_u (-1)^{Q(u)} · (∑_y (-1)^{polar(u,y)})

    For u ∈ rad(Q): polar(u,·) = 0, so inner sum = |V|
    For u ∉ rad(Q): polar(u,·) is a nonzero F₂-linear functional,
                     so inner sum = 0 by character orthogonality

    Therefore S(Q)² = |V| · ∑_{u ∈ rad(Q)} (-1)^{Q(u)}.
-/
theorem expSum_sq_eq_card_mul_radical_sum (Q : QuadFormF2 V) :
    Q.expSum ^ 2 = (Fintype.card V : ℤ) *
      ∑ u ∈ Finset.univ.filter (fun u => u ∈ Q.radical), signZ (Q u) := by
  -- Start by using the definition of S(Q) and then expand the square
  have h_expand : (Q.expSum) ^ 2 = ∑ x, ∑ y, signZ (Q x) * signZ (Q y) := by
    simp +decide only [expSum, sq, ← Finset.mul_sum _ _ _, ← sum_mul];
  -- For each fixed y, the inner sum ∑_x signZ(Q(u+y) + Q(y)) is equal to ∑_u signZ(Q(u) + polar(u,y)).
  have h_inner : ∀ y : V, ∑ x, signZ (Q x) * signZ (Q y) = ∑ u, signZ (Q u) * signZ (Q.polar u y) := by
    intro y
    have h_inner_sum : ∑ x, signZ (Q x + Q y) = ∑ u, signZ (Q u + Q.polar u y) := by
      apply Finset.sum_bij (fun x _ => x + y);
      · simp +decide;
      · aesop;
      · exact fun b _ => ⟨ b - y, Finset.mem_univ _, sub_add_cancel _ _ ⟩;
      · simp +decide [ QuadFormF2.polar ];
        simp +decide [ add_assoc, ZMod2.add_self ];
        grind +locals;
    convert h_inner_sum using 2 <;> simp +decide [ signZ_mul ];
  -- For each fixed u, the inner sum ∑_y signZ(polar(u,y)) is equal to |V| if u ∈ rad(Q) and 0 otherwise.
  have h_inner_sum : ∀ u : V, ∑ y, signZ (Q.polar u y) = if u ∈ Q.radical then (Fintype.card V : ℤ) else 0 := by
    intro u
    by_cases hu : u ∈ Q.radical;
    · rw [ if_pos hu, Finset.sum_congr rfl fun y hy => by rw [ show Q.polar u y = 0 from by simpa using hu y ] ] ; simp +decide [ signZ ];
    · -- Since $u \notin \text{rad}(Q)$, the inner sum $\sum_{y \in V} \text{signZ}(Q.polar(u, y))$ is zero by the orthogonality of characters.
      have h_inner_zero : ∑ y : V, signZ (Q.polar u y) = 0 := by
        -- Since $u \notin \text{rad}(Q)$, there exists some $y_0 \in V$ such that $Q.polar u y_0 \neq 0$.
        obtain ⟨y₀, hy₀⟩ : ∃ y₀ : V, Q.polar u y₀ ≠ 0 := by
          exact not_forall.mp fun h => hu <| (mem_radical Q u).mpr h
        -- Since $Q.polar u y₀ \neq 0$, we can pair each $y$ with $y + y₀$.
        have h_pair : ∑ y : V, signZ (Q.polar u y) = ∑ y : V, signZ (Q.polar u (y + y₀)) := by
          rw [ ← Equiv.sum_comp ( Equiv.addRight y₀ ) ] ; aesop;
        -- Since $Q.polar u y₀ \neq 0$, we have $signZ (Q.polar u (y + y₀)) = -signZ (Q.polar u y)$.
        have h_sign : ∀ y : V, signZ (Q.polar u (y + y₀)) = -signZ (Q.polar u y) := by
          intro y; rw [ show Q.polar u ( y + y₀ ) = Q.polar u y + Q.polar u y₀ from ?_ ] ; simp +decide [ hy₀, signZ_mul ] ;
          · cases Fin.exists_fin_two.mp ⟨ Q.polar u y₀, rfl ⟩ <;> simp_all +decide [ signZ ];
          · exact polar_add_right Q u y y₀;
        norm_num [ h_sign ] at h_pair; linarith;
      aesop;
  simp_all +decide [ Finset.sum_ite, Finset.mul_sum _ _ _, mul_comm ];
  rw [ Finset.sum_comm ];
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_inner_sum ];
  simp +decide [ Finset.sum_ite, Finset.mul_sum _ _ _ ]

/-! ## Orthogonality of characters -/

/-
For a nonzero F₂-linear functional φ : V → ZMod 2,
    ∑_{x ∈ V} (-1)^{φ(x)} = 0.
    This is the fundamental orthogonality relation for additive characters.
-/
omit [DecidableEq V] in
lemma sum_signZ_linear_vanish {φ : V →ₗ[ZMod 2] ZMod 2} (hφ : φ ≠ 0) :
    ∑ x : V, signZ (φ x) = 0 := by
  -- Let $v₀$ be a vector such that $\varphi(v₀) = 1$.
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, φ v₀ = 1 := by
    contrapose! hφ; ext x; have := Fin.exists_fin_two.mp ⟨ φ x, rfl ⟩ ; aesop;
  -- By the properties of the linear functional φ, we can pair each x with x + v₀.
  have h_pair : ∑ x : V, signZ (φ x) = ∑ x : V, signZ (φ (x + v₀)) := by
    rw [ ← Equiv.sum_comp ( Equiv.addRight v₀ ) ] ; aesop;
  -- Since $\varphi$ is linear, $\varphi(x + v₀) = \varphi(x) + \varphi(v₀)$.
  have h_linear : ∀ x : V, φ (x + v₀) = φ x + 1 := by
    aesop;
  have h_sign : ∀ x : V, signZ (φ x + 1) = -signZ (φ x) := by
    intro x; rcases Fin.exists_fin_two.mp ⟨ φ x, rfl ⟩ with ( h | h ) <;> simp +decide [ h ] ;
  norm_num [ h_linear, h_sign ] at h_pair; linarith;

/-
For a linear functional φ, the inner sum ∑_y (-1)^{φ(y)} equals |V| if φ = 0
    and 0 if φ ≠ 0.
-/
omit [DecidableEq V] in
lemma sum_signZ_linear (φ : V →ₗ[ZMod 2] ZMod 2) :
    ∑ y : V, signZ (φ y) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
  split_ifs with h;
  · aesop;
  · exact sum_signZ_linear_vanish h

/-! ## Radical contribution -/

/-
For u ∈ rad(Q), the inner sum ∑_y (-1)^{B(u,y)} = |V|
    since B(u,·) = 0 for radical elements.
-/
omit [DecidableEq V] in
lemma inner_sum_radical (Q : QuadFormF2 V) {u : V} (hu : u ∈ Q.radical) :
    ∑ y : V, signZ (Q.polar u y) = (Fintype.card V : ℤ) := by
  unfold QuadFormF2.radical at hu; aesop;

/-
For u ∉ rad(Q), the inner sum ∑_y (-1)^{B(u,y)} = 0.
-/
omit [DecidableEq V] in
lemma inner_sum_nonradical (Q : QuadFormF2 V) {u : V} (hu : u ∉ Q.radical) :
    ∑ y : V, signZ (Q.polar u y) = 0 := by
  -- Since $u \notin \text{rad}(Q)$, the linear map $y \mapsto Q.polar u y$ is non-zero.
  have h_nonzero : ∃ y : V, Q.polar u y ≠ 0 := by
    exact not_forall.mp fun h => hu <| (mem_radical Q u).mpr h
  convert sum_signZ_linear_vanish _;
  rotate_left;
  all_goals try infer_instance;
  exact { toFun := fun y => Q.polar u y, map_add' := fun x y => by simp [ polar_add_right ], map_smul' := fun c y => by simp [ polar_smul_right ] };
  · exact fun h => h_nonzero.elim fun y hy => hy <| by simpa using congr_arg ( fun f => f y ) h;
  · rfl

/-! ## Consequences of the main theorem -/

/-
If Q restricted to the radical is nonzero (as a linear map),
    then the radical sum vanishes, hence S(Q) = 0.

    Proof: Q|_rad is F₂-linear (by additive_on_radical). If it is nonzero,
    then by character orthogonality ∑_{w ∈ rad} (-1)^{Q(w)} = 0.
    By the main theorem, S(Q)² = |V| · 0 = 0, so S(Q) = 0.
-/
omit [DecidableEq V] in
theorem expSum_zero_of_radical_nonvanishing (Q : QuadFormF2 V)
    (h : Q.radicalRestriction ≠ 0) :
    Q.expSum = 0 := by
  -- By the main theorem, S(Q)² = |V| · ∑_{u ∈ rad} (-1)^{Q(u)}
  have h_main : (Q.expSum : ℤ)^2 = (Fintype.card V : ℤ) * ∑ u ∈ (Q.radical : Set V), signZ (Q u) := by
    grind +suggestions;
  -- Since Q.radicalRestriction ≠ 0, the sum ∑_{u ∈ rad} (-1)^{Q(u)} is zero.
  have h_sum_zero : ∑ u ∈ (Q.radical : Set V).toFinset, signZ (Q u) = 0 := by
    convert sum_signZ_linear_vanish h using 1;
    refine' Finset.sum_bij ( fun x hx => ⟨ x, _ ⟩ ) _ _ _ _ <;> simp_all +decide
    exact fun a ha => (fun {a b} => Int.neg_inj.mp) rfl
  aesop

/-
When Q vanishes on the radical: ∑_{u ∈ rad} (-1)^{Q(u)} = |rad|.
-/
omit [DecidableEq V] in
theorem radical_sum_eq_card_of_vanishing (Q : QuadFormF2 V)
    (h : Q.radicalRestriction = 0) :
    ∑ u ∈ Finset.univ.filter (fun u : V => u ∈ Q.radical), signZ (Q u) =
      (Finset.univ.filter (fun u : V => u ∈ Q.radical)).card := by
  convert Finset.sum_const ( 1 : ℤ );
  · rw [ ← radical_vanishing_iff ] at h;
    aesop;
  · simp +decide

/-- **The Main Connection Theorem.**
    When Q vanishes on the radical: S(Q)² = |V| · |rad(Q)|.

    For V = F_{2^n} with |V| = 2^n and rank(B) = 2k:
    - |rad(Q)| = 2^{n - 2k}
    - S(Q)² = 2^n · 2^{n-2k} = 2^{2(n-k)}
    - S(Q) = ε · 2^{n-k} where ε = ±1

    This shows the exponential sum takes values in {0, ±2^{n-k}},
    which is the origin of the three-valued Walsh spectrum of Kasami codes. -/
theorem expSum_sq_eq_card_mul_radical_card (Q : QuadFormF2 V)
    (h : Q.radicalRestriction = 0) :
    Q.expSum ^ 2 = (Fintype.card V : ℤ) *
      (Finset.univ.filter (fun u : V => u ∈ Q.radical)).card := by
  rw [expSum_sq_eq_card_mul_radical_sum, radical_sum_eq_card_of_vanishing Q h]

end QuadFormF2

end