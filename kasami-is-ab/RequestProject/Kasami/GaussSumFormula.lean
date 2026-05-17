/-
# Gauss Sum Formula for GF(2)-Quadratic Forms

Correct formula: G(Q)² = 2^n · ∑_{z ∈ Rad} (-1)^{Q(z)}

## Proof sketch
G² = (∑_x (-1)^{Q(x)})²
   = ∑_{x,z} (-1)^{Q(x)+Q(x+z)}       [y = x+z]
   = ∑_z (-1)^{Q(z)} · ∑_x (-1)^{B(x,z)}  [Q(x)+Q(x+z) = Q(z)+B(x,z)]
   = ∑_{z∈R} (-1)^{Q(z)} · 2^n            [inner sum = 2^n if z∈R, else 0]
   = 2^n · ∑_{z∈R} (-1)^{Q(z)}
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiFunction

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### GF(2)-valued functions and their bilinear forms -/

/-- The bilinear form associated to Q: B(x,y) = Q(x+y) + Q(x) + Q(y). -/
def qBilinForm (n : ℕ) (Q : F2n n → ZMod 2) (x y : F2n n) : ZMod 2 :=
  Q (x + y) + Q x + Q y

/-- The radical of Q: {z | ∀ y, B(z,y) = 0}. -/
def qRadical (n : ℕ) (Q : F2n n → ZMod 2) : Finset (F2n n) :=
  Finset.univ.filter (fun z => ∀ y : F2n n, qBilinForm n Q z y = 0)

/-- The Gauss sum of Q. -/
noncomputable def qGaussSum (n : ℕ) (Q : F2n n → ZMod 2) : ℤ :=
  ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x))

/-- **Sub-lemma 1**: Q(x) + Q(x+z) = Q(z) + B(x,z) (mod 2).
    This follows from the definition of B and char 2. -/
theorem q_shift_identity (n : ℕ) (Q : F2n n → ZMod 2) (x z : F2n n) :
    Q x + Q (x + z) = Q z + qBilinForm n Q x z := by
  simp only [qBilinForm]
  have h : Q z + Q z = 0 := CharTwo.add_self_eq_zero _
  conv_rhs => rw [show Q z + (Q (x + z) + Q x + Q z) = Q x + Q (x + z) + (Q z + Q z) from by abel]
  rw [h, add_zero]

/-- **Sub-lemma 2**: Inner character sum for radical elements equals 2^n. -/
theorem inner_sum_radical (n : ℕ) (hn : n ≠ 0) (Q : F2n n → ZMod 2) (z : F2n n)
    (hz : z ∈ qRadical n Q) :
    ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q x z)) = (2 ^ n : ℤ) := by
  have hB : ∀ x, qBilinForm n Q x z = 0 := by
    intro x
    have hz' : ∀ y, qBilinForm n Q z y = 0 := by
      simpa [qRadical, Finset.mem_filter] using hz
    -- B is symmetric in char 2: B(x,z) = B(z,x)
    have : qBilinForm n Q x z = qBilinForm n Q z x := by
      simp [qBilinForm]; ring
    rw [this]; exact hz' x
  simp_rw [hB]
  simp [F2n.card n hn]

/-
**Sub-lemma 3**: Inner character sum for non-radical elements equals 0.
    Requires B to be additive (i.e., Q is a quadratic form).
-/
theorem inner_sum_non_radical (n : ℕ) (hn : n ≠ 0) (Q : F2n n → ZMod 2)
    (hB_add_left : ∀ x₁ x₂ z, qBilinForm n Q (x₁ + x₂) z =
      qBilinForm n Q x₁ z + qBilinForm n Q x₂ z)
    (z : F2n n) (hz : z ∉ qRadical n Q) :
    ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q x z)) = 0 := by
  -- Since $z \notin \text{radical}(Q)$, there exists $y \in \text{F2n } n$ such that $qBilinForm n Q z y \neq 0$.
  obtain ⟨y, hy⟩ : ∃ y : F2n n, qBilinForm n Q z y ≠ 0 := by
    exact not_forall.mp fun h => hz <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩;
  -- By the properties of the trace and the bilinear form, we have $\sum_{x \in \text{F2n } n} (-1)^{\text{Tr}(qBilinForm n Q x z)} = \sum_{x \in \text{F2n } n} (-1)^{\text{Tr}(qBilinForm n Q (x + y) z)}$.
  have h_sum_shift : ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q x z)) = ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q (x + y) z)) := by
    rw [ ← Equiv.sum_comp ( Equiv.addRight y ) ] ; aesop;
  -- By the properties of the trace and the bilinear form, we have $\sum_{x \in \text{F2n } n} (-1)^{\text{Tr}(qBilinForm n Q (x + y) z)} = \sum_{x \in \text{F2n } n} (-1)^{\text{Tr}(qBilinForm n Q x z) + \text{Tr}(qBilinForm n Q y z)}$.
  have h_sum_shifted : ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q (x + y) z)) = ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q x z) + ZMod.val (qBilinForm n Q y z)) := by
    simp +decide [ hB_add_left, ZMod.val_add ];
    exact Finset.sum_congr rfl fun _ _ => by rw [ ← Nat.mod_add_div ( ( qBilinForm n Q _ _ |> ZMod.val ) + ( qBilinForm n Q _ _ |> ZMod.val ) ) 2 ] ; norm_num [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
  -- Since $qBilinForm n Q y z \neq 0$, we have $(-1)^{ZMod.val (qBilinForm n Q y z)} = -1$.
  have h_neg_one : (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q y z)) = -1 := by
    cases Fin.exists_fin_two.mp ⟨ qBilinForm n Q y z, rfl ⟩ <;> simp_all +decide;
    unfold qBilinForm at *; simp_all +decide [ add_comm ] ;
    grind +revert;
  norm_num [ pow_add, h_neg_one ] at * ; linarith

/-
**The correct Gauss sum squared formula**.
    G(Q)² = 2^n · ∑_{z ∈ Rad(Q)} (-1)^{Q(z)}

    Hypotheses:
    - Q(0) = 0
    - B(x,y) = Q(x+y)+Q(x)+Q(y) is additive in x (for each fixed y)
-/
theorem gauss_sum_sq_formula (n : ℕ) (hn : n ≠ 0) (Q : F2n n → ZMod 2)
    (hQ0 : Q 0 = 0)
    (hB_add : ∀ x₁ x₂ z, qBilinForm n Q (x₁ + x₂) z =
      qBilinForm n Q x₁ z + qBilinForm n Q x₂ z) :
    qGaussSum n Q ^ 2 = (2 ^ n : ℤ) *
      ∑ z ∈ qRadical n Q, (-1 : ℤ) ^ (ZMod.val (Q z)) := by
  -- By definition of $qGaussSum$, we can expand $G(Q)^2$ as follows:
  have h_expand : (qGaussSum n Q)^2 = ∑ z : F2n n, (-1 : ℤ) ^ (ZMod.val (Q z)) * (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q x z))) := by
    have h_expand : (qGaussSum n Q)^2 = ∑ x : F2n n, ∑ y : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x)) * (-1 : ℤ) ^ (ZMod.val (Q y)) := by
      simp +decide only [qGaussSum, pow_two, ← Finset.mul_sum _ _ _, ← Finset.sum_mul];
    -- By changing variables $y = x + z$, we can rewrite the double sum.
    have h_change_var : ∑ x : F2n n, ∑ y : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x)) * (-1 : ℤ) ^ (ZMod.val (Q y)) = ∑ x : F2n n, ∑ z : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x)) * (-1 : ℤ) ^ (ZMod.val (Q (x + z))) := by
      exact Finset.sum_congr rfl fun x hx => by rw [ ← Equiv.sum_comp ( Equiv.addLeft x ) ] ; simp +decide ;
    -- By using the identity $Q(x) + Q(x+z) = Q(z) + B(x,z)$, we can rewrite the inner sum.
    have h_inner_sum : ∀ x z : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x)) * (-1 : ℤ) ^ (ZMod.val (Q (x + z))) = (-1 : ℤ) ^ (ZMod.val (Q z)) * (-1 : ℤ) ^ (ZMod.val (qBilinForm n Q x z)) := by
      intros x z
      have h_identity : Q x + Q (x + z) = Q z + qBilinForm n Q x z := by
        grind +locals;
      have h_exp : (Q x).val + (Q (x + z)).val ≡ (Q z).val + (qBilinForm n Q x z).val [MOD 2] := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      rw [ ← pow_add, ← pow_add ];
      rw [ ← Nat.mod_add_div ( ( Q x |> ZMod.val ) + ( Q ( x + z ) |> ZMod.val ) ) 2, ← Nat.mod_add_div ( ( Q z |> ZMod.val ) + ( qBilinForm n Q x z |> ZMod.val ) ) 2, h_exp ] ; norm_num [ pow_add, pow_mul ];
    simp_all +decide only [Finset.mul_sum _ _ _];
    rw [ Finset.sum_comm ];
  rw [ h_expand, Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_subset ( Finset.subset_univ ( qRadical n Q ) ) ];
  · exact Finset.sum_congr rfl fun x hx => by rw [ mul_comm, inner_sum_radical n hn Q x ( by simpa using hx ) ] ;
  · exact fun x _ hx => mul_eq_zero_of_right _ ( inner_sum_non_radical n hn Q hB_add x hx )

/-! ### Corollary: AB criterion from radical size -/

/-
If the radical has exactly 2 elements {0, z₀}, then
    G² = 2^n · (1 + (-1)^{Q(z₀)}) ∈ {0, 2^{n+1}}.
-/
theorem gauss_sum_sq_from_radical_two (n : ℕ) (hn : n ≠ 0) (Q : F2n n → ZMod 2)
    (hQ0 : Q 0 = 0)
    (hB_add : ∀ x₁ x₂ z, qBilinForm n Q (x₁ + x₂) z =
      qBilinForm n Q x₁ z + qBilinForm n Q x₂ z)
    (hrad : (qRadical n Q).card = 2) :
    qGaussSum n Q ^ 2 = 0 ∨ qGaussSum n Q ^ 2 = (2 ^ (n + 1) : ℤ) := by
  have := gauss_sum_sq_formula n hn Q hQ0 hB_add; simp_all +decide [ pow_succ' ] ;
  -- Since the radical has exactly 2 elements, let's denote them as 0 and z₀.
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : F2n n, qRadical n Q = {0, z₀} := by
    have := Finset.card_eq_two.mp hrad;
    obtain ⟨ x, y, hxy, h ⟩ := this; use if x = 0 then y else x; split_ifs <;> simp_all +decide [ Finset.ext_iff ] ;
    have := h 0; simp_all +decide [ qRadical ] ;
    have := h 0; simp_all +decide [ qBilinForm ] ;
    grind;
  cases Fin.exists_fin_two.mp ⟨ Q z₀, rfl ⟩ <;> simp_all +decide [ pow_succ' ];
  · grind +suggestions;
  · rw [ Finset.sum_pair ] <;> aesop

end
end Kasami