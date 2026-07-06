import RequestProject.Steiner.Walsh

/-!
# Walsh algebra (Section 2.1, algebraic consequences) — layer F3 applied

This module specialises the reusable exponential-sum invariants of
`RequestProject.Foundations.CharacterSum` to the concrete `walshTransform` of
Definition 2.1.  Each lemma is a single identity or inequality obtained by
unfolding `walshTransform` into a character sum and quoting one foundational
invariant.

See `ROADMAP.md` (layer F3).  The point of this layer is the Sorry-Audit (M3)
observation that *all* of Section 3 is bounding `|W_F(ψ,a,b)|`, and the trivial
"diagonal" bound `≤ qⁿ` proved here is the universal fall-back that the
Weil/Deligne/Rojas–León estimates improve upon.
-/

open scoped BigOperators

namespace Flystel

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-! ## F3.applied — the trivial (diagonal) Walsh bound -/

/-- **Atomic step (diagonal bound).**
The Walsh transform is a sum of `qⁿ` unit-norm character values, so its norm is
at most `qⁿ`.  This is `Foundations.norm_charSum_le` transported through
`Fintype.card_pi_const`. -/
theorem norm_walshTransform_le {n m : ℕ} (ψ : AddChar Fq ℂ)
    (F : (Fin n → Fq) → (Fin m → Fq)) (a : Fin n → Fq) (b : Fin m → Fq) :
    ‖walshTransform ψ F a b‖ ≤ (Fintype.card Fq : ℝ) ^ n := by
  rw [walshTransform_def]
  have h := Foundations.norm_charSum_le ψ
    (fun x : Fin n → Fq => dotProduct a x + dotProduct b (F x))
  rw [Fintype.card_pi_const] at h
  push_cast at h
  exact h

/-- **Atomic step (re-indexing the Walsh sum).**
Pre-composing the domain with a bijection `e` of `Fqⁿ` re-indexes the Walsh sum
and so leaves it unchanged once the masks are pulled back through `e`.  This is
the abstract form of the CCZ reindexing of `AffineCCZ`. -/
theorem walshTransform_comp_equiv {n m : ℕ} (ψ : AddChar Fq ℂ)
    (F : (Fin n → Fq) → (Fin m → Fq)) (a : Fin n → Fq) (b : Fin m → Fq)
    (e : (Fin n → Fq) ≃ (Fin n → Fq)) :
    ∑ x, ψ (dotProduct a (e x) + dotProduct b (F (e x)))
      = walshTransform ψ F a b := by
  rw [walshTransform_def]
  exact Foundations.charSum_comp_equiv ψ
    (fun z : Fin n → Fq => dotProduct a z + dotProduct b (F z)) e

/-! ## F3.applied — variable separation over `Fq² = (Fin 2 → Fq)`

The Caramello `F̂ × F̂` move, transported through the index isomorphism
`(Fin 2 → Fq) ≃ Fq × Fq` (`finTwoArrowEquiv`).  This is the identity used in
Theorems 3.3/3.5/3.6 in the masks where the two field variables decouple. -/

/-- **Atomic step (Walsh-shaped variable separation).**
A two-variable character sum over `Fq²` whose phase splits as `g(p₀) + h(p₁)`
factors as the product of the two one-variable sums.  Combines
`Foundations.charSum_add_factor` with the reindexing `finTwoArrowEquiv`. -/
theorem sum_two_var_factor (ψ : AddChar Fq ℂ) (g h : Fq → Fq) :
    ∑ p : Fin 2 → Fq, ψ (g (p 0) + h (p 1))
      = (∑ x, ψ (g x)) * (∑ y, ψ (h y)) := by
  rw [← Foundations.charSum_add_factor ψ g h]
  exact Fintype.sum_equiv (finTwoArrowEquiv Fq) _ _ (fun p => by simp [finTwoArrowEquiv])

/-! ## F3.applied — vanishing of the linear (`b = 0`) Walsh case

The `b = 0` case of every §3 theorem: the Walsh transform reduces to a linear
character sum `∑ₓ ψ(⟨a,x⟩)`, which vanishes whenever `a ≠ 0` by orthogonality
over `Fqⁿ`.  This is the structural engine behind case 2 of Theorems 3.3/3.5/3.6
(`a ≠ 0, b = 0 ⇒ W_F = 0`). -/

/-
**Atomic step (orthogonality over `Fqⁿ`).**
For a non-trivial character `ψ` and a non-zero mask `a`, the linear character sum
`∑ₓ ψ(⟨a,x⟩)` over `Fqⁿ` vanishes.  The map `x ↦ ⟨a,x⟩` is a surjective linear
form, so the sum factors as `qⁿ⁻¹ · ∑_{t∈Fq} ψ(t) = 0`.
-/
theorem sum_char_dotProduct_eq_zero {n : ℕ} (ψ : AddChar Fq ℂ) (hψ : ψ ≠ 1)
    (a : Fin n → Fq) (ha : a ≠ 0) :
    ∑ x : Fin n → Fq, ψ (dotProduct a x) = 0 := by
  -- Since $a \neq 0$, the inner product form $x \mapsto \langle a, x \rangle$ is a surjective non-zero group homomorphism $Fq^n \to Fq$.
  have h_surjective : Function.Surjective (fun x : Fin n → Fq => a ⬝ᵥ x) := by
    intro b; simp_all +decide [ funext_iff, dotProduct ] ;
    obtain ⟨ i, hi ⟩ := ha; use fun j => if j = i then b / a i else 0; simp +decide [ hi, mul_div_cancel₀ ] ;
  obtain ⟨y, hy⟩ : ∃ y : Fin n → Fq, a ⬝ᵥ y = 1 := h_surjective 1;
  -- By changing variables $x \mapsto x + t y$, we can show that the sum is invariant under this transformation.
  have h_invariant : ∀ t : Fq, ∑ x : Fin n → Fq, ψ (a ⬝ᵥ (x + t • y)) = ∑ x : Fin n → Fq, ψ (a ⬝ᵥ x) := by
    intro t
    apply Finset.sum_bij (fun x _ => x + t • y);
    · simp +decide;
    · aesop;
    · exact fun b _ => ⟨ b - t • y, Finset.mem_univ _, by simp +decide ⟩;
    · exact fun _ _ => rfl;
  -- By changing variables $x \mapsto x + t y$, we can show that the sum is invariant under this transformation, leading to the conclusion that the sum is zero.
  have h_sum_zero : ∑ t : Fq, ∑ x : Fin n → Fq, ψ (a ⬝ᵥ (x + t • y)) = ∑ x : Fin n → Fq, ψ (a ⬝ᵥ x) * ∑ t : Fq, ψ t := by
    simp +decide only [dotProduct_add, dotProduct_smul, hy, Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← AddChar.map_add_eq_mul ] ; simp +decide );
  simp_all +decide [ ← Finset.sum_mul ];
  have := Flystel.Foundations.sum_eq_zero_of_ne_one hψ; simp_all +decide [ mul_comm ] ;

/-- **Atomic step (Walsh vanishes for `b = 0`, `a ≠ 0`).**
When `b = 0` the Walsh transform is the linear character sum `∑ₓ ψ(⟨a,x⟩)`, which
vanishes for `a ≠ 0`.  This discharges case 2 of Theorems 3.3/3.5/3.6. -/
theorem walshTransform_eq_zero_of_b_eq_zero {n m : ℕ} (ψ : AddChar Fq ℂ) (hψ : ψ ≠ 1)
    (F : (Fin n → Fq) → (Fin m → Fq)) (a : Fin n → Fq) (ha : a ≠ 0) :
    walshTransform ψ F a 0 = 0 := by
  rw [walshTransform_def]
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  exact sum_char_dotProduct_eq_zero ψ hψ a ha

end Flystel