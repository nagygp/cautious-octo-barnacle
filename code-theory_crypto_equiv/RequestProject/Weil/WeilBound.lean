import RequestProject.Weil.PointCountBound
import RequestProject.Weil.Trace
import RequestProject.Weil.Amplification
import RequestProject.Weil.Extensions

/-!
# The headline one-variable Weil bound

This module assembles the previous pieces into the **general (non-monomial) one-variable Weil
bound** for additive character sums:
$$ \Bigl\| \sum_{x \in \mathbb F_q} \psi\bigl(f(x)\bigr) \Bigr\| \;\le\; (d-1)\,\sqrt q, $$
for a nontrivial additive character `ψ` and a polynomial `f` of degree `d` with `p ∤ d`.

## The assembly

1. **Bridge** (`exists_bridge`).  Choosing the standard additive character `ψ₀ = e ∘ Tr`, additive
   orthogonality turns the Artin–Schreier point count into a sum of character sums over the
   order-`p` group `{ψ₀.mulShift t : t ∈ 𝔽_p}`:
   `#C_f(𝔽_q) = ∑_{t ∈ 𝔽_p} charSum (ψ₀.mulShift t) f`,
   the `t = 0` term contributing `q`.

2. **Point-count bound** (`abs_curvePointCount_sub_card_le`): `|#C_f(𝔽_q) - q| ≤ (d-1)(p-1)√q`.

3. **Descent to a single character** (`weil_bound`).  Steps (1)–(2) directly bound the *sum* of the
   `p-1` nontrivial character sums `∑_{t ≠ 0} charSum (ψ₀.mulShift t) f`.  The sharp bound for an
   *individual* nontrivial character then follows by the elementary extension-field amplification
   ("tensor-power trick"): apply the point-count bound over every extension `𝔽_{q^k}`, take
   `2k`-th roots of `‖S‖^{2k}`, and let `k → ∞`.  (Equivalently, this is the statement that the
   reciprocal roots of the Artin–Schreier L-function have absolute value `√q`.)  Combined with
   `charSum_mulShift`, which shows every nontrivial character contributes a sum of the same shape,
   one obtains the bound for every nontrivial `ψ`.

## Main statement
* `Weil.weil_bound` — the headline `‖∑ₓ ψ(f x)‖ ≤ (d-1)√q`.
-/

open scoped BigOperators
open Polynomial

namespace Weil

variable {F : Type*} [Field F] [Fintype F]

/-
**Bridge identity (additive form).**  There is a fixed nontrivial additive character `ψ₀`
(the standard one `e ∘ Tr_{F/𝔽_p}`) so that for every `f` the Artin–Schreier point count is the
sum of the character sums over the order-`p` group `{ψ₀.mulShift t : t ∈ 𝔽_p}`:
`#C_f(𝔽_q) = ∑_{t ∈ primeField F} charSum (ψ₀.mulShift t) f`.

The `t = 0` summand is `charSum ψ₀^{0} f = q`, so subtracting it expresses `#C_f - q` as the sum of
the `p - 1` *nontrivial* character sums in this group.
-/
lemma exists_bridge :
    ∃ ψ₀ : AddChar F ℂ, ψ₀ ≠ 1 ∧
      ∀ f : F[X], (asPointCount f : ℂ)
        = ∑ t ∈ primeField F, charSum (ψ₀.mulShift t) f := by
  have := @Weil.bridge_pointwise F;
  obtain ⟨ψ₀, hψ₀⟩ := this;
  refine' ⟨ ψ₀, hψ₀.1, fun f => _ ⟩;
  rw [ Weil.asPointCount_eq_sum ];
  simp +decide only [Nat.cast_sum, hψ₀.2, charSum];
  exact Finset.sum_comm

/-
**The general one-variable Weil bound.**

Let `F = 𝔽_q` be a finite field of characteristic `p`, let `ψ : AddChar F ℂ` be a *nontrivial*
additive character, and let `f ∈ F[X]` be a polynomial whose degree `d` is *prime to `p`*
(`¬ p ∣ d`; this in particular forces `d ≥ 1`).  Then
$$ \Bigl\| \sum_{x \in \mathbb F_q} \psi\bigl(f(x)\bigr) \Bigr\| \;\le\; (d-1)\,\sqrt q. $$
-/
theorem weil_bound (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : F[X])
    (hd : ¬ ringChar F ∣ f.natDegree) :
    ‖charSum ψ f‖ ≤ (f.natDegree - 1 : ℝ) * Real.sqrt (Fintype.card F) := by
  by_contra h_contra;
  obtain ⟨E, instField, instFt, instAlg, ⟨e⟩, hcard⟩ := Weil.Extensions.exists_extension_tower (F := F);
  have := Weil.Extensions.exists_charSum_eigenvalues_le E hcard ψ hψ f hd;
  have h_extCharSum_eq_charSum : Extensions.extCharSum (E 1) ψ f = charSum ψ f := by
    refine' Finset.sum_bij ( fun x _ => e x ) _ _ _ _ <;> simp +decide;
    · exact e.surjective;
    · intro x; simp +decide [ Extensions.liftChar, Extensions.baseChange ] ;
      have h_trace : Algebra.trace F (E 1) = (Algebra.trace F F).comp (e.toLinearMap) := by
        ext x; simp +decide [ Algebra.trace ] ;
        convert LinearMap.trace_conj' _ _ using 2;
        swap;
        exact e.symm.toLinearEquiv;
        ext y; simp +decide [ LinearMap.mul ] ;
      simp +decide [ h_trace, Polynomial.aeval_def ];
      simp +decide [ Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range ];
  obtain ⟨ r, α, hr, hα, h ⟩ := this;
  refine' h_contra _;
  rw [ ← h_extCharSum_eq_charSum, h 1 le_rfl ];
  simp +zetaDelta at *;
  exact le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => hα _ ) ( by simpa [ Nat.cast_sub ( show 1 ≤ f.natDegree from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hr ) ( Real.sqrt_nonneg _ ) ) )

end Weil