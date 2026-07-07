import RequestProject.Walsh.Moments

/-!
# Differential spectrum and the APN second-moment characterization

This module advances the **symmetric/ZK cryptanalysis** track (see
`RESEARCH_DIRECTIONS.md`, item *Chabaud–Vaudenay*).  It establishes the
elementary but load-bearing facts about the **differential spectrum**
`N_f(a, ·)` of a vectorial Boolean function `f : F → F` over a finite field of
characteristic two, and the resulting **second-moment characterization of APN**:

> for every nonzero `a`, the differential counts are all even, satisfy
> `∑_b N_f(a, b) = |F|` and `∑_b N_f(a, b)^2 ≥ 2|F|`, with **equality iff**
> every `N_f(a, b) ≤ 2`.

The equality case is the differential-spectrum half of the Chabaud–Vaudenay
relation between APN-ness and the second moment of the differential spectrum, and
it characterizes the APN property purely in terms of a single quadratic sum.

## Main results

* `diffCount_even` — every differential count `N_f(a, b)` is even (`a ≠ 0`).
* `sum_diffCount_sq_ge` — the second-moment lower bound
  `2|F| ≤ ∑_b N_f(a, b)^2` for `a ≠ 0`.
* `local_apn_iff_sum_sq` — for `a ≠ 0`, all `N_f(a, b) ≤ 2` **iff**
  `∑_b N_f(a, b)^2 = 2|F|`.
* `isAPN_iff_sum_diffCount_sq` — `f` is APN **iff** for every `a ≠ 0`,
  `∑_b N_f(a, b)^2 = 2|F|`.
-/

set_option maxHeartbeats 1600000

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
The differential count `N_f(a, b)` is even when `a ≠ 0`: the solution set of
`f(x + a) + f(x) = b` is invariant under the fixed-point-free involution
`x ↦ x + a`, so its solutions pair up.
-/
theorem diffCount_even (f : F → F) (a : F) (ha : a ≠ 0) (b : F) :
    Even (diffCount f a b) := by
  obtain ⟨g, hg⟩ : ∃ g : Finset F, g.card = Fintype.card {x : F // f (x + a) + f x = b} ∧ ∀ x ∈ g, x + a ∈ g ∧ x + a ≠ x := by
    refine' ⟨ Finset.univ.filter fun x => f ( x + a ) + f x = b, _, _ ⟩ <;> simp +decide [ Fintype.card_subtype ];
    grind;
  -- Since $g$ is a finite set, we can partition it into pairs $\{x, x+a\}$.
  have h_partition : ∃ p : Finset (Finset F), (∀ s ∈ p, s.card = 2) ∧ (∀ s₁ ∈ p, ∀ s₂ ∈ p, s₁ ≠ s₂ → Disjoint s₁ s₂) ∧ g = Finset.biUnion p id := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) g, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · grind;
    · ext x; aesop;
  obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h_partition; rw [ show diffCount f a b = g.card from ?_ ] ; rw [ hp₃, Finset.card_biUnion ] ; aesop;
  · exact fun x hx y hy hxy => hp₂ x hx y hy hxy;
  · unfold diffCount; aesop;

/-
**Second-moment lower bound.**  For `a ≠ 0`,
`2|F| ≤ ∑_b N_f(a, b)^2`.  Since each `N_f(a, b)` is even and nonnegative,
`N(N - 2) ≥ 0`, and `∑_b N_f(a, b) = |F|`.
-/
theorem sum_diffCount_sq_ge (f : F → F) (a : F) (ha : a ≠ 0) :
    2 * (Fintype.card F : ℤ) ≤ ∑ b : F, (diffCount f a b : ℤ) ^ 2 := by
  have h_even : ∀ b : F, Even (diffCount f a b) := fun b => diffCount_even f a ha b
  convert Finset.sum_le_sum fun b _ => show ( diffCount f a b : ℤ ) ^ 2 ≥ 2 * diffCount f a b from ?_ using 1;
  · rw_mod_cast [ ← Finset.mul_sum _ _ _, WalshAB.diffCount_sum ];
  · obtain ⟨ k, hk ⟩ := h_even b;
    rcases k with ( _ | _ | k ) <;> simp_all +decide ; nlinarith

/-- **Local APN characterization.**  For `a ≠ 0`, the differential counts in
direction `a` are all `≤ 2` **iff** their second moment attains the minimum
`2|F|`.  (Equality case of `sum_diffCount_sq_ge`.) -/
theorem local_apn_iff_sum_sq (f : F → F) (a : F) (ha : a ≠ 0) :
    (∀ b : F, diffCount f a b ≤ 2) ↔
      ∑ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) := by
  constructor <;> intro h;
  · have h_even : ∀ b : F, Even (diffCount f a b) := fun b => diffCount_even f a ha b
    have h_sum : ∑ b : F, (diffCount f a b : ℤ) ^ 2 = ∑ b : F, 2 * (diffCount f a b : ℤ) := by
      exact Finset.sum_congr rfl fun b _ => by specialize h b; specialize h_even b; interval_cases diffCount f a b <;> trivial;
    rw [ h_sum, ← Finset.mul_sum _ _ _, ← Nat.cast_sum, WalshAB.diffCount_sum ];
  · intro b
    by_contra h_contra
    have h_pos : (diffCount f a b : ℤ)^2 - 2 * (diffCount f a b : ℤ) > 0 := by
      nlinarith only [ h_contra ];
    have h_sum_pos : ∑ b : F, ((diffCount f a b : ℤ)^2 - 2 * (diffCount f a b : ℤ)) > 0 := by
      refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => _ ) ( Finset.mem_univ b ) );
      · exact h_pos;
      · obtain ⟨ k, hk ⟩ := diffCount_even f a ha x;
        rcases k with ( _ | _ | k ) <;> simp_all +decide ; nlinarith;
    simp_all +decide [ Finset.sum_sub_distrib, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.mul_sum _ _ _ ] at h_sum_pos ; linarith [ show ( ∑ x : F, ( diffCount f a x : ℤ ) ) = Fintype.card F from mod_cast WalshAB.diffCount_sum f a ]

/-
**Second-moment characterization of APN.**  `f` is APN **iff** for every
nonzero `a` the second moment of the differential spectrum attains its minimum
`2|F|`.
-/
theorem isAPN_iff_sum_diffCount_sq (f : F → F) :
    IsAPN f ↔ ∀ a : F, a ≠ 0 → ∑ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) := by
  constructor;
  · exact fun h a ha => WalshAB.local_apn_iff_sum_sq f a ha |>.1 fun b => h a ha b;
  · intro h a ha b; specialize h a ha; have := local_apn_iff_sum_sq f a ha; simp_all +decide ;
    exact this b

end WalshAB