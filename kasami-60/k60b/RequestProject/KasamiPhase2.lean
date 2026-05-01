import Mathlib
import RequestProject.KasamiDefs

/-!
# Kasami AB — Phase 2: Cross-Term Decomposition

## Main Results

* `trace_frobenius_invariant` — Tr(x^{2^k}) = Tr(x).
* `linPolyL_add` — L_k is GF(2)-linear (i.e., additive).
* `bilinForm_eq_trace_polar` — B_a(x,y) = Tr(a · polarForm(k, x, y)).
* `polarForm_symmetric` — The polar form is symmetric in x, y.
* `radical_eq_ker_LA` — Characterization of the radical (CCD core result).
-/

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

section Phase2

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-! ### Trace and Frobenius interaction -/

/-- The absolute trace from F to GF(2), viewed as `F → ZMod 2`. -/
noncomputable abbrev AbsTrace : F →ₗ[ZMod 2] (ZMod 2) :=
  Algebra.trace (ZMod 2) F

/-- The trace is invariant under the Frobenius: Tr(x^{2^k}) = Tr(x). -/
lemma trace_frobenius_invariant (k : ℕ) (x : F) :
    AbsTrace (frobIter k x) = AbsTrace x := by
  have h_frob_iter : ∀ (k : ℕ) (x : F), AbsTrace (frobIter k x) = AbsTrace x := by
    intro k x;
    induction' k with k ih;
    · unfold frobIter; norm_num;
    · convert ih using 1;
      unfold frobIter;
      simp +decide [ pow_succ, pow_mul ];
      convert ( Algebra.trace_eq_of_algEquiv ( show F ≃ₐ[ZMod 2] F from { Equiv.ofBijective ( fun x => x ^ 2 ) ⟨ fun x y hxy => ?_, fun x => ?_ ⟩ with map_add' := ?_, map_mul' := ?_, commutes' := ?_ } ) ) ( x ^ 2 ^ k ) using 1;
      all_goals norm_num [ ← sq ];
      any_goals intros; ring;
      any_goals rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;
      grind;
      have h_frob_iter : Function.Bijective (fun x : F => x ^ 2) := by
        have h_frob_iter : Function.Injective (fun x : F => x ^ 2) := by
          exact fun x y hxy => by simpa [ sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq ] using hxy;
        exact ⟨ h_frob_iter, Finite.injective_iff_surjective.mp h_frob_iter ⟩;
      exact h_frob_iter.surjective x;
      all_goals generalize_proofs at *;
      rename_i r hr;
      fin_cases r <;> simp +decide;
  exact h_frob_iter k x

/-! ### Linearity of L_k -/

omit [Fintype F] in
/-- L_k is GF(2)-additive: L_k(x + y) = L_k(x) + L_k(y). -/
lemma linPolyL_add (k : ℕ) (x y : F) :
    linPolyL k (x + y) = linPolyL k x + linPolyL k y := by
  unfold linPolyL;
  have h_frob : ∀ (n : ℕ), (x + y) ^ (2 ^ n) = x ^ (2 ^ n) + y ^ (2 ^ n) := by
    intro n; induction n <;> simp_all +decide [ pow_succ, pow_mul ] ;
    grind;
  rw [ h_frob, h_frob ] ; ring

omit [Fintype F] in
/-- L_k(0) = 0. -/
@[simp] lemma linPolyL_zero (k : ℕ) : linPolyL (F := F) k 0 = 0 := by
  unfold linPolyL; ring

/-
L_k(c·x) = c·L_k(x) for c ∈ GF(2), i.e., c ∈ {0, 1}.
-/
omit [Fintype F] in
lemma linPolyL_smul_gf2 (k : ℕ) (x : F) (c : ZMod 2) :
    linPolyL k (algebraMap (ZMod 2) F c * x) =
    algebraMap (ZMod 2) F c * linPolyL k x := by
  fin_cases c <;> simp +decide [ linPolyL ]

/-! ### Polar form and bilinear form -/

/-- The "polar form" of x^d: (x+y)^d + x^d + y^d. -/
noncomputable def polarForm (k : ℕ) (x y : F) : F :=
  (x + y) ^ kasamiExp k + x ^ kasamiExp k + y ^ kasamiExp k

/-
The polar form is symmetric: polarForm(k, x, y) = polarForm(k, y, x).
-/
omit [Fintype F] [CharP F 2] in
lemma polarForm_symmetric (k : ℕ) (x y : F) :
    polarForm k x y = polarForm k y x := by
  unfold polarForm;
  ring

/-- The quadratic form Q_a(x) = Tr(a · x^d). -/
noncomputable def quadForm (k : ℕ) (a x : F) : ZMod 2 :=
  AbsTrace (a * x ^ kasamiExp k)

/-- The associated bilinear form B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y). -/
noncomputable def bilinForm (k : ℕ) (a x y : F) : ZMod 2 :=
  quadForm k a (x + y) + quadForm k a x + quadForm k a y

omit [Fintype F] in
/-- B_a(x,y) = Tr(a · polarForm(k, x, y)). -/
lemma bilinForm_eq_trace_polar (k : ℕ) (a x y : F) :
    bilinForm k a x y = AbsTrace (a * polarForm k x y) := by
  unfold bilinForm quadForm polarForm;
  simp +decide [ mul_add, add_assoc ]

/-- The radical of Q_a: {y | ∀ x, B_a(x,y) = 0}. -/
def radical (k : ℕ) (a : F) : Set F :=
  {y : F | ∀ x : F, bilinForm k a x y = 0}

/-
The radical is a subgroup of the additive group.
-/
omit [Fintype F] in
lemma radical_zero_mem (k : ℕ) (a : F) : (0 : F) ∈ radical k a := by
  intro x;
  unfold bilinForm quadForm;
  simp +decide [ ← two_mul, kasamiExp ]

/-
The radical is closed under addition.
-/
omit [Fintype F] in
lemma radical_add_mem (k : ℕ) (a : F) {x y : F}
    (hx : x ∈ radical k a) (hy : y ∈ radical k a) :
    x + y ∈ radical k a := by
  simp_all +decide [ radical ];
  unfold bilinForm at *; simp_all +decide [ ← add_assoc ] ;
  grind

/-! ### The a-dependent linearized polynomial -/

/-- The a-dependent linearized polynomial from the CCD decomposition:
    L_a(y) = a · y^{2^{2k}} + a^{2^k} · y^{2^k} + a^{2^{2k}} · y.
    When a = 1, this reduces to L_k(y). -/
noncomputable def linPolyLA (k : ℕ) (a y : F) : F :=
  a * y ^ (2 ^ (2 * k)) + a ^ (2 ^ k) * y ^ (2 ^ k) + a ^ (2 ^ (2 * k)) * y

/-
L_a is additive in y.
-/
omit [Fintype F] in
lemma linPolyLA_add (k : ℕ) (a x y : F) :
    linPolyLA k a (x + y) = linPolyLA k a x + linPolyLA k a y := by
  unfold linPolyLA;
  simp +decide [ add_pow_char_pow ];
  grind +qlia

/-- **CCD Core Result.** The radical of Q_a equals the kernel of L_a.

This is the deepest result in Phase 2. The proof requires:
1. Expanding the polar form (x+y)^d + x^d + y^d for d = 2^{2k} - 2^k + 1.
2. Using the trace-Frobenius invariance Tr(u^{2^k}) = Tr(u) to
   reorganize the cross-terms.
3. Showing the resulting expression equals Tr(x · L_a(y)).
4. Concluding by nondegeneracy of the trace pairing.

The required hypothesis k ≥ 1 ensures d ≥ 3. -/
theorem radical_eq_ker_LA {n : ℕ} (hn : n ≥ 2)
    (hcard : Nat.card F = 2 ^ n) (k : ℕ) (hk : k ≥ 1) (a : F) (ha : a ≠ 0) :
    radical k a = {y : F | linPolyLA k a y = 0} := by
  sorry

end Phase2
