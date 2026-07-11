import Mathlib
import KasamiPermutations.KasamiMap
import KasamiPermutations.TraceFreeCriterion
import KasamiPermutations.FiniteField.Trace
import KasamiPermutations.TraceVersionCriterion

/-!
# Equation (1) of Theorem 1's proof — end to end

This module carries the **equation (1)** thread of the proof of Dobbertin's
Theorem 1, reusing only the minimal set of library lemmas collected in the
`Equation1/` folder (`Defs`, `Theorem5`, `Theorem8Trace`, `Theorem8C1`,
`Q1General`, which in turn rest on `FiniteFieldPrereqs`).

Equation (1) is the equation `q_α(x) = c` cleared of denominators,
`c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)` (`eqn1`, defined in `Defs`).
The chain is:

* `qKasami_bijective_iff` — `q_α` is a permutation of `L` iff `k' + α·n ≡ 1 (mod 2)`;
* `eqn2_of_eqn1` — **the first substantive step (1) ⟹ (2)**: adding the `2^k`-th
  power of (1) to itself gives the linearized equation `ℓ(x) = 0`;
* `linearized_root_unique` / `ell_eq_Q` / `eqn1_nonzero_root_unique` — the two cases showing that
  equation (1) has at most one (nonzero) solution for each fixed `c`.

The `qKasami_*` bridge lemmas identify the paper's `q_α` with the library
polynomials `qeps` (for `α = 0`) and `gmap` (for `α = 1`).

Two internal statements were minimally corrected to be provable; the original
skeleton statements are kept (commented out) next to their corrected forms, with
the reason documented at each.
-/

namespace Kasami

open scoped BigOperators
open Finset
open Kasami.FiniteField Kasami.TraceFreeCriterion Kasami.TraceVersionCriterion

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

/-! ## Bridges to the library machinery -/

omit [Fintype L] [CharP L 2] in
/-- `qKasami … 0` is the trace-free Kasami map `qeps … 0`. -/
lemma qKasami_zero_eq_qeps (z : L) :
    qKasami (L := L) n k k' 0 z = Kasami.TraceFreeCriterion.qeps n k k' (0 : L) z := by
  simp [qKasami, Kasami.TraceFreeCriterion.qeps, Kasami.TraceFreeCriterion.sTrace]

omit [Fintype L] [CharP L 2] in
/-- `qKasami … 1` is the trace-version map `gmap`. -/
lemma qKasami_one_eq_gmap (z : L) :
    qKasami (L := L) n k k' 1 z = Kasami.TraceVersionCriterion.gmap n k k' z := by
  simp only [qKasami, Kasami.TraceVersionCriterion.gmap, Kasami.TraceFreeCriterion.qeps, Kasami.TraceFreeCriterion.sTrace,
    Tr, Kasami.FiniteField.truncTrace, Nat.cast_one, one_mul]

omit [CharP L 2] in
/-- Clearing the denominator of `qKasami` on units: for `x ≠ 0`,
`q_α(x)·x^{2^k+1}` equals the numerator `Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`. -/
lemma qKasami_mul_unit (hn : Fintype.card L = 2 ^ n) (hexp : 2 ^ k + 1 ≤ 2 ^ n - 1)
    (α : ℕ) {x : L} (hx : x ≠ 0) :
    qKasami (L := L) n k k' α x * x ^ (2 ^ k + 1)
      = (∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))) + (α : L) * Tr n x := by
  unfold qKasami
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hexp, ← hn,
    FiniteField.pow_card_sub_one_eq_one x hx, mul_one]

/-! ## Theorem 1 -/

/-
**Theorem 1 (Dobbertin 1999).**  `q_α` is a permutation polynomial on
`L = 𝔽_{2ⁿ}` iff `k' + α·n ≡ 1 (mod 2)`.
-/
theorem qKasami_bijective_iff (hn : Fintype.card L = 2 ^ n) (hk : k < n) (hcop : Nat.Coprime k n)
    (hk' : k * k' % n = 1 % n) (hk0 : 0 < k) (hexp : 2 ^ k + 1 < 2 ^ n - 1)
    (α : ℕ) (hα : α = 0 ∨ α = 1) :
    Function.Bijective (qKasami (L := L) n k k' α) ↔ (k' + α * n) % 2 = 1 := by
  rcases hα with ( rfl | rfl );
  · have hfun : (qKasami (L := L) n k k' 0) = Kasami.TraceFreeCriterion.qeps n k k' (0 : L) := by
      funext z
      exact qKasami_zero_eq_qeps z
    rw [hfun];
    convert Kasami.TraceFreeCriterion.qeps_bijective_iff hn hk0 hk hcop _ hexp ( Or.inl rfl ) using 1;
    · cases Nat.mod_two_eq_zero_or_one k' <;> simp +decide [ *, Nat.even_iff ];
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
  · rw [ show qKasami n k k' 1 = Kasami.TraceVersionCriterion.gmap n k k' from funext fun z => qKasami_one_eq_gmap z ];
    convert Kasami.TraceVersionCriterion.gmap_bijective_iff hn hk0 hk hcop _ hexp using 1;
    · simp +decide [ Nat.odd_iff, Nat.add_mod ];
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ]

/-! ## Equation (1) and the step (1) ⟹ (2) -/

/-
Equation (2) is derived from equation (1) by adding its `2^k`-th power.

**Correction.**  The original skeleton statement `eqn2_of_eqn1_orig` is
*false*: at `x = 0` the cleared equation `eqn1` holds vacuously (`0 = 0`), yet
`ℓ(0) = 1 ≠ 0`.  The faithful version adds `x ≠ 0` and the field hypotheses
`hn` and `k·k' ≡ 1 (mod n)` (used by the Artin–Schreier telescoping).
-/
theorem eqn2_of_eqn1 (hn : Fintype.card L = 2 ^ n) (hkk1 : k * k' % n = 1)
    (α : ℕ) (c x : L) (hx : x ≠ 0) (h : eqn1 (L := L) n k k' α c x) :
    ell (L := L) k c x = 0 := by
  -- Apply the lemma `ell_of_eq` with the given hypotheses.
  apply Kasami.TraceFreeCriterion.ell_of_eq hn hkk1 (by
  have hα : (α : L) = 0 ∨ (α : L) = 1 := by
    rcases Nat.even_or_odd' α with ⟨ c, rfl | rfl ⟩ <;> simp +decide [ *, CharTwo.two_eq_zero ];
  have hTr : Tr n x = 0 ∨ Tr n x = 1 := by
    convert Kasami.FiniteField.trace_bit hn x using 1
  aesop) hx h.symm

/-! #### Case 1: `c ≠ γ^{2^k+1} + γ` for all `γ ∈ L`

In this case the homogeneous part `ℓ₀(x) = ℓ(x) + 1` has no non-zero solution,
since `ℓ₀(x) = (1/c)·(γ₀(x)^{2^k+1} + γ₀(x) + c)²·x` for `γ₀(x) = (c·x^{2^k−1})^{2ⁿ−1}`.
Hence (2) has precisely one solution, and we are done. -/

/-
**Theorem 1, Case 1.**  If `c` is not of the form `γ^{2^k+1} + γ`, then
equation (2) `ℓ(x) = 0` has precisely one solution in `L`.
-/
theorem linearized_root_unique (hn : Fintype.card L = 2 ^ n) (hk0 : 0 < k) (hkn : k < n)
    (c : L) (hc : ∀ γ : L, c ≠ γ ^ (2 ^ k + 1) + γ) :
    {x : L | ell (L := L) k c x = 0}.ncard = 1 := by
  -- By definition of $ell$, we know that $ell k c x = 0$ if and only if $ell0 k c x = 1$.
  simp [ell];
  -- By definition of $phi$, we know that $phi(x) = c^{2^k} * x^{2^{2k}} + x^{2^k} + c * x$.
  set phi : L → L := fun x => c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x;
  -- To show that `phi` is injective, suppose `phi a = phi b`; set `z := a + b`; then `phi z = phi a + phi b = 0` (additivity, characteristic 2). If `z ≠ 0`, then `Kasami.TraceFreeCriterion.ell0_root_imp_image hn hk0 hkn (hc' : c ≠ 0) (hz : z ≠ 0) (h0 : c^(2^k)*z^(2^(2*k)) + z^(2^k) + c*z = 0)` produces `γ` with `c = γ^(2^k+1)+γ`, contradicting `hc γ`. So `z = 0`, i.e. `a = b` (char 2: `a + b = 0 → a = b`).
  have h_inj : Function.Injective phi := by
    intro a b hab
    have hz : phi (a + b) = 0 := by
      simp +zetaDelta at *;
      simp_all +decide [ add_pow_char_pow, mul_add, add_assoc ];
      grind
    have hz_zero : a + b = 0 := by
      by_contra hz_nonzero
      have hz_root : ∃ γ : L, c = γ ^ (2 ^ k + 1) + γ := by
        have := @Kasami.TraceFreeCriterion.ell0_root_imp_image L;
        exact this hn hk0 hkn ( show c ≠ 0 from fun h => hc 0 <| by simp +decide [ h ] ) hz_nonzero hz
      exact hc (hz_root.choose) hz_root.choose_spec
    have h_eq : a = b := by
      grind +revert
    exact h_eq;
  -- Since `phi` is bijective, there is a unique `x` with `phi x = 1`.
  obtain ⟨x, hx⟩ : ∃! x, phi x = 1 := by
    exact ( Finite.injective_iff_surjective.mp h_inj ) 1 |> fun ⟨ x, hx ⟩ => ⟨ x, hx, fun y hy => h_inj <| hy.trans hx.symm ⟩;
  use x;
  grind

/-! ## Case 2 -/

omit [Fintype L] in
/-- In Case 2, `ℓ(x) = Q(x)^{2^k} + f·Q(x)` where `f = γ^{2^k−1} + γ⁻¹`. -/
theorem ell_eq_Q (k : ℕ) (c γ x : L) (hγ : γ ≠ 0)
    (hc : c = γ ^ (2 ^ k + 1) + γ) :
    ell (L := L) k c x
      = Qmap (L := L) k c γ x ^ (2 ^ k)
        + (γ ^ (2 ^ k - 1) + γ⁻¹) * Qmap (L := L) k c γ x := by
  unfold ell Qmap
  exact Kasami.TraceFreeCriterion.Q_factor hγ hc x

/-
**Theorem 1, Case 2.**  If `c = γ^{2^k+1} + γ` (with `c ≠ 0`), then exactly one
**nonzero** `x` solves equation (1).

**Correction.**  The original skeleton statement `theorem_1_case2_orig`
counted *all* solutions of the cleared equation `eqn1`; but `x = 0` always
satisfies `eqn1` (both sides are `0`), so that count is never `1` when a genuine
(nonzero) solution exists.  The paper's claim — "exactly one of the roots solves
(1)" — is faithfully the count of **nonzero** solutions, which needs `c ≠ 0`
(equivalently `γ ≠ 1`, since `γ = 1` gives `c = 0`).
-/
theorem eqn1_nonzero_root_unique (hn : Fintype.card L = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (hk0 : 0 < k)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (α : ℕ) (hα : α = 0 ∨ α = 1)
    (hpar : (k' + α * n) % 2 = 1) (c γ : L) (hc0 : c ≠ 0)
    (hc : c = γ ^ (2 ^ k + 1) + γ) :
    {x : L | x ≠ 0 ∧ eqn1 (L := L) n k k' α c x}.ncard = 1 := by
  convert Set.ncard_eq_one.mpr _ using 1;
  obtain ⟨a, ha⟩ : ∃ a : L, qKasami (L := L) n k k' α a = c ∧ a ≠ 0 := by
    obtain ⟨a, ha⟩ : ∃ a : L, qKasami (L := L) n k k' α a = c := by
      convert Function.Bijective.surjective ( qKasami_bijective_iff hn hk hcop hk' hk0 hexp α hα |>.2 hpar ) c using 1;
    refine' ⟨ a, ha, _ ⟩ ; rintro rfl ; simp_all +decide [ qKasami ];
    rw [ zero_pow ( Nat.sub_ne_zero_of_lt hexp ) ] at ha ; aesop;
  refine' ⟨ a, Set.eq_singleton_iff_unique_mem.mpr ⟨ _, fun x hx => _ ⟩ ⟩ <;> simp_all +decide [ eqn1 ];
  · convert qKasami_mul_unit ( hn := hn ) ( show 2 ^ k + 1 ≤ 2 ^ n - 1 from le_of_lt hexp ) α ha.2 using 1 ; aesop;
  · have h_eq : qKasami (L := L) n k k' α x = γ ^ (2 ^ k + 1) + γ := by
      have h_eq : qKasami (L := L) n k k' α x * x ^ (2 ^ k + 1) = (∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))) + (α : L) * Tr n x := by
        convert qKasami_mul_unit hn ( le_of_lt hexp ) α hx.1 using 1;
      exact mul_left_cancel₀ ( pow_ne_zero ( 2 ^ k + 1 ) hx.1 ) ( by linear_combination' h_eq - hx.2 );
    have h_eq : Function.Bijective (qKasami (L := L) n k k' α) := by
      apply (qKasami_bijective_iff hn hk hcop hk' hk0 hexp α hα).mpr hpar;
    exact h_eq.injective ( by aesop )

end Kasami