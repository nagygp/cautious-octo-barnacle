import Mathlib
import RequestProject.Walsh.Transform

/-!
# Foundations, Layer A1 — quadratic-form Gauss/Weil sums over `GF(2ⁿ)`

This module transcribes **Layer A1** of the value-set dependency chain laid out in
`Docs/VanishFutureDirections.md` §6: the classical evaluation of the
*quadratic-form Gauss/Weil sum*

```
  S(Q) = ∑_{x ∈ GF(2ⁿ)} χ(Q x)            (χ = WalshAB.χ, the ±1 sign character)
```

for a **quadratic form** `Q : F → F` over `GF(2ⁿ)`.  Classically (Lidl–Niederreiter
Ch. 5–6; Carlet Ch. 6) this sum is an *algebraic integer* taking values in

```
  S(Q) ∈ { 0, +2^{(n+r)/2}, -2^{(n+r)/2} }
```

where `r` is the dimension of the **radical** of the associated bilinear
(polarization) form.  Because the characteristic-2 sign character `χ` is already
`ℤ`-valued (`χ : F → ℤ`, values `±1`), the "algebraic integer in `ℤ[ζ]`" packaging
is here literally an integer, and the substantive content is the
`{0, ±2^{(n+r)/2}}` evaluation, which is proved unconditionally below.

## The argument

Write `B(x,y) = polar Q x y = Q(x+y) + Q x + Q y` for the polar form, which for a
quadratic `Q` is **biadditive** (and symmetric).  The squared Gauss sum factors:

```
  S(Q)² = ∑_{x,y} χ(Q x + Q y)
        = ∑_u χ(Q u) · ∑_x χ(B(x,u))          (substitute y = x + u; polarization)
        = q · ∑_{u ∈ radical} χ(Q u)            (orthogonality of x ↦ χ(B(x,u)))
        = q · |radical|   or   0                (χ∘Q is a character on the radical)
```

Since the radical is an `F₂`-subspace of `F`, `|radical| = 2^r`, giving
`S(Q)² ∈ {0, 2^{n+r}}` and hence `S(Q) ∈ {0, ±2^{(n+r)/2}}`.

This layer is *foundational input* for Layer A2 (the 2-adic / Stickelberger
divisibility bound `2^{(n+1)/2} ∣ R(s)`): a Frobenius substitution rewrites the
Kasami cross-correlation `R(s)` as such a quadratic Gauss sum, whose 2-adic
valuation is read off the radical dimension supplied here.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Quadratic forms and their polar (bilinear) form -/

/-- The **polar form** of `Q`: `B(x,y) = Q(x+y) + Q x + Q y`. -/
def polar (Q : F → F) (x y : F) : F := Q (x + y) + Q x + Q y

/-- A function `Q : F → F` is a **quadratic form** when its polar form is
biadditive (it is automatically symmetric). -/
structure IsQuadraticForm (Q : F → F) : Prop where
  /-- additivity of the polar form in the first argument -/
  polar_add_left : ∀ x₁ x₂ y, polar Q (x₁ + x₂) y = polar Q x₁ y + polar Q x₂ y
  /-- additivity of the polar form in the second argument -/
  polar_add_right : ∀ x y₁ y₂, polar Q x (y₁ + y₂) = polar Q x y₁ + polar Q x y₂

/-
The polar form is symmetric.
-/
omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem polar_comm (Q : F → F) (x y : F) : polar Q x y = polar Q y x := by
  unfold polar; rw [add_comm x y]; ring

/-
A quadratic form vanishes at `0`.
-/
omit [Fintype F] [DecidableEq F] in
theorem IsQuadraticForm.map_zero {Q : F → F} (hQ : IsQuadraticForm Q) : Q 0 = 0 := by
  have := hQ.polar_add_left 0 0 0;
  simp_all +decide [ polar ];
  grind

/-
The polarization identity in characteristic 2:
`Q x + Q (x + u) = polar Q x u + Q u`.
-/
omit [Fintype F] [DecidableEq F] in
theorem add_shift_eq (Q : F → F) (x u : F) :
    Q x + Q (x + u) = polar Q x u + Q u := by
  simp +decide [ polar, ← eq_sub_iff_add_eq ];
  grind

/-! ## The Gauss sum and the radical -/

/-- The **quadratic-form Gauss sum** `S(Q) = ∑_x χ(Q x)`. -/
noncomputable def quadGaussSum (Q : F → F) : ℤ := ∑ x : F, χ (Q x)

/-- The **radical** of `Q`: the set of `u` on which the polar form is trace-trivial,
i.e. `Tr (polar Q x u) = 0` for all `x`. -/
noncomputable def radical (Q : F → F) : Finset F :=
  univ.filter (fun u => ∀ x, Tr (polar Q x u) = 0)

omit [DecidableEq F] in
theorem mem_radical {Q : F → F} {u : F} :
    u ∈ radical Q ↔ ∀ x, Tr (polar Q x u) = 0 := by
  simp [radical]

omit [DecidableEq F] in
theorem zero_mem_radical {Q : F → F} (hQ : IsQuadraticForm Q) : (0 : F) ∈ radical Q := by
  rw [mem_radical]
  intro x
  have h : polar Q x 0 = 0 := by simp [polar, hQ.map_zero, CharTwo.add_self_eq_zero]
  rw [h, Tr_zero]

omit [DecidableEq F] in
theorem add_mem_radical {Q : F → F} (hQ : IsQuadraticForm Q) {u v : F}
    (hu : u ∈ radical Q) (hv : v ∈ radical Q) : u + v ∈ radical Q := by
  simp_all +decide [ radical, hQ.polar_add_right ]

/-! ## Orthogonality for additive forms -/

/-
Orthogonality for a `χ`-character built from an additive map: if
`φ : F → F` satisfies `φ (x+y) = φ x + φ y`, then `∑_x χ(φ x)` is `q` when
`φ` is trace-trivial and `0` otherwise.
-/
theorem sum_chi_additive (φ : F → F) (hφ : ∀ x y, φ (x + y) = φ x + φ y) :
    ∑ x : F, χ (φ x) = if (∀ x, Tr (φ x) = 0) then (Fintype.card F : ℤ) else 0 := by
  split_ifs with h;
  · simp +decide [ h, χ ];
  · -- There exists $x_0$ such that $Tr(\varphi(x_0)) \neq 0$, hence $Tr(\varphi(x_0)) = 1$ in $ZMod 2$, so $\chi(\varphi(x_0)) = -1$.
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, Tr (φ x₀) ≠ 0 := by
      exact not_forall.mp h
    have hx₀_val : χ (φ x₀) = -1 := by
      exact if_neg hx₀;
    -- Use the shift bijection $x \mapsto x + x₀$ (an `Equiv.addRight x₀`): $\sum_x \chi(\varphi(x)) = \sum_x \chi(\varphi(x + x₀))$ by `Equiv.sum_comp`.
    have h_shift : ∑ x : F, χ (φ x) = ∑ x : F, χ (φ (x + x₀)) := by
      rw [ ← Equiv.sum_comp ( Equiv.addRight x₀ ) ] ; aesop;
    -- Then $\chi(\varphi(x+x₀)) = \chi(\varphi(x)) \cdot \chi(\varphi(x₀)) = - \chi(\varphi(x))$.
    have h_char : ∀ x : F, χ (φ (x + x₀)) = -χ (φ x) := by
      intro x; rw [ hφ, WalshAB.χ_mul ] ; simp +decide [ hx₀_val ] ;
    norm_num [ h_char ] at h_shift; linarith;

/-
The inner sum `∑_x χ(polar Q x u)` collapses to `q` on the radical and `0`
elsewhere.
-/
theorem inner_sum_eq {Q : F → F} (hQ : IsQuadraticForm Q) (u : F) :
    ∑ x : F, χ (polar Q x u) = if u ∈ radical Q then (Fintype.card F : ℤ) else 0 := by
  convert sum_chi_additive ( fun x => polar Q x u ) ( fun x y => ?_ ) using 1;
  · simp +decide [ mem_radical ];
  · exact hQ.polar_add_left x y u

/-! ## The squared Gauss sum -/

/-
The squared Gauss sum factors as a double sum via the polarization identity.
-/
theorem quadGaussSum_sq_eq_double (Q : F → F) :
    quadGaussSum Q ^ 2 = ∑ u : F, χ (Q u) * ∑ x : F, χ (polar Q x u) := by
  unfold quadGaussSum;
  simp +decide only [pow_two, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx;
  rw [ Finset.sum_mul _ _ _ ];
  refine' Finset.sum_bij ( fun y _ => x + y ) _ _ _ _ <;> simp +decide [ polar ];
  · exact fun b => ⟨ b - x, add_sub_cancel _ _ ⟩;
  · grind +suggestions

/-
**The squared Gauss sum collapses onto the radical:**
`S(Q)² = q · ∑_{u ∈ radical} χ(Q u)`.
-/
theorem quadGaussSum_sq_eq_radical_sum {Q : F → F} (hQ : IsQuadraticForm Q) :
    quadGaussSum Q ^ 2 = (Fintype.card F : ℤ) * ∑ u ∈ radical Q, χ (Q u) := by
  rw [ quadGaussSum_sq_eq_double, Finset.mul_sum ];
  rw [ ← Finset.sum_subset ( Finset.subset_univ ( radical Q ) ) ];
  · exact Finset.sum_congr rfl fun x hx => by rw [ inner_sum_eq hQ x, if_pos hx ] ; ring;
  · intro x hx hx'; rw [ inner_sum_eq hQ x ] ; aesop;

/-
The restriction of `χ ∘ Q` to the radical is a character, so its sum is
`|radical|` (when trace-trivial there) or `0`.
-/
theorem radical_sum_eq {Q : F → F} (hQ : IsQuadraticForm Q) :
    ∑ u ∈ radical Q, χ (Q u)
      = if (∀ u ∈ radical Q, Tr (Q u) = 0) then ((radical Q).card : ℤ) else 0 := by
  split_ifs with h;
  · exact Eq.trans ( Finset.sum_congr rfl fun x hx => by unfold χ; aesop ) ( by simp +decide );
  · obtain ⟨u₀, hu₀⟩ : ∃ u₀ ∈ radical Q, Tr (Q u₀) ≠ 0 := by
      exact by push_neg at h; exact h;
    -- By the properties of the character $\chi$, we have $\chi(Q(u + u₀)) = -\chi(Q(u))$ for all $u \in \text{radical } Q$.
    have h_char : ∀ u ∈ radical Q, χ (Q (u + u₀)) = -χ (Q u) := by
      intro u hu
      have h_polar : Q (u + u₀) = polar Q u u₀ + Q u + Q u₀ := by
        simp only [polar]; abel_nf; simp [CharTwo.two_eq_zero]
      simp_all +decide [ χ, Tr_add ];
      simp_all +decide [ mem_radical ];
      cases Fin.exists_fin_two.mp ⟨ Tr ( Q u ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ Tr ( Q u₀ ), rfl ⟩ <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
    have h_bij : Finset.image (fun u => u + u₀) (radical Q) = radical Q := by
      refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
      · exact fun x hx => add_mem_radical hQ hx hu₀.1;
      · rw [ Finset.card_image_of_injective _ ( add_left_injective u₀ ) ];
    have h_sum_zero : ∑ u ∈ radical Q, χ (Q u) = ∑ u ∈ radical Q, χ (Q (u + u₀)) := by
      conv_lhs => rw [ ← h_bij, Finset.sum_image ( by simp +decide ) ] ;
    rw [ Finset.sum_congr rfl h_char ] at h_sum_zero ; norm_num at h_sum_zero ; linarith

/-
**Dichotomy for the squared Gauss sum:** either it is `0`, or it equals
`q · |radical|`.
-/
theorem quadGaussSum_sq_eq_or {Q : F → F} (hQ : IsQuadraticForm Q) :
    quadGaussSum Q ^ 2 = 0
    ∨ quadGaussSum Q ^ 2 = (Fintype.card F : ℤ) * ((radical Q).card : ℤ) := by
  rw [ quadGaussSum_sq_eq_radical_sum hQ, radical_sum_eq hQ ];
  split_ifs <;> simp +decide

/-! ## The radical is an `F₂`-subspace -/

/-
The cardinality of the radical is a power of two, of exponent at most `n`.
-/
omit [DecidableEq F] in
theorem radical_card_pow_two {n : ℕ} {Q : F → F} (hQ : IsQuadraticForm Q)
    (hcard : Fintype.card F = 2 ^ n) :
    ∃ r : ℕ, r ≤ n ∧ (radical Q).card = 2 ^ r := by
  obtain ⟨H, hH⟩ : ∃ H : AddSubgroup F, H.carrier = {u | ∀ x, Tr (polar Q x u) = 0} := by
    refine' ⟨ { carrier := { u : F | ∀ x : F, Tr ( polar Q x u ) = 0 }, add_mem' := _, zero_mem' := _, neg_mem' := _ }, rfl ⟩;
    · intro a b ha hb x;
      have := hQ.polar_add_right x a b; simp_all +decide [ polar ] ;
    · simp +decide [ polar, hQ.map_zero ];
      simp +decide [ ← two_smul ℤ, CharTwo.two_eq_zero ];
    · grind +suggestions;
  -- Since the radical is exactly the set of elements in H, their cardinalities are equal.
  have h_card_eq : (radical Q).card = Fintype.card H := by
    convert Set.toFinset_card ( H.carrier ) using 1;
    congr ; ext ; simp +decide [ mem_radical, hH ];
  have := AddSubgroup.card_addSubgroup_dvd_card H; simp_all +decide [ Nat.dvd_prime_pow ] ;

/-! ## The headline Layer A1 evaluation -/

/-
**Layer A1 (squared form).**  For a quadratic form `Q` over `GF(2ⁿ)` the
squared Gauss sum is either `0` or `2^{n+r}`, where `2^r` is the size of the
radical (`r` the rank-defect of the polar form).
-/
theorem quadGaussSum_sq {n : ℕ} {Q : F → F} (hQ : IsQuadraticForm Q)
    (hcard : Fintype.card F = 2 ^ n) :
    ∃ r : ℕ, r ≤ n ∧ (quadGaussSum Q ^ 2 = 0 ∨ quadGaussSum Q ^ 2 = 2 ^ (n + r)) := by
  rcases quadGaussSum_sq_eq_or hQ with h | h;
  · exact ⟨ 0, zero_le _, Or.inl h ⟩;
  · obtain ⟨ r, hr₁, hr₂ ⟩ := radical_card_pow_two hQ hcard; use r; simp_all +decide [ pow_add ] ;

/-
**Layer A1 (value form).**  For a quadratic form `Q` over `GF(2ⁿ)`, the Gauss
sum `S(Q) = ∑_x χ(Q x)` takes a value in `{0, ±2^{(n+r)/2}}`: it is either `0`, or
`±2^m` where `2m = n + r` and `2^r` is the size of the radical.
-/
theorem quadGaussSum_value {n : ℕ} {Q : F → F} (hQ : IsQuadraticForm Q)
    (hcard : Fintype.card F = 2 ^ n) :
    ∃ r : ℕ, r ≤ n ∧
      (quadGaussSum Q = 0
        ∨ ∃ m : ℕ, 2 * m = n + r ∧ (quadGaussSum Q = 2 ^ m ∨ quadGaussSum Q = -(2 ^ m))) := by
  obtain ⟨ r, hr, h ⟩ := quadGaussSum_sq hQ hcard;
  cases' h with h h;
  · exact ⟨ r, hr, Or.inl <| sq_eq_zero_iff.mp h ⟩;
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (quadGaussSum Q).natAbs = 2 ^ m := by
      have h_abs : (quadGaussSum Q).natAbs ^ 2 = 2 ^ (n + r) := by
        simpa [ ← Int.natCast_inj ] using h;
      have : (quadGaussSum Q).natAbs ∣ 2 ^ (n + r) := h_abs ▸ dvd_pow_self _ two_ne_zero; ( rw [ Nat.dvd_prime_pow ( by decide ) ] at this; tauto; );
    refine' ⟨ r, hr, Or.inr ⟨ m, _, _ ⟩ ⟩;
    · apply_fun Int.natAbs at h ; simp_all +decide [ Int.natAbs_pow ];
      simpa [ ← pow_mul' ] using h;
    · exact Int.natAbs_eq_iff.mp hm

end Vanish.Foundations