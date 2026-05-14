import Mathlib
import ABTopos.CodingTheory.BinaryCode
import ABTopos.Spectral.WalshGauss

/-!
# Spectral-Dual Bridge — Isomorphic Context Transfer

Bridges the remaining `sorry` infrastructure in `WalshGauss.lean` to
**Mathlib** via three isomorphic paths:

  Ⅰ. **Coding Duality Transfer** — Walsh spectrum ↔ weight distribution
  Ⅱ. **Fourier Character Norm**  — Parseval + `AddChar` from Mathlib
  Ⅲ. **Combinatorial Reduction** — APN ↔ |Δ_f| via double-counting

Each section follows the *one concept, one lemma* principle from
`REFACTORING.md`.

## Mathlib hooks
- `Mathlib.NumberTheory.GaussSum`        → `gaussSum_mul_gaussSum_eq_card`
- `Mathlib.Algebra.Group.AddChar`        → `AddChar.sum_eq_zero_of_ne_one`
- `Mathlib.FieldTheory.Finite.Basic`     → `FiniteField.card`
- `Mathlib.Analysis.Fourier.*`           → character norms

## Namespace
All definitions live in `ABTopos.SpectralDualBridge` to maintain the
modular hierarchy.
-/

open Finset BigOperators

noncomputable section

namespace ABTopos.SpectralDualBridge

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

-- ════════════════════════════════════════════════════════════════
-- Ⅰ.  THE CODING DUALITY TRANSFER
-- ════════════════════════════════════════════════════════════════

/-! ### §1  Additive characters as Mathlib `AddChar`

Map the hand-rolled `χ_` from `WalshGauss.lean` into Mathlib's
`AddChar` framework so we can invoke `gaussSum_mul_gaussSum_eq_card`.
-/

/-- Canonical additive character of 𝔽₂ⁿ as a Mathlib `AddChar`.
    ψ(x) := (−1)^{Tr(x)} ∈ ℂˣ. -/
def ψ₀ : AddChar 𝔽 ℂ where
  toFun := χ_ 𝔽
  map_zero_eq_one' := by
    unfold χ_
    simp [map_zero]
  map_add_eq_mul' := χ_add 𝔽

/-- The Mathlib additive character agrees with the hand-rolled `χ_`. -/
lemma ψ₀_eq_χ (x : 𝔽) : ψ₀ 𝔽 x = χ_ 𝔽 x := rfl

/-! ### §2  Code associated to a power function

Given `f(x) = x^d`, define the *graph code*
  C_f := { (a, f(x+a) − f(x)) | x, a ∈ 𝔽 }
whose weight distribution encodes the Walsh spectrum.
-/

/-- The **differential code** of a power function: the image of the
    map  x ↦ (Tr(ux), Tr(ux^d))  for all x, encoded as GF(2)-vectors.
    This is the dual of the code whose weight enumerator gives the
    Walsh spectrum via MacWilliams. -/
def differentialCodeword (d : ℕ) (u : 𝔽) (x : 𝔽) : Fin 2 → ZMod 2 :=
  ![AbsTrace 𝔽 (u * x), AbsTrace 𝔽 (x ^ d)]

/-! ### §3  Weight distribution ↔ Walsh spectrum

The Walsh coefficient Ŵ(u) counts the number of x with
Tr(ux + x^d) = 0 minus those with Tr(ux + x^d) = 1.

  Ŵ(u) = #{Tr = 0} − #{Tr = 1} = 2·#{Tr = 0} − |𝔽|

This is exactly the MacWilliams-type identity relating the
weight distribution of C_f⊥ to the Walsh transform of f.
-/

/-- Number of `x` where the trace `Tr(ux + x^d)` equals zero. -/
def traceZeroCount (d : ℕ) (u : 𝔽) : ℕ :=
  (univ.filter (fun x : 𝔽 => AbsTrace 𝔽 (u * x + x ^ d) = 0)).card

/-
**Dual weight iso (direction 1):** Walsh coefficient from trace count.
    Ŵ(u) = 2 · #{Tr(ux + x^d) = 0} − |𝔽|

    This is the isomorphism `walsh_spec(f) ≅ weight_dist(C_f⊥)`:
    the Walsh coefficient at `u` is determined by the weight-0
    count of the u-th fibre of the dual code.
-/
lemma dual_weight_iso (d : ℕ) (u : 𝔽) :
    Ŵ 𝔽 d u = 2 * (traceZeroCount 𝔽 d u : ℂ) - (Fintype.card 𝔽 : ℂ) := by
  unfold Ŵ;
  unfold χ_;
  -- Split the sum into two parts: one where the trace is zero and one where it is not.
  have h_split_sum : ∑ x : 𝔽, (-1 : ℂ) ^ (AbsTrace 𝔽 (u * x + x ^ d)).val = ∑ x ∈ Finset.univ.filter (fun x => AbsTrace 𝔽 (u * x + x ^ d) = 0), 1 + ∑ x ∈ Finset.univ.filter (fun x => AbsTrace 𝔽 (u * x + x ^ d) ≠ 0), (-1 : ℂ) := by
    rw [ Finset.sum_filter, Finset.sum_filter ];
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x _ => by rcases h : AbsTrace 𝔽 ( u * x + x ^ d ) with ( _ | _ | n ) <;> simp_all +decide ; tauto;
  simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
  rw [ Nat.cast_sub ] <;> norm_num [ traceZeroCount ] ; ring;
  exact Finset.card_le_univ _

/-! ### §4  Sub-lemmas for `ab_spectral_collapse`

Break the monolithic collapse into three atomic steps:
  (a) `iso_to_code`          — map Walsh to code weight
  (b) `apply_pless_identity` — Pless power-moment on 3-weight code
  (c) `map_back_to_walsh`    — solve back for Ŵ values
-/

/-
**(a) iso_to_code**: If the Walsh spectrum is 3-valued
    {0, +C, −C}, the associated code is a 3-weight code
    with weights in {0, (q−C)/2, (q+C)/2, q}.
-/
lemma iso_to_code (d : ℕ) (C : ℝ) (hC : C > 0)
    (hSpec : ∀ u : 𝔽, ‖Ŵ 𝔽 d u‖ = 0 ∨ ‖Ŵ 𝔽 d u‖ = C) :
    ∀ u : 𝔽,
      traceZeroCount 𝔽 d u = Fintype.card 𝔽 / 2 ∨
      traceZeroCount 𝔽 d u = (Fintype.card 𝔽 + Nat.floor C) / 2 ∨
      traceZeroCount 𝔽 d u = (Fintype.card 𝔽 - Nat.floor C) / 2 := by
  intro u
  have h_case : ‖Ŵ 𝔽 d u‖ = 0 ∨ ‖Ŵ 𝔽 d u‖ = C := hSpec u
  cases' h_case with h_zero h_C;
  · have h_trace_zero : 2 * (traceZeroCount 𝔽 d u : ℂ) - (Fintype.card 𝔽 : ℂ) = 0 := by
      rw [ ← dual_weight_iso ] ; aesop;
    norm_cast at h_trace_zero;
    exact Or.inl ( by rw [ Int.subNatNat_eq_coe ] at h_trace_zero; omega );
  · -- Since ‖Ŵ 𝔽 d u‖ = C, we have |2 * traceZeroCount 𝔽 d u - Fintype.card 𝔽| = C.
    have h_abs : |(2 * traceZeroCount 𝔽 d u - Fintype.card 𝔽 : ℝ)| = C := by
      convert h_C using 1;
      rw [ dual_weight_iso ];
      norm_cast;
    cases abs_cases ( 2 * ( traceZeroCount 𝔽 d u : ℝ ) - Fintype.card 𝔽 ) <;> simp_all +decide [ Nat.floor_eq_iff ];
    · norm_num [ show ⌊C⌋₊ = 2 * traceZeroCount 𝔽 d u - Fintype.card 𝔽 from Nat.floor_eq_iff ( by positivity ) |>.2 ⟨ by rw [ Nat.cast_sub ( show Fintype.card 𝔽 ≤ 2 * traceZeroCount 𝔽 d u from by exact_mod_cast ( by linarith : ( Fintype.card 𝔽 : ℝ ) ≤ 2 * traceZeroCount 𝔽 d u ) ) ] ; push_cast; linarith, by rw [ Nat.cast_sub ( show Fintype.card 𝔽 ≤ 2 * traceZeroCount 𝔽 d u from by exact_mod_cast ( by linarith : ( Fintype.card 𝔽 : ℝ ) ≤ 2 * traceZeroCount 𝔽 d u ) ) ] ; push_cast; linarith ⟩ ];
      exact Or.inr <| Or.inl <| Eq.symm <| Nat.div_eq_of_eq_mul_left zero_lt_two <| by linarith [ Nat.sub_add_cancel <| show Fintype.card 𝔽 ≤ 2 * traceZeroCount 𝔽 d u from by exact_mod_cast ( by linarith : ( Fintype.card 𝔽 : ℝ ) ≤ 2 * traceZeroCount 𝔽 d u ) ] ;
    · refine' Or.inr ( Or.inr _ );
      rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
      rw [ Nat.sub_eq_of_eq_add ];
      exact Eq.symm ( Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.floor_le hC.le ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.lt_floor_add_one C ] } ) )

/-- **(b) apply_pless_identity**: The second Pless power moment
    for a code of length n and size |C| satisfies
    P₂(C) = |C| · n (character-sum orthogonality).
    This is a finite-field Parseval identity. -/
lemma apply_pless_identity (d : ℕ) :
    ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2 :=
  walsh_parseval 𝔽 d

/-- **(c) map_back_to_walsh**: Given the Parseval sum and the
    fourth-moment bound, recover the spectral constant C.
    If M₂ = q² and M₄ ≤ 2q³, then C = √(2q). -/
lemma map_back_to_walsh (d : ℕ) (q : ℝ) (hq : q = (Fintype.card 𝔽 : ℝ))
    (hM₂ : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = q ^ 2)
    (hM₄ : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 4 ≤ 2 * q ^ 3)
    (hFlat : ∃ C : ℝ, C ≥ 0 ∧ ∀ u : 𝔽, ‖Ŵ 𝔽 d u‖ = 0 ∨ ‖Ŵ 𝔽 d u‖ = C) :
    ∃ C : ℝ, C ≥ 0 ∧ C ^ 2 = 2 * q ∧
      ∀ u : 𝔽, ‖Ŵ 𝔽 d u‖ = 0 ∨ ‖Ŵ 𝔽 d u‖ = C := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- Ⅱ.  THE FOURIER CHARACTER NORM
-- ════════════════════════════════════════════════════════════════

/-! ### §5  Parseval via Mathlib `AddChar`

Use `AddChar.sum_eq_zero_of_ne_one` and the Mathlib Gauss-sum
machinery to give a clean proof of Parseval's identity for the
Walsh transform.
-/

/-- Shifted additive character: ψ_u(x) := ψ₀(ux). -/
def ψ_shift (u : 𝔽) : AddChar 𝔽 ℂ where
  toFun := fun x => ψ₀ 𝔽 (u * x)
  map_zero_eq_one' := by simp [mul_zero]
  map_add_eq_mul' := fun a b => by
    simp only [mul_add]
    exact (ψ₀ 𝔽).map_add_eq_mul' (u * a) (u * b)

/-
Orthogonality of shifted characters from Mathlib:
    ∑_x ψ_u(x) = |𝔽| if u = 0, else 0.

    This replaces the hand-rolled `χ_orthogonality` with a proof
    routed through `AddChar.sum_eq_zero_of_ne_one`.
-/
lemma ψ_shift_orthogonality (u : 𝔽) :
    ∑ x : 𝔽, ψ_shift 𝔽 u x =
      if u = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
  have h_add_char_nontrivial : ∀ (ψ : AddChar 𝔽 ℂ), ψ ≠ 1 → ∑ x : 𝔽, ψ x = 0 := by
    intro ψ hψ
    by_contra h_nonzero;
    -- Since ψ is not the trivial character, there exists some y ∈ 𝔽 such that ψ(y) ≠ 1.
    obtain ⟨y, hy⟩ : ∃ y : 𝔽, ψ y ≠ 1 := by
      exact not_forall.mp fun h => hψ <| by ext; simp +decide [ h ] ;
    have h_sum_shift : ∑ x : 𝔽, ψ (x + y) = ∑ x : 𝔽, ψ x := by
      exact Equiv.sum_comp ( Equiv.addRight y ) _;
    have h_sum_shift : ∑ x : 𝔽, ψ (x + y) = ∑ x : 𝔽, ψ x * ψ y := by
      exact Finset.sum_congr rfl fun x _ => by rw [ AddChar.map_add_eq_mul ] ;
    rw [ ← Finset.sum_mul _ _ _ ] at h_sum_shift ; simp_all +decide [ mul_comm ];
  split_ifs with hu;
  · simp +decide [ hu, ψ_shift ];
  · have h_nontrivial : ∃ v : 𝔽, ψ₀ 𝔽 v ≠ 1 := by
      by_contra! h;
      have := χ_orthogonality 𝔽 1; simp_all +decide ;
      unfold ψ₀ at h; simp_all +decide [ χ_ ] ;
    obtain ⟨ v, hv ⟩ := h_nontrivial;
    have h_nontrivial : ∑ x : 𝔽, ψ₀ 𝔽 (u * x) = ∑ x : 𝔽, ψ₀ 𝔽 x := by
      exact Equiv.sum_comp ( Equiv.mulLeft₀ u hu ) fun x => ψ₀ 𝔽 x;
    exact h_nontrivial.trans ( h_add_char_nontrivial _ fun h => hv <| by simpa using congr_arg ( fun f => f v ) h )

/-- **walsh_l2_norm (Parseval):**  ‖𝒲_f‖₂² = 2^{2n}.

    The L²-norm of the Walsh transform equals |𝔽|².
    Proof: expand ‖Ŵ(u)‖² = Ŵ(u)·conj(Ŵ(u)), exchange sums,
    apply `ψ_shift_orthogonality`.

    This is the Fourier-analytic engine behind `cauchy_schwarz_rigidity`:
    it shows that the total spectral energy is fixed, so if the
    spectrum is flat, the level is determined. -/
theorem walsh_l2_norm (d : ℕ) :
    ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2 :=
  walsh_parseval 𝔽 d

/-! ### §6  Gauss norm via Mathlib

Use `gaussSum_mul_gaussSum_eq_card` to prove the Stickelberger
norm identity ‖𝔤(ψ)‖² = q. -/

/-- The Mathlib Gauss sum agrees with the hand-rolled `𝔤`
    up to the splitting of the sum over 𝔽 vs 𝔽ˣ. -/
lemma gauss_sum_eq_mathlib (χ : MulChar 𝔽 ℂ) :
    gaussSum χ (ψ₀ 𝔽) = ∑ x : 𝔽, (χ x : ℂ) * ψ₀ 𝔽 x := by
  rfl

/-- **Stickelberger via Mathlib**: ‖gaussSum χ ψ₀‖² = |𝔽|
    for non-trivial χ, assuming ψ₀ is primitive.

    This is a direct application of `gaussSum_mul_gaussSum_eq_card`. -/
lemma stickelberger_via_mathlib (χ : MulChar 𝔽 ℂ) (hχ : χ ≠ 1)
    (hψ : (ψ₀ 𝔽).IsPrimitive) :
    gaussSum χ (ψ₀ 𝔽) * gaussSum χ⁻¹ (ψ₀ 𝔽)⁻¹ = (Fintype.card 𝔽 : ℂ) :=
  gaussSum_mul_gaussSum_eq_card hχ hψ

-- ════════════════════════════════════════════════════════════════
-- Ⅲ.  COMBINATORIAL REDUCTION OF THE TRIPLE-COUNT
-- ════════════════════════════════════════════════════════════════

/-! ### §7  Differential set Δ_f and APN

Reduce the Kasami APN triple-count to a cardinality argument on
the differential set Δ_f = { D_a(f)(x) | x ∈ 𝔽, a ≠ 0 }.
-/

/-- The **full differential set** of a power function x ↦ x^d:
    Δ_f := ⋃_{a ≠ 0} { (x+a)^d + x^d | x ∈ 𝔽 }. -/
def DeltaFull (d : ℕ) : Finset (𝔽 × 𝔽) :=
  (univ.filter (fun a : 𝔽 => a ≠ 0) ×ˢ univ).image
    (fun p : 𝔽 × 𝔽 => (p.1, (p.2 + p.1) ^ d + p.2 ^ d))

/-
**Sublemma: apn_card_delta (→ direction)**:
    If f is APN, then |Δ_f| = (2^n − 1) · 2^{n−1}.

    Proof: For each a ≠ 0 (there are 2^n − 1 such a), the APN
    property means each equation D_a(f)(x) = b has 0 or 2 solutions.
    Since ∑_b |fib_b| = |𝔽| = 2^n and each |fib_b| ∈ {0, 2},
    we get |Im(D_a)| = 2^n / 2 = 2^{n−1}.  Summing over a:
      |Δ_f| = (2^n − 1) · 2^{n−1}

    This connects to `Mathlib.Data.Fintype.Card` via `Finset.card_image`.
-/
lemma apn_card_delta_forward (d n : ℕ) (hn : 3 ≤ n)
    (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hAPN : IsAPN 𝔽 d) :
    (DeltaFull 𝔽 d).card = (2 ^ n - 1) * 2 ^ (n - 1) := by
  -- By definition of $DeltaFull$, we know that for each nonzero $a$, the image of $D_a(f)$ has size $2^{n-1}$.
  have h_delta_size : ∀ a : 𝔽, a ≠ 0 → (Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) (Finset.univ : Finset 𝔽)).card = 2 ^ (n - 1) := by
    intro a ha
    have h_fiber : ∀ b : 𝔽, (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) (Finset.univ : Finset 𝔽)).card ≤ 2 := by
      exact fun b => hAPN a b ha;
    have h_fiber_sum : ∑ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) (Finset.univ : Finset 𝔽), (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) (Finset.univ : Finset 𝔽)).card = 2 ^ n := by
      rw [ ← hcard, ← Finset.card_biUnion ];
      · convert Finset.card_univ ; ext x ; aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    have h_fiber_sum : ∑ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) (Finset.univ : Finset 𝔽), (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) (Finset.univ : Finset 𝔽)).card ≤ 2 * (Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) (Finset.univ : Finset 𝔽)).card := by
      simpa [ mul_comm ] using Finset.sum_le_sum fun x ( hx : x ∈ Finset.image ( fun x : 𝔽 => ( x + a ) ^ d + x ^ d ) Finset.univ ) => h_fiber x;
    have h_fiber_sum : ∀ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) (Finset.univ : Finset 𝔽), (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) (Finset.univ : Finset 𝔽)).card ≥ 2 := by
      intro b hb
      obtain ⟨x, hx⟩ : ∃ x : 𝔽, (x + a) ^ d + x ^ d = b := by
        aesop;
      refine' Finset.one_lt_card.mpr ⟨ x, _, x + a, _, _ ⟩ <;> simp_all +decide [ add_comm a ];
      rw [ ← hx ] ; ring;
      rw [ show a * 2 = 0 by rw [ mul_two, CharTwo.add_self_eq_zero ] ] ; ring;
    have := Finset.sum_le_sum h_fiber_sum; simp_all +decide [ pow_succ' ] ;
    cases n <;> simp_all +decide [ pow_succ' ] ; linarith;
  convert Finset.sum_congr rfl fun a ha => h_delta_size a <| Finset.mem_filter.mp ha |>.2 using 1;
  any_goals exact Finset.univ;
  · rw [ show DeltaFull 𝔽 d = Finset.biUnion ( Finset.filter ( fun a => a ≠ 0 ) Finset.univ ) ( fun a => Finset.image ( fun x => ( a, ( x + a ) ^ d + x ^ d ) ) Finset.univ ) from ?_, Finset.card_biUnion ];
    · refine' Finset.sum_congr rfl fun a ha => _;
      refine' Finset.card_bij ( fun x hx => x.2 ) _ _ _ <;> simp +decide;
    · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by aesop;
    · ext ⟨a, b⟩; simp [DeltaFull];
  · simp +decide [ Finset.filter_ne', Finset.card_univ, hcard ]

/-
**Sublemma: apn_card_delta (← direction)**:
    If |Δ_f| = (2^n − 1) · 2^{n−1}, then f is APN.

    Proof (contrapositive): if some D_a has a fibre of size ≥ 4,
    then |Im(D_a)| < 2^{n−1}, so |Δ_f| < (2^n − 1) · 2^{n−1}.
-/
lemma apn_card_delta_backward (d n : ℕ) (hn : 3 ≤ n)
    (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hDelta : (DeltaFull 𝔽 d).card = (2 ^ n - 1) * 2 ^ (n - 1)) :
    IsAPN 𝔽 d := by
  -- Since this sublemma is a harder direction of the equivalence and the proof is more involved, we will use it as a black box result.
  by_contra h_contra;
  -- By definition of $DeltaFull$, we know that
  have hDeltaFull_card : ∑ a ∈ Finset.univ.filter (fun a : 𝔽 => a ≠ 0), (Finset.univ.image (fun x : 𝔽 => (x + a) ^ d + x ^ d)).card < (2 ^ n - 1) * 2 ^ (n - 1) := by
    -- Since there exists $a \neq 0$ such that $|D_a^{-1}(b)| \geq 4$ for some $b$, we have $|Im(D_a)| \leq 2^{n-1} - 1$.
    obtain ⟨a, ha_ne_zero, b, hb⟩ : ∃ a : 𝔽, a ≠ 0 ∧ ∃ b : 𝔽, (Finset.univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b)).card ≥ 4 := by
      contrapose! h_contra; simp_all +decide [ IsAPN ] ;
      intro a b ha
      have h_card : (Finset.univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b)).card % 2 = 0 := by
        have h_card : ∀ x : 𝔽, (x + a) ^ d + x ^ d = b → (x + a) ∈ Finset.univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b) := by
          simp +contextual [ add_comm a ];
          intro x hx; rw [ ← hx ] ; ring;
          rw [ show a * 2 = 0 by rw [ mul_two, CharTwo.add_self_eq_zero ] ] ; ring;
        have h_card : ∃ S : Finset (Finset 𝔽), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) ∧ Finset.univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b) = Finset.biUnion S id := by
          refine' ⟨ Finset.image ( fun x => { x, x + a } ) ( Finset.univ.filter ( fun x => ( x + a ) ^ d + x ^ d = b ) ), _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
          · grind +splitImp;
          · ext x; simp [Finset.mem_biUnion, Finset.mem_image];
            grind;
        obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_card; rw [ hS₃, Finset.card_biUnion ] <;> aesop;
      exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( Nat.le_of_lt_succ ( h_contra a ha b ) ) ( by aesop_cat ) );
    have h_card_image : (Finset.univ.image (fun x : 𝔽 => (x + a) ^ d + x ^ d)).card ≤ (Fintype.card 𝔽 - 4) / 2 + 1 := by
      have h_card_image : ∑ b' ∈ Finset.univ.image (fun x : 𝔽 => (x + a) ^ d + x ^ d), (Finset.univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b')).card = Fintype.card 𝔽 := by
        rw [ ← Finset.card_biUnion ];
        · convert Finset.card_univ using 2 ; ext x ; aesop;
        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
      have h_card_image : ∑ b' ∈ Finset.univ.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) \ {b}, (Finset.univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b')).card ≥ 2 * ((Finset.univ.image (fun x : 𝔽 => (x + a) ^ d + x ^ d)).card - 1) := by
        have h_card_image : ∀ b' ∈ Finset.univ.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) \ {b}, (Finset.univ.filter (fun x : 𝔽 => (x + a) ^ d + x ^ d = b')).card ≥ 2 := by
          intro b' hb'
          obtain ⟨x, hx⟩ : ∃ x : 𝔽, (x + a) ^ d + x ^ d = b' := by
            grind +splitIndPred;
          refine' Finset.one_lt_card.mpr ⟨ x, _, x + a, _, _ ⟩ <;> simp_all +decide [ add_comm a ];
          simp_all +decide [ add_assoc, CharTwo.add_self_eq_zero ];
          rw [ add_comm, hx ];
        refine' le_trans _ ( Finset.sum_le_sum h_card_image );
        simp +decide [ mul_comm, Finset.card_sdiff ];
        grind;
      rw [ Finset.sum_eq_add_sum_diff_singleton ( show b ∈ image ( fun x : 𝔽 => ( x + a ) ^ d + x ^ d ) univ from by
                                                    exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt hb ) ) fun x hx => Finset.mem_image.mpr ⟨ x, Finset.mem_univ _, by simpa using hx ⟩ ) ] at *;
      omega;
    refine' lt_of_lt_of_le ( Finset.sum_lt_sum _ _ ) _;
    use fun _ => 2 ^ ( n - 1 );
    · intro i hi
      have h_card_image_i : (Finset.univ.image (fun x : 𝔽 => (x + i) ^ d + x ^ d)).card ≤ (Fintype.card 𝔽) / 2 := by
        have h_card_image_i : ∀ b : 𝔽, (Finset.univ.filter (fun x : 𝔽 => (x + i) ^ d + x ^ d = b)).card ≥ 2 * (if b ∈ Finset.univ.image (fun x : 𝔽 => (x + i) ^ d + x ^ d) then 1 else 0) := by
          intro b
          by_cases hb : b ∈ Finset.univ.image (fun x : 𝔽 => (x + i) ^ d + x ^ d);
          · obtain ⟨ x, hx ⟩ := Finset.mem_image.mp hb;
            refine' le_trans _ ( Finset.card_mono <| show { x, x + i } ⊆ Finset.filter ( fun y => ( y + i ) ^ d + y ^ d = b ) Finset.univ from _ ) <;> simp_all +decide [ Finset.subset_iff ];
            simp_all +decide [ add_assoc, CharTwo.add_self_eq_zero ];
            rw [ add_comm, hx ];
          · simp [hb];
        have h_card_image_i : ∑ b ∈ Finset.univ.image (fun x : 𝔽 => (x + i) ^ d + x ^ d), (Finset.univ.filter (fun x : 𝔽 => (x + i) ^ d + x ^ d = b)).card = Fintype.card 𝔽 := by
          rw [ Finset.sum_image' ];
          rotate_left;
          use fun _ => 1;
          · simp +decide [ Finset.sum_filter ];
          · simp +decide;
        have h_card_image_i : ∑ b ∈ Finset.univ.image (fun x : 𝔽 => (x + i) ^ d + x ^ d), (Finset.univ.filter (fun x : 𝔽 => (x + i) ^ d + x ^ d = b)).card ≥ 2 * (Finset.univ.image (fun x : 𝔽 => (x + i) ^ d + x ^ d)).card := by
          refine' le_trans _ ( Finset.sum_le_sum fun x hx => ‹∀ b : 𝔽, #{x | ( x + i ) ^ d + x ^ d = b} ≥ 2 * if b ∈ image ( fun x => ( x + i ) ^ d + x ^ d ) univ then 1 else 0› x ) ; simp +decide [ Finset.sum_ite ];
          rw [ mul_comm, Finset.filter_true_of_mem ] ; aesop;
        grind;
      cases n <;> simp_all +decide [ pow_succ' ];
    · refine' ⟨ a, _, _ ⟩ <;> simp_all +decide [ pow_succ' ];
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
      grind +splitImp;
    · simp +decide [ Finset.filter_ne', Finset.card_univ, hcard ];
  contrapose! hDeltaFull_card;
  refine' hDelta ▸ _;
  have hDeltaFull_card : DeltaFull 𝔽 d ⊆ Finset.biUnion (Finset.univ.filter (fun a : 𝔽 => a ≠ 0)) (fun a => Finset.image (fun b => (a, b)) (Finset.univ.image (fun x : 𝔽 => (x + a) ^ d + x ^ d))) := by
    simp +decide [ Finset.subset_iff, DeltaFull ];
  exact le_trans ( Finset.card_le_card hDeltaFull_card ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun x hx => Finset.card_image_le ) )

/-- **apn_card_delta**: APN ↔ |Δ_f| = 2^{n−1}(2^n − 1).

    The main iff connecting the APN property to a cardinality
    statement on the differential set. This sidesteps the
    triple-count complexity by reducing to double-counting on the
    bipartite graph of (x, D_a(f)(x)). -/
theorem apn_card_delta (d n : ℕ) (hn : 3 ≤ n)
    (hcard : Fintype.card 𝔽 = 2 ^ n) :
    IsAPN 𝔽 d ↔ (DeltaFull 𝔽 d).card = (2 ^ n - 1) * 2 ^ (n - 1) :=
  ⟨apn_card_delta_forward 𝔽 d n hn hcard,
   apn_card_delta_backward 𝔽 d n hn hcard⟩

/-! ### §8  Delta cardinality from the Walsh spectrum

Connect |Δ| to the Walsh L²-norm via the Fourier inversion formula:
  |Δ| = (1/|𝔽|) ∑_u |Ŵ(u)|²

This links the APN cardinality criterion to the Parseval identity. -/

/-- |Δ(d)| via Fourier inversion:
    |Δ| = (1/q) ∑_u Ŵ(u)² (real part, summed over all u).

    The connection to `walsh_l2_norm` then yields |Δ| = q for the
    full image, or q/2 per nonzero a. -/
lemma delta_card_via_parseval (d : ℕ) :
    ((Delta 𝔽 d).card : ℝ) =
      (1 / (Fintype.card 𝔽 : ℝ)) *
        ∑ u : 𝔽, (Ŵ 𝔽 d u * starRingEnd ℂ (Ŵ 𝔽 d u)).re := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- §9  AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════

#print axioms walsh_l2_norm
#print axioms apn_card_delta
#print axioms stickelberger_via_mathlib

end ABTopos.SpectralDualBridge

end