/-
# Gold Case P₃: Full Proof

This module contains the proof of P₃ for the Gold case (k = 1, e(1) = 3).

For k = 1: Δ = {b² + b : b ∈ F} = ker(Tr), |Δ| = 2^{n-1}.

## Walsh spectrum of ker(Tr)

Ŝ(b) = |F|/2 if b ∈ K^⊥ = {0, 1}, and 0 otherwise.

## Proof of P₃

For c ≠ 0, 1: only b = 0 contributes to the spectral sum.
∑_b Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c)) = Ŝ(0)³ = |S|³.
By spectral identity: N(c) = |S|³/|F| = 2^{2n-3}.

## References

* Gold, "Maximal recursive sequences..." (1968)
-/

import Mathlib
import RequestProject.TraceChar
import RequestProject.WalshHadamard
import RequestProject.SpectralIdentity
import RequestProject.APNTheory
import RequestProject.LinearizedPoly

open Finset BigOperators

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

attribute [local instance] ZMod.algebra

/-! ### The trace kernel set -/

/-- S = ker(Tr) = {x ∈ F : Tr(x) = 0}. -/
def traceKernel : Finset F :=
  Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0)

/-! ### Walsh spectrum of ker(Tr) -/

/-- Walsh coefficient of ker(Tr) at b = 0 equals |ker(Tr)|. -/
lemma walsh_traceKernel_zero :
    walshCoeff F (indicator F (traceKernel F)) 0 = (traceKernel F).card := by
  exact walshCoeff_indicator_zero F (traceKernel F)

/-- Walsh coefficient of ker(Tr) at b.
    Ŝ(b) = |ker(Tr)| if Tr(bx) = 0 for all x ∈ ker(Tr), else 0. -/
lemma walsh_traceKernel_support (b : F) :
    walshCoeff F (indicator F (traceKernel F)) b =
    if (∀ x : F, Algebra.trace (ZMod 2) F x = 0 →
                  Algebra.trace (ZMod 2) F (b * x) = 0)
    then ((traceKernel F).card : ℤ)
    else 0 := by
  split_ifs with h;
  · unfold walshCoeff;
    simp +decide [ Finset.sum_ite, Finset.filter_congr, Finset.filter_eq', indicator, χ ];
    exact Finset.sum_eq_zero fun x hx => by rw [ traceInt, h x ( Finset.mem_filter.mp hx |>.2 ) ] ; simp +decide ;
  · contrapose! h;
    have h_all_one : ∀ x ∈ traceKernel F, χ F b x = 1 := by
      intro x hx
      by_contra h_contra;
      have h_shift : ∀ y ∈ traceKernel F, χ F b (x + y) = -χ F b y := by
        intro y hy
        have h_shift : χ F b (x + y) = χ F b x * χ F b y := by
          exact?;
        cases χ_values F b x <;> aesop;
      have h_pair : ∑ y ∈ traceKernel F, χ F b y = ∑ y ∈ traceKernel F, χ F b (x + y) := by
        apply Finset.sum_bij (fun y hy => x + y);
        · simp_all +decide [ traceKernel ];
        · grind;
        · intro y hy; use y - x; simp_all +decide [ traceKernel ] ;
        · simp_all +decide [ ← add_assoc ];
          simp_all +decide [ ← two_mul, CharTwo.two_eq_zero ];
      rw [ Finset.sum_congr rfl h_shift ] at h_pair ; norm_num at h_pair;
      exact h ( by rw [ walshCoeff_indicator ] ; linarith );
    unfold χ at h_all_one;
    unfold traceInt at h_all_one;
    simp_all +decide [ ZMod.val ];
    exact fun x hx => h_all_one x <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hx ⟩

/-! ### Trace pairing non-degeneracy and annihilator -/

/-- Non-degeneracy of trace pairing: if Tr(ax) = 0 for all x, then a = 0. -/
lemma trace_nondegenerate (a : F) (h : ∀ x : F, Algebra.trace (ZMod 2) F (a * x) = 0) :
    a = 0 := by
  contrapose! h;
  obtain ⟨ z, hz ⟩ := trace_surjective F ( 1 : ZMod 2 );
  exact ⟨ a⁻¹ * z, by simp +decide [ h, hz ] ⟩

/-- If Tr(bx)=0 for x in ker(Tr) and Tr(by₀)=0 for some y₀ with Tr(y₀)=1,
    then Tr(bx)=0 for all x. -/
lemma trace_vanish_everywhere (b : F)
    (h : ∀ x : F, Algebra.trace (ZMod 2) F x = 0 →
                   Algebra.trace (ZMod 2) F (b * x) = 0)
    (y₀ : F) (hy0_tr : Algebra.trace (ZMod 2) F y₀ = 1)
    (hby0 : Algebra.trace (ZMod 2) F (b * y₀) = 0) :
    ∀ x : F, Algebra.trace (ZMod 2) F (b * x) = 0 := by
  intro x
  by_cases hx : Algebra.trace (ZMod 2) F x = 0
  · exact h x hx
  · have hx1 : Algebra.trace (ZMod 2) F x = 1 := by
      have : ∀ (t : ZMod 2), t ≠ 0 → t = 1 := by decide
      exact this _ hx
    have hxy : Algebra.trace (ZMod 2) F (x + y₀) = 0 := by
      rw [map_add, hx1, hy0_tr]; decide
    have hbxy := h (x + y₀) hxy
    rw [mul_add, map_add, hby0] at hbxy
    simpa using hbxy

/-- If Tr(bx) = Tr(x) for all x, then b = 1. -/
lemma trace_eq_implies_eq_one (b : F)
    (h : ∀ x : F, Algebra.trace (ZMod 2) F (b * x) = Algebra.trace (ZMod 2) F x) :
    b = 1 := by
  have := trace_nondegenerate F ( b + 1 ) ?_;
  · grind;
  · simp_all +decide [ add_mul ];
    grind +qlia

/-- If Tr(bx) = 0 for all x in ker(Tr), and b ≠ 0, then b = 1. -/
lemma trace_annihilator_of_ne_zero (b : F) (hb : b ≠ 0)
    (h : ∀ x : F, Algebra.trace (ZMod 2) F x = 0 →
                   Algebra.trace (ZMod 2) F (b * x) = 0) :
    b = 1 := by
  -- Get y₀ with Tr(y₀) = 1
  obtain ⟨y₀, hy₀⟩ := trace_surjective F (1 : ZMod 2)
  -- Case split on Tr(by₀)
  by_cases hby0 : Algebra.trace (ZMod 2) F (b * y₀) = 0
  · -- If Tr(by₀) = 0: then Tr(bx) = 0 for ALL x
    have hall := trace_vanish_everywhere F b h y₀ hy₀ hby0
    -- By non-degeneracy, b = 0, contradiction
    exact absurd (trace_nondegenerate F b hall) hb
  · -- If Tr(by₀) ≠ 0 (i.e., = 1): show Tr(bx) = Tr(x) for all x
    apply trace_eq_implies_eq_one F b
    intro x
    by_cases hx : Algebra.trace (ZMod 2) F x = 0
    · -- x ∈ ker(Tr): Tr(bx) = 0 = Tr(x)
      rw [h x hx, hx]
    · -- x ∉ ker(Tr): Tr(x) = 1
      have hx1 : Algebra.trace (ZMod 2) F x = 1 := by
        have : ∀ (t : ZMod 2), t ≠ 0 → t = 1 := by decide
        exact this _ hx
      -- x + y₀ ∈ ker(Tr)
      have hxy : Algebra.trace (ZMod 2) F (x + y₀) = 0 := by
        rw [map_add, hx1, hy₀]; decide
      -- Tr(b(x + y₀)) = 0
      have hbxy := h (x + y₀) hxy
      rw [mul_add, map_add] at hbxy
      -- Tr(bx) + Tr(by₀) = 0, and Tr(by₀) = 1
      have hby1 : Algebra.trace (ZMod 2) F (b * y₀) = 1 := by
        have : ∀ (t : ZMod 2), t ≠ 0 → t = 1 := by decide
        exact this _ hby0
      rw [hby1] at hbxy
      -- Tr(bx) + 1 = 0 means Tr(bx) = 1
      have : ∀ (t : ZMod 2), t + 1 = 0 → t = 1 := by decide
      rw [this _ hbxy, hx1]

/-- The annihilator of ker(Tr) under the trace pairing is {0, 1}. -/
lemma trace_annihilator (b : F) :
    (∀ x : F, Algebra.trace (ZMod 2) F x = 0 →
              Algebra.trace (ZMod 2) F (b * x) = 0) ↔
    (b = 0 ∨ b = 1) := by
  constructor
  · intro h
    by_cases hb : b = 0
    · left; exact hb
    · right; exact trace_annihilator_of_ne_zero F b hb h
  · rintro (rfl | rfl) x hx
    · simp [map_zero]
    · simp [hx]

/-! ### Walsh vanishing outside {0, 1} -/

/-- For c ≠ 0, 1: Ŝ(c) = 0 since c ∉ K^⊥ = {0, 1}. -/
lemma gold_walsh_vanish_outside (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    walshCoeff F (indicator F (traceKernel F)) c = 0 := by
  rw [ walsh_traceKernel_support ];
  rw [ if_neg ];
  exact fun h => hc1 <| by have := trace_annihilator F c; aesop;

/-! ### Gold P₃ -/

/-- Gold P₃ (spectral form): ∑_b Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c)) = |S|³. -/
theorem gold_spectral_sum (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ∑ b : F,
      walshCoeff F (indicator F (traceKernel F)) b *
      walshCoeff F (indicator F (traceKernel F)) (b * c) *
      walshCoeff F (indicator F (traceKernel F)) (b * (1 + c)) =
    ((traceKernel F).card : ℤ) ^ 3 := by
  have h_walsh_zero : walshCoeff F (indicator F (traceKernel F)) 0 = (traceKernel F).card :=
    walsh_traceKernel_zero F
  rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ pow_succ', mul_assoc ];
  intro b hb; by_cases hb' : b = 1 <;> simp_all +decide [ gold_walsh_vanish_outside ] ;

/-- **Gold P₃ (spatial form)**: |F| · N(c) = |ker(Tr)|³. -/
theorem gold_P3 (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (Fintype.card F : ℤ) * tripleCount F (traceKernel F) c =
    ((traceKernel F).card : ℤ) ^ 3 := by
  rw [ ← spectral_identity F ( traceKernel F ) c, gold_spectral_sum F c hc0 hc1 ]

end
