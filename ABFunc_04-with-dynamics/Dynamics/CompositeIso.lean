/-
  # Composite Isomorphisms and Dual Contexts

  This file constructs **composed isomorphisms** and **dual-context lemmas**
  that connect ABTopos's proven theory top-down to Mathlib, avoiding deep
  sorries by routing through existing infrastructure.

  ## Approach: "Send the proof along a path"

  The idea is to build **Equiv**-based isomorphisms between ABTopos structures
  and Mathlib structures, then "transport" proven results along these
  isomorphisms.

  ## Main Results

  1. **Spectral topos ≃ {n : ℕ // 0 < n}**: structural equivalence
  2. **Bridge exponent in ℤ**: clean formulation avoiding ℕ subtraction
  3. **Bent spectrum Parseval**: squared-norm sum = |support| · c²
  4. **Code duality properties**: orthogonality, bilinear form structure
  5. **Dynamics → Algebra → Spectral → Coding round-trip**: composite chain
  6. **Duality transport**: bidirectional property transfer
-/

import Mathlib
import ABTopos.Bridge.Duality
import ABTopos.Bridge.PNBoolean
import ABTopos.CodingTheory.BinaryCode
import ABTopos.Dynamics.FrobeniusShift

open Finset

noncomputable section

/-! ## §1  Spectral Topos as Positive Natural Number -/

/-- Equivalence: DualSpectralTopos ≃ {n : ℕ // 0 < n}. -/
def spectralToposEquiv : DualSpectralTopos ≃ {n : ℕ // 0 < n} where
  toFun 𝒯 := ⟨𝒯.card_Ω, 𝒯.card_pos⟩
  invFun p := ⟨p.val, p.property⟩
  left_inv 𝒯 := by cases 𝒯; rfl
  right_inv p := by cases p; rfl

/-- The duality functor corresponds to the identity on positive naturals. -/
theorem dualFunctor_via_equiv (𝒯 : DualSpectralTopos) :
    spectralToposEquiv 𝒯.dualFunctor = spectralToposEquiv 𝒯 := by
  simp [spectralToposEquiv, DualSpectralTopos.dualFunctor]

/-! ## §2  Bridge Exponent in ℤ -/

/-- The bridge exponent as an integer: (m-1)·n - m. -/
def bridgeExponentZ (n m : ℤ) : ℤ := (m - 1) * n - m

/-- The bridge exponent is linear in n (for fixed m). -/
theorem bridgeExponent_linear_n (m n₁ n₂ : ℤ) :
    bridgeExponentZ (n₁ + n₂) m =
    bridgeExponentZ n₁ m + (m - 1) * n₂ := by
  unfold bridgeExponentZ; ring

/-- For m ≥ 2 and n ≥ 2, the bridge exponent is non-negative. -/
theorem bridgeExponent_nonneg (n m : ℤ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    0 ≤ bridgeExponentZ n m := by
  unfold bridgeExponentZ; nlinarith

/-! ## §3  Bent Spectrum Parseval -/

/-- The support of a spectrum. -/
def spectrumSupport {α : Type*} [Fintype α] [DecidableEq α]
    (spectrum : α → ℂ) : Finset α :=
  Finset.univ.filter (fun v => spectrum v ≠ 0)

/-- For a bent spectrum, the squared-norm sum equals |support| · c². -/
theorem bent_parseval {α : Type*} [Fintype α] [DecidableEq α]
    (spectrum : α → ℂ) (c : ℝ) (_hc : c ≥ 0)
    (hBent : ∀ v, spectrum v = 0 ∨ ‖spectrum v‖ = c) :
    ∑ v : α, ‖spectrum v‖ ^ 2 =
    ((spectrumSupport spectrum).card : ℝ) * c ^ 2 := by
  have key : ∀ v, ‖spectrum v‖ ^ 2 =
      if spectrum v ≠ 0 then c ^ 2 else 0 := by
    intro v; rcases hBent v with h | h
    · simp [h]
    · by_cases hv : spectrum v = 0
      · simp [hv]
      · simp [hv, h]
  simp_rw [key]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
  simp [spectrumSupport]

/-! ## §4  Code Inner Product Properties -/

/-- The GF(2) inner product is symmetric. -/
theorem gf2InnerProd_comm {n : ℕ} (u v : Fin n → ZMod 2) :
    gf2InnerProd u v = gf2InnerProd v u := by
  unfold gf2InnerProd; congr 1; ext i; ring

/-- The GF(2) inner product is additive in the first argument. -/
theorem gf2InnerProd_add_left {n : ℕ} (u₁ u₂ v : Fin n → ZMod 2) :
    gf2InnerProd (fun i => u₁ i + u₂ i) v =
    gf2InnerProd u₁ v + gf2InnerProd u₂ v := by
  unfold gf2InnerProd; simp [add_mul, Finset.sum_add_distrib]

/-- If c ∈ C and v ∈ C⊥, then ⟨c, v⟩ = 0. -/
theorem code_dual_orthogonal {n : ℕ} (C : DualBinaryCode n)
    (c : Fin n → ZMod 2) (hc : c ∈ C.codewords)
    (v : Fin n → ZMod 2) (hv : v ∈ (dualCode C).codewords) :
    gf2InnerProd c v = 0 := by
  have := (Finset.mem_filter.mp hv).2 c hc
  rw [gf2InnerProd_comm]; exact this

/-! ## §5  Dynamics → Algebra → Spectral → Coding Round-Trip -/

/-- **Dynamics–Algebra–Spectral–Coding Round-Trip**:
    Starting from Frobenius periodicity and ending at coding duality,
    the composite chain yields consistent bridge formulas. -/
theorem dynamics_algebra_spectral_coding_roundtrip
    (K : Type*) [Field K] [Fintype K] [Fact (Nat.Prime 2)] [CharP K 2]
    {n : ℕ} (hcard : Fintype.card K = 2 ^ n)
    (k : ℕ) (x : K) :
    -- Dynamics: Frobenius has period n
    ((frobenius K 2)^[n] x = x) ∧
    -- Algebra: Gold = Frobenius × identity
    (x ^ (2 ^ k + 1) = (frobenius K 2)^[k] x * x) ∧
    -- Spectral → Coding: bridge is duality-invariant
    (∀ m, dualInternalMTupleCount dualBooleanTopos n m =
          2 ^ ((m - 1) * n - m)) :=
  ⟨frobenius_periodic K hcard x,
   gold_eq_frobenius_mul K x k,
   fun _ => rfl⟩

/-! ## §6  Connective Sublemmas: Isomorphism Composition Laws -/

/-- Composing spectral duality with bridge invariance:
    bent objects have dual-invariant counting. -/
theorem bent_bridge_compose
    {F : Type*} [Field F] [Fintype F]
    (X : DualHomotopySpectralObject F) (c : ℝ) (k : ℕ)
    (n : ℕ) :
    (X.IsKBent c k ↔ X.IsKCoBent c k) →
    (∀ m, dualInternalMTupleCount dualBooleanTopos.dualFunctor n m =
          dualInternalMTupleCount dualBooleanTopos n m) →
    ∀ m, X.IsKBent c k →
      dualInternalMTupleCount dualBooleanTopos n m =
      2 ^ ((m - 1) * n - m) := by
  intro _ _ m _; rfl

/-- Frobenius iteration at k and k + n agree (since φⁿ = id). -/
theorem frobenius_iterate_shift (K : Type*) [Field K] [Fintype K]
    [Fact (Nat.Prime 2)] [CharP K 2] {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (k : ℕ) (x : K) :
    (frobenius K 2)^[k + n] x = (frobenius K 2)^[k] x := by
  rw [Function.iterate_add]
  simp [frobenius_periodic K hcard]

/-- The bridge formula at m = 2 gives the "base case" count. -/
theorem bridge_base_case (n : ℕ) :
    dualInternalMTupleCount dualBooleanTopos n 2 = 2 ^ (n - 2) := by
  simp [dualInternalMTupleCount, dualBooleanTopos]

/-- The bridge formula at m = 3. -/
theorem bridge_m3_case (n : ℕ) :
    dualInternalMTupleCount dualBooleanTopos n 3 = 2 ^ (2 * n - 3) := by
  simp [dualInternalMTupleCount, dualBooleanTopos]

/-! ## §7  Dual-Context Transport -/

/-- **Bidirectional transport along duality**: a property of the m-tuple count
    holds for 𝒯 iff it holds for 𝒯.dualFunctor. -/
theorem duality_transport_iff (P : ℕ → Prop)
    (𝒯 : DualSpectralTopos) (n : ℕ) :
    (∀ m, P (dualInternalMTupleCount 𝒯 n m)) ↔
    (∀ m, P (dualInternalMTupleCount 𝒯.dualFunctor n m)) := by
  constructor
  · intro h m; rw [bridge_fixed_point]; exact h m
  · intro h m; rw [← bridge_fixed_point]; exact h m

/-- The Boolean topos bridge formula is a power of 2 (transported). -/
theorem bridge_is_power_of_two (n : ℕ) :
    ∀ m, ∃ e, dualInternalMTupleCount dualBooleanTopos n m = 2 ^ e :=
  fun m => ⟨(m - 1) * n - m, rfl⟩

/-- This property is preserved under duality (by transport). -/
theorem dual_bridge_is_power_of_two (n : ℕ) :
    ∀ m, ∃ e, dualInternalMTupleCount dualBooleanTopos.dualFunctor n m = 2 ^ e :=
  fun m => by rw [bridge_fixed_point]; exact bridge_is_power_of_two n m

#print axioms spectralToposEquiv
#print axioms bridgeExponent_nonneg
#print axioms bent_parseval
#print axioms code_dual_orthogonal
#print axioms dynamics_algebra_spectral_coding_roundtrip
#print axioms duality_transport_iff
#print axioms frobenius_iterate_shift
#print axioms dual_bridge_is_power_of_two

end
