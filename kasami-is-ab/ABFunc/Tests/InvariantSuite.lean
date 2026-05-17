/-
  # Invariant Test Suite — Machine-Verified Stabilizing Moves

  Formal `native_decide` proofs implementing the 10 stabilizing moves.
  Each theorem is a machine-verified statement that the invariant check passes.

  ## Verified Properties
  - Parseval identity holds for all tested functions
  - APN fibres are exactly {0, 2} (not just ≤ 2)
  - Frobenius-equivalent exponents yield the same APN/AB status
  - CCZ invariants (Walsh spectrum) match for equivalent functions
  - Known classification is correct (Gold, Kasami, Welch, Inverse)
  - GF(2^7) probe for AB6 conjecture
-/
import Detect.GF2n
import Detect.APNDetector
import Detect.ABDetector
import Detect.Equivalence
import Detect.Invariants

/-! ## §1  Move 8: Parseval Identity — Machine Verified

The Walsh-Parseval identity ∑_{a, b≠0} |W(a,b)|² = (2^n - 1)·2^{2n}
is the fundamental sanity check. If this fails, the Walsh computation
is buggy. -/

/-- Parseval holds for Gold x³ on GF(2³). -/
theorem parseval_gold_gf8 : parsevalTotal 3 (powerMap 3 3) = true := by native_decide

/-- Parseval holds for Gold x³ on GF(2⁵). -/
theorem parseval_gold_gf32 : parsevalTotal 5 (powerMap 5 3) = true := by native_decide

/-- Parseval holds for Kasami x¹³ on GF(2⁵). -/
theorem parseval_kasami_gf32 : parsevalTotal 5 (powerMap 5 13) = true := by native_decide

/-- Parseval holds for Welch x⁷ on GF(2⁵). -/
theorem parseval_welch_gf32 : parsevalTotal 5 (powerMap 5 7) = true := by native_decide

/-- Parseval holds for non-APN x² on GF(2⁵) (Parseval is universal). -/
theorem parseval_frobenius_gf32 : parsevalTotal 5 (powerMap 5 2) = true := by native_decide

/-- Parseval holds for AB10 candidate x⁶ on GF(2⁵). -/
theorem parseval_ab10_gf32 : parsevalTotal 5 (powerMap 5 6) = true := by native_decide

/-! ## §2  Move 2: Exact APN Fibre Structure

For genuine APN functions in characteristic 2, fibres must be
*exactly* size 0 or 2 (never 1). This is a stronger check than ≤ 2. -/

/-- Gold x³ on GF(2³): all fibres are {0, 2}. -/
theorem fibres_gold_gf8 : verifyAPNFibres 3 (powerMap 3 3) = true := by native_decide

/-- Gold x³ on GF(2⁵): all fibres are {0, 2}. -/
theorem fibres_gold_gf32 : verifyAPNFibres 5 (powerMap 5 3) = true := by native_decide

/-- Kasami x¹³ on GF(2⁵): all fibres are {0, 2}. -/
theorem fibres_kasami_gf32 : verifyAPNFibres 5 (powerMap 5 13) = true := by native_decide

/-- Welch x⁷ on GF(2⁵): all fibres are {0, 2}. -/
theorem fibres_welch_gf32 : verifyAPNFibres 5 (powerMap 5 7) = true := by native_decide

/-- AB10 candidate x⁶ on GF(2⁵): all fibres are {0, 2}. -/
theorem fibres_ab10_gf32 : verifyAPNFibres 5 (powerMap 5 6) = true := by native_decide

/-! ## §3  Move 3: Frobenius Orbit Invariance

If d' = 2d mod (2^n - 1), then x^d and x^{d'} are EA-equivalent.
They must have identical APN and AB status. -/

/-- x³ and x⁶ are Frobenius-equivalent on GF(2⁵) (6 = 3·2 mod 31). -/
theorem frob_equiv_3_6_gf32 : isFrobeniusEquiv 5 3 6 = true := by native_decide

/-- x³ and x¹² are Frobenius-equivalent on GF(2⁵) (12 = 3·4 mod 31). -/
theorem frob_equiv_3_12_gf32 : isFrobeniusEquiv 5 3 12 = true := by native_decide

/-- x³ and x²⁴ are Frobenius-equivalent on GF(2⁵) (24 = 3·8 mod 31). -/
theorem frob_equiv_3_24_gf32 : isFrobeniusEquiv 5 3 24 = true := by native_decide

/-- Frobenius-equivalent functions have the same APN status. -/
theorem frob_apn_consistent_3_6 :
    checkAPN 5 (powerMap 5 3) = checkAPN 5 (powerMap 5 6) := by native_decide

/-- Frobenius-equivalent functions have the same AB status. -/
theorem frob_ab_consistent_3_6 :
    isAB 5 (powerMap 5 3) = isAB 5 (powerMap 5 6) := by native_decide

/-- x³ and x¹³ are NOT Frobenius-equivalent (different families). -/
theorem frob_not_equiv_3_13 : isFrobeniusEquiv 5 3 13 = false := by native_decide

/-! ## §4  Move 6: Classification Verification

Verify that known families are correctly identified. -/

/-- Gold classification: x³ on GF(2⁵). -/
theorem classify_gold : isGoldExp 5 3 = true := by native_decide

/-- Kasami classification: x¹³ on GF(2⁵). -/
theorem classify_kasami : isKasamiExp 5 13 = true := by native_decide

/-- Welch classification: x⁷ on GF(2⁵). -/
theorem classify_welch : isWelchExp 5 7 = true := by native_decide

/-- Inverse classification: x³⁰ on GF(2⁵). -/
theorem classify_inverse : isInverseExp 5 30 = true := by native_decide

/-! ## §5  Move 4: CCZ Invariant Consistency

Functions in the same CCZ class must have the same Walsh spectrum
(as a multiset of squared values). -/

/-- x³ and x⁶ (Frobenius-equivalent) have the same CCZ invariants. -/
theorem ccz_invariants_3_6 :
    sameCCZInvariants 5 (powerMap 5 3) (powerMap 5 6) = true := by native_decide

/-- x³ and x¹³ (both AB on GF(2⁵)) share the same CCZ invariants
    (differential uniformity 2, Walsh spectrum {0, 64}). -/
theorem ccz_invariants_3_13 :
    sameCCZInvariants 5 (powerMap 5 3) (powerMap 5 13) = true := by native_decide

/-- x³ (APN+AB) and x³⁰ (APN, not AB) have DIFFERENT CCZ invariants. -/
theorem ccz_invariants_3_30 :
    sameCCZInvariants 5 (powerMap 5 3) (powerMap 5 30) = false := by native_decide

/-! ## §6  Move 9: Systematic Falsification

Verify that known non-APN/non-AB functions are correctly rejected. -/

/-- x² is NOT APN on GF(2⁵). -/
theorem not_apn_x2 : checkAPN 5 (powerMap 5 2) = false := by native_decide

/-- x⁴ is NOT APN on GF(2⁵). -/
theorem not_apn_x4 : checkAPN 5 (powerMap 5 4) = false := by native_decide

/-- Inverse x³⁰ is APN but NOT AB on GF(2⁵). -/
theorem inverse_apn_not_ab :
    checkAPN 5 (powerMap 5 30) = true ∧ isAB 5 (powerMap 5 30) = false := by
  constructor <;> native_decide

/-! ## §7  Move 7: Small Field Sanity — GF(2³)

On GF(2³) there are very few APN functions.
x³ is the only APN power map (up to Frobenius). -/

/-- x³ is APN on GF(2³). -/
theorem gold_apn_gf8 : checkAPN 3 (powerMap 3 3) = true := by native_decide

/-- x³ is AB on GF(2³). -/
theorem gold_ab_gf8 : isAB 3 (powerMap 3 3) = true := by native_decide

/-- x⁵ is APN on GF(2³) (Frobenius of x³ via 5 = 3·2-1? let's check). -/
theorem x5_apn_gf8 : checkAPN 3 (powerMap 3 5) = true := by native_decide

/-- x⁵ is AB on GF(2³). -/
theorem x5_ab_gf8 : isAB 3 (powerMap 3 5) = true := by native_decide

/-- x² is NOT APN on GF(2³). -/
theorem not_apn_x2_gf8 : checkAPN 3 (powerMap 3 2) = false := by native_decide

/-! ## §8  GF(2⁷) Probe for Conjecture AB6 (Move 7 on larger field)

Conjecture AB6 claims x^{(2^j+1)(2^k+1)} is APN.
For j=1, k=2, n=7: d = 3·5 = 15.
This is the critical test that was flagged as needing verification. -/

-- Note: GF(2^7) has 128 elements. Walsh computation is O(128³) ≈ 2M ops.
-- This is feasible for native_decide but may be slow for #eval.

/-- x¹⁵ is APN on GF(2⁷). -/
theorem ab6_apn_gf128 : checkAPN 7 (powerMap 7 15) = true := by native_decide

/-- x¹⁵ has differential uniformity 2 on GF(2⁷). -/
theorem du_ab6_gf128 : differentialUniformity 7 (powerMap 7 15) = 2 := by native_decide

/-- x¹⁵ is Frobenius-equivalent to x³⁰ on GF(2⁷)? Let's check. -/
theorem frob_15_gf128 : isFrobeniusEquiv 7 15 30 = true := by native_decide

/-- x¹⁵ is NOT a Gold exponent on GF(2⁷) — it's a Double-Gold. -/
theorem classify_15_not_gold_gf128 : isGoldExp 7 15 = false := by native_decide

/-- x¹⁵ is NOT a Kasami exponent on GF(2⁷). -/
theorem classify_15_not_kasami_gf128 : isKasamiExp 7 15 = false := by native_decide

/-! ## §9  Cross-Consistency: APN ↔ Diff Uniformity -/

/-- Gold has differential uniformity exactly 2 on GF(2⁵). -/
theorem du_gold_gf32 : differentialUniformity 5 (powerMap 5 3) = 2 := by native_decide

/-- Inverse has differential uniformity exactly 2 on GF(2⁵). -/
theorem du_inverse_gf32 : differentialUniformity 5 (powerMap 5 30) = 2 := by native_decide

/-- x² has differential uniformity > 2 on GF(2⁵). -/
theorem du_x2_gf32 : differentialUniformity 5 (powerMap 5 2) > 2 := by native_decide

/-! ## §10  Master Invariant Check

A combined theorem asserting all critical invariants pass simultaneously. -/

/-- **Master Invariant Theorem for Gold x³ on GF(2⁵)**:
    Parseval ∧ APN ∧ AB ∧ exact fibres ∧ classification ∧ Frobenius consistency. -/
theorem gold_gf32_all_invariants :
    parsevalTotal 5 (powerMap 5 3) = true ∧
    checkAPN 5 (powerMap 5 3) = true ∧
    isAB 5 (powerMap 5 3) = true ∧
    verifyAPNFibres 5 (powerMap 5 3) = true ∧
    isGoldExp 5 3 = true ∧
    isFrobeniusEquiv 5 3 6 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Master Invariant Theorem for Kasami x¹³ on GF(2⁵)**. -/
theorem kasami_gf32_all_invariants :
    parsevalTotal 5 (powerMap 5 13) = true ∧
    checkAPN 5 (powerMap 5 13) = true ∧
    isAB 5 (powerMap 5 13) = true ∧
    verifyAPNFibres 5 (powerMap 5 13) = true ∧
    isKasamiExp 5 13 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Master Invariant Theorem for AB10 candidate x⁶ on GF(2⁵)**. -/
theorem ab10_gf32_all_invariants :
    parsevalTotal 5 (powerMap 5 6) = true ∧
    checkAPN 5 (powerMap 5 6) = true ∧
    isAB 5 (powerMap 5 6) = true ∧
    verifyAPNFibres 5 (powerMap 5 6) = true ∧
    differentialUniformity 5 (powerMap 5 6) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Axiom Audit -/

#print axioms parseval_gold_gf32
#print axioms fibres_gold_gf32
#print axioms frob_equiv_3_6_gf32
#print axioms frob_apn_consistent_3_6
#print axioms classify_gold
#print axioms ccz_invariants_3_6
#print axioms gold_gf32_all_invariants
#print axioms ab6_apn_gf128
