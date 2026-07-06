/-
  Foundations, Layer 1 — the absolute trace `Tr : 𝔽_{2ⁿ} → 𝔽₂`.

  Integrated from `dobbertin-kasami-power.zip`.  Grounded directly in Mathlib's
  `Algebra.trace`; nothing is assumed.
-/
import Mathlib
import RequestProject.DobbertinKasami.Blueprint

open scoped BigOperators

namespace DobbertinKasami

variable {n : ℕ}

/-- **Additivity** of the absolute trace (Lidl–Niederreiter, Thm 2.23(ii)). -/
@[simp] lemma Tr_add (x y : Lfield n) : Tr n (x + y) = Tr n x + Tr n y :=
  map_add (Algebra.trace (ZMod 2) (Lfield n)) x y

/-- The trace kills `0`. -/
@[simp] lemma Tr_zero : Tr n (0 : Lfield n) = 0 :=
  map_zero (Algebra.trace (ZMod 2) (Lfield n))

/-- `𝔽₂`-homogeneity of the trace (Lidl–Niederreiter, Thm 2.23(ii)). -/
lemma Tr_smul (c : ZMod 2) (x : Lfield n) : Tr n (c • x) = c • Tr n x :=
  map_smul (Algebra.trace (ZMod 2) (Lfield n)) c x

/-- **Trace of one** equals the degree of the extension reduced mod 2,
`Tr(1) = n (mod 2)` (Lidl–Niederreiter, Thm 2.23; `trace(algebraMap 1) = finrank • 1`). -/
lemma Tr_one (hn : n ≠ 0) : Tr n (1 : Lfield n) = (n : ZMod 2) := by
  have := Algebra.trace_algebraMap ( R := ZMod 2 ) ( S := Lfield n ) 1; simp_all +decide [ map_one ] ;
  rw [ GaloisField.finrank ] ; aesop

/-- **Frobenius invariance** of the trace: `Tr(x²) = Tr(x)`
(Lidl–Niederreiter, Thm 2.23(iii); the trace is invariant under the Galois group,
whose generator is the Frobenius `x ↦ x²`). -/
lemma Tr_frobenius (hn : n ≠ 0) (x : Lfield n) : Tr n (x ^ 2) = Tr n x := by
  have h_trace_eq : ∀ y : Lfield n, (algebraMap (ZMod 2) (Lfield n)) (Tr n y) = ∑ i ∈ Finset.range n, y ^ (2 ^ i) := by
    convert FiniteField.algebraMap_trace_eq_sum_pow ( ZMod 2 ) ( GaloisField 2 n ) using 1;
    rw [ GaloisField.finrank ] ; aesop;
    assumption;
  have h_frobenius : x ^ (2 ^ n) = x := by
    have h_frobenius : ∀ x : Lfield n, x ^ (Nat.card (Lfield n)) = x := by
      haveI := Fintype.ofFinite ( Lfield n ) ; simp +decide [ FiniteField.pow_card ] ;
    convert h_frobenius x using 1 ; rw [ GaloisField.card ] ; aesop;
  have h_sum_eq : ∑ i ∈ Finset.range n, (x ^ 2) ^ (2 ^ i) = ∑ i ∈ Finset.range n, x ^ (2 ^ (i + 1)) := by
    exact Finset.sum_congr rfl fun _ _ => by ring;
  have h_sum_eq : ∑ i ∈ Finset.range n, x ^ (2 ^ (i + 1)) = ∑ i ∈ Finset.range (n + 1), x ^ (2 ^ i) - x ^ (2 ^ 0) := by
    simp +decide [ Finset.sum_range_succ' ];
  simp_all +decide [ Finset.sum_range_succ ];
  exact ( algebraMap ( ZMod 2 ) ( Lfield n ) ).injective <| by aesop;

/-- **Surjectivity** of the absolute trace onto `𝔽₂`
(Lidl–Niederreiter, Thm 2.23(i)). -/
lemma Tr_surjective : Function.Surjective (Tr n) := by
  convert Algebra.trace_surjective ( ZMod 2 ) ( GaloisField 2 n )

end DobbertinKasami
