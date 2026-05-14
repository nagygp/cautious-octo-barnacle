/-
  ABTopos/Walsh.lean — Parseval identity and Walsh spectrum properties

  The Parseval identity states:
    Σ_{a ∈ F₂ⁿ} Wf(a)² = 2^{2n}
  for any Boolean function f : F₂ⁿ → F₂.

  This is the foundational identity from which the AB/nonlinearity bounds follow.
-/
import Mathlib
import RequestProject.ABTopos.Defs

open Finset BigOperators ABTopos

namespace ABTopos

/-- Parseval's identity for the Walsh–Hadamard transform of a Boolean function:
    Σ_{a ∈ F₂ⁿ} Wf(a)² = 2^{2n}.

    Proof sketch: Expand Wf(a)² = (Σ_x (-1)^{f(x)+⟨a,x⟩})(Σ_y (-1)^{f(y)+⟨a,y⟩}),
    swap the order of summation over a, and use the orthogonality of characters:
    Σ_a (-1)^{⟨a,x⟩ + ⟨a,y⟩} = Σ_a (-1)^{⟨a,x+y⟩} = 2ⁿ · δ_{x,y}. -/
theorem parseval_walsh {n : ℕ} (f : F2Vec n → ZMod 2) :
    ∑ a : F2Vec n, (walshHadamard f a) ^ 2 = (2 : ℤ) ^ (2 * n) := by sorry

/-- Parseval's identity for the vectorial Walsh spectrum:
    Σ_{a ∈ F₂ⁿ} Wf(a,b)² = 2^{2n}  for any fixed b ≠ 0.

    This follows directly from the Boolean Parseval applied to the
    component function x ↦ ⟨b, f(x)⟩. -/
theorem parseval_walsh_vectorial {n : ℕ} (f : F2Vec n → F2Vec n)
    (b : F2Vec n) (hb : b ≠ 0) :
    ∑ a : F2Vec n, (walshSpectrum f a b) ^ 2 = (2 : ℤ) ^ (2 * n) := by
  exact parseval_walsh (fun x => innerF2 b (f x))

/-- The squared Walsh value is always nonneg. -/
lemma walshHadamard_sq_nonneg {n : ℕ} (f : F2Vec n → ZMod 2) (a : F2Vec n) :
    0 ≤ (walshHadamard f a) ^ 2 :=
  sq_nonneg _

/-- The Walsh–Hadamard value at 0 counts the "balance" of f:
    Wf(0) = 2ⁿ - 2 · |{x | f(x) = 1}|. -/
lemma walshHadamard_zero {n : ℕ} (f : F2Vec n → ZMod 2) :
    walshHadamard f 0 =
      ↑(Finset.univ.filter fun x : F2Vec n => f x = 0).card -
      ↑(Finset.univ.filter fun x : F2Vec n => f x ≠ 0).card := by sorry

/-- Key bound: For n odd, the covering-radius bound gives
    max_a |Wf(a)|² ≥ 2^{n+1} for any Boolean function f.
    Equality holds iff f is bent (for even n) or AB (for odd n). -/
theorem walsh_covering_bound {n : ℕ} (hn : 0 < n) (f : F2Vec n → ZMod 2) :
    ∃ a : F2Vec n, (2 : ℤ) ^ (n + 1) ≤ (walshHadamard f a) ^ 2 ∨
      (walshHadamard f a) ^ 2 = (2 : ℤ) ^ (2 * n) := by sorry

end ABTopos
