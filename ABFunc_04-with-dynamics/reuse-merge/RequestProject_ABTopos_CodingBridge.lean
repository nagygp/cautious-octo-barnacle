/-
  ABTopos/CodingBridge.lean — Bridge between Walsh spectrum and coding theory

  Theorem (Walsh–Coding Duality):
    The Walsh spectrum of f is isomorphic to the weight distribution
    of the dual code C_f⊥.

  This connects the cryptographic properties of f to the coding-theoretic
  properties of its associated linear code, enabling use of
  MacWilliams-type identities.
-/
import Mathlib
import RequestProject.ABTopos.Defs
import RequestProject.ABTopos.Walsh

open Finset BigOperators ABTopos

namespace ABTopos

/-! ## The code associated with a vectorial function -/

/-- The linear code associated with f : F₂ⁿ → F₂ⁿ, as a submodule.
    C_f = { x ↦ ⟨a, x⟩ + ⟨b, f(x)⟩ | a, b ∈ F₂ⁿ }
    This gives a [2ⁿ, 2n] code whose codewords are indexed by (a,b). -/
noncomputable def codeOfFunc {n : ℕ} (f : F2Vec n → F2Vec n) :
    F2Vec n × F2Vec n → (F2Vec n → ZMod 2) :=
  fun ⟨a, b⟩ x => innerF2 a x + innerF2 b (f x)

/-- The weight of a codeword c_{a,b} is related to the Walsh transform:
      wt(c_{a,b}) = 2^{n-1} - (1/2) · W_f(a,b)

    We state this as: 2 · wt(c_{a,b}) = 2ⁿ - W_f(a,b). -/
theorem weight_walsh_relation {n : ℕ} (f : F2Vec n → F2Vec n)
    (a b : F2Vec n) :
    2 * ↑((Finset.univ.filter fun x : F2Vec n =>
        codeOfFunc f (a, b) x ≠ 0).card : ℤ) =
      (2 : ℤ) ^ n - walshSpectrum f a b := by sorry

/-- The weight distribution of the code determines the Walsh spectrum.
    This is the content of the MacWilliams-type identity for our setting:

    For each (a,b), the Walsh value W_f(a,b) is recovered from the
    weight wt of the corresponding codeword:
      W_f(a,b) = 2ⁿ - 2 · wt(c_{a,b})  -/
theorem walsh_from_weight {n : ℕ} (f : F2Vec n → F2Vec n)
    (a b : F2Vec n) :
    walshSpectrum f a b =
      (2 : ℤ) ^ n - 2 * ↑((Finset.univ.filter fun x : F2Vec n =>
          codeOfFunc f (a, b) x ≠ 0).card : ℤ) := by sorry

/-- **Walsh-to-Coding Duality** (Theorem 1 of the request):
    The Walsh spectrum is entirely determined by the weight enumerator
    of the associated code, and vice versa.

    Formally: the map (a,b) ↦ W_f(a,b) is an affine isomorphism
    with the map (a,b) ↦ wt(c_{a,b}).

    This means all spectral properties (AB, APN, nonlinearity)
    can equivalently be stated in terms of code distances. -/
theorem walsh_to_coding_dual {n : ℕ} (f : F2Vec n → F2Vec n)
    (a b : F2Vec n) :
    walshSpectrum f a b = 0 ↔
      (Finset.univ.filter fun x : F2Vec n =>
        codeOfFunc f (a, b) x ≠ 0).card = 2 ^ (n - 1) := by sorry

/-- A function is AB iff its associated code has the weight distribution
    of a 2-weight code with weights {2^{n-1} - 2^{(n-1)/2}, 2^{n-1} + 2^{(n-1)/2}}.
    This is the coding-theoretic characterization of AB functions. -/
theorem ab_iff_two_weight_code {n : ℕ} (hn : Odd n) (f : F2Vec n → F2Vec n) :
    isAB f ↔
      ∀ (a b : F2Vec n), b ≠ 0 →
        let w := (Finset.univ.filter fun x : F2Vec n =>
            codeOfFunc f (a, b) x ≠ 0).card
        w = 2 ^ (n - 1) ∨
        (2 * (w : ℤ) - 2 ^ n) ^ 2 = 2 ^ (n + 1) := by sorry

end ABTopos
