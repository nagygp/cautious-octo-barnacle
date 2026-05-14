/-
  ABTopos/Defs.lean — Core definitions for Almost Bent / APN function theory

  We work over F₂ⁿ modeled as `Fin n → ZMod 2`, with the standard inner product
  ⟨a, x⟩ = Σᵢ aᵢ · xᵢ  (in ZMod 2).

  The Walsh–Hadamard transform, nonlinearity, APN property, and AB property
  are defined here. All definitions are designed to interface cleanly with
  Mathlib's `ZMod`, `Finset`, and `AddChar` infrastructure.
-/
import Mathlib

open Finset BigOperators

namespace ABTopos

/-- The vector space F₂ⁿ, modeled as `Fin n → ZMod 2`. -/
abbrev F2Vec (n : ℕ) := Fin n → ZMod 2

/-- Standard inner product over F₂ⁿ: ⟨a, x⟩ = Σᵢ aᵢ · xᵢ in ZMod 2. -/
def innerF2 {n : ℕ} (a x : F2Vec n) : ZMod 2 :=
  ∑ i : Fin n, a i * x i

/-- Lift from ZMod 2 to the sign: 0 ↦ 1, 1 ↦ -1.
    This gives (-1)^b for b ∈ F₂. -/
noncomputable def signLift (b : ZMod 2) : ℤ :=
  if b = 0 then 1 else -1

/-- The Walsh–Hadamard transform of a Boolean function f : F₂ⁿ → F₂,
    evaluated at a ∈ F₂ⁿ:
      Wf(a) = Σ_{x ∈ F₂ⁿ} (-1)^{f(x) + ⟨a,x⟩}  -/
noncomputable def walshHadamard {n : ℕ} (f : F2Vec n → ZMod 2) (a : F2Vec n) : ℤ :=
  ∑ x : F2Vec n, signLift (f x + innerF2 a x)

/-- The Walsh spectrum of a vectorial function f : F₂ⁿ → F₂ⁿ,
    using component functions b · f(x):
      Wf(a, b) = Σ_{x ∈ F₂ⁿ} (-1)^{⟨b, f(x)⟩ + ⟨a,x⟩}  -/
noncomputable def walshSpectrum {n : ℕ} (f : F2Vec n → F2Vec n)
    (a b : F2Vec n) : ℤ :=
  walshHadamard (fun x => innerF2 b (f x)) a

/-- A function f : F₂ⁿ → F₂ⁿ is Almost Perfect Nonlinear (APN) if
    for every nonzero a, the derivative Dₐf(x) = f(x+a) + f(x)
    is at most 2-to-1. -/
def isAPN {n : ℕ} (f : F2Vec n → F2Vec n) : Prop :=
  ∀ (a : F2Vec n), a ≠ 0 → ∀ (b : F2Vec n),
    (Finset.univ.filter fun x => f (x + a) + f x = b).card ≤ 2

/-- The nonlinearity of a Boolean function f : F₂ⁿ → F₂ is
      NL(f) = 2^{n-1} - (1/2) max_a |Wf(a)|
    We store 2 · NL(f) to stay in ℤ. -/
noncomputable def twiceNonlinearity {n : ℕ} (f : F2Vec n → ZMod 2) : ℤ :=
  2 ^ n - (Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩
    (fun a : F2Vec n => (walshHadamard f a).natAbs) : ℤ)

/-- A vectorial function f : F₂ⁿ → F₂ⁿ is Almost Bent (AB) if n is odd and
    its Walsh spectrum takes only values in {0, ±2^{(n+1)/2}}. -/
def isAB {n : ℕ} (f : F2Vec n → F2Vec n) : Prop :=
  ∀ (a b : F2Vec n), b ≠ 0 →
    walshSpectrum f a b = 0 ∨
    (walshSpectrum f a b) ^ 2 = (2 : ℤ) ^ (n + 1)

/-- A vectorial function f : F₂ⁿ → F₂ⁿ is maximally nonlinear if every
    nonzero component function b · f achieves the covering-radius bound:
      max_a |Wf(a,b)| = 2^{(n+1)/2}  for all b ≠ 0.
    Equivalently, |Wf(a,b)|² ∈ {0, 2^{n+1}} for all a, b ≠ 0. -/
def isMaximallyNonlinear {n : ℕ} (f : F2Vec n → F2Vec n) : Prop :=
  ∀ (a b : F2Vec n), b ≠ 0 →
    (walshSpectrum f a b) ^ 2 = 0 ∨
    (walshSpectrum f a b) ^ 2 = (2 : ℤ) ^ (n + 1)

/-- The linear code associated with f : F₂ⁿ → F₂ⁿ.
    Cf = {(x, f(x)) | x ∈ F₂ⁿ} viewed as a set of codewords in F₂^{2n}. -/
def graphCode {n : ℕ} (f : F2Vec n → F2Vec n) : Set (F2Vec (2 * n)) :=
  { w | ∃ x : F2Vec n, ∀ i : Fin (2 * n),
    w i = if h : i.val < n then x ⟨i.val, h⟩ else f x ⟨i.val - n, by omega⟩ }

/-- Hamming weight of a vector in F₂ⁿ. -/
def hammingWeight {n : ℕ} (v : F2Vec n) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

/-
signLift squares to 1.
-/
lemma signLift_sq (b : ZMod 2) : signLift b ^ 2 = 1 := by
  fin_cases b <;> rfl

/-- signLift is multiplicative under addition in ZMod 2:
    (-1)^{a+b} = (-1)^a · (-1)^b. -/
lemma signLift_add (a b : ZMod 2) : signLift (a + b) = signLift a * signLift b := by
  unfold signLift
  fin_cases a <;> fin_cases b <;> simp [show (1 : ZMod 2) + 1 = 0 from by decide]

end ABTopos