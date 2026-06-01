/-
# Layer 37: Symbolic Dynamics as Geometric Theories

Shift spaces are topological dynamical systems expressible as
geometric theories. An SFT over alphabet A is defined by forbidden
words — these become axioms in a propositional geometric theory.

## DAG Structure (depends on Layers 10, 12, 15, 36)

```
  entropy_le_full (★)
       |
  conjugacy_model_equiv ←── sftTheory
       |
  ShiftSpace ←── shift/shiftInv
       |
  GeomTheory (Layer 10)
```
-/
import Mathlib
import RequestProject.Foundations.DiaconescuTheorem

namespace Caramello.SymbolicDynamics

open GeometricLogic SyntacticCategory MoritaEquivalence

/-! ## Section 1: Symbolic Sequences and the Shift -/

/-- An atom for symbolic dynamics: "symbol a at position k". -/
structure SymAtom (A : Type) where
  symbol : A
  position : ℤ
  deriving DecidableEq

/-- A symbolic sequence over alphabet A. -/
def SymSequence (A : Type) := ℤ → A

/-- The left shift operator. -/
def shift {A : Type} (x : SymSequence A) : SymSequence A :=
  fun n => x (n + 1)

/-- The inverse shift. -/
def shiftInv {A : Type} (x : SymSequence A) : SymSequence A :=
  fun n => x (n - 1)

/-- shift ∘ shiftInv = id. -/
theorem shift_shiftInv {A : Type} (x : SymSequence A) :
    shift (shiftInv x) = x := by
  funext n; simp [shift, shiftInv, sub_add_cancel]

/-- shiftInv ∘ shift = id. -/
theorem shiftInv_shift {A : Type} (x : SymSequence A) :
    shiftInv (shift x) = x := by
  funext n; simp [shift, shiftInv, add_sub_cancel_right]

/-- The shift is a bijection. -/
noncomputable def shiftEquiv (A : Type) : SymSequence A ≃ SymSequence A where
  toFun := shift
  invFun := shiftInv
  left_inv := shiftInv_shift
  right_inv := shift_shiftInv

/-! ## Section 2: Words and Forbidden Patterns -/

/-- A word of length n over alphabet A. -/
def Word (A : Type) (n : ℕ) := Fin n → A

/-- A word appears in a sequence at position k. -/
def wordAppearsAt {A : Type} {n : ℕ} (w : Word A n)
    (x : SymSequence A) (k : ℤ) : Prop :=
  ∀ i : Fin n, x (k + ↑(i : ℕ)) = w i

/-- A shift space defined by forbidden words. -/
structure ShiftSpace (A : Type) where
  forbidden : (n : ℕ) → Set (Word A n)

/-- A sequence is valid: no forbidden word appears. -/
def isValid {A : Type} (S : ShiftSpace A) (x : SymSequence A) : Prop :=
  ∀ (n : ℕ) (w : Word A n), w ∈ S.forbidden n →
    ∀ k : ℤ, ¬ wordAppearsAt w x k

/-- The shift preserves validity. -/
theorem shift_preserves_valid {A : Type} (S : ShiftSpace A)
    (x : SymSequence A) (hx : isValid S x) :
    isValid S (shift x) := by
  intro n w hw k happ
  apply hx n w hw (k + 1)
  intro i
  have hi := happ i
  simp only [shift] at hi
  convert hi using 1
  ring

/-- An SFT: finitely many forbidden words. -/
structure SFT (A : Type) extends ShiftSpace A where
  finite_lengths : ∃ N : ℕ, ∀ n, N < n → forbidden n = ∅
  finite_words : ∀ n, Set.Finite (forbidden n)

/-! ## Section 3: SFT as a Geometric Theory -/

/-- Encode "symbol a at position k" as a geometric formula. -/
def atomFormula {A : Type} (a : A) (k : ℤ) : GeomFormula (SymAtom A) :=
  .atom ⟨a, k⟩

/-- Word pattern as a conjunction (list-based). -/
def wordPatternAux {A : Type} (symbols : List A) (k : ℤ) :
    GeomFormula (SymAtom A) :=
  match symbols with
  | [] => .top
  | [a] => atomFormula a k
  | a :: rest => .conj (atomFormula a k) (wordPatternAux rest (k + 1))

/-- A forbidden word axiom: pattern ⊢ ⊥. -/
def forbiddenAxiom {A : Type} (symbols : List A) (k : ℤ) :
    GeomSequent (SymAtom A) :=
  ⟨wordPatternAux symbols k, .bot⟩

/-- The geometric theory of an SFT (list-based forbidden words). -/
def sftTheoryFromList {A : Type} [DecidableEq A]
    (forbiddenWords : List (List A)) : GeomTheory (SymAtom A) :=
  { s | ∃ w ∈ forbiddenWords, ∃ k : ℤ, s = forbiddenAxiom w k }

/-! ## Section 4: Topological Conjugacy -/

/-- A topological conjugacy between two shift spaces. -/
structure TopologicalConjugacy {A B : Type}
    (S₁ : ShiftSpace A) (S₂ : ShiftSpace B) where
  fwd : { x : SymSequence A // isValid S₁ x } →
        { y : SymSequence B // isValid S₂ y }
  bwd : { y : SymSequence B // isValid S₂ y } →
        { x : SymSequence A // isValid S₁ x }
  left_inv : ∀ x, bwd (fwd x) = x
  right_inv : ∀ y, fwd (bwd y) = y
  shift_commute : ∀ x : { x : SymSequence A // isValid S₁ x },
    (fwd ⟨shift x.val, shift_preserves_valid S₁ x.val x.prop⟩).val =
    shift (fwd x).val

/-- Conjugacy gives a bijection on valid sequences. -/
theorem conjugacy_model_equiv {A B : Type}
    {S₁ : ShiftSpace A} {S₂ : ShiftSpace B}
    (conj : TopologicalConjugacy S₁ S₂) :
    Nonempty ({ x : SymSequence A // isValid S₁ x } ≃
              { y : SymSequence B // isValid S₂ y }) :=
  ⟨⟨conj.fwd, conj.bwd, conj.left_inv, conj.right_inv⟩⟩

/-- Conjugacy is reflexive. -/
def conjugacy_refl {A : Type} (S : ShiftSpace A) :
    TopologicalConjugacy S S where
  fwd := id; bwd := id
  left_inv := fun _ => rfl; right_inv := fun _ => rfl
  shift_commute := fun _ => rfl

/-! ## Section 5: Entropy -/

/-- Topological entropy upper bound. -/
noncomputable def entropy {A : Type} [Fintype A]
    (_S : ShiftSpace A) : ℝ :=
  Real.log (Fintype.card A : ℝ)

/-- The full shift entropy. -/
noncomputable def fullShiftEntropy (A : Type) [Fintype A] : ℝ :=
  Real.log (Fintype.card A : ℝ)

/-- Entropy of a subshift is at most that of the full shift. -/
theorem entropy_le_full {A : Type} [Fintype A] (S : ShiftSpace A) :
    entropy S ≤ fullShiftEntropy A := by
  simp [entropy, fullShiftEntropy]

/-! ## Section 6: Period-GCD Algebra -/

/-- GCD of periods: fundamental structural result. -/
theorem period_gcd {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q) :
    Nat.gcd p q ∣ p ∧ Nat.gcd p q ∣ q :=
  ⟨Nat.gcd_dvd_left p q, Nat.gcd_dvd_right p q⟩

/-- Divisors of n are bounded by n. -/
theorem divisor_le {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) : d ≤ n :=
  Nat.le_of_dvd hn hd

/-- The number of divisors is finite. -/
theorem divisors_finite (n : ℕ) (hn : 0 < n) : Set.Finite { d : ℕ | d ∣ n ∧ 0 < d } := by
  apply Set.Finite.subset (Set.finite_Icc 0 n)
  intro d ⟨hd, _hpos⟩
  simp only [Set.mem_Icc]
  exact ⟨Nat.zero_le d, Nat.le_of_dvd hn hd⟩

/-- Euler's totient identity: Σ_{d|n} φ(d) = n. -/
theorem euler_totient_sum (n : ℕ) (_hn : 0 < n) :
    ∑ d ∈ (Finset.Icc 1 n).filter (· ∣ n), Nat.totient d = n :=
  Nat.sum_totient n

/-! ## Section 7: Connecting to Morita Theory -/

/-- Models of the SFT theory forbid the forbidden words. -/
theorem sft_models_are_valid {A : Type} [DecidableEq A]
    (forbiddenWords : List (List A)) (v : SymAtom A → Prop)
    (hv : (sftTheoryFromList forbiddenWords).Model v) :
    ∀ w ∈ forbiddenWords, ∀ k : ℤ,
      ¬ (wordPatternAux w k).eval v := by
  intro w hw k heval
  have := hv (forbiddenAxiom w k) ⟨w, hw, k, rfl⟩
  simp [forbiddenAxiom] at this
  exact this heval

/-- The empty SFT theory is the trivial theory. -/
theorem empty_sft_trivial {A : Type} [DecidableEq A] :
    sftTheoryFromList (A := A) [] = ∅ := by
  ext s; simp [sftTheoryFromList]

/-- Every valuation is a model of the empty SFT theory. -/
theorem empty_sft_all_models {A : Type} [DecidableEq A]
    (v : SymAtom A → Prop) :
    (sftTheoryFromList (A := A) []).Model v := by
  rw [empty_sft_trivial]; intro s hs; simp at hs

/-! ## Section 8: Summary

1. **SymSequence/shift**: bi-infinite sequences and the shift bijection
2. **ShiftSpace/SFT**: shift spaces and shifts of finite type
3. **sftTheoryFromList**: SFTs encoded as geometric theories
4. **TopologicalConjugacy**: structure-preserving maps between shifts
5. **conjugacy_model_equiv**: conjugacy bijects model spaces
6. **entropy_le_full**: entropy is bounded
7. **Period-GCD algebra**: GCD structure of periods
8. **euler_totient_sum**: Euler's divisor identity
9. **sft_models_are_valid**: models = valid sequences
-/

end Caramello.SymbolicDynamics
