import RequestProject.Foundations.Fourier
import RequestProject.Foundations.KasamiABWeightDistribution
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-2: the MacWilliams transform

This module is the **second from-scratch foundational module of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15), building on B-fp-1
(`KasamiABWeightDistribution.lean`) and the project's Fourier kernel
(`Foundations/Fourier.lean`).

Direction (B) closes the additive-energy value `16·E = q³ + 2q²` through the
MacWilliams / Pless power-moment route.  Its missing engine — absent from
Mathlib — is the **MacWilliams transform**: the duality, via Poisson summation
over a code `C` and its dual `C⊥`, relating weight enumerators of `C` and `C⊥`.

This module supplies that engine in its harmonic-analytic core form.  For a
finite commutative ring `R` (the ambient code space), a primitive additive
character `ψ : AddChar R R'` into a domain `R'`, and a subgroup (linear code)
`C ≤ R`, the **dual code** is the annihilator

```
   C⊥ = dualCode ψ C = { y | ∀ x ∈ C, ψ(x·y) = 1 } .
```

The results are:

* the dual code as an `AddSubgroup`, with the membership unfolding
  (`mem_dualCode`) and the double-dual inclusion `C ≤ C⊥⊥`
  (`subset_dualCode_dualCode`);
* **subgroup character orthogonality** — the heart of Poisson summation —
  `∑_{y∈C⊥} ψ(x·y) = |C⊥|` if `x ∈ C⊥⊥` and `0` otherwise
  (`sum_char_over_dual`);
* the **MacWilliams / Poisson transform**
  `∑_{y∈C⊥} 𝓕ψ f (y) = |C⊥| · ∑_{x∈C⊥⊥} f(x)` (`macwilliams_poisson`);
* under nondegeneracy of the pairing (`|D|·|D⊥| = |R|` for every subgroup `D`),
  the **double-dual identity** `C⊥⊥ = C` (`dualCode_dualCode_eq`) and hence the
  MacWilliams identity in its standard form
  `∑_{y∈C⊥} 𝓕ψ f (y) = |C⊥| · ∑_{x∈C} f(x)` (`macwilliams_identity`).

Specializing `f` to a weight monomial `z ↦ z^{wt}` (a product over coordinates)
turns `macwilliams_identity` into the classical MacWilliams weight-enumerator
identity; the autocorrelation fourth-moment bridge `hWK` (core B-fp-4) is the
remaining deep frontier.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure character theory on finite
abelian groups (no analysis, any characteristic) and introduces no axioms; the
nondegeneracy `|D|·|D⊥| = |R|` is carried as an explicit hypothesis where used.

## Sources

MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 5 (the
MacWilliams identity); Terras, *Fourier Analysis on Finite Groups*, Ch. 4
(Poisson summation); Carlet, *Boolean Functions for Cryptography and Coding
Theory*, Ch. 6.
-/

namespace Vanish.Foundations

open AddChar Finset BigOperators

open scoped Classical

variable {R R' : Type*} [CommRing R] [Fintype R] [DecidableEq R] [CommRing R'] [IsDomain R']

/-! ## 1. The dual code (annihilator) -/

/-- **The dual code** of `C` with respect to the character `ψ`: the annihilator
`C⊥ = { y | ∀ x ∈ C, ψ(x·y) = 1 }`, an additive subgroup of `R`. -/
def dualCode (ψ : AddChar R R') (C : AddSubgroup R) : AddSubgroup R where
  carrier := {y | ∀ x ∈ C, ψ (x * y) = 1}
  add_mem' := by
    intro a b ha hb x hx
    rw [mul_add, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
  zero_mem' := by
    intro x _
    rw [mul_zero, AddChar.map_zero_eq_one]
  neg_mem' := by
    intro a ha x hx
    have h : ψ (x * -a) * ψ (x * a) = 1 := by
      rw [← AddChar.map_add_eq_mul]
      have hz : x * -a + x * a = 0 := by ring
      rw [hz, AddChar.map_zero_eq_one]
    rw [ha x hx, mul_one] at h
    exact h

omit [Fintype R] [DecidableEq R] [IsDomain R'] in
/-- Membership in the dual code. -/
@[simp] theorem mem_dualCode {ψ : AddChar R R'} {C : AddSubgroup R} {y : R} :
    y ∈ dualCode ψ C ↔ ∀ x ∈ C, ψ (x * y) = 1 := Iff.rfl

/-
**Double-dual inclusion.**  Every codeword lies in its double dual:
`C ≤ C⊥⊥`.
-/
theorem subset_dualCode_dualCode (ψ : AddChar R R') (C : AddSubgroup R) :
    C ≤ dualCode ψ (dualCode ψ C) := by
  intro x hx y hy;
  simpa [ mul_comm ] using hy x hx

/-! ## 2. Subgroup character orthogonality (the Poisson kernel) -/

/-
**Subgroup character orthogonality.**  For a primitive additive character `ψ`
and the dual code `C⊥`, summing `y ↦ ψ(x·y)` over `C⊥` gives `|C⊥|` when
`x ∈ C⊥⊥` and `0` otherwise.  This is the orthogonality relation underlying
Poisson summation.
-/
theorem sum_char_over_dual (ψ : AddChar R R') (C : AddSubgroup R) (x : R) :
    ∑ y : dualCode ψ C, ψ (x * (y : R))
      = if x ∈ dualCode ψ (dualCode ψ C) then (Nat.card (dualCode ψ C) : R') else 0 := by
  split_ifs with hx;
  · rw [ Finset.sum_congr rfl fun y hy => ?_ ];
    convert Finset.sum_const ( 1 : R' );
    · simp +decide [ Nat.card_eq_fintype_card ];
    · exact hx _ y.2 |> fun h => by simpa [ mul_comm ] using h;
  · -- Since $x \notin \text{dualCode} \psi (\text{dualCode} \psi C)$, there exists $y₀ \in \text{dualCode} \psi C$ such that $\psi(x * y₀) \neq 1$.
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ ∈ dualCode ψ C, ψ (x * y₀) ≠ 1 := by
      contrapose! hx;
      exact fun y hy => by simpa [ mul_comm ] using hx y hy;
    -- Consider multiplying the sum by $\psi(x * y₀)$.
    have h_mul : ∑ y : ↥(dualCode ψ C), ψ (x * (y : R)) = ∑ y : ↥(dualCode ψ C), ψ (x * (y₀ + y : R)) := by
      rw [ ← Equiv.sum_comp ( Equiv.addLeft ⟨ y₀, hy₀.1 ⟩ ) ] ; simp +decide [ mul_add ];
    -- Using the property of the character $\psi$, we can simplify the expression.
    have h_simplify : ∑ y : ↥(dualCode ψ C), ψ (x * (y₀ + y : R)) = ψ (x * y₀) * ∑ y : ↥(dualCode ψ C), ψ (x * (y : R)) := by
      simp +decide only [mul_add, map_add_eq_mul, Finset.mul_sum _ _ _];
    exact mul_left_cancel₀ ( sub_ne_zero_of_ne hy₀.2 ) ( by linear_combination' h_simplify.symm + h_mul.symm )

/-! ## 3. The MacWilliams / Poisson transform -/

/-
**The MacWilliams / Poisson transform.**  Summing the Fourier transform of an
arbitrary `f` over the dual code recovers the sum of `f` over the double dual,
scaled by `|C⊥|`:

```
   ∑_{y ∈ C⊥} 𝓕ψ f (y) = |C⊥| · ∑_{x ∈ C⊥⊥} f(x).
```
-/
theorem macwilliams_poisson (ψ : AddChar R R') (C : AddSubgroup R) (f : R → R') :
    ∑ y : dualCode ψ C, fourierTransform ψ f (y : R)
      = (Nat.card (dualCode ψ C) : R')
          * ∑ x : dualCode ψ (dualCode ψ C), f (x : R) := by
  convert sum_char_over_dual ψ C using 1;
  constructor <;> intro h;
  · convert sum_char_over_dual ψ C using 1;
  · convert congr_arg ( fun x : R' => x ) ( Finset.sum_comm ) using 1;
    simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_comm, h ];
    rw [ ← Finset.sum_filter ];
    rw [ ← Finset.sum_mul _ _ _ ];
    refine' congr_arg₂ _ ( Finset.sum_bij ( fun x _ => x ) _ _ _ _ ) rfl <;> simp +decide;
    · exact fun a ha x hx => by simpa only [ mul_comm ] using ha x fun y hy => by simpa only [ mul_comm ] using hx y hy;
    · exact fun b hb x hx => by simpa [ mul_comm ] using hb x fun y hy => by simpa [ mul_comm ] using hx y hy;

/-! ## 4. The MacWilliams identity under nondegeneracy -/

/-
**Double-dual identity.**  Under nondegeneracy of the pairing
(`|D|·|D⊥| = |R|` for every subgroup `D`), the double dual collapses: `C⊥⊥ = C`.
-/
theorem dualCode_dualCode_eq (ψ : AddChar R R') (C : AddSubgroup R)
    (hcard : ∀ D : AddSubgroup R, Nat.card D * Nat.card (dualCode ψ D) = Fintype.card R) :
    dualCode ψ (dualCode ψ C) = C := by
  apply SetLike.ext';
  have h_eq : (Nat.card C : ℤ) = (Nat.card (dualCode ψ (dualCode ψ C)) : ℤ) := by
    exact_mod_cast ( mul_left_cancel₀ ( show ( Nat.card ( dualCode ψ C ) : ℕ ) ≠ 0 from Nat.ne_of_gt ( Nat.card_pos ) ) <| by nlinarith [ hcard C, hcard ( dualCode ψ C ) ] : ( Nat.card C : ℕ ) = Nat.card ( dualCode ψ ( dualCode ψ C ) ) );
  refine' Set.eq_of_subset_of_card_le _ _;
  · contrapose! h_eq;
    exact ne_of_lt ( mod_cast Set.ncard_lt_ncard ( lt_of_le_of_ne ( subset_dualCode_dualCode ψ C ) fun h => h_eq <| h.symm ▸ Set.Subset.refl _ ) );
  · norm_cast at h_eq ; aesop

/-
**The MacWilliams identity.**  Under nondegeneracy of the pairing, the
MacWilliams / Poisson transform lands on the code itself:

```
   ∑_{y ∈ C⊥} 𝓕ψ f (y) = |C⊥| · ∑_{x ∈ C} f(x).
```
-/
theorem macwilliams_identity (ψ : AddChar R R') (C : AddSubgroup R) (f : R → R')
    (hcard : ∀ D : AddSubgroup R, Nat.card D * Nat.card (dualCode ψ D) = Fintype.card R) :
    ∑ y : dualCode ψ C, fourierTransform ψ f (y : R)
      = (Nat.card (dualCode ψ C) : R') * ∑ x : C, f (x : R) := by
  convert macwilliams_poisson ψ C f using 1;
  rw [ dualCode_dualCode_eq ψ C hcard ]

end Vanish.Foundations