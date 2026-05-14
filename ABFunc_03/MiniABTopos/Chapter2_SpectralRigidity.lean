import Mathlib
import MiniABTopos.Chapter1_SpectralFoundations
/-!
# Chapter 2 — Spectral Rigidity

## What this chapter builds on

Chapter 1 gave us spectral objects, bentness, diversity, and the
KEY LEMMA: bent → diversity = 1.

## What this chapter proves

We now draw out the consequences of that key lemma. The main result
is the **Spectral Rigidity Theorem**:

> A bent spectrum is *maximally rigid* — its higher "homotopy groups"
> are all trivial, meaning the spectrum is completely determined by
> a single number (the carrier size).

We also prove:
- The **Silence Constraint**: spectral noise (two distinct nonzero
  magnitudes) forces diversity > 1 and prevents rigidity.
- **k-Bent monotonicity**: if you're rigid up to level k+1, you're
  also rigid up to level k.
- **Euler characteristic** rigidity: discrete objects have completely
  determined Euler characteristics.

## The big picture

The theory has a clean logical structure:

    Bent spectrum ──KEY LEMMA──▶ diversity = 1
                                     │
                   Postnikov ◀───────┘
                   construction
                        │
                        ▼
              πₖ = diversity = 1
              for all k ≥ 1
                        │
                        ▼
              SPECTRAL RIGIDITY
              (discreteness)

The reverse direction also holds:
    Two distinct nonzero magnitudes ──▶ diversity > 1 ──▶ NOT discrete
-/

open Finset BigOperators

noncomputable section

/-! ## §1 Homotopy Spectral Objects — Adding "Higher Structure"

A **homotopy spectral object** enriches a bare spectral object with
a sequence of "homotopy group sizes" π₀, π₁, π₂, ...

**Intuition from topology**: In algebraic topology, a space X has
homotopy groups π₀(X), π₁(X), π₂(X), ... that measure its "holes"
at different dimensions. Here we work with their *cardinalities*:
- π₀ = |carrier| (the "number of points")
- πₖ for k ≥ 1 measures "spectral complexity at level k"

A **discrete** object has πₖ = 1 for all k ≥ 1 — no higher
structure, maximally simple.
-/

/-- A **homotopy spectral object**: a spectral object enriched with
    homotopy group cardinalities πₖ.

    All πₖ must be positive (≥ 1), since they represent cardinalities
    of nonempty groups. -/
structure HomotopySpectralObject (F : Type*) [Field F] [Fintype F] where
  /-- The underlying spectral object -/
  base : SpectralObject F
  /-- The cardinality of the k-th homotopy group -/
  homotopyCard : ℕ → ℕ
  /-- All homotopy groups are nonempty -/
  homotopyCard_pos : ∀ k, 0 < homotopyCard k

/-- A homotopy spectral object is **discrete** if all higher homotopy
    groups are trivial: πₖ = 1 for k ≥ 1.

    Discrete = maximally simple = no higher spectral complexity. -/
def HomotopySpectralObject.IsDiscrete {F : Type*} [Field F] [Fintype F]
    (X : HomotopySpectralObject F) : Prop :=
  ∀ k, k ≥ 1 → X.homotopyCard k = 1

/-- An object is **k-Bent** if it has a bent base spectrum AND all
    homotopy groups up to level k are trivial.

    k-Bentness is the condition "bent AND rigid up to level k". -/
def HomotopySpectralObject.IsKBent {F : Type*} [Field F] [Fintype F]
    (X : HomotopySpectralObject F) (c : ℝ) (k : ℕ) : Prop :=
  X.base.IsBent c ∧ ∀ j, 1 ≤ j → j ≤ k → X.homotopyCard j = 1

/-- Two homotopy spectral objects are **quasi-isomorphic** if all
    their homotopy groups have the same cardinality. -/
def HomotopySpectralObject.QuasiIso {F : Type*} [Field F] [Fintype F]
    (X Y : HomotopySpectralObject F) : Prop :=
  ∀ k, X.homotopyCard k = Y.homotopyCard k

/-! ## §2 The Postnikov Construction — From Spectrum to Homotopy

The **Postnikov construction** is the machine that converts a bare
spectral object into a homotopy spectral object. The key idea:

    π₀ := |carrier|        (the domain size)
    πₖ := spectralDiversity (for all k ≥ 1)

**Why this works**: The spectral diversity measures "how many
distinct nonzero magnitudes" the spectrum has. If the spectrum is
bent, diversity = 1, so πₖ = 1 for all k ≥ 1 — the object is
automatically discrete!

**Crucial point**: The discreteness is *derived* from bentness,
not assumed. The Postnikov construction computes πₖ from the data;
it doesn't hardcode πₖ = 1.
-/

/-- The **Postnikov construction**: builds a homotopy spectral object
    from a bare spectral object.

    - π₀ = |carrier| (domain size)
    - πₖ = spectral diversity (for k ≥ 1)

    Requires at least one nonzero spectral value (nontrivial spectrum). -/
def postnikovConstruction {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    (X : SpectralObject F)
    (hNontriv : ∃ v, X.spectrum v ≠ 0) :
    HomotopySpectralObject F where
  base := X
  homotopyCard := fun k => match k with
    | 0 => Fintype.card X.carrier
    | _ + 1 => X.spectralDiversity
  homotopyCard_pos := by
    intro k; cases k with
    | zero =>
      obtain ⟨v, _⟩ := hNontriv
      exact Fintype.card_pos_iff.mpr ⟨v⟩
    | succ _ => exact X.diversity_pos hNontriv

/-! ## §3 The Spectral Rigidity Theorem

This is the MAIN THEOREM of the spectral theory.

**Statement**: If a spectrum is bent at level c > 0 and has at
least one nonzero value, then its Postnikov construction is
*necessarily discrete* (πₖ = 1 for all k ≥ 1).

**Proof chain**:
  1. Bent ⟹ all nonzero norms equal c (by definition of IsBent)
  2. c > 0, so the set of distinct nonzero norms is exactly {c}
  3. Hence spectralDiversity = |{c}| = 1 (by `bent_diversity_eq_one`)
  4. Therefore πₖ = spectralDiversity = 1 for k ≥ 1 ∎

**Why this is profound**: The discreteness is a *theorem*, not a
definition. It says that the analytic property (bentness) forces
a combinatorial/topological property (trivial higher homotopy).
-/

/-- **SPECTRAL RIGIDITY THEOREM**: Bent spectra are necessarily discrete.

    If the Walsh spectrum is bent at level c > 0 and nontrivial,
    the Postnikov construction is discrete: πₖ = 1 for all k ≥ 1. -/
theorem bent_implies_discrete {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    (X : SpectralObject F) (c : ℝ) (hc : c > 0)
    (hBent : X.IsBent c)
    (hNontriv : ∃ v, X.spectrum v ≠ 0) :
    (postnikovConstruction X hNontriv).IsDiscrete := by
  intro k hk
  cases k with
  | zero => omega
  | succ n =>
    simp [postnikovConstruction]
    exact bent_diversity_eq_one X c hc hBent hNontriv

/-! ## §4 The Silence Constraint — Noise Prevents Rigidity

The converse direction: if a spectrum has two Walsh coefficients
with DIFFERENT nonzero magnitudes, then:
- The diversity is > 1 (at least two distinct nonzero norms)
- The Postnikov construction has π₁ > 1
- The object is NOT discrete

This is the formal version of "spectral noise breaks rigidity."
-/

/-- **SILENCE CONSTRAINT**: Two distinct nonzero magnitudes force
    spectral diversity > 1.

    If ‖W(v₁)‖ ≠ 0, ‖W(v₂)‖ ≠ 0, and ‖W(v₁)‖ ≠ ‖W(v₂)‖,
    then diversity > 1. -/
theorem silence_constraint {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F)
    (v₁ v₂ : X.carrier)
    (hv₁ : X.spectrum v₁ ≠ 0)
    (hv₂ : X.spectrum v₂ ≠ 0)
    (hdist : ‖X.spectrum v₁‖ ≠ ‖X.spectrum v₂‖) :
    X.spectralDiversity > 1 := by
  refine Finset.one_lt_card.mpr ?_
  exact ⟨‖X.spectrum v₁‖, by aesop, ‖X.spectrum v₂‖, by aesop, hdist⟩

/-- **Corollary**: Spectral noise prevents discreteness.
    If two Walsh coefficients have distinct nonzero norms, the
    Postnikov construction has π₁ > 1 — the object is NOT discrete. -/
theorem noise_prevents_discreteness {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    (X : SpectralObject F)
    (hNontriv : ∃ v, X.spectrum v ≠ 0)
    (v₁ v₂ : X.carrier)
    (hv₁ : X.spectrum v₁ ≠ 0)
    (hv₂ : X.spectrum v₂ ≠ 0)
    (hdist : ‖X.spectrum v₁‖ ≠ ‖X.spectrum v₂‖) :
    (postnikovConstruction X hNontriv).homotopyCard 1 > 1 := by
  simp [postnikovConstruction]
  exact silence_constraint X v₁ v₂ hv₁ hv₂ hdist

/-! ## §5 Characterising Discreteness

Discreteness of the Postnikov construction is equivalent to
diversity = 1. This gives a clean biconditional.
-/

/-- **Discreteness ⟺ Unit Diversity**: The Postnikov construction is
    discrete if and only if the spectral diversity equals 1. -/
theorem discreteness_iff_diversity_one {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    (X : SpectralObject F)
    (hNontriv : ∃ v, X.spectrum v ≠ 0) :
    (postnikovConstruction X hNontriv).IsDiscrete ↔
    X.spectralDiversity = 1 :=
  ⟨fun h => h 1 le_rfl, fun h k hk => by cases k <;> tauto⟩

/-! ## §6 k-Bent Properties

Useful structural properties of the k-Bent condition.
-/

/-- **k-Bent monotonicity**: (k+1)-Bent implies k-Bent.

    If you're rigid through level k+1, you're certainly rigid
    through level k. -/
theorem kBent_monotone {F : Type*} [Field F] [Fintype F]
    (X : HomotopySpectralObject F) (c : ℝ) (k : ℕ)
    (h : X.IsKBent c (k + 1)) : X.IsKBent c k :=
  ⟨h.1, fun j hj1 hjk => h.2 j hj1 (by omega)⟩

/-- **Discrete + Bent ⟹ k-Bent at all levels**: A discrete object
    with a bent base is k-Bent for every k simultaneously. -/
theorem discrete_implies_kBent {F : Type*} [Field F] [Fintype F]
    (X : HomotopySpectralObject F) (c : ℝ)
    (hBent : X.base.IsBent c) (hDisc : X.IsDiscrete) :
    ∀ k, X.IsKBent c k :=
  fun _ => ⟨hBent, fun j hj1 _ => hDisc j hj1⟩

/-- **Bent Postnikov objects are k-Bent at all levels.**
    Combines the rigidity theorem with `discrete_implies_kBent`. -/
theorem postnikov_bent_all_kBent {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    (X : SpectralObject F) (c : ℝ) (hc : c > 0)
    (hBent : X.IsBent c)
    (hNontriv : ∃ v, X.spectrum v ≠ 0) :
    ∀ k, (postnikovConstruction X hNontriv).IsKBent c k :=
  discrete_implies_kBent _ c hBent (bent_implies_discrete X c hc hBent hNontriv)

/-! ## §7 Euler Characteristic — A Numerical Invariant

The **Euler characteristic** is a single integer that summarises
the homotopy group data. It's the alternating sum:
    χ_N = π₀ − π₁ + π₂ − π₃ + ⋯ ± πₙ

For discrete objects (πₖ = 1 for k ≥ 1), this simplifies dramatically.
-/

/-- The Euler characteristic truncated at level N:
    χ_N(X) = Σ_{k=0}^{N} (−1)^k · πₖ -/
def eulerCharacteristic {F : Type*} [Field F] [Fintype F]
    (X : HomotopySpectralObject F) (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1),
    (-1 : ℤ) ^ k * (X.homotopyCard k : ℤ)

/-- **Quasi-isomorphism preserves Euler characteristic.**

    If two objects have the same homotopy groups, they have the
    same Euler characteristic. -/
theorem euler_quasiIso_invariant {F : Type*} [Field F] [Fintype F]
    (X Y : HomotopySpectralObject F) (N : ℕ)
    (hQI : X.QuasiIso Y) :
    eulerCharacteristic X N = eulerCharacteristic Y N := by
  simp only [eulerCharacteristic]
  congr 1; apply funext; intro k; congr 1
  exact_mod_cast hQI k

/-- **Discrete Euler term**: For a discrete object, each higher
    homotopy group contributes (−1)^k · 1 = (−1)^k to the Euler
    characteristic. -/
theorem euler_discrete_term {F : Type*} [Field F] [Fintype F]
    (X : HomotopySpectralObject F) (k : ℕ) (hk : k ≥ 1)
    (hDisc : X.IsDiscrete) :
    (-1 : ℤ) ^ k * (X.homotopyCard k : ℤ) = (-1 : ℤ) ^ k := by
  rw [hDisc k hk]; simp

end
