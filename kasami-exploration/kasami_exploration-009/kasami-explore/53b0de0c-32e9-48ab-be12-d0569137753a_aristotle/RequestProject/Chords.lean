import Mathlib
import RequestProject.PitchClass

/-!
# Chords: Products in the Category of Pitch Classes

## Musical Context
Dobbins describes alternating **C6** (C E G A) and **dim7** chords.
A chord is a *set* of pitch classes — or better, a *multiset* or *list*
(since voicing order matters for keyboard layout).

## Category Theory Connections

### Chords as Products / Tuples
A 4-note chord is an element of `PitchClass × PitchClass × PitchClass × PitchClass`,
i.e., the **4-fold product** in **Set** (or **Type** in Lean).

In category theory, products satisfy a **universal property**: for any object X
with maps to A and B, there exists a *unique* map X → A × B.
The projections `Prod.fst` and `Prod.snd` are the *universal arrows*.

### Chords as Finite Subsets
Alternatively, a chord-*type* (ignoring octave and voicing) is a `Finset PitchClass`.
This is a **subobject** in the category of sets — a *monomorphism* from the chord
into the full chromatic set.

### Higher Operads Connection 🎯
An **operad** describes operations with multiple inputs and one output.
A *chord voicing function* takes a chord type + a voicing rule → a specific voicing.
This is an **operadic composition**: the chord type is a *corolla* (tree with n leaves),
and voicing applies operations at each leaf.

In **higher operads** (e.g., ∞-operads), we'd have *homotopies between voicings* —
two voicings are "the same up to coherent equivalence" if they produce the same
harmonic function. This connects to Dobbins' observation that C6 = Am7 = FΔ9 = D9sus
are all "the same chord" up to reinterpretation — they are *equivalent objects*
in a *chord interpretation groupoid*.

## Lean Best Practices
- Use **structures** for data with named fields (clearer than tuples)
- Use **typeclasses** for ad-hoc polymorphism (like Haskell)
- Use **instances** to register canonical behaviors
-/

open PitchClass

/-- A four-voice chord voicing. Each field names a voice from top to bottom.

    **Lean best practice**: Use `structure` instead of `def ... := α × β × γ × δ`.
    Named fields are self-documenting and prevent mixups (which voice is which?).

    **Category theory**: A structure is a **limit** (specifically a **product**) in
    the category of types. The field accessors `.soprano`, `.alto`, etc. are the
    **projection morphisms** — the universal arrows of the product cone.

    **Type theory**: This is a **dependent record type** (Σ-type with named fields).
    In HoTT, it would be a **mere product** (0-truncated Σ-type). -/
structure FourVoiceChord where
  soprano : PitchClass
  alto    : PitchClass
  tenor   : PitchClass
  bass    : PitchClass
deriving Repr, DecidableEq

namespace FourVoiceChord

/-- Convert a chord to its pitch class set (forgetting voicing/octave).

    **Lean tip**: `{a, b, c, d}` is syntactic sugar for `insert a (insert b ...)`.

    **Category theory**: This is a **forgetful functor** from the category of
    voiced chords to the category of unvoiced chord types. It *forgets structure*
    (voicing order) and keeps only the essential pitch content. -/
def toPitchClassSet (c : FourVoiceChord) : Finset PitchClass :=
  {c.soprano, c.alto, c.tenor, c.bass}

/-- The interval content (all pairwise intervals) of a chord.
    This is an *invariant* under transposition — a **natural transformation**
    from the transposition functor to the interval-content functor.

    **Beautiful pattern**: Two chords with the same interval vector are
    **Z-related** in music theory. This is an *isomorphism* in the
    category of interval structures, but not necessarily in the category
    of pitch-class sets. A *failure of faithfulness* of the interval functor! -/
def intervals (c : FourVoiceChord) : List PitchClass :=
  let notes := [c.soprano, c.alto, c.tenor, c.bass]
  notes.flatMap fun p => notes.map fun q => interval p q

/-!
## The Dobbins Voicings

### Close Position C6
All notes within one octave, stacked in thirds/steps: A G E C (top to bottom)
Actually, C6 = C E G A. In close position from the top: A G E C.

### Drop-2 Voicing
Take close position and drop the *second voice from top* down an octave.
This is a **natural transformation** between two voicing functors:
- Close position: a functor `ChordType → Voicing`
- Drop-2: another functor `ChordType → Voicing`
The "drop" operation is the *component* of the natural transformation at each chord.

**Opetopic connection**: The drop-2 operation can be seen as a **2-cell** (face)
in an opetope. The 0-cells are individual notes, the 1-cells are intervals between
adjacent voices, and the 2-cell is the "re-voicing operation" that reshapes the
interval structure while preserving the pitch-class content.
-/

/-- C6 chord in close position: C E G A (bottom to top).
    **Lean best practice**: Use named arguments for clarity. -/
def C6_close : FourVoiceChord :=
  { soprano := A, alto := G, tenor := E, bass := C }

/-- C6 chord in drop-2 voicing: drop the alto (G) down an octave.
    In pitch-class terms the notes are the same; the voicing differs
    in *register* (octave placement), which our `PitchClass` model abstracts away.

    **Insight**: This abstraction is both a strength and a limitation.
    In HoTT terms, we've *truncated* the pitch space to its 0-truncation (ℤ₁₂).
    The full pitch space ℤ (MIDI note numbers) is the *universal cover*
    of the circle group ℤ₁₂ — a beautiful topological connection! -/
def C6_drop2 : FourVoiceChord :=
  { soprano := A, alto := E, tenor := G, bass := C }

/-- Diminished seventh chord built on C♯: C♯ E G A♯.
    Note: C♯ E G are *shared* with the C6 chord!
    This common-tone relationship is what makes Dobbins' pattern so smooth.

    **Category theory**: The intersection C6 ∩ C♯dim7 = {E, G} is a
    **pullback** (fiber product) in the category of pitch-class sets. -/
def Csdim7 : FourVoiceChord :=
  { soprano := As, alto := G, tenor := E, bass := Cs }

end FourVoiceChord

/-!
## Chord Equivalences: The Groupoid of Reinterpretation

Dobbins emphasizes that C6 can function as Am7, FΔ9, D9sus, etc.
These are **different objects in the chord-function category** that happen
to have the **same underlying pitch-class set**.

### Category Theory
This is a classic example of a **groupoid**: objects are chord interpretations,
and morphisms are reinterpretations. Every morphism is invertible (if C6 = Am7,
then Am7 = C6).

### HoTT Connection
In HoTT, we'd say the pitch-class set `{C, E, G, A}` has **multiple
identifications** as different chord functions. The space of all chord
functions mapping to this set is a **fiber** of the forgetful map
`ChordFunction → Finset PitchClass`.

If this fiber is contractible, the chord has a *unique* interpretation.
If not, the non-trivial **loop space** represents the *ambiguity* of
harmonic function — a precise formalization of musical ambiguity!

### Opetopes
An **opetope** is a higher-dimensional shape used in higher category theory.
The chord-reinterpretation situation can be modeled as:
- **0-cells**: individual pitch classes
- **1-cells**: intervals (morphisms between pitch classes)
- **2-cells**: chord types (composites of intervals)
- **3-cells**: reinterpretations (equivalences between chord types)

This is the beginning of an **opetopic set** — a presheaf on the
category of opetopes. The Dobbins pattern lives naturally in this world!
-/

/-- A chord function: a named harmonic interpretation of a voicing.

    **Lean best practice**: Use an inductive type (sum type) for a
    *closed* set of alternatives. This is **pattern matching** in FP —
    the compiler ensures you handle every case.

    **Category theory**: An inductive type is an **initial algebra**
    of an endofunctor. The recursor is the **universal arrow** from
    the initial algebra to any other algebra. -/
inductive ChordFunction where
  | major6 (root : PitchClass)        -- e.g., C6
  | minor7 (root : PitchClass)        -- e.g., Am7 (= C6)
  | majorAdd9 (root : PitchClass)     -- e.g., FΔ9 (contains C E G A too if we allow)
  | susDom9 (root : PitchClass)       -- e.g., D9sus
  | dim7 (root : PitchClass)          -- e.g., C♯°7
deriving Repr, DecidableEq

/-- The pitch classes of a chord function.
    **Lean best practice**: Use `match` for *structural* case analysis.
    Each branch is a *clause* — Lean checks exhaustiveness at compile time.

    **Functional programming**: This is a **catamorphism** (fold over an
    inductive type) — the canonical way to eliminate/use an inductive value. -/
def ChordFunction.pitchClasses : ChordFunction → Finset PitchClass
  | .major6 r    => {r, r + 4, r + 7, r + 9}
  | .minor7 r    => {r, r + 3, r + 7, r + 10}
  | .majorAdd9 r => {r, r + 4, r + 7, r + 9}  -- simplified
  | .susDom9 r   => {r, r + 5, r + 7, r + 10} -- simplified
  | .dim7 r      => {r, r + 3, r + 6, r + 9}

/-!
## 🌟 Beautiful Pattern: C6 = Am7

The pitch-class sets of C6 and Am7 are *identical*.
This is a theorem we can **prove** in Lean!

**Lean best practice**: State properties as `theorem`s, not just `#eval` checks.
Theorems are *machine-verified* — they can never be wrong.
`#eval` checks are *tests* — they could miss edge cases.
-/

/-
C major 6 and A minor 7 have the same pitch classes.
    This formalizes Dobbins' observation about chord reinterpretation.

    **Proof step**: Both sides reduce to the same `Finset` by computation.
    `decide` asks Lean to check equality by *brute-force evaluation* —
    possible because `PitchClass` is finite and has decidable equality.

    **Category theory**: This is an *isomorphism* in the groupoid of
    chord interpretations — a witness that two objects are equivalent.
-/
theorem C6_eq_Am7_pitchClasses :
    (ChordFunction.major6 C).pitchClasses = (ChordFunction.minor7 A).pitchClasses := by
  decide +revert

/-
Diminished seventh chords are symmetric: every note can be the root.
    C♯dim7 = Edim7 = Gdim7 = A♯dim7. We prove one case.

    **Beautiful pattern**: The dim7 chord has the *largest symmetry group*
    of any chord type — it's invariant under transposition by minor thirds.
    Its stabilizer subgroup in ℤ₁₂ is ℤ₃ (≅ {0, 3, 6, 9}).

    **Category theory**: This high symmetry means the dim7 chord's
    **automorphism group** in the chord groupoid is unusually large.
    In physics terms, it has a large **gauge symmetry**.
-/
theorem dim7_symmetric :
    (ChordFunction.dim7 Cs).pitchClasses = (ChordFunction.dim7 E).pitchClasses := by
  simp +decide [ ChordFunction.dim7 ]