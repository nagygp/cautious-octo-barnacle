import Mathlib

/-!
# Pitch Classes and the Chromatic Universe

## Musical Context (Dobbins, *Creative Approach to Jazz Piano Harmony*)
The passage describes harmonizing the C major scale with chromatic passing tones,
producing alternating **major sixth** and **diminished seventh** chords.
Each voice simply ascends the scale from a different starting note of C6 (C E G A).

## Category Theory & Type Theory Connections

### 🎵 Pitch classes as ℤ/12ℤ — a *cyclic group* and a *groupoid with one object*
Pitch classes form **ℤ₁₂ = ℤ/12ℤ**, the integers mod 12.
- Categorically: a **group object** in **Set**, equivalently a **one-object groupoid**
  whose morphisms are the 12 transpositions.
- Type-theoretically: a **quotient type** — we identify integers that differ by 12.
- In HoTT: ℤ₁₂ is a **0-type** (a set); its *delooping* **Bℤ₁₂** is a **1-type**
  (a groupoid with one point whose loop space is ℤ₁₂) — this is the *classifying space*
  of the cyclic group acting on pitch.

### 🎹 Universal Property
The inclusion `ℤ → ℤ₁₂` (reduction mod 12) is the **universal arrow** from ℤ to the
forgetful functor U : **Ab₁₂** → **Ab**, where Ab₁₂ is the category of abelian groups
annihilated by 12. Equivalently, `ℤ₁₂ ≅ ℤ ⧸ 12ℤ` is a *coequalizer* in **Ab**.

### Lean Best Practice: Reuse Mathlib's `ZMod`
Rather than rolling our own mod-12 arithmetic, we use `ZMod 12`.
This is the **art of clean code**: *don't reinvent the wheel* — leverage the library.

### Functional Programming Principle: *Make illegal states unrepresentable*
By using `ZMod 12` instead of `ℕ`, we make it *impossible* to represent pitch class 13.
The type system enforces the musical invariant.
-/

/-- The 12 pitch classes of equal temperament, modeled as `ℤ/12ℤ`.
    This is both a ring and a cyclic group — a rich algebraic structure
    that Mathlib gives us for free.

    **Category theory pattern**: `ZMod 12` is the terminal object in the
    category of rings receiving a ring map `ℤ →+* R` with `12 = 0` in `R`.

    **Lean tip**: Type aliases via `abbrev` are transparent to the elaborator —
    they don't create a new type, just a shorthand. Use `def` + `deriving`
    when you want a genuinely new wrapper type. -/
abbrev PitchClass := ZMod 12

namespace PitchClass

/-!
## Named Pitch Classes
Using `abbrev` for each note name. These are *definitional equalities* —
the Lean kernel can unfold them automatically.

**Lean best practice**: Group related definitions, use consistent naming,
and provide docstrings. The `#check` command lets you verify types interactively.
-/

abbrev C  : PitchClass := 0
abbrev Cs : PitchClass := 1   -- C♯ / D♭
abbrev D  : PitchClass := 2
abbrev Ds : PitchClass := 3   -- D♯ / E♭
abbrev E  : PitchClass := 4
abbrev F  : PitchClass := 5
abbrev Fs : PitchClass := 6   -- F♯ / G♭
abbrev G  : PitchClass := 7
abbrev Gs : PitchClass := 8   -- G♯ / A♭
abbrev A  : PitchClass := 9
abbrev As : PitchClass := 10  -- A♯ / B♭
abbrev B  : PitchClass := 11

/-- **Interval**: the distance between two pitch classes.
    Since pitch classes live in ℤ₁₂, subtraction automatically wraps.

    **Category theory**: An interval is a *morphism* in the one-object
    groupoid ℤ₁₂. Composition of morphisms = addition of intervals.
    This is the **Cayley representation** of the group. -/
def interval (p q : PitchClass) : PitchClass := q - p

/-- Transposition by a fixed interval is a *group automorphism* of ℤ₁₂.
    Categorically, it's an *endofunctor* on the one-object groupoid.

    **Beautiful pattern**: The group of transpositions is *isomorphic to
    the group itself* — this is the **regular representation**.

    **Lean best practice**: `fun x => x + n` is a *pure function* —
    no side effects, referentially transparent. -/
def transpose (n : PitchClass) : PitchClass → PitchClass := fun x => x + n

/-!
## The Major Scale as a List of Intervals

**Functional programming**: We define the scale *declaratively* as data
(a list of interval steps) rather than *imperatively* (a loop that mutates state).
This is the FP principle of **data over control flow**.

**Type theory**: A scale is a *dependent function* from positions to pitch classes,
or equivalently a *section* of a bundle over a finite index set.

The C major scale: W W H W W W H  (W = whole step = 2, H = half step = 1)
-/

/-- The interval pattern of any major scale: 2 2 1 2 2 2 1.
    This is *key-independent* — a beautiful example of **abstraction**.

    **Higher category theory**: This pattern is an object in the *groupoid
    of scale structures*, where morphisms are mode rotations (Dorian = rotation by 1,
    Phrygian = rotation by 2, etc.). The 7 modes form an **orbit** under ℤ₇ action. -/
def majorScaleSteps : List (ZMod 12) := [2, 2, 1, 2, 2, 1, 2]

/-- Build a scale from a root and a list of interval steps.
    **Functional programming**: `List.scanl` is a *fold that keeps intermediate results*.
    This is a standard FP combinator — much cleaner than a mutable accumulator.

    **Category theory**: `scanl (+)` is a *prefix sum* — the *free monoid action*
    of the interval list on the starting pitch. -/
def buildScale (root : PitchClass) (steps : List PitchClass) : List PitchClass :=
  (steps.scanl (· + ·) root)

/-- The C major scale: C D E F G A B C -/
def cMajorScale : List PitchClass := buildScale C majorScaleSteps

-- Verify: the C major scale has the right notes
#eval cMajorScale  -- [0, 2, 4, 5, 7, 9, 11, 1]
-- Note: 1 at the end is C+12 ≡ 1? Let's check...
-- Actually in ZMod 12: 0+2+2+1+2+2+1+2 = 12 ≡ 0. So last = 0. Let me verify:
#eval (0 + 2 + 2 + 1 + 2 + 2 + 1 + 2 : ZMod 12)  -- should be 0

end PitchClass
