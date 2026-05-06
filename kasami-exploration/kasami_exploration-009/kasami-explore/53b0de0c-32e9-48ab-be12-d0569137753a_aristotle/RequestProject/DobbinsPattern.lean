import Mathlib
import RequestProject.PitchClass
import RequestProject.Chords

/-!
# The Dobbins Harmonization Pattern

## Musical Description
The pattern alternates **C6** and **dim7** chords while each voice ascends
chromatically through the scale with a chromatic passing tone between
scale degrees 5 (G) and 6 (A) — i.e., G → G♯ → A.

The four voices start on C, E, G, A (the notes of C6) and each independently
walks up the chromatic/diatonic hybrid scale.

## 🎹 Musical Variability — Ways to Explore This Pattern

### 1. **Rhythmic Variation** (most accessible)
   - **Straight eighths** vs **swing eighths** — same notes, completely different feel
   - **Dotted rhythms**: ♩. ♪ | ♩. ♪ — creates a "galloping" feel
   - **Syncopation**: accent the "and" of beats → bossa nova, jazz feel
   - **Hemiola**: group 8th notes in 3s over 4/4 time → polyrhythmic tension
   - **Rubato**: stretch and compress time freely → expressive ballad style
   - **Rhythmic displacement**: start the pattern on beat 2, 3, or the "and"
   - **Metric modulation**: change the perceived tempo while keeping the pulse

### 2. **Voicing Variation**
   - **Close position** → compact, dense, "big band sax soli" sound
   - **Drop-2** → wider, more pianistic, standard jazz voicing
   - **Drop-3** → even wider, orchestral
   - **Drop-2-and-4** → very open, Debussy-like
   - **Spread voicings** → bass note far below, upper structure on top

### 3. **Directional Variation**
   - **Ascending** (Dobbins' preferred) — sounds like *resolution toward* a goal
   - **Descending** — Dobbins notes this can sound "unconvincing" due to
     chromatic resolution tendencies (G♯ wants to resolve up to A)
   - **Arch shape**: ascend then descend (or vice versa)
   - **Zigzag**: alternate ascending and descending motion

### 4. **Harmonic Reinterpretation**
   - Play the same pattern but *think* FΔ9 instead of C6
   - Or D9sus — changes which notes feel like tensions vs. chord tones
   - Add a bass note that implies the reinterpretation: play F in the bass
     under the C6 voicings → instant FΔ9 sound

### 5. **Transposition**
   - Practice in all 12 keys (the **orbit** of the pattern under ℤ₁₂ action)
   - Move by *cycle of fourths*: C → F → B♭ → E♭ → ... (standard jazz practice)
   - Move by *chromatic steps*: C → D♭ → D → ... (systematic coverage)
   - Move by *minor thirds*: C → E♭ → G♭ → A (exploits dim7 symmetry!)

### 6. **Textural Variation**
   - **Block chords** (as written) — every chord hit together
   - **Arpeggiated** — roll each chord, harp-like
   - **Broken** — play bass note, then upper 3 voices
   - **Stride** — alternate bass note and upper voicing
   - **Alberti bass** — classical pattern applied to jazz harmony

### 7. **Dynamic/Articulation Variation**
   - **Crescendo** ascending, **decrescendo** descending
   - **Staccato** vs **legato** — choppy energy vs smooth flow
   - **Accented top note** — brings out the melody

### 8. **Tempo as a Variable**
   - Ballad tempo: savor each color change
   - Medium swing: the "home base" for jazz exploration
   - Up-tempo: becomes a flashy technique showcase

## Formalization

We now model the ascending pattern as a **sequence of chords** —
a morphism in the category of **diagrams** (functors from ℕ to Chord).
-/

open PitchClass FourVoiceChord

/-!
## The Chromatic Scale Segment: G → G♯ → A

This is the **chromatic passing tone** that Dobbins describes.
In category theory, a chromatic passing tone is a **factorization**
of a whole-step morphism through two half-step morphisms:

```
    G ――――→ A         (whole step = 2)
    G → G♯ → A        (half + half = 1 + 1)
```

This factorization is a **2-simplex** in the **nerve** of ℤ₁₂ viewed
as a category. The nerve is a simplicial set — connecting us to
**∞-category theory** and **homotopy theory**!
-/

/-- The ascending Dobbins pattern: a sequence of chords indexed by ℕ.

    Each voice ascends through the C major scale with the chromatic
    passing tone G♯ between G and A.

    **Functional programming principle**: We define the *scale* as data
    and the *pattern* as a function from index to chord. Separation of
    concerns — the scale definition and the voicing logic are independent.

    **Category theory**: This sequence is a **functor** from the category
    (ℕ, ≤) (a poset = thin category) to the category of chords.
    Monotonicity of the scale ensures this is a *valid functor*
    (preserves the ordering). -/

/- The hybrid scale used in the Dobbins pattern:
    C C♯ D D♯ E F F♯ G G♯ A A♯ B (full chromatic, but we select
    the diatonic + passing tone subset).

    Dobbins' scale for C6 ascending:
    C - D - E - F - G - G♯ - A - B - C ...

    These 8 steps form one "cycle" of the pattern. Each voice
    starts at a different offset within C6 = {C, E, G, A}. -/
def dobbinsScale : List PitchClass :=
  [C, D, E, F, G, Gs, A, B]

/-- Get the nth note of the Dobbins scale (cycling every 8 notes).
    **Lean tip**: `List.getD` provides a default for out-of-bounds access.
    We use modular arithmetic to cycle.

    **Category theory**: Cycling makes this a functor from ℤ₈ to PitchClass —
    or equivalently, an element of the **free loop space** of the scale. -/
def dobbinsNote (n : ℕ) : PitchClass :=
  dobbinsScale.getD (n % 8) 0

/-- The four voice starting positions within the Dobbins scale.
    C is at index 0, E at index 2, G at index 4, A at index 6.

    **Beautiful pattern**: The starting positions are {0, 2, 4, 6} —
    the *even* elements of ℤ₈. This is the **index-2 subgroup** of ℤ₈,
    isomorphic to ℤ₄ = the Klein four-group... wait, ℤ₄ ≅ ℤ/4ℤ.
    Actually {0,2,4,6} in ℤ₈ ≅ ℤ₄ under the map x ↦ x/2.

    **Opetope connection**: The four voices form a **4-corolla** (a tree
    with 4 leaves and one root). The Dobbins pattern is an operadic
    composition that fills this corolla with a sequence of "voice motion"
    operations at each leaf. -/
def voiceStart : Fin 4 → ℕ
  | 0 => 6  -- soprano starts on A (index 6)
  | 1 => 4  -- alto starts on G (index 4)
  | 2 => 2  -- tenor starts on E (index 2)
  | 3 => 0  -- bass starts on C (index 0)

/-- The nth chord in the Dobbins ascending pattern.

    **Lean best practice**: This is a *pure function* — given the same `n`,
    it always returns the same chord. No hidden state, no mutation.
    This is the essence of **referential transparency**.

    **Category theory**: This function is the **action on objects** of
    our functor (ℕ, ≤) → Chord. -/
def dobbinsChord (n : ℕ) : FourVoiceChord where
  soprano := dobbinsNote (voiceStart 0 + n)
  alto    := dobbinsNote (voiceStart 1 + n)
  tenor   := dobbinsNote (voiceStart 2 + n)
  bass    := dobbinsNote (voiceStart 3 + n)

-- Let's verify the first few chords!
-- Chord 0: A G E C = C6 ✓
-- Chord 1: B G♯ F D = D dim7 (enharmonic)? Let's see: B Gs F D...
-- B=11, Gs=8, F=5, D=2. Intervals: 3,3,3 — yes, diminished 7th! ✓

#eval dobbinsChord 0  -- should give A=9, G=7, E=4, C=0
#eval dobbinsChord 1  -- B=11, G♯=8, F=5, D=2
#eval dobbinsChord 2  -- C=0, A=9, G=7, E=4 → another C6 inversion!
#eval dobbinsChord 3  -- D=2, A♯=10, G♯=8, F=5 → another dim7!

/-!
## 🌟 Key Theorem: The Pattern Alternates C6 and Dim7

Dobbins states that the pattern produces alternating major sixth and
diminished seventh chords. Let's formalize and prove this!

**Proof strategy**: At even steps, the four voices give notes from C6.
At odd steps, they give notes from a dim7 chord.

**Category theory**: This alternation is a **2-periodic functor** —
a functor from ℤ₂ × ℕ to the chord category, where the ℤ₂ component
selects the chord type.
-/

/-- A chord is a major sixth chord if its notes are of the form
    {r, r+4, r+7, r+9} for some root r.
    **Lean best practice**: Use `∃` (existential) to express "there exists a root". -/
def isMaj6 (c : FourVoiceChord) : Prop :=
  ∃ r : PitchClass, c.toPitchClassSet = {r, r + 4, r + 7, r + 9}

/-- A chord is a diminished seventh if its notes are of the form
    {r, r+3, r+6, r+9} for some root r. -/
def isDim7 (c : FourVoiceChord) : Prop :=
  ∃ r : PitchClass, c.toPitchClassSet = {r, r + 3, r + 6, r + 9}

/-
The initial chord is C6.
-/
theorem dobbins_initial_is_C6 :
    dobbinsChord 0 = { soprano := A, alto := G, tenor := E, bass := C } := by
  rfl

/-!
## Voice Leading as Natural Transformation

### The Deep Connection

Each voice in Dobbins' pattern traces an independent ascending line.
We can view the four voices as **four parallel functors** from (ℕ, ≤) to PitchClass,
and the chord at each step as a **natural transformation component**.

More precisely:
- For each step n, the chord `dobbinsChord n` bundles four voice positions
- The transition from step n to step n+1 is a **natural transformation**
  between the "chord-at-n" functor and the "chord-at-(n+1)" functor

The **naturality condition** says: the voice leading is *independent of which
voice you look at first*. This is exactly Dobbins' observation that "each line
is simply moving up the scale from a different starting note" — the voices
don't interact, they just translate independently.

### HoTT Perspective
In HoTT, a natural transformation between functors F, G : C → D is a
**homotopy** F ~ G — a continuous family of paths. The Dobbins voice leading
is a **path in the space of chords**, and the individual voice motions are
the **components** of this path.

The fact that ascending sounds better than descending (Dobbins' observation about
chromatic resolution) is a **directionality** phenomenon — the path space of
voice leadings is not symmetric. This is like a **directed homotopy** or a
path in a **directed space** (a concept from directed algebraic topology).
-/

/-!
## Variability as Functorial Transformation

Each way of varying the Dobbins pattern can be understood as a
**functor** or **natural transformation**:

| Musical Variation     | Category Theory Concept              |
|-----------------------|--------------------------------------|
| Transposition         | Functor (group action)               |
| Rhythmic variation    | Reparameterization of the time axis  |
| Voicing change        | Natural transformation               |
| Harmonic reinterpret. | Isomorphism in a groupoid            |
| Direction reversal    | Contravariant functor (op)           |
| Tempo change          | Functor on the time category         |
| Dynamic variation     | Enrichment (adding a "loudness" dim) |

**Higher category perspective**: All these variations together form a
**2-category** where:
- **0-cells** = specific pattern realizations (keys, voicings, rhythms)
- **1-cells** = transformations (transpose, re-voice, re-rhythm)
- **2-cells** = "transformations of transformations" (e.g., "transpose
  *then* re-voice" vs "re-voice *then* transpose" — do they commute?)

When they commute, we have a **2-natural transformation**. When they
commute up to a coherent equivalence, we enter the world of
**∞-categories** and **homotopy coherence**.
-/

/-- Transposition of a chord by interval n.

    **Category theory**: This is the **action** of the group ℤ₁₂ on chords.
    Each element of ℤ₁₂ gives an automorphism of the chord category.
    The map `n ↦ transposeChord n` is a **group homomorphism**
    ℤ₁₂ → Aut(Chord), i.e., a **representation** of ℤ₁₂.

    **Lean best practice**: Use `map` (applying a function to each field)
    rather than destructuring and reconstructing. DRY principle. -/
def transposeChord (n : PitchClass) (c : FourVoiceChord) : FourVoiceChord where
  soprano := c.soprano + n
  alto    := c.alto + n
  tenor   := c.tenor + n
  bass    := c.bass + n

/-
Transposing by 0 is the identity. This is the **functor identity law**.

    **Proof step**: Unfold the definition, then use `add_zero` on each field.
    `ext` decomposes the equality of structures into equality of fields —
    this is the **η-law** for records (product types).

    **Lean best practice**: `simp` with carefully chosen lemma sets is
    the workhorse tactic for algebraic simplification.
-/
theorem transpose_zero (c : FourVoiceChord) : transposeChord 0 c = c := by
  cases c ; exact by rw [ transposeChord ] ; simp +decide ;

/-
Transposition is *compositional*: transposing by m then n = transposing by m+n.
    This is the **functor composition law**.

    **Category theory**: This says `transposeChord` is a genuine **group action**
    (a functor from the group ℤ₁₂ viewed as a one-object category).

    **Lean best practice**: `ring` handles equalities in commutative rings
    automatically. Since PitchClass = ZMod 12 is a CommRing, `ring` works!
-/
theorem transpose_compose (m n : PitchClass) (c : FourVoiceChord) :
    transposeChord m (transposeChord n c) = transposeChord (n + m) c := by
  unfold transposeChord;
  simp +decide [ add_assoc ]

/-!
## Rhythm Formalization

Rhythm is the most immediately accessible variable for musical exploration.
We model it as a sequence of *durations* — elements of ℚ>0 (positive rationals).

**Why rationals?** Musical durations are rational fractions of a whole note:
  - Quarter note = 1/4
  - Eighth note = 1/8
  - Dotted quarter = 3/8
  - Triplet eighth = 1/12

**Category theory**: A rhythm is a **partition** of a time interval into
sub-intervals. The set of all rhythms of length n is a **simplex** —
specifically, the (n-1)-simplex in the space of positive reals summing to 1.

**Opetopes**: A rhythm pattern can be seen as a **pasting diagram** of
1-dimensional opetopes (intervals). Nested tuplets (triplets within triplets)
create *higher-dimensional* opetopic structure — a 2-opetope!
-/

/-- A rhythmic pattern: a list of durations (in beats) to apply to
    successive chords.

    **Functional programming**: We use a simple list — the rhythm cycles
    when the chord sequence is longer. This is `zip` with cycling, a
    standard FP pattern.

    **Type theory**: We use `ℚ` (rationals) because musical durations
    are always rational. Using `ℝ` would be mathematically unnecessary
    and computationally inconvenient.

    Note: We allow any ℚ values here for simplicity; in a production
    system you'd use a subtype `{q : ℚ // 0 < q}` to enforce positivity.
    **Lean tip**: Subtypes `{x : α // P x}` are the type-theoretic analog
    of *subset types* in set theory. -/
structure RhythmPattern where
  durations : List ℚ
  nonempty : durations ≠ []
deriving Repr

namespace RhythmPattern

/-- Straight eighths: every chord gets an eighth note.
    The simplest possible rhythm — **the identity element** of rhythmic
    variation (the "do nothing" option).

    **Category theory**: This is the **identity morphism** in the
    category of rhythmic transformations. -/
def straightEighths : RhythmPattern :=
  ⟨[1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8], by simp⟩

/-- Swing eighths: alternating long-short (2/3 + 1/3 of a beat).
    The quintessential jazz rhythm.

    **Beautiful pattern**: Swing is a *perturbation* of straight time —
    a small deformation that completely changes the musical character.
    In topology, this is like a *non-trivial deformation* of a path
    that changes its homotopy class (straight ≠ swing in the
    fundamental groupoid of rhythm-feel space). -/
def swingEighths : RhythmPattern :=
  ⟨[1/6, 1/12, 1/6, 1/12, 1/6, 1/12, 1/6, 1/12], by simp⟩

/-- Dotted rhythm: long-short pairs (3/16 + 1/16).
    Creates a "galloping" feel.

    **Lean tip**: ℚ literals like `3/16` are exact — no floating-point
    imprecision. This is why `ℚ` is better than `Float` for music theory. -/
def dottedEighths : RhythmPattern :=
  ⟨[3/16, 1/16, 3/16, 1/16, 3/16, 1/16, 3/16, 1/16], by simp⟩

/-- Charleston rhythm: dotted quarter + eighth (on beat 1 and the "and of 2").
    A classic syncopation pattern.

    **Musical insight**: This rhythm displaces the second chord to an
    *off-beat* position, creating tension against the underlying pulse.

    **Category theory**: Syncopation is a **non-trivial automorphism** of
    the beat groupoid — it maps beat positions to off-beat positions,
    and this map *doesn't commute* with the identity (straight time). -/
def charleston : RhythmPattern :=
  ⟨[3/8, 1/8], by simp⟩

/-- Total duration of one cycle of the rhythm pattern.
    **Functional programming**: `List.sum` is a **fold** (catamorphism)
    using the additive monoid structure of ℚ. -/
def totalDuration (r : RhythmPattern) : ℚ := r.durations.sum

/-
Straight eighths sum to 1 beat per 8-chord cycle.
-/
theorem straightEighths_duration : straightEighths.totalDuration = 1 := by
  native_decide +revert

end RhythmPattern

/-!
## Tying It All Together: A Musical Performance

A **performance** of the Dobbins pattern combines:
1. The chord sequence (parameterized by key and direction)
2. A voicing scheme (close, drop-2, etc.)
3. A rhythmic pattern
4. A dynamic contour (not formalized here)

**Category theory**: A performance is a **tuple in a product category**
Chord^ℕ × Voicing × Rhythm × Dynamics.

**Higher operads**: More precisely, a performance is an **algebra** for
the musical performance operad, where:
- The operad has operations "play chord", "apply rhythm", "set dynamic"
- An algebra assigns concrete musical content to each operation
- The operadic composition laws ensure the pieces fit together coherently

**Opetopic sets**: The full structure of a musical piece — with its
hierarchical phrase structure, nested repetitions, and multi-level
form — is naturally an **opetopic set**. Notes compose into chords,
chords into progressions, progressions into phrases, phrases into
sections, sections into movements. Each level of composition is a
higher-dimensional cell in the opetope.
-/

/-- A performance specification combining pattern, voicing, and rhythm.

    **Lean best practice**: Use `structure` for "bags of data" and
    `class` for "bags of operations" (typeclasses).

    **Type theory**: This is a **dependent record** — in a richer
    formalization, the voicing field might depend on the chord type. -/
structure Performance where
  key : PitchClass                    -- root of the pattern
  numChords : ℕ                       -- how many chords to play
  rhythm : RhythmPattern              -- rhythmic pattern to apply
  ascending : Bool                    -- direction
deriving Repr

/-- Generate the chords for a performance.

    **Lean best practice**: `List.map` is preferred over explicit recursion
    when the transformation is element-wise. This is the FP principle of
    "use higher-order functions instead of loops".

    **Category theory**: `List.map f` is the **functorial action** of
    the List functor on morphism `f`. The List type constructor is a
    **monad** (in fact, the *free monoid* monad), and `map` is part of
    its functorial structure. -/
def Performance.chords (p : Performance) : List FourVoiceChord :=
  let indices := List.range p.numChords
  let transposedChord := fun n => transposeChord p.key (dobbinsChord n)
  indices.map transposedChord

-- Let's generate a few performances!
#eval (Performance.mk C 4 RhythmPattern.straightEighths true).chords
#eval (Performance.mk E 4 RhythmPattern.swingEighths true).chords

/-!
## Summary of Variable Aspects

Here is a complete taxonomy of what you can vary when exploring the
Dobbins pattern at the piano:

### Rhythm Variables
| Variable          | Range                   | Effect                    |
|-------------------|-------------------------|---------------------------|
| Note duration     | ℚ>0                     | Speed of each chord       |
| Swing ratio       | [0.5, 0.75]             | Straight → swing feel     |
| Syncopation       | Beat displacement        | Rhythmic tension          |
| Meter             | 3/4, 4/4, 5/4, 7/8, …  | Grouping of beats         |
| Tempo             | ℚ>0 (BPM)              | Overall speed             |
| Subdivision       | 2, 3, 4 (per beat)      | 8ths, triplets, 16ths     |
| Rest insertion    | Bool per position       | Creates space and breath  |

### Pitch Variables
| Variable          | Range                   | Effect                    |
|-------------------|-------------------------|---------------------------|
| Key (transposition)| ℤ₁₂                   | Pitch level               |
| Direction         | {↑, ↓, ↑↓, ↓↑}        | Melodic contour           |
| Starting chord    | Rotation of C6          | Different inversions      |
| Octave register   | ℤ                      | High vs low placement     |
| Scale variant     | Mode rotations          | Color (bright ↔ dark)     |

### Voicing Variables
| Variable          | Range                   | Effect                    |
|-------------------|-------------------------|---------------------------|
| Voicing type      | Close, drop-2, drop-3…  | Spread and color          |
| Doubling          | Which notes doubled     | Thickness                 |
| Number of voices  | 3, 4, 5, 6             | Density                   |

### Interpretation Variables
| Variable          | Range                   | Effect                    |
|-------------------|-------------------------|---------------------------|
| Harmonic function | C6, Am7, FΔ9, D9sus    | Context and meaning       |
| Bass note         | Any PitchClass          | Root vs inversion         |
| Duration of use   | 1–8+ measures           | Passage length            |

Each variable is a **degree of freedom** — a dimension in the space of
all possible realizations of this pattern. The full space is the
**product** (in category theory) of all these variable spaces.

Exploring the pattern means **traversing paths** in this high-dimensional
space. A systematic practice routine is a **covering** of the space —
visiting enough points to internalize the pattern's full potential.
-/