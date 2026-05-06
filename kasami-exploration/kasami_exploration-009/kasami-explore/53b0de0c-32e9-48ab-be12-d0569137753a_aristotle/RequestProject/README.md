# Dobbins Harmonization Pattern — Lean Formalization

## Project Structure

- **`PitchClass.lean`** — Pitch classes as ℤ/12ℤ, intervals, scales, transposition
- **`Chords.lean`** — Four-voice chords, voicings, chord functions, reinterpretation groupoid
- **`DobbinsPattern.lean`** — The ascending pattern, variability taxonomy, rhythm, performance

## Proven Theorems (all sorry-free, machine-verified)

| Theorem | Statement |
|---------|-----------|
| `C6_eq_Am7_pitchClasses` | C major 6 and A minor 7 share the same pitch-class set |
| `dim7_symmetric` | C♯dim7 = Edim7 (diminished 7th chords are symmetric under minor 3rds) |
| `dobbins_initial_is_C6` | The first chord in the pattern is C6 (A G E C) |
| `transpose_zero` | Transposing by 0 is the identity (functor identity law) |
| `transpose_compose` | Transposition composes: T_m ∘ T_n = T_{n+m} (functor composition law) |
| `straightEighths_duration` | Eight straight eighths sum to 1 beat |

## Musical Variability (see DobbinsPattern.lean for full details)

Eight categories of variation are documented with category-theoretic interpretations:

1. **Rhythm** — swing, dotted, syncopation, hemiola, rubato, displacement
2. **Voicing** — close, drop-2, drop-3, spread
3. **Direction** — ascending, descending, arch, zigzag
4. **Harmonic reinterpretation** — C6 = Am7 = FΔ9 = D9sus
5. **Transposition** — all 12 keys, cycle of 4ths, chromatic, minor 3rds
6. **Texture** — block, arpeggiated, broken, stride, Alberti
7. **Dynamics/articulation** — crescendo, staccato, legato, accents
8. **Tempo** — ballad to up-tempo

## Mathematical Connections (annotated throughout the code)

- **Category Theory**: Chords as products, transposition as group action/functor, voice leading as natural transformation, reinterpretation as groupoid isomorphism
- **Type Theory**: ZMod 12 as quotient type, structures as Σ-types, inductive types as initial algebras, pattern matching as catamorphism
- **HoTT**: Pitch space ℤ as universal cover of ℤ₁₂, delooping Bℤ₁₂, directed homotopy for voice leading asymmetry
- **Higher Categories**: Scale nerve as simplicial set, variability as 2-category, performance as ∞-categorical composition
- **Operads & Opetopes**: Chord voicing as operadic composition, voices as corolla leaves, hierarchical musical structure as opetopic set
