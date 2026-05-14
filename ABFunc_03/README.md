This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# AB/APN Functions via Topos Theory — Lean 4 Formalization

A Lean 4 formalization of Almost Bent (AB) and Almost Perfect Nonlinear (APN)
functions using category theory and topos theory, with connections to coding
theory and spectral analysis.

## Project Structure

```
ABTopos/
├── Foundation/           ← Core topos and categorical structures
│   ├── ElemTopos.lean        Elementary topos, group objects, AB category
│   └── TypeTopos.lean        Boolean topos (Type), finite group instantiations
├── Spectral/             ← Spectral theory and Walsh analysis
│   ├── SpectralObject.lean   Spectral objects, Postnikov construction
│   ├── KasamiCollapse.lean   Kasami spectral data, three-valued collapse
│   ├── KasamiCIC.lean        CIC-style self-contained Kasami formalization
│   └── WalshGauss.lean       Walsh/Gauss sums over finite fields (WIP)
├── CodingTheory/         ← Binary linear codes and weight enumerators
│   └── BinaryCode.lean       κ_m formula, Pless moments, Kerdock correspondence
├── Bridge/               ← Bridge theorems and duality
│   ├── PNBoolean.lean        PN–Boolean relatives bridge
│   ├── Duality.lean          Categorical duality (kBent ↔ kCoBent, MacWilliams)
│   └── RosettaStone.lean     Spectral-topos-coding Rosetta Stone theorem
├── Category/             ← Extended category structures
│   └── APNFunctions.lean     APN function category, conjectures, k-uniform
├── Candidates/           ← AB/APN function candidates and verification
│   ├── RigidityDetector.lean 10-point rigidity screening protocol
│   ├── ABCandidates.lean     10 AB function candidates
│   ├── RigidCandidates.lean  20 rigidity-certified candidates
│   ├── KasamiInduction.lean  Coulter-Matthews AB by induction
│   └── Discovery.lean        Pipeline integration
├── Conjectures/          ← Open conjectures
│   ├── APN.lean              APN conjectures (differential image, designs, etc.)
│   ├── NewAB.lean            10 new AB function conjectures
│   └── NewAPN.lean           New APN conjectures
└── Tests/                ← Verification and sanity checks
    ├── Sanity.lean           10 structural sanity checks
    └── CategoryTheory.lean   Category theory verification tests
```

## Key Results

See [ANALYSIS.md](ANALYSIS.md) for a detailed assessment of formalization quality,
including which results are genuinely proven vs. definitional, and specific
recommendations for strengthening the formalization.

## Building

```bash
lake build
```

Requires Lean 4.28.0 with Mathlib v4.28.0.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).
