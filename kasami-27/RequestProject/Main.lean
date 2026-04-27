/-
# Kasami Function: Almost Bent Proof Assembly

This project formalizes the proof that the Kasami power function is Almost Bent.
See ARCHITECTURE.md for the full decomposition into tiny lemmas and their status.
See ASSEMBLY_REPORT.md for which lemmas are formalized vs sorry'd.
-/

-- Layer 0: Field and Trace Infrastructure
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter

-- Layer 1: Kasami Exponent
import RequestProject.Kasami.KasamiExponent

-- Layer 2-3: CCD Factorization and Helpers
import RequestProject.Kasami.CCDFactorization
import RequestProject.Kasami.CCDHelpers

-- Linearized Polynomial Theory (Layer 3)
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel
import RequestProject.LinearizedPoly.KasamiKernel
import RequestProject.LinearizedPoly.ArtinSchreier

-- Quadratic Form Theory over GF(2) (Layer 4)
import RequestProject.QuadFormGF2.Defs
import RequestProject.QuadFormGF2.GaussSum
import RequestProject.QuadFormGF2.Kasami

-- Walsh-Hadamard Transform
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiFunction

-- Fourth Moment and Autocorrelation
import RequestProject.Kasami.FourthMoment

-- Difference Set and Triple Count
import RequestProject.Kasami.DifferenceSet
import RequestProject.Kasami.TripleCount
import RequestProject.Kasami.KasamiP3
import RequestProject.Kasami.DualP3

-- APN and Vanishing Infrastructure
import RequestProject.Kasami.APNFromAB
import RequestProject.Kasami.VanishingProof

-- Bridge: Quadratic Form ↔ WHT (the key missing connections)
import RequestProject.Kasami.QuadFormBridge
