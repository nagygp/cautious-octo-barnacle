/-
# Kasami Almost Bent Proof — Assembled Project

This project assembles all formalized and partially-formalized components
for proving that the Kasami function is Almost Bent (AB).

See KASAMI_AB_MODULARIZATION.md for the full proof architecture.
See ASSEMBLY_REPORT.md for which lemmas are formalized vs sorry'd.
-/

-- Layer 0: Field and Trace Infrastructure
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter

-- Layer 1: Kasami Exponent
import RequestProject.Kasami.KasamiExponent

-- Layer 2-3: Quadratic Forms and Linearized Polynomials
import RequestProject.QuadFormGF2.Defs
import RequestProject.QuadFormGF2.GaussSum
import RequestProject.QuadFormGF2.Kasami
import RequestProject.LinearizedPoly.Defs
import RequestProject.LinearizedPoly.Kernel
import RequestProject.LinearizedPoly.KasamiKernel
import RequestProject.LinearizedPoly.ArtinSchreier

-- Layer 4-5: Walsh-Hadamard, Almost Bent, Assembly
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.CCDFactorization
import RequestProject.Kasami.CCDHelpers
import RequestProject.Kasami.DifferenceSet
import RequestProject.Kasami.TripleCount
import RequestProject.Kasami.VanishingProof
import RequestProject.Kasami.KasamiP3
import RequestProject.Kasami.APNFromAB
import RequestProject.Kasami.DualP3
