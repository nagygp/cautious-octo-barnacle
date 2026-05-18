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

-- Layer 1.5: Characteristic 2 Algebra
import RequestProject.Kasami.Char2Algebra

-- Layer 2: Quadratic Forms and Gold-Kasami Bridge
import RequestProject.QuadFormGF2.Defs
import RequestProject.QuadFormGF2.GaussSum
import RequestProject.QuadFormGF2.Kasami
import RequestProject.Kasami.QuadFormBridge

-- Layer 3: Linearized Polynomials
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

-- Power function APN theory
import RequestProject.Kasami.PowerAPN
import RequestProject.Kasami.PowerFnAB

-- CCD-Gold Bridge
import RequestProject.Kasami.CCDGoldBridge

-- Frobenius Adjoint infrastructure
import RequestProject.Kasami.FrobeniusAdjoint

-- Radical Cardinality helpers
import RequestProject.Kasami.RadicalCard

-- Decomposition of the 3 remaining sorries
import RequestProject.Kasami.KasamiNormIdentity
import RequestProject.Kasami.ABVanishing
import RequestProject.Kasami.KasamiABProof
import RequestProject.Kasami.GammaIndicator
import RequestProject.Kasami.GoldAB

-- Correct decomposition of kasami_is_ab
import RequestProject.Kasami.KasamiABDecomposition
